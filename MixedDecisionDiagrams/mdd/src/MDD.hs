{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE InstanceSigs #-}
module MDD where

import Debug.Trace ( trace )
import Data.Hashable
import qualified Data.HashMap.Strict as HashMap
import Control.Monad.State
-- proof of concept GenDDs where no merging of isomorphic nodes happen and no cashing / moization of results during traversal.
-- GenDDs can model check second order logic formulas containing variables in multiple (disjointed and/or nested) infinite domains.


-- |======================================== Data Types + Explanation ==============================================

type NodeId = Int


data Inf = Dc | Neg1 | Neg0 | Pos1 | Pos0
    deriving (Eq, Show)

data Dd =  Node Int NodeId NodeId               -- left = pos, right = neg
                | InfNodes Int NodeId NodeId NodeId NodeId NodeId    -- sets the inference type when traversing through the tree depending which literal type is inf. We place them at the top (of each sub path of infinite domain). We can have multiple branches due to the multiple possible contexts.
                | EndInfNode NodeId
                | Leaf Bool
    deriving (Eq)


instance Hashable Dd where
  hash :: Dd -> Int
  hash (Leaf b) = if b then 1 else 0
  hash (Node idx l r) = idx `hashWithSalt` l `hashWithSalt` r
  hash (InfNodes idx dc n1 n0 p1 p0) = idx `hashWithSalt` dc `hashWithSalt` n1 `hashWithSalt` n0 `hashWithSalt` p1 `hashWithSalt` p0
  hash (EndInfNode d) = d `hashWithSalt` (2::Int)
  hashWithSalt :: Int -> Dd -> Int
  hashWithSalt _ (Leaf b) = if b then 1 else 0
  hashWithSalt s (Node idx l r) = s `hashWithSalt` idx `hashWithSalt` l `hashWithSalt` r
  hashWithSalt s (InfNodes idx dc n1 n0 p1 p0) = s `hashWithSalt` idx `hashWithSalt` dc `hashWithSalt` n1 `hashWithSalt` n0 `hashWithSalt` p1 `hashWithSalt` p0
  hashWithSalt s (EndInfNode d) = s `hashWithSalt` d `hashWithSalt` (2::Int)

data Context = Context {
  nodelookup :: NodeLookup,
  cache :: Cache,
  cache_ :: SingleCache,
  func_context :: [(Inf, FType)]
}

data FType = Union | Inter | MixedIntersection | MixedUnion | Absorb | Remove | T_and_r
    deriving (Eq, Show)


type NodeLookup =  HashMap.HashMap NodeId (NodeId, Dd)
type Cache =  HashMap.HashMap (NodeId, NodeId) Dd
type SingleCache =  HashMap.HashMap NodeId Dd

getDd :: NodeId -> State Context Dd
getDd nodeId = state $ \c@Context{nodelookup = nm} -> (case HashMap.lookup nodeId nm of
       Just result -> snd result
       Nothing -> error $ "Node adress "++ show nodeId ++" without Node in NodeLookup table/map"
          , c)

-- | gets the nodeid from child node to apply function on, then stores the result
traverse :: (Dd -> State Context Dd) -> NodeId -> State Context NodeId
traverse f nodeId = do
  dd <- getDd nodeId
  resultDd <- f dd
  auto_insert resultDd


merge_rule :: (Dd -> Dd -> State Context Dd) -> Dd -> Dd -> State Context NodeId
merge_rule f a b = do
  result <- f a b
  auto_insert result

merge_rule_ :: (Dd -> State Context Dd) -> Dd -> State Context NodeId
merge_rule_ f dd = do
  result <- f dd
  auto_insert result


elim_rules_ :: (Dd -> State Context Dd) -> Dd -> State Context NodeId
elim_rules_ f dd = do
  -- Apply the transformation function to dd within the State monad
  result <- f dd
  -- Calculate the hash of the result for use as the key in the insert operation
  let key = hash result
  -- Insert the result into the context and get back the nodeId (or key)
  insert key result

-- merge_rule_ :: (Context -> Dd -> (Context, Dd)) -> Context -> Dd -> (Context, NodeId)
-- merge_rule_ f c a = let
--   (rc, result) = f c a
--   (new_id, c') =  insert (hash result) result rc
--   in (c', new_id)

auto_insert :: Dd -> State Context NodeId
auto_insert a = do
  let key = hash a `debug` ("auto_insert " ++ show (hash a))
  -- Use the previously refactored insert logic, now directly within the State monad
  insert key a

-- A higher-order function for handling cache lookup and update
withCache :: Dd -> Dd -> (Dd -> Dd -> State Context Dd) -> State Context Dd
withCache ddA ddB computation = do  -- Assume hashDd is a function that computes a hash for a Dd
  let key = (hash ddA, hash ddB)
  ctx <- get  -- Get the current context
  case HashMap.lookup key (cache ctx) of
    Just result -> return result
    Nothing -> do
      result <- computation ddA ddB
      modify (\c -> c {cache = HashMap.insert key result (cache c)})
      return result

-- withCache_ adapted for State Monad
withCache_ :: Dd -> (Dd -> State Context Dd) -> State Context Dd
withCache_ dd computation = do
  let key = hash dd
  ctx <- get  -- Get the current context
  case HashMap.lookup key (cache_ ctx) of
    Just result -> return result  -- If result is in cache, return it
    Nothing -> do
      result <- computation dd  -- Perform the computation with dd if not in cache
      modify (\c -> c { cache_ = HashMap.insert key result (cache_ c) })  -- Update the cache
      return result


-- Refactored insert function to use State Monad
insert :: NodeId -> Dd -> State Context NodeId
insert k v = do
  c <- get -- Get the current context
  let nm = nodelookup c
  case HashMap.lookup k nm of
    Just result ->
      if v == snd result
      then return k -- Return existing key without change
      else if fst result == 0
           then do
             let k' = getFreeKey nm
             modify (\c -> c { nodelookup = HashMap.insert k (k', snd result) nm })
             insert k' v -- Recursive call with new key
           else insert (fst result) v -- Recursive call with existing forwarding address
    Nothing -> do
      let newKey = getFreeKey nm -- Assuming getFreeKey generates a unique key
      modify (\c -> c { nodelookup = HashMap.insert k (newKey, v) nm })
      return newKey -- Return the new key


getFreeKey :: HashMap.HashMap Int v -> Int
getFreeKey nm
  | HashMap.null nm = 1
  | otherwise = head [x | x <- [1..n+1], not (HashMap.member x nm)]
  where
    n = HashMap.size nm

remove :: NodeId -> Context -> Context
remove i c@Context{nodelookup = nm} = c{nodelookup = HashMap.delete i nm}


top :: Dd
top = Leaf True

bot :: Dd
bot = Leaf False



-- At the variable class given represented by the ordinal, create a path containing the specified nodes from the list with the given inference rule.
-- We assume fixed variable classes, it is the responsibility of the user to give the correct ordinal
-- give empty list to create empty ZDD, e.g. : makePath (Order [1,2]) [] Neg1

-- For making paths that take multiple Infnodes through finite types.
-- used for e.g. [2::Neg1, 1::Neg1, 3::Neg1]
-- possible to give an empty list for the nodes to be set to positive
-- place a minus sign before a node nr to set it to negative.

data Level = L [(Int, Inf)] Int deriving (Eq, Show)

makeNode :: Level -> State Context NodeId
makeNode (L [] _) = error "empty context"
makeNode (L [(i, inf)] nodePosition) = case inf of
    Dc -> do
        rid <- loopDc nodePosition
        auto_insert $ InfNodes i rid 0 1 0 1 `debug` ("auto insert infnode " ++ show i)
    Neg1 -> do
        rid <- loopNeg nodePosition False
        auto_insert $ InfNodes i 0 rid 1 0 1 `debug` ("auto insert infnode " ++ show i)
    Neg0 -> do
        rid <- loopNeg nodePosition True
        auto_insert $ InfNodes i 1 0 rid 0 1 `debug` ("auto insert infnode " ++ show i)
    Pos1 -> do
        rid <- loopPos nodePosition False
        auto_insert $ InfNodes i 0 0 1 rid 1 `debug` ("auto insert infnode " ++ show i)
    Pos0 -> do
        rid <- loopPos nodePosition True
        auto_insert $ InfNodes i 1 0 1 0 rid `debug` ("auto insert infnode " ++ show i)
    where
        loopDc n = if n <= 0
          then auto_insert $ Node (abs n) 1 0  `debug` ("auto insert node " ++ show n)
          else auto_insert $ Node n 0 1  `debug` ("auto insert node " ++ show n)
        loopNeg n end = if n <= 0
          then auto_insert $ Leaf end
          else auto_insert $ Node n (hash $ Leaf $ not end) (hash $ Leaf end)
        loopPos n end = if n <= 0
          then auto_insert $ Leaf end
          else auto_insert $ Node n (hash $ Leaf end) (hash $ Leaf $ not end)

makeNode (L ((i, inf):cs) nodePosition) = case inf of
    Dc -> do
        rid <- makeNode (L cs nodePosition)
        auto_insert $ InfNodes i rid 0 1 0 1
    Neg1 -> do
        rid <- makeNode (L cs nodePosition)
        auto_insert $ InfNodes i 0 rid 1 0 1
    Neg0 -> do
        rid <- makeNode (L cs nodePosition)
        auto_insert $ InfNodes i 1 0 rid 0 1
    Pos1 -> do
        rid <- makeNode (L cs nodePosition)
        auto_insert $ InfNodes i 0 0 1 rid 1
    Pos0 -> do
        rid <- makeNode (L cs nodePosition)
        auto_insert $ InfNodes i 1 0 1 0 rid


debug :: a -> String -> a
debug f s = trace s f

path :: [(Int, Inf)] -> [Int] -> State Context NodeId
path = makeLocalPath


makeLocalPath :: [(Int, Inf)] -> [Int] -> State Context NodeId
makeLocalPath = makeLocalPath'

unpackEndInf :: Dd -> State Context Dd
unpackEndInf (EndInfNode d) = getDd d
unpackEndInf _ = error "not possible"
-- -- < 0:dc > 3' 4' <2: n1>

makeLocalPath' :: [(Int, Inf)] -> [Int] -> State Context NodeId
makeLocalPath' [] _ = error "empty context"
makeLocalPath' [(i, inf)] nodeList = case inf of
    Dc -> do
        rid <- loopDc nodeList False
        auto_insert $ InfNodes i rid 0 1 0 1 `debug` ("auto insert infnode " ++ show i)
    Neg1 -> do
        rid <- loopNeg nodeList False
        auto_insert $ InfNodes i 0 rid 1 0 1 `debug` ("auto insert infnode " ++ show i)
    Neg0 -> do
        rid <- loopNeg nodeList True
        auto_insert $ InfNodes i 1 0 rid 0 1 `debug` ("auto insert infnode " ++ show i)
    Pos1 -> do
        rid <- loopPos nodeList False
        auto_insert $ InfNodes i 0 0 1 rid 1 `debug` ("auto insert infnode " ++ show i)
    Pos0 -> do
        rid <- loopPos nodeList True
        auto_insert $ InfNodes i 1 0 1 0 rid `debug` ("auto insert infnode " ++ show i)
    where
        loopDc (n:ns) end = do
          r <- loopDc ns end
          if n <= 0 then auto_insert $ Node (abs n) 1 r
          else auto_insert $ Node n r 0
        loopDc [] end = return $ hash $ Leaf $ not end

        loopNeg [] end = return $ hash $ Leaf $ not end
        loopNeg (n:ns) end = do
          r <- loopNeg ns end
          if n <= 0 then auto_insert $ Node (abs n) (hash $ Leaf end) r
          else auto_insert $ Node n r (hash $ Leaf end)

        loopPos [] end = return $ hash $ Leaf $ not end
        loopPos (n:ns) end = do
          r <- loopPos ns end
          if n <= 0 then auto_insert $ Node (abs n) r (hash $ Leaf end)
          else auto_insert $ Node n (hash $ Leaf end) r

makeLocalPath' ((i, inf):ns) nodeList = do
    rid <- makeLocalPath' ns nodeList
    case inf of
        Dc -> auto_insert $ InfNodes i rid 0 1 0 1
        Neg1 -> auto_insert $ InfNodes i 0 rid 1 0 1
        Neg0 -> auto_insert $ InfNodes i 1 0 rid 0 1
        Pos1 -> auto_insert $ InfNodes i 0 0 1 rid 1
        Pos0 -> auto_insert $ InfNodes i 1 0 1 0 rid

  --  where
        -- close = (!! l) . iterate EndInfNode
-- shw :: Dd -> String
-- shw d = do
--   ctx <- get
--   -- dd <- get d
--   -- make a string from the pure ctx and dd
--   show $ DdWithLookup (nodelookup ctx) dd

-- Define a wrapper type for Dd that includes the NodeLookup
data DdWithLookup = DL NodeLookup Dd

instance Show DdWithLookup where
    show (DL nm dd) = showDDwithLookup nm dd

showDDwithLookup :: NodeLookup -> Dd -> String
showDDwithLookup nm (Leaf True) = "1"
showDDwithLookup nm (Leaf False) = "0"
showDDwithLookup nm (EndInfNode d) = " <> " ++ showDDwithLookup nm (getDd_ nm d)
showDDwithLookup nm (Node a l r) = " " ++ showDDwithLookup nm (getDd_ nm a) ++ " (" ++ showDDwithLookup nm (getDd_ nm l) ++ ") (" ++ showDDwithLookup nm (getDd_ nm r) ++ ")"
showDDwithLookup nm (InfNodes a dc 0 1 0 1) = " " ++ showDDwithLookup nm (getDd_ nm a) ++ " ( dc: " ++ showDDwithLookup nm (getDd_ nm dc) ++ " )"

showDDwithLookup nm (InfNodes a dc 0 1 0 p0) = " " ++ showDDwithLookup nm (getDd_ nm a) ++ " ( dc: " ++ showDDwithLookup nm (getDd_ nm dc) ++ " ) ( p0: " ++ showDDwithLookup nm (getDd_ nm p0) ++ " )"
showDDwithLookup nm (InfNodes a dc 0 1 p1 1) = " " ++ showDDwithLookup nm (getDd_ nm a) ++ " ( dc: " ++ showDDwithLookup nm (getDd_ nm dc) ++ " ) ( p1: " ++ showDDwithLookup nm (getDd_ nm p1) ++ " )"
showDDwithLookup nm (InfNodes a dc 0 n0 0 1) = " " ++ showDDwithLookup nm (getDd_ nm a) ++ " ( dc: " ++ showDDwithLookup nm (getDd_ nm dc) ++ " ) ( n0: " ++ showDDwithLookup nm (getDd_ nm n0) ++ " )"
showDDwithLookup nm (InfNodes a dc n1 1 0 1) = " " ++ showDDwithLookup nm (getDd_ nm a) ++ " ( dc: " ++ showDDwithLookup nm (getDd_ nm dc) ++ " ) ( n1: " ++ showDDwithLookup nm (getDd_ nm n1) ++ " )"

showDDwithLookup nm (InfNodes a dc 0 1 p1 p0) = " " ++ showDDwithLookup nm (getDd_ nm a) ++ " ( dc: " ++ showDDwithLookup nm (getDd_ nm dc) ++ " ) ( p1: " ++ showDDwithLookup nm (getDd_ nm p1) ++ " ) ( p0: " ++ showDDwithLookup nm (getDd_ nm p0) ++ " )"
showDDwithLookup nm (InfNodes a dc 0 n0 0 p0) = " " ++ showDDwithLookup nm (getDd_ nm a) ++ " ( dc: " ++ showDDwithLookup nm (getDd_ nm dc) ++ " ) ( n0: " ++ showDDwithLookup nm (getDd_ nm n0) ++ " ) ( p0: " ++ showDDwithLookup nm (getDd_ nm p0) ++ " )"
showDDwithLookup nm (InfNodes a dc 0 n0 p1 1) = " " ++ showDDwithLookup nm (getDd_ nm a) ++ " ( dc: " ++ showDDwithLookup nm (getDd_ nm dc) ++ " ) ( n0: " ++ showDDwithLookup nm (getDd_ nm n0) ++ " ) ( p1: " ++ showDDwithLookup nm (getDd_ nm p1) ++ " )"
showDDwithLookup nm (InfNodes a dc n1 1 0 p0) = " " ++ showDDwithLookup nm (getDd_ nm a) ++ " ( dc: " ++ showDDwithLookup nm (getDd_ nm dc) ++ " ) ( n1: " ++ showDDwithLookup nm (getDd_ nm n1) ++ " ) ( p0: " ++ showDDwithLookup nm (getDd_ nm p0) ++ " )"
showDDwithLookup nm (InfNodes a dc n1 1 p1 1) = " " ++ showDDwithLookup nm (getDd_ nm a) ++ " ( dc: " ++ showDDwithLookup nm (getDd_ nm dc) ++ " ) ( n1: " ++ showDDwithLookup nm (getDd_ nm n1) ++ " ) ( p1: " ++ showDDwithLookup nm (getDd_ nm p1) ++ " )"
showDDwithLookup nm (InfNodes a dc n1 n0 0 1) = " " ++ showDDwithLookup nm (getDd_ nm a) ++ " ( dc: " ++ showDDwithLookup nm (getDd_ nm dc) ++ " ) ( n1: " ++ showDDwithLookup nm (getDd_ nm n1) ++ " ) ( n0: " ++ showDDwithLookup nm (getDd_ nm n0) ++ " )"

showDDwithLookup nm (InfNodes a dc 0 n0 p1 p0) = " " ++ showDDwithLookup nm (getDd_ nm a) ++ " ( dc: " ++ showDDwithLookup nm (getDd_ nm dc) ++ " ) ( n0: " ++ showDDwithLookup nm (getDd_ nm n0) ++ " ) ( p1: " ++ showDDwithLookup nm (getDd_ nm p1) ++ " ) ( p0: " ++ showDDwithLookup nm (getDd_ nm p0) ++ " )"
showDDwithLookup nm (InfNodes a dc n1 1 p1 p0) = " " ++ showDDwithLookup nm (getDd_ nm a) ++ " ( dc: " ++ showDDwithLookup nm (getDd_ nm dc) ++ " ) ( n1: " ++ showDDwithLookup nm (getDd_ nm n1) ++ " ) ( p1: " ++ showDDwithLookup nm (getDd_ nm p1) ++ " ) ( p0: " ++ showDDwithLookup nm (getDd_ nm p0) ++ " )"
showDDwithLookup nm (InfNodes a dc n1 n0 0 p0) = " " ++ showDDwithLookup nm (getDd_ nm a) ++ " ( dc: " ++ showDDwithLookup nm (getDd_ nm dc) ++ " ) ( n1: " ++ showDDwithLookup nm (getDd_ nm n1) ++ " ) ( n0: " ++ showDDwithLookup nm (getDd_ nm n0) ++ " ) ( p0: " ++ showDDwithLookup nm (getDd_ nm p0) ++ " )"
showDDwithLookup nm (InfNodes a dc n1 n0 p1 0) = " " ++ showDDwithLookup nm (getDd_ nm a) ++ " ( dc: " ++ showDDwithLookup nm (getDd_ nm dc) ++ " ) ( n1: " ++ showDDwithLookup nm (getDd_ nm n1) ++ " ) ( n0: " ++ showDDwithLookup nm (getDd_ nm n0) ++ " ) ( p1: " ++ showDDwithLookup nm (getDd_ nm p1) ++ " )"

showDDwithLookup nm (InfNodes a dc n1 n0 p1 p0) = " " ++ showDDwithLookup nm (getDd_ nm a) ++ " ( dc: " ++ showDDwithLookup nm (getDd_ nm dc) ++ " ) ( n1: " ++ showDDwithLookup nm (getDd_ nm n1) ++ " ) ( n0: " ++ showDDwithLookup nm (getDd_ nm n0) ++ " ) ( p1: " ++ showDDwithLookup nm (getDd_ nm p1) ++ " ) ( p0: " ++ showDDwithLookup nm (getDd_ nm p0) ++ " )"

getDd_ :: NodeLookup -> NodeId -> Dd
getDd_ nm nodeId = case HashMap.lookup nodeId nm of
       Just result -> snd result
       Nothing -> error "Node adress without Node in NodeLookup table/map"