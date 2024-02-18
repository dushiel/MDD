{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE InstanceSigs #-}
module MDD where

import Debug.Trace ( trace )
import Data.Hashable
import qualified Data.HashMap.Strict as HashMap

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
getDd :: Context -> NodeId -> Dd
getDd Context{nodelookup = nm} node_id = case HashMap.lookup node_id nm of
       Just result -> snd result
       Nothing -> error "Node adress without Node in NodeLookup table/map"

merge_rule :: (Context -> Dd -> Dd -> (Context, Dd)) -> Context -> Dd -> Dd -> (Context, NodeId)
merge_rule f c a b = let
  (rc, result) = f c a b
  (new_id, c') = insert (hash result) result rc
  in (c', new_id)

merge_rule_ :: (Context -> Dd -> (Context, Dd)) -> Context -> Dd -> (Context, NodeId)
merge_rule_ f c a = let
  (rc, result) = f c a
  (new_id, c') =  insert (hash result) result rc
  in (c', new_id)

auto_insert :: Context -> Dd -> (Context, NodeId)
auto_insert c a = let
  (new_id, c') =  insert (hash a) a c
  in (c', new_id)
-- A higher-order function for handling cache lookup and update
withCache :: Context -> (NodeId, NodeId) -> (Context, Dd) -> (Context, Dd)
withCache c@Context { cache = nc } (keyA, keyB) func_with_args =
  case HashMap.lookup (keyA, keyB) nc of
    Just result -> (c, result)
    Nothing -> let
      (updatedContext, result) = func_with_args
      updatedCache = HashMap.insert (keyA, keyB) result nc
      in (updatedContext { cache = updatedCache }, result)

withCache_ :: Context -> NodeId -> (Context, Dd) -> (Context, Dd)
withCache_ c@Context { cache_ = nc } key func_with_args =
  case HashMap.lookup key nc of
    Just result -> (c, result)
    Nothing -> let
      (updatedContext, result) = func_with_args
      updatedCache = HashMap.insert key result nc
      in (updatedContext { cache_ = updatedCache }, result)


insert :: Int -> Dd -> Context -> (Int, Context)
insert k v c@Context{nodelookup=nm} = case HashMap.lookup k nm of
       Just result -> if v == snd result
         then (k, c) -- future-todo keep track of how many nodes there are for garbage collection
         else
          if fst result == 0
            then let
              k' = getFreeKey nm
              c' = c{nodelookup = HashMap.insert k (k', snd result) nm}
              in insert k' v c'
          else
             insert (fst result) v c
       Nothing -> (k, c{nodelookup = HashMap.insert k (getFreeKey nm, v) nm})


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


makeNode :: Context -> Level -> (Context, NodeId)
makeNode c (L [] _) = error "empty context"
makeNode c (L [(i, inf)] nodePosition)
    | inf == Dc = let (rc, rid) = auto_insert c (loopDc nodePosition False) in auto_insert rc (InfNodes i rid 0 1 0 1)
    | inf == Neg1 = let (rc, rid) = auto_insert c (loopNeg nodePosition False) in auto_insert rc (InfNodes i 0 rid 1 0 1)
    | inf == Neg0 = let (rc, rid) = auto_insert c (loopNeg nodePosition True) in auto_insert rc (InfNodes i 1 0 rid 0 1)
    | inf == Pos1 = let (rc, rid) = auto_insert c (loopPos nodePosition False) in auto_insert rc (InfNodes i 0 0 1 rid 1)
    | inf == Pos0 = let (rc, rid) = auto_insert c (loopPos nodePosition True) in auto_insert rc (InfNodes i 1 0 1 0 rid)
    where
        loopDc n end = if n <=0 then Node (abs n) 1 (hash $ Leaf $ not end) else Node n (hash $ Leaf $ not end) 0
        loopNeg n end = if n <=0 then Node (abs n) (hash $ Leaf end) (hash $ Leaf $ not end) else Node n (hash $ Leaf $ not end) (hash $ Leaf end)
        loopPos n end = if n <=0 then Node (abs n) (hash $ Leaf $ not end) (hash $ Leaf end) else Node n (hash $ Leaf end) (hash $ Leaf $ not end)
        -- close = (!! l) . iterate EndInfNode
makeNode c (L ((i, inf):cs) nodePosition)
    | inf == Dc = let (rc, rid) = makeNode c (L cs nodePosition) in auto_insert rc (InfNodes i rid 0 1 0 1)
    | inf == Neg1 = let (rc, rid) = makeNode c (L cs nodePosition) in auto_insert rc (InfNodes i 0 rid 1 0 1)
    | inf == Neg0 = let (rc, rid) = makeNode c (L cs nodePosition) in auto_insert rc (InfNodes i 1 0 rid 0 1)
    | inf == Pos1 = let (rc, rid) = makeNode c (L cs nodePosition) in auto_insert rc (InfNodes i 0 0 1 rid 1)
    | inf == Pos0 = let (rc, rid) = makeNode c (L cs nodePosition) in auto_insert rc (InfNodes i 1 0 1 0 rid)
    -- where
        -- close = (!! l) . iterate EndInfNode

path :: Context -> [(Int, Inf)] -> [Int] -> (Context, NodeId)
path = makeLocalPath


makeLocalPath :: Context -> [(Int, Inf)] -> [Int] -> (Context, NodeId)
makeLocalPath = makeLocalPath'

-- unpackEndInf :: Dd -> Dd
-- unpackEndInf (EndInfNode d) = d
-- unpackEndInf _ = error "not possible"
-- < 0:dc > 3' 4' <2: n1>

makeLocalPath' :: Context -> [(Int, Inf)] -> [Int] -> (Context, NodeId)
makeLocalPath' c [] _ = error "empty context"

makeLocalPath' c [(i, inf)] nodeList
    | inf == Dc = let (rc, rid) = loopDc c nodeList False in auto_insert rc (InfNodes i rid 0 1 0 1)
    | inf == Neg1 = let (rc, rid) = loopNeg c nodeList False in auto_insert rc (InfNodes i 0 rid 1 0 1)
    | inf == Neg0 = let (rc, rid) = loopNeg c nodeList True in auto_insert rc (InfNodes i 1 0 rid 0 1)
    | inf == Pos1 = let (rc, rid) = loopPos c nodeList False in auto_insert rc (InfNodes i 0 0 1 rid 1)
    | inf == Pos0 = let (rc, rid) = loopPos c nodeList True in auto_insert rc (InfNodes i 1 0 1 0 rid)
    where
        loopDc c (n:ns) end = let
          r = loopDc c ns end in
          if n <=0 then auto_insert (fst r) (Node (abs n) 1 (hash $ snd r))
          else auto_insert (fst r) (Node n (hash $ snd r) 0)
        loopDc c [] end = (c, hash $ Leaf $ not end)
        loopNeg c [] end = (c, hash $ Leaf $ not end)
        loopNeg c (n:ns) end = let
          r = loopNeg c ns end in
            if n <=0 then auto_insert (fst r) (Node (abs n) (hash $ Leaf end) (hash $ snd r))
            else auto_insert (fst r) (Node n (hash $ snd r) (hash $ Leaf end))
        loopPos c [] end = (c, hash $ Leaf $ not end)
        loopPos c (n:ns) end = let
          r = loopPos c ns end in
            if n <=0 then auto_insert (fst r) (Node (abs n) (hash $ snd r) (hash $ Leaf end))
            else auto_insert (fst r) (Node n (hash $ Leaf end) (hash $ snd r))
        -- close = (!! l) . iterate EndInfNode

makeLocalPath' c ((i, inf):ns) nodeList
    | inf == Dc = let (rc, rid) = makeLocalPath' c ns nodeList in auto_insert rc (InfNodes i rid 0 1 0 1)
    | inf == Neg1 = let (rc, rid) = makeLocalPath' c ns nodeList in auto_insert rc (InfNodes i 0 rid 1 0 1)
    | inf == Neg0 = let (rc, rid) = makeLocalPath' c ns nodeList in auto_insert rc (InfNodes i 1 0 rid 0 1)
    | inf == Pos1 = let (rc, rid) = makeLocalPath' c ns nodeList in auto_insert rc (InfNodes i 0 0 1 rid 1)
    | inf == Pos0 = let (rc, rid) = makeLocalPath' c ns nodeList in auto_insert rc (InfNodes i 1 0 1 0 rid)
  --  where
        -- close = (!! l) . iterate EndInfNode




instance Show Dd where
    show (Leaf True) = "1"
    show (Leaf False) = "0"
    show (EndInfNode d) = " <> " ++ show d
    show (Node a l r) = " " ++ show a ++ " (" ++ show l ++ ") (" ++ show r ++ ")"
    show (InfNodes a dc 0 1 0 1) = " " ++ show a ++ " ( dc: " ++ show dc ++ " )"

    show (InfNodes a dc 0 1 0 p0) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( p0: " ++ show p0 ++ " )"
    show (InfNodes a dc 0 1 p1 1) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( p1: " ++ show p1 ++ " )"
    show (InfNodes a dc 0 n0 0 1) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n0: " ++ show n0 ++ " )"
    show (InfNodes a dc n1 1 0 1) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n1: " ++ show n1 ++ " )"

    show (InfNodes a dc 0 1 p1 p0) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( p1: " ++ show p1 ++ " ) ( p0: " ++ show p0 ++ " )"
    show (InfNodes a dc 0 n0 0 p0) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n0: " ++ show n0 ++ " ) ( p0: " ++ show p0 ++ " )"
    show (InfNodes a dc 0 n0 p1 1) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n0: " ++ show n0 ++ " ) ( p1: " ++ show p1 ++ " )"
    show (InfNodes a dc n1 1 0 p0) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n1: " ++ show n1 ++ " ) ( p0: " ++ show p0 ++ " )"
    show (InfNodes a dc n1 1 p1 1) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n1: " ++ show n1 ++ " ) ( p1: " ++ show p1 ++ " )"
    show (InfNodes a dc n1 n0 0 1) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n1: " ++ show n1 ++ " ) ( n0: " ++ show n0 ++ " )"

    show (InfNodes a dc 0 n0 p1 p0) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n0: " ++ show n0 ++ " ) ( p1: " ++ show p1 ++ " ) ( p0: " ++ show p0 ++ " )"
    show (InfNodes a dc n1 1 p1 p0) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n1: " ++ show n1 ++ " ) ( p1: " ++ show p1 ++ " ) ( p0: " ++ show p0 ++ " )"
    show (InfNodes a dc n1 n0 0 p0) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n1: " ++ show n1 ++ " ) ( n0: " ++ show n0 ++ " ) ( p0: " ++ show p0 ++ " )"
    show (InfNodes a dc n1 n0 p1 0) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n1: " ++ show n1 ++ " ) ( n0: " ++ show n0 ++ " ) ( p1: " ++ show p1 ++ " )"

    show (InfNodes a dc n1 n0 p1 p0) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n1: " ++ show n1 ++ " ) ( n0: " ++ show n0 ++ " ) ( p1: " ++ show p1 ++ " ) ( p0: " ++ show p0 ++ " )"
