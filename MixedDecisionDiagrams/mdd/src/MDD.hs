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

data Dd' = Dd_NodeMap Dd NodeLookup
data NodeId' = Id_NodeMap NodeId NodeLookup

instance Hashable Dd where
  hash :: Dd -> NodeId
  hash (Leaf b) = if b then 1 else 0
  hash (Node idx l r) = idx `hashWithSalt` l `hashWithSalt` r
  hash (InfNodes idx dc n1 n0 p1 p0) = idx `hashWithSalt` dc `hashWithSalt` n1 `hashWithSalt` n0 `hashWithSalt` p1 `hashWithSalt` p0
  hash (EndInfNode d) = d `hashWithSalt` (2::NodeId)
  hashWithSalt :: NodeId -> Dd -> NodeId
  hashWithSalt _ (Leaf b) = if b then 1 else 0
  hashWithSalt s (Node idx l r) = s `hashWithSalt` idx `hashWithSalt` l `hashWithSalt` r
  hashWithSalt s (InfNodes idx dc n1 n0 p1 p0) = s `hashWithSalt` idx `hashWithSalt` dc `hashWithSalt` n1 `hashWithSalt` n0 `hashWithSalt` p1 `hashWithSalt` p0
  hashWithSalt s (EndInfNode d) = s `hashWithSalt` d `hashWithSalt` (2::NodeId)

data Context = Context {
  cache :: Cache,
  cache_ :: SingleCache,
  func_stack :: [(Inf, FType)]
}

data FType = Union | Inter | MixedIntersection | MixedUnion | Absorb | Remove | T_and_r
    deriving (Eq, Show)


type NodeLookup =  HashMap.HashMap NodeId (NodeId, Dd)


getDd :: NodeId' -> Dd'
getDd (Id_NodeMap node_id nm) = case HashMap.lookup node_id nm of
       Just result -> Dd_NodeMap (snd result) nm
       Nothing -> error "Node adress without Node in NodeLookup table/map"

getDd_ :: NodeId -> NodeLookup -> Dd
getDd_ node_id nm = case HashMap.lookup node_id nm of
       Just result -> snd result
       Nothing -> error "Node adress without Node in NodeLookup table/map"

merge_rule :: (Context -> Dd' -> Dd' -> (Context, Dd')) -> Context -> Dd' -> Dd' -> (Context, NodeId')
merge_rule f c a b = let
  (rc, result) = f c a b
  new_id = insert result
  in (rc, new_id)

merge_rule_ :: (Context -> Dd' -> (Context, Dd')) -> Context -> Dd' -> (Context, NodeId')
merge_rule_ f c a = let
  (rc, result) = f c a
  new_id = insert result
  in (rc, new_id)

insert :: Dd' -> NodeId'
insert (Dd_NodeMap a nm) = insert_id (hash a) a nm

insert_id :: NodeId -> Dd -> NodeLookup -> NodeId'
insert_id k v nm = case HashMap.lookup k nm of
       Just result -> if v == snd result
         then Id_NodeMap k nm -- future-todo keep track of how many nodes there are for garbage collection
         else
          if fst result == 0
            then let
              k' = getFreeKey nm
              nm' = HashMap.insert k (k', snd result) nm
              in insert_id k' v nm'
          else
             insert_id (fst result) v nm
       Nothing -> Id_NodeMap k (HashMap.insert k (getFreeKey nm, v) nm)


getFreeKey :: HashMap.HashMap NodeId v -> NodeId
getFreeKey nm
  | HashMap.null nm = 1
  | otherwise = head [x | x <- [1..n+1], not (HashMap.member x nm)]
  where
    n = HashMap.size nm

remove :: NodeId' -> NodeLookup
remove (Id_NodeMap node_id nm) = undefined
 -- todo @gpt add logic for checking whether dd is right
 -- HashMap.delete (node_id, getDd node_id) nm



-- * functions for Caching / Memoization of results during traversal

type Cache =  HashMap.HashMap (NodeId, NodeId) Dd
type SingleCache =  HashMap.HashMap NodeId Dd

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




-- * Basic construction of nodes

-- At the variable class given represented by the ordinal, create a path containing the specified nodes from the list with the given inference rule.
-- We assume fixed variable classes, it is the responsibility of the user to give the correct ordinal
-- give empty list to create empty ZDD, e.g. : makePath (Order [1,2]) [] Neg1

-- For making paths that take multiple Infnodes through finite types.
-- used for e.g. [2::Neg1, 1::Neg1, 3::Neg1]
-- possible to give an empty list for the nodes to be set to positive
-- place a minus sign before a node nr to set it to negative.

data Level = L [(Int, Inf)] Int deriving (Eq, Show)

top :: Dd
top = Leaf True

bot :: Dd
bot = Leaf False


makeNode :: Level -> NodeLookup -> NodeId'
makeNode (L [] _) _ = error "empty context"
makeNode (L [(i, inf)] nodePosition) nm
    | inf == Dc = let (Id_NodeMap rid rm) = loopDc nodePosition False in ins' (InfNodes i rid 0 1 0 1) rm
    | inf == Neg1 = let (Id_NodeMap rid rm) = loopNeg nodePosition False in ins' (InfNodes i 0 rid 1 0 1) rm
    | inf == Neg0 = let (Id_NodeMap rid rm) = loopNeg nodePosition True in ins' (InfNodes i 1 0 rid 0 1) rm
    | inf == Pos1 = let (Id_NodeMap rid rm) = loopPos nodePosition False in ins' (InfNodes i 0 0 1 rid 1) rm
    | inf == Pos0 = let (Id_NodeMap rid rm) = loopPos nodePosition True in ins' (InfNodes i 1 0 1 0 rid) rm
    where
        ins' d rm = insert $ Dd_NodeMap d rm
        ins d = insert $ Dd_NodeMap d nm
        loopDc n end = if n <=0 then ins (Node (abs n) 1 (hash $ Leaf $ not end)) else ins (Node n (hash $ Leaf $ not end) 0)
        loopNeg n end = if n <=0 then ins (Node (abs n) (hash $ Leaf end) (hash $ Leaf $ not end)) else ins (Node n (hash $ Leaf $ not end) (hash $ Leaf end))
        loopPos n end = if n <=0 then ins (Node (abs n) (hash $ Leaf $ not end) (hash $ Leaf end)) else ins (Node n (hash $ Leaf end) (hash $ Leaf $ not end))
        -- close = (!! l) . iterate EndInfNode
makeNode (L ((i, inf):cs) nodePosition) nm
    | inf == Dc = let (Id_NodeMap rid rm) = makeNode (L cs nodePosition) nm in ins' (InfNodes i rid 0 1 0 1) rm
    | inf == Neg1 = let (Id_NodeMap rid rm) = makeNode (L cs nodePosition) nm in ins' (InfNodes i 0 rid 1 0 1) rm
    | inf == Neg0 = let (Id_NodeMap rid rm) = makeNode (L cs nodePosition) nm in ins' (InfNodes i 1 0 rid 0 1) rm
    | inf == Pos1 = let (Id_NodeMap rid rm) = makeNode (L cs nodePosition) nm in ins' (InfNodes i 0 0 1 rid 1) rm
    | inf == Pos0 = let (Id_NodeMap rid rm) = makeNode (L cs nodePosition) nm in ins' (InfNodes i 1 0 1 0 rid) rm
    where
        ins' d rm = insert $ Dd_NodeMap d rm
        -- close = (!! l) . iterate EndInfNode




path :: [(Int, Inf)] -> [Int] -> NodeLookup -> NodeId'
path = makeLocalPath

makeLocalPath :: [(Int, Inf)] -> [Int] -> NodeLookup -> NodeId'
makeLocalPath = makeLocalPath'

-- unpackEndInf :: Dd -> Dd
-- unpackEndInf (EndInfNode d) = d
-- unpackEndInf _ = error "not possible"
-- < 0:dc > 3' 4' <2: n1>

makeLocalPath' :: [(Int, Inf)] -> [Int] -> NodeLookup -> NodeId'
makeLocalPath' [] _ _ = error "empty context"

makeLocalPath' [(i, inf)] nodeList nm
    | inf == Dc = let (Id_NodeMap rid rm) = loopDc nm nodeList False in ins' (InfNodes i rid 0 1 0 1) rm
    | inf == Neg1 = let (Id_NodeMap rid rm) = loopNeg nm nodeList False in ins' (InfNodes i 0 rid 1 0 1) rm
    | inf == Neg0 = let (Id_NodeMap rid rm) = loopNeg nm nodeList True in ins' (InfNodes i 1 0 rid 0 1) rm
    | inf == Pos1 = let (Id_NodeMap rid rm) = loopPos nm nodeList False in ins' (InfNodes i 0 0 1 rid 1) rm
    | inf == Pos0 = let (Id_NodeMap rid rm) = loopPos nm nodeList True in ins' (InfNodes i 1 0 1 0 rid) rm
    where
        ins' d rm = insert $ Dd_NodeMap d rm
        ins d nm'' = insert $ Dd_NodeMap d nm''
        loopDc nm_ (n:ns) end = let
          (Id_NodeMap id' nm') = loopDc nm_ ns end in
          if n <=0 then ins (Node (abs n) 1 id') nm'
          else ins (Node n id' 0) nm'
        loopDc nm_ [] end = Id_NodeMap (hash $ Leaf $ not end) nm_



        loopNeg nm_ [] end = Id_NodeMap (hash $ Leaf $ not end) nm_
        loopNeg nm_ (n:ns) end = let
          (Id_NodeMap id' nm') = loopNeg nm_ ns end in
            if n <=0 then ins (Node (abs n) (hash $ Leaf end) id') nm'
            else ins (Node n id' (hash $ Leaf end)) nm'

        loopPos nm_ [] end = Id_NodeMap (hash $ Leaf $ not end) nm_
        loopPos nm_ (n:ns) end = let
          (Id_NodeMap id' nm') = loopPos nm_ ns end in
            if n <=0 then ins (Node (abs n) id' (hash $ Leaf end)) nm'
            else ins (Node n (hash $ Leaf end) id') nm'
        -- close = (!! l) . iterate EndInfNode

makeLocalPath' ((i, inf):ns) nodeList nm
    | inf == Dc = let (Id_NodeMap rid rm) = makeLocalPath' ns nodeList nm in ins' (InfNodes i rid 0 1 0 1) rm
    | inf == Neg1 = let (Id_NodeMap rid rm) = makeLocalPath' ns nodeList nm in ins' (InfNodes i 0 rid 1 0 1) rm
    | inf == Neg0 = let (Id_NodeMap rid rm) = makeLocalPath' ns nodeList nm in ins' (InfNodes i 1 0 rid 0 1) rm
    | inf == Pos1 = let (Id_NodeMap rid rm) = makeLocalPath' ns nodeList nm in ins' (InfNodes i 0 0 1 rid 1) rm
    | inf == Pos0 = let (Id_NodeMap rid rm) = makeLocalPath' ns nodeList nm in ins' (InfNodes i 1 0 1 0 rid) rm
    where
      ins' d rm = insert $ Dd_NodeMap d rm
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
