{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module MDD.Construction where

import MDD.Types
import MDD.NodeLookup
import MDD.Traversal.Context
import Data.List (sortBy)
import Data.Ord (Down(..))
import Data.Hashable
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.Map as Map

-- | Refactored with help of AI

-- ==========================================================================================================
-- * Basic construction of nodes and paths
-- ==========================================================================================================

-- short helper functions:

leaf :: Bool -> Node
leaf b = ((hash $ Leaf b, 0), Leaf b)

leafid :: Bool -> NodeId
leafid b = (hash $ Leaf b, 0)

l0' :: Int -> NodeId
l0' b | b == 0 = l_u
      | otherwise = l_0

l1' :: Int -> NodeId
l1' b | b == 1 = l_u
      | otherwise = l_1

-- | Convert a LevelL description into a Path structure
levelLtoPath :: LevelL -> Path
levelLtoPath (Ll ((i, inf) : ns) int) = P' [(i, inf, levelLtoPath (Ll ns int))]
levelLtoPath (Ll [] int) = P'' [int]

-- | Top-level function to create a Mixed Decision Diagram node from a LevelL
makeNode :: NodeLookup -> LevelL -> MDD
makeNode nl l = path_ nl (levelLtoPath l)

-- | Main path construction logic
path :: Path -> MDD
path p = MDD $ path' (-1) (init_lookup, (l_u, Node (-5) l_u l_u)) (sortPathDesc p)

path_ :: NodeLookup -> Path -> MDD
path_ nl p = MDD $  path' (-1) (nl, (l_u, Node (-5) l_u l_u)) (sortPathDesc p)

add_path :: MDD -> Path -> MDD
add_path mdd p = let
    nl = (fst $ unMDD mdd)
    starting_default_trick_mdd = (l_u, Node (-5) l_u l_u)
    (nl', node) = path' (-1) (nl, starting_default_trick_mdd) (sortPathDesc p)
    in MDD (nl', node)


-- | Function to sort the Path data structure in a depth-first manner
-- from highest to lowest on the integers.
sortPathDesc :: Path -> Path
sortPathDesc (P'' ints) = P'' ints
sortPathDesc (P' taggedPaths) =
    let sortedInnerPaths = map (\(tag, inf, p) -> (tag, inf, sortPathDesc p)) taggedPaths
        sortedTaggedPaths = sortBy (\(tagA, _, _) (tagB, _, _) -> compare (Down tagA) (Down tagB)) sortedInnerPaths
    in P' sortedTaggedPaths

-- | Recursive path building helper
path' :: Int -> (NodeLookup, Node) -> Path -> (NodeLookup, Node)
path' b (c, n) (P' ((i, inf, P'' nodelist) : pl))
    | inf == Dc1 || inf == Dc0 = path' b (insert c' (InfNodes i rid l_u l_u)) (P' pl)
    | inf == Pos1 = path' b (insert c' (InfNodes i (l0' b) rid l_u)) (P' pl)
    | inf == Neg1 = path' b (insert c' (InfNodes i (l0' b) l_u rid)) (P' pl)
    | inf == Pos0 = path' b (insert c' (InfNodes i (l1' b) rid l_u)) (P' pl)
    | inf == Neg0 = path' b (insert c' (InfNodes i (l1' b) l_u rid)) (P' pl)
      where
        (c', (rid, _)) = localpath' (c, n) inf nodelist
path' b (c, n) (P' ((i, inf, pc) : pl))
    | inf == Dc1 || inf == Dc0 = path' b (insert cDc (InfNodes i ridDc l_u l_u)) (P' pl)
    | inf == Pos1 = path' b (insert c1 (InfNodes i (l0' b) rid1 l_u)) (P' pl)
    | inf == Neg1 = path' b (insert c1 (InfNodes i (l0' b) l_u rid1)) (P' pl)
    | inf == Pos0 = path' b (insert c0 (InfNodes i (l1' b) rid0 l_u)) (P' pl)
    | inf == Neg0 = path' b (insert c0 (InfNodes i (l1' b) l_u rid0)) (P' pl)
      where
        (c0, (rid0, _)) = path' 1 (c, n) pc
        (c1, (rid1, _)) = path' 0 (c, n) pc
        (cDc, (ridDc, _)) = path' b (c, n) pc
path' b (c, n) (P' []) = (c, n)


-- | Builds a localized path within a specific variable class domain
localpath' :: (NodeLookup, Node) -> InfL -> [Int] -> (NodeLookup, Node)
localpath' (c, n) inf nodeList
    | inf == Dc1 = loopDc c True nodeList n
    | inf == Pos1 = loopPos c True nodeList n
    | inf == Neg1 = loopNeg c True nodeList n
    | inf == Dc0 = loopDc c False nodeList n
    | inf == Pos0 = loopPos c False nodeList n
    | inf == Neg0 = loopNeg c False nodeList n
    where
        loopDc c b [] consequence = if consequence == initNode
            then (c, leaf b)
            else insert c $ EndInfNode $ fst consequence
        loopDc c b (n:ns) consequence = let
          (c', (next_iter, _)) = loopDc c b ns consequence in
            if n == 0 then
              if consequence == initNode then (c, leaf b)
                else insert c' $ EndInfNode $ fst consequence
            else if n >= 0
                  then insert c' (Node n next_iter (leafid $ not b))
                  else insert c' (Node (abs n) (leafid $ not b) next_iter)

        loopPos c b [] consequence = if consequence == initNode
            then (c, leaf b)
            else insert c $ EndInfNode $ fst consequence
        loopPos c b (n:ns) consequence = let
          (c', (next_iter, _)) = loopPos c b ns consequence in
            if n == 0  then
              if consequence == initNode then (c, leaf b)
                else insert c' $ EndInfNode $ fst consequence
            else if n >= 0
                  then insert c' (Node n next_iter l_u )
                      else insert c' (Node (abs n) l_u next_iter )

        loopNeg c b [] consequence = if consequence == initNode
            then (c, leaf b)
            else insert c $ EndInfNode $ fst consequence
        loopNeg c b (n:ns) consequence = let
          (c', (next_iter, _)) = loopNeg c b ns consequence in
            if n == 0  then
              if consequence == initNode then (c, leaf b)
                else insert c' $ EndInfNode $ fst consequence
            else if n >= 0
                  then insert c' (Node n next_iter l_u)
                      else insert c' (Node (abs n) l_u next_iter)

        initNode = (l_u, Node (-5) l_u l_u)