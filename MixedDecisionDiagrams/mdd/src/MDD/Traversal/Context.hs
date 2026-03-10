{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module MDD.Traversal.Context where

import MDD.Types
import MDD.NodeLookup
import Data.Hashable -- Added to bring the 'hash' function into scope
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Map as Map

-- | The distinct types of Contexts for different operations.
-- The Context is the central state manager for all MDD operations, usually existing only during a operator / traversal function call.
-- It tracks the global NodeLookup (nodelookup), operation caches,
-- and the class variable / background evaluation stacks (dc_stack) needed to resolve unknowns and absorb calls.

class HasNodeLookup a where
    getLookup :: a -> NodeLookup
    setLookup :: NodeLookup -> a -> a

instance HasNodeLookup NodeLookup where
    getLookup = id
    setLookup nl _ = nl

-- | Caching types for memoization of recursive results.
-- For Binary operations, the cache key includes both NodeIds and the current dc_stack state.
-- todo: should this also be the case for unary operations?
type Cache = Map.Map String (HashMap.HashMap (NodeId, NodeId, ([Node], [Node], [Node])) NodeId)
type SingleCache = HashMap.HashMap NodeId NodeId
type ShowCache = HashMap.HashMap NodeId [String]

-- | Context for Binary Operations (e.g., union, intersection).
-- dc_stack: Tracks the hierarchy of continuous branches as the algorithm descends into sub-classes.
-- It represents (dcA, dcB, dcR) respectively.
-- - dcR is the resulting continuous dc branch used for absorption/elimination checks.
-- - dcA and dcB are the dc components of the inputs, used to resolve Unknown leaves.
data BiOpContext = BCxt {
  bin_nodelookup :: NodeLookup,
  bin_cache :: Cache,
  bin_dc_stack :: ([Node], [Node], [Node]), -- (dcA, dcB, dcR)
  bin_current_level :: (Level', Level')
}

instance HasNodeLookup BiOpContext where
    getLookup = bin_nodelookup
    setLookup nl ctx = ctx { bin_nodelookup = nl }

-- | Context for Unary Operations (e.g., negation, draw, to_static).
-- un_dc_stack tracks dcR (resulting continuous branches) for absorption/elimination checks.
-- Unlike binary operations, unary operations don't need to track the original input's dc branches
-- since Unknown resolution is not needed (Unknown is returned as-is in unary operations).
data UnOpContext = UCxt {
  un_nodelookup :: NodeLookup,
  un_cache :: SingleCache,
  un_dc_stack :: [Node],  -- Only dcR (resulting continuous branches), no dcs needed
  un_current_level :: Level'
}

instance HasNodeLookup UnOpContext where
    getLookup = un_nodelookup
    setLookup nl ctx = ctx { un_nodelookup = nl }

-- | Context for Drawing/Printing Operations.
data DrawOperatorContext = DrawOperatorContext {
  draw_nodelookup :: NodeLookup,
  draw_cache :: ShowCache
}

instance HasNodeLookup DrawOperatorContext where
    getLookup = draw_nodelookup
    setLookup nl ctx = ctx { draw_nodelookup = nl }


-- *| Initialization helpers

init_binary_context :: NodeLookup -> BiOpContext
init_binary_context nl = BCxt {
    bin_nodelookup = nl,
    bin_cache = Map.fromList (map (, HashMap.empty)
        ["union", "intersection", "inter", "interDc", "unionDc", "absorb", "traverse_and_return", "remove_outercomplement"]),
    bin_dc_stack = ([((0,0), Unknown)], [((0,0), Unknown)], [((0,0), Unknown)]),
    bin_current_level = ([(0, Dc)], [(0, Dc)])
}

init_unary_context :: NodeLookup -> UnOpContext
init_unary_context nl = UCxt {
    un_nodelookup = nl,
    un_cache = HashMap.empty,
    un_dc_stack = [((0,0), Unknown)],  -- Only dcR, no dcs needed, -- todo make it into ((1,0), Leaf True)
    un_current_level = [(0, Dc)]
}

init_draw_context :: NodeLookup -> DrawOperatorContext
init_draw_context nl = DrawOperatorContext {
    draw_nodelookup = nl,
    draw_cache = HashMap.empty
}


-- *| Node Retrieval and Persistence


-- | Basic node retrieval from context using the global lookup table.
getDd :: (HasNodeLookup c) => c -> NodeId -> Dd
getDd c node_id =
    let nm = getLookup c
    in case HashMap.lookup (fst node_id) nm of
       Just result -> case Map.lookup (snd node_id) result of
          Just entry -> dd entry
          Nothing -> error $ "Node address without Alternative in NodeLookup: " ++ show node_id
       Nothing -> error $ "Node address not in table/map: " ++ show node_id

-- | Retrieves a full Node (Id and Data) from the context.
getNode :: (HasNodeLookup c) => c -> NodeId -> Node
getNode c node_id = (node_id, getDd c node_id)

-- | Insertion of a Dd node into the context's lookup table.
-- Returns the updated context and the resulting Node.
insert :: (HasNodeLookup c) => c -> Dd -> (c, Node)
insert c d =
    -- Calls insert_id from MDD.Manager. hash is now in scope.
    let (new_id, rnm) = insert_id (hash d) d (getLookup c)
    in (setLookup rnm c, (new_id, d))