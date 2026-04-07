{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module MDD.Traversal.Context
  ( -- * Typeclasses
    HasNodeLookup(..)
    -- * Context Types
  , BiOpContext(..)
  , UnOpContext(..)
  , DrawOperatorContext(..)
    -- * Cache Types
  , Cache
  , SingleCache
  , ShowCache
    -- * Initialization
  , init_binary_context
  , init_unary_context
  , init_draw_context
  , binaryOperationNames
  , emptyBinaryCache
    -- * Node Operations
  , getDd
  , getNode
  , insert
    -- * Context Conversion
  , binaryToUnaryContext
  , unaryToBinaryContext
    -- * Cache Operations
  , lookupBinaryCache
  , insertBinaryCache
  , lookupUnaryCache
  , insertUnaryCache
  ) where

import MDD.Types
import MDD.NodeLookup
import Data.Hashable -- Added to bring the 'hash' function into scope
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Map as Map

-- | The distinct types of Contexts for different operations.
-- The Context is the central state manager for all MDD operations, usually existing only during a operator / traversal function call.
-- It tracks the global NodeLookup (nodelookup), operation caches,
-- and the class variable / background evaluation stacks (dc_stack) needed to resolve unknowns and absorb calls.

-- | Unified typeclass for all context types that provide node lookup functionality
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



-- * Initialization Helpers


-- | Standard binary operation function names for cache initialization
binaryOperationNames :: [String]
binaryOperationNames =
    ["union", "intersection", "inter", "interDc", "unionDc", "absorb",
     "traverse_and_return", "remove_outercomplement"]

-- | Create an empty binary cache with all operation names initialized
emptyBinaryCache :: Cache
emptyBinaryCache = Map.fromList (map (, HashMap.empty) binaryOperationNames)

-- | Initialize a binary context with the given NodeLookup
init_binary_context :: NodeLookup -> BiOpContext
init_binary_context nl = BCxt {
    bin_nodelookup = nl,
    bin_cache = emptyBinaryCache,
    bin_dc_stack = ([((0,0), Unknown)], [((0,0), Unknown)], [((0,0), Unknown)]),
    bin_current_level = ([(0, Dc)], [(0, Dc)])
}

-- | Initialize a unary context with the given NodeLookup
init_unary_context :: NodeLookup -> UnOpContext
init_unary_context nl = UCxt {
    un_nodelookup = nl,
    un_cache = HashMap.empty,
    un_dc_stack = [((0,0), Unknown)],  -- Only dcR, no dcs needed
    un_current_level = [(0, Dc)]
}

-- | Initialize a draw context with the given NodeLookup
init_draw_context :: NodeLookup -> DrawOperatorContext
init_draw_context nl = DrawOperatorContext {
    draw_nodelookup = nl,
    draw_cache = HashMap.empty
}



-- * Node Retrieval and Persistence


-- | Basic node retrieval from context using the global lookup table.
getDd :: (HasNodeLookup c) => c -> NodeId -> Dd
getDd c node_id =
    let nm = getLookup c
    in case HashMap.lookup (fst node_id) nm of
       Just result -> case Map.lookup (snd node_id) result of
          Just entry -> dd entry
          Nothing -> error $ "Node address without Alternative in NodeLookup: " ++ show node_id ++
                             ", lookup table size: " ++ show (HashMap.size nm)
       Nothing -> error $ "Node address not in table/map: " ++ show node_id ++
                          ", lookup table size: " ++ show (HashMap.size nm)

-- | Retrieves a full Node (Id and Data) from the context.
getNode :: (HasNodeLookup c) => c -> NodeId -> Node
getNode c node_id = (node_id, getDd c node_id)

-- | Insertion of a Dd node into the context's lookup table.
-- Returns the updated context and the resulting Node.
insert :: (HasNodeLookup c) => c -> Dd -> (c, Node)
insert c d =
    let (new_id, rnm) = insert_id (hash d) d (getLookup c)
    in (setLookup rnm c, (new_id, d))


-- * Context Conversion Helpers


-- | Convert a binary context to a unary context for absorb operations.
-- Extracts dcR from binary context and uses the first level from bin_current_level.
binaryToUnaryContext :: BiOpContext -> UnOpContext
binaryToUnaryContext c = UCxt {
    un_nodelookup = bin_nodelookup c,
    un_cache = HashMap.empty,  -- Cache not needed for absorb
    un_dc_stack = let (_, _, dcRs) = bin_dc_stack c in dcRs,
    un_current_level = let (lvA, _) = bin_current_level c in lvA
}

-- | Convert a unary context back to a binary context, preserving original binary context state.
-- Used after unary operations (like absorb) to restore the binary context.
unaryToBinaryContext :: UnOpContext -> BiOpContext -> BiOpContext
unaryToBinaryContext unaryCtx originalBinaryCtx = BCxt {
    bin_nodelookup = un_nodelookup unaryCtx,  -- Updated nodelookup from unary context
    bin_cache = bin_cache originalBinaryCtx,  -- Preserve original cache
    bin_dc_stack = bin_dc_stack originalBinaryCtx,  -- Preserve original stack
    bin_current_level = bin_current_level originalBinaryCtx  -- Preserve original current level
}


-- * Common Cache Operations


-- | Lookup a value in a binary cache
lookupBinaryCache :: BiOpContext -> String -> (NodeId, NodeId, ([Node], [Node], [Node])) -> Maybe NodeId
lookupBinaryCache c funcName key = do
    funcCache <- Map.lookup funcName (bin_cache c)
    HashMap.lookup key funcCache

-- | Insert a value into a binary cache
insertBinaryCache :: BiOpContext -> String -> (NodeId, NodeId, ([Node], [Node], [Node])) -> NodeId -> BiOpContext
insertBinaryCache c funcName key value =
    let currentCache = bin_cache c
        funcCache = Map.findWithDefault HashMap.empty funcName currentCache
        updatedFuncCache = HashMap.insert key value funcCache
        updatedCache = Map.insert funcName updatedFuncCache currentCache
    in c { bin_cache = updatedCache }

-- | Lookup a value in a unary cache
lookupUnaryCache :: UnOpContext -> NodeId -> Maybe NodeId
lookupUnaryCache c key = HashMap.lookup key (un_cache c)

-- | Insert a value into a unary cache
insertUnaryCache :: UnOpContext -> NodeId -> NodeId -> UnOpContext
insertUnaryCache c key value =
    c { un_cache = HashMap.insert key value (un_cache c) }