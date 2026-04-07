{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module MDD.Ops.Binary where

import MDD.Types
import MDD.Context
import MDD.Manager
import MDD.Stack
import MDD.Traversal
import MDD.Draw (debug_manipulation)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Map as Map
import Data.Kind (Constraint)
import Debug.Trace (trace)
-- ==========================================================================================================
-- * Binary Caching Helper
-- ==========================================================================================================

-- | A higher-order function for handling cache lookup and update.
-- |
-- | The cache prevents redundant computations during binary operations (union, intersection, etc.).
-- | It uses a two-level structure:
-- |   - First level: Maps function names (e.g., "union", "inter") to their caches
-- |   - Second level: Maps (NodeId A, NodeId B, dc_stack state) to previously computed results
-- |
-- | The dc_stack is included in the cache key because the same node pair can produce different
-- | results depending on the hierarchical context (which InfNode layers we're currently in).
withCache :: BiOpContext -> (Node, Node, String) -> (BiOpContext, Node) -> (BiOpContext, Node)
withCache c@BCxt{bin_cache = nc, bin_dc_stack = dck} ((keyA, _), (keyB, _), keyFunc) func_with_args =
  case Map.lookup keyFunc nc of
    Just nc' -> case HashMap.lookup (keyA, keyB, dck) nc' of
      Just result -> (c, getNode c result) -- Cache hit: return previously computed result
      Nothing -> let
        (updatedContext, r@(result, _)) = func_with_args
        new_dck = bin_dc_stack updatedContext
        updatedCache = Map.insert keyFunc (HashMap.insert (keyA, keyB, new_dck) result nc') nc
        in (updatedContext { bin_cache = updatedCache }, r) -- Cache miss: compute and store result
    Nothing -> error ("function not in map, bad initialisation?: " ++ show keyFunc)



-- ==========================================================================================================
-- * Binary Operation Typeclass (Dd1)
-- ==========================================================================================================

-- | The Dd1 typeclass defines binary operations (union, intersection) parameterized by
-- | the inference type @a@ (Dc, Neg, or Pos). The inference type determines which elimination
-- | rules are applied during traversal (see DdF3 in MDD.Traversal).

type Dd1 :: Inf -> Constraint
class Dd1 a where
    leaf_cases :: BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
    dcB_leaf_cases :: BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
    dcA_leaf_cases :: BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
    apply :: BiOpContext -> String -> NodeId -> NodeId -> (BiOpContext, Node)
    applyDcB :: BiOpContext -> String -> NodeId -> NodeId -> (BiOpContext, Node)
    applyDcA :: BiOpContext -> String -> NodeId -> NodeId -> (BiOpContext, Node)

    apply' :: BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
    applyDcB' :: BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
    applyDcA' :: BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
    endinf_case :: BiOpContext -> String -> NodeId -> NodeId -> NodeId -> NodeId -> (BiOpContext, Node)

instance (DdF3 a, Dd1_helper a) => Dd1 a where
    -- | Main entry point: converts NodeIds to Nodes and wraps with debug output
    apply c s a b = debug_manipulation (apply' @a c s (getNode c a) (getNode c b)) s (s ++ to_str @a) c (getNode c a) (getNode c b)

    -- | Main binary operation dispatcher. Handles all combinations of node types.
    -- | Pattern matches are ordered from most specific to most general.

    -- Cases 1-4: At least one argument is a terminal (Leaf or Unknown)
    --   -> Delegate to leaf_cases for terminal handling
    apply' c s a@(_, Leaf _) b = leaf_cases @a c s a b
    apply' c s a b@(_, Leaf _) = leaf_cases @a c s a b
    apply' c s a@(_, Unknown) b = leaf_cases @a c s a b
    apply' c s a b@(_, Unknown) = leaf_cases @a c s a b

    -- Case 5: Both arguments are EndInfNodes (both exiting their respective classes)
    --   -> Pop the inference type stack to determine which inference context to use
    --   -> Then apply operation in the parent class context
    apply' c s a@(a_id, EndInfNode ac) b@(b_id, EndInfNode bc) = withCache c (a, b, s) $
        endinf_case @a c s a_id b_id ac bc

    -- Cases 6-8: Both arguments are regular Nodes (variable nodes)
    --   -> Compare positions to determine traversal strategy
    apply' c s a@(a_id, Node positionA pos_childA neg_childA)  b@(b_id, Node positionB pos_childB neg_childB)
        -- Case 6: Positions match (same variable)
        --   -> Traverse both positive and negative branches in parallel
        --   -> traverse_dc synchronizes dc_stack traversal with main traversal (handles "catch-up")
        --   -> reset_stack_bin restores original stack state between branches
        | positionA == positionB =
            let c_ = traverse_dc @a "pos child" c pos_childA pos_childB  -- Sync dc_stack for pos branch
                (c', (pos_result, _)) = apply @a c_ s pos_childA pos_childB

                c_' = traverse_dc @a "neg child" (reset_stack_bin c' c) neg_childA neg_childB  -- Sync dc_stack for neg branch
                (c'', (neg_result, _)) = apply @a c_' s neg_childA neg_childB
            in withCache c (a, b, s) $ applyElimRule @a (reset_stack_bin c'' c) (Node positionA pos_result neg_result)
        -- Case 7: positionA < positionB (A's variable comes before B's in ordering)
        | positionA < positionB = uncurry (applyElimRule @a) (inferNodeB' @a (apply' @a) c s a b)
        -- Case 8: positionA > positionB (B's variable comes before A's)
        | positionA > positionB = uncurry (applyElimRule @a) (inferNodeA' @a (apply' @a) c s a b)

    -- Cases 9-12: InfNodes vs Node (entering/exiting class hierarchy)
    apply' c s a@(a_id, InfNodes positionA _ _ _) b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        -- Case 9: positionA > positionB (InfNode's class comes after Node's variable)
        | positionA > positionB = withCache c (a, b, s) $
                uncurry (applyElimRule @a) (inferNodeA' @a (apply' @a) c s a b)
        -- Case 10: positionA < positionB (InfNode's class comes before Node's variable)
        --   -> Need to enter the class hierarchy: applyInfB wraps Node in the class context
        | positionA < positionB = withCache c (a, b, s) $
                absorb @a $ applyInfB @a c s a b
    apply' c s a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        -- Case 11: positionA > positionB (Node's variable comes after InfNode's class)
        --   -> Need to enter class hierarchy: applyInfA wraps Node in the class context
        | positionA > positionB = withCache c (a, b, s) $
                absorb @a $ applyInfA @a c s a b
        -- Case 12: positionA < positionB (Node's variable comes before InfNode's class)
        | positionA < positionB = withCache c (a, b, s) $
                uncurry (applyElimRule @a) (inferNodeB' @a (apply' @a) c s a b)

    -- Cases 13-15: Both arguments are InfNodes (class hierarchy operations)
    apply' c s a@(a_id, InfNodes positionA _ _ _)  b@(b_id, InfNodes positionB _ _ _)
        -- Case 13: Positions match (same class)
        | positionA == positionB = withCache c (a, b, s) $ absorb @a $ applyInf @a c s a b
        -- Case 14: positionA < positionB (A's class comes before B's)
        | positionA < positionB = withCache c (a, b, s) $ absorb @a $ applyInfB @a c s a b
        -- Case 15: positionA > positionB (A's class comes after B's)
        | positionA > positionB = withCache c (a, b, s) $ absorb @a $ applyInfA @a c s a b

    -- Cases 16-19: EndInfNode vs Node (hierarchy mismatch)
    --   -> EndInfNode means we're exiting a class, but Node / InfNode means we're still in that class
    --   -> Need to infer what the EndInfNode's argument should be at the Node's position
    apply' c s a@(a_id, EndInfNode _) b@(b_id, Node idx _ _) = withCache c (a, b, s) $ uncurry (applyElimRule @a) (inferNodeA' @a (apply' @a) c s a b)
    apply' c s a@(a_id, Node{}) b@(b_id, EndInfNode _) = withCache c (a, b, s) $ uncurry (applyElimRule @a) (inferNodeB' @a (apply' @a) c s a b)
    apply' c s a@(a_id, EndInfNode _) b@(b_id, InfNodes{}) = withCache c (a, b, s) $ absorb @a $ applyInfA @a c s a b
    apply' c s a@(a_id, InfNodes{}) b@(b_id, EndInfNode _) = withCache c (a, b, s) $ absorb @a $ applyInfB @a c s a b

    -- | Handles all cases where at least one argument is a terminal value (Leaf, Unknown).
    -- | This function dispatches to specialized handlers based on the combination of terminal types.
    leaf_cases c s a@(_, Leaf _) b@(_, Node{}) = withCache c (a, b, s) $ uncurry (applyElimRule @a) (inferNodeA' @a (apply' @a) c s a b)
    leaf_cases c s a@(_, Node{}) b@(_, Leaf _) = withCache c (a, b, s) $ uncurry (applyElimRule @a) (inferNodeB' @a (apply' @a) c s a b )
    leaf_cases c s a@(a_id, Leaf True) b@(b_id, EndInfNode bc) = withCache c (a, b, s) $
        endinf_case @a c s a_id b_id (1,0) bc
    leaf_cases c s a@(a_id, EndInfNode ac) b@(b_id, Leaf True) = withCache c (a, b, s) $
        endinf_case @a c s a_id b_id ac (1,0)
    leaf_cases c s a@(a_id, Leaf False) b@(b_id, EndInfNode bc) = withCache c (a, b, s) $
        endinf_case @a c s a_id b_id (2,0) bc
    leaf_cases c s a@(a_id, EndInfNode ac) b@(b_id, Leaf False) = withCache c (a, b, s) $
        endinf_case @a c s a_id b_id ac (2,0)
    leaf_cases c s a@(a_id, Leaf _) b@(b_id, InfNodes{}) = withCache c (a, b, s) $
        applyInfA @a c s a b
    leaf_cases c s a@(a_id, InfNodes {}) b@(b_id, Leaf _) = withCache c (a, b, s) $
        applyInfB @a c s a b

    -- Unknown resolution
    --   -> When Unknown is encountered, we need to look up the dc branch from the dc_stack
    --   -> dcA and dcB are the continuous branches for arguments A and B respectively
    leaf_cases c s a@(_, Unknown) b@(_, Unknown) = (c , a)  -- Both Unknown: return first (they'll resolve the same as in dcR, no matter whether union or intersection is used)
    leaf_cases c s a@(_, Unknown) b =
        let (c', dcA) = pop_dcA' c
        in applyDcA' @a c' s dcA b
    leaf_cases c s a b@(_, Unknown) =
        let (c', dcB) = pop_dcB' c
        in applyDcB' @a c' s a dcB

    -- Cases 12-13: Union/Intersection base cases for Leaf vs Leaf
    --   -> Union: True is dominant
    --   -> Intersection: False is dominant
    --   -> absorb ensures result is canonical (may replace with Unknown if redundant)
    leaf_cases c "union" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then absorb @a (c, a) else absorb @a (c, b)
    leaf_cases c "inter" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then absorb @a (c, b) else absorb @a (c, a)

    -- Fallback: should not happen with proper type handling
    leaf_cases c s a b = error ("leaf case: " ++ s)

-- | ======================== DC versions (Argument B is DC type) ========================
-- |
-- | These functions handle binary operations where argument B comes from a Dc (continuous/don't-care) branch.
-- | The key difference is that when inferring nodes for B, we use @Dc@ inference rules instead of @a@.
-- | This is because B represents the continuous background, so its elimination rules follow Dc semantics.
    -- |   - When inferring nodes for B, uses @Dc@ inference rules (inferNodeB' @Dc)
    -- |   - Cache key includes "Dc" suffix to distinguish from regular operations
    -- |   - All cases mirror apply' but with Dc-specific inference for argument B

    -- | Entry point for applyDcB: converts NodeIds to Nodes and wraps with debug
    applyDcB c s a b = debug_manipulation (applyDcB' @a c s (getNode c a) (getNode c b)) s (s ++ "DcB " ++ to_str @a) c (getNode c a) (getNode c b)

    -- Cases 1-4: Terminal values -> delegate to dcB_leaf_cases
    applyDcB' c s a@(_, Leaf _) b = dcB_leaf_cases @a c s a b
    applyDcB' c s a b@(_, Leaf _) = dcB_leaf_cases @a c s a b
    applyDcB' c s a@(_, Unknown) b = dcB_leaf_cases @a c s a b
    applyDcB' c s a b@(_, Unknown) = dcB_leaf_cases @a c s a b

    -- Cases 5-6: EndInfNode vs Node (note: B uses @Dc@ inference when inferring)
    applyDcB' c s a@(a_id, EndInfNode _) b@(b_id, Node idx _ _) = withCache c (a, b, (s ++ "Dc")) $ uncurry (applyElimRule @a) (inferNodeA' @a (applyDcB' @a) c s a b)
    applyDcB' c s a@(a_id, Node{}) b@(b_id, EndInfNode _) = withCache c (a, b, (s ++ "Dc")) $ uncurry (applyElimRule @a) (inferNodeB' @Dc (applyDcB' @a) c s a b)
    applyDcB' c s a@(a_id, EndInfNode ac) b@(b_id, EndInfNode bc) = withCache c (a, b, (s ++ "Dc")) $
        endinf_case @a c s a_id b_id ac bc

    -- Cases 7-9: Node vs Node (B is from Dc, so uses @Dc@ inference when positionA < positionB)
    applyDcB' c s a@(a_id, Node positionA pos_childA neg_childA)  b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB =
            let c_ = traverse_dc @a "pos child" c pos_childA pos_childB
                (c', (pos_result, _)) = applyDcB @a c_ s pos_childA pos_childB

                c_' = traverse_dc @a "neg child" (reset_stack_bin c' c) neg_childA neg_childB
                (c'', (neg_result, _)) = applyDcB @a c_' s neg_childA neg_childB
            in withCache c (a, b, (s ++ "Dc")) $ applyElimRule @a (reset_stack_bin c'' c) (Node positionA pos_result neg_result)
        | positionA < positionB = uncurry (applyElimRule @a) (inferNodeB' @Dc (applyDcB' @a) c s a b)  -- B is Dc, use @Dc@ inference
        | positionA > positionB = uncurry (applyElimRule @a) (inferNodeA' @a (applyDcB' @a) c s a b)

    -- Cases 10-15: InfNodes vs Node/InfNodes/EndInfNode (similar to apply', but B uses @Dc@ when wrapping)
    applyDcB' c s a@(a_id, InfNodes positionA _ _ _) b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB = withCache c (a, b, (s ++ "Dc")) $
                uncurry (applyElimRule @a) (inferNodeA' @a (applyDcB' @a) c s a b)
    applyDcB' c s a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA < positionB = withCache c (a, b, (s ++ "Dc")) $
                uncurry (applyElimRule @a) (inferNodeB' @Dc (applyDcB' @a) c s a b)  -- B is Dc
    applyDcB' c s a@(a_id, InfNodes positionA _ _ _)  b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = applyInf @a c s a b
        | positionA < positionB = applyInfB @Dc c s a b  -- B is Dc, use @Dc@ when wrapping
        | positionA > positionB = applyInfA @a c s a b
    applyDcB' c s a@(a_id, EndInfNode _) b@(b_id, InfNodes{}) = withCache c (a, b, (s ++ "Dc")) $ applyInfA @a c s a b
    applyDcB' c s a@(a_id, InfNodes{}) b@(b_id, EndInfNode _) = withCache c (a, b, (s ++ "Dc")) $ applyInfB @Dc c s a b  -- B is Dc


    dcB_leaf_cases c s a@(_, Leaf _) b@(_, Node{}) = withCache c (a, b, s ++ "Dc") $ uncurry (applyElimRule @a) (inferNodeA' @a (applyDcB' @a) c s a b )
    dcB_leaf_cases c s a@(_, Node{}) b@(_, Leaf _) = withCache c (a, b, s ++ "Dc") $ uncurry (applyElimRule @a) (inferNodeB' @Dc (applyDcB' @a) c s a b)  -- B is Dc
    dcB_leaf_cases c s a@(a_id, Leaf True) b@(b_id, EndInfNode bc) = withCache c (a, b, s ++ "Dc") $
        endinf_case @a c s a_id b_id (1,0) bc
    dcB_leaf_cases c s a@(a_id, EndInfNode ac) b@(b_id, Leaf True) = withCache c (a, b, s ++ "Dc") $
        endinf_case @a c s a_id b_id ac (1,0)
    dcB_leaf_cases c s a@(a_id, Leaf False) b@(b_id, EndInfNode bc) = withCache c (a, b, s ++ "Dc") $
        endinf_case @a c s a_id b_id (2,0) bc
    dcB_leaf_cases c s a@(a_id, EndInfNode ac) b@(b_id, Leaf False) = withCache c (a, b, s ++ "Dc") $
        endinf_case @a c s a_id b_id ac (2,0)
    dcB_leaf_cases c s a@(a_id, Leaf _) b@(b_id, InfNodes{}) = withCache c (a, b, s ++ "Dc") $
        applyInfA @a c s a b
    dcB_leaf_cases c s a@(a_id, InfNodes {}) b@(b_id, Leaf _) = withCache c (a, b, s ++ "Dc") $
        applyInfB @Dc c s a b  -- B is Dc

    -- Unknown resolution: if A is Unknown, return it (it will resolve to dcA elsewhere)
    -- If B is Unknown, resolve it by popping dcB from stack
    dcB_leaf_cases c s a@(_, Unknown) b = (c, a)  -- A is Unknown, return as-is
    dcB_leaf_cases c s a b@(_, Unknown) =  -- B is Unknown, resolve from dcB
        let (c', dcB) = pop_dcB'' c
        in applyDcB' @a c' s a dcB
    dcB_leaf_cases c "union" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then absorb @a (c, a) else absorb @a (c, b)
    dcB_leaf_cases c "inter" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then absorb @a (c, b) else absorb @a (c, a)

-- | ======================== DcA versions (Argument A is DC type) ========================
-- |
-- | These functions handle binary operations where argument A comes from a Dc (continuous/don't-care) branch.
-- | The key difference is that when inferring nodes for A, we use @Dc@ inference rules instead of @a@.
-- | This is the mirror of applyDcB, but for argument A.
    -- |   - When inferring nodes for A, uses @Dc@ inference rules (inferNodeA' @Dc)
    -- |   - Cache key includes "Dc" suffix to distinguish from regular operations
    -- |   - All cases mirror apply' but with Dc-specific inference for argument A


    -- | Entry point for applyDcA: converts NodeIds to Nodes and wraps with debug
    applyDcA c s a b = debug_manipulation (applyDcA' @a c s (getNode c a) (getNode c b)) s (s ++ "DcA " ++ to_str @a) c (getNode c a) (getNode c b)

    -- Cases 1-4: Terminal values -> delegate to dcA_leaf_cases
    applyDcA' c s a@(_, Leaf _) b = dcA_leaf_cases @a c s a b
    applyDcA' c s a b@(_, Leaf _) = dcA_leaf_cases @a c s a b
    applyDcA' c s a@(_, Unknown) b = dcA_leaf_cases @a c s a b
    applyDcA' c s a b@(_, Unknown) = dcA_leaf_cases @a c s a b

    -- Cases 5-6: EndInfNode vs Node (note: A uses @Dc@ inference when inferring)
    applyDcA' c s a@(a_id, EndInfNode _) b@(b_id, Node idx _ _) = withCache c (a, b, (s ++ "Dc")) $ uncurry (applyElimRule @a) (inferNodeA' @Dc (applyDcA' @a) c s a b)  -- A is Dc
    applyDcA' c s a@(a_id, Node{}) b@(b_id, EndInfNode _) = withCache c (a, b, (s ++ "Dc")) $ uncurry (applyElimRule @a) (inferNodeB' @a (applyDcA' @a) c s a b)
    applyDcA' c s a@(a_id, EndInfNode ac) b@(b_id, EndInfNode bc) = withCache c (a, b, (s ++ "Dc")) $
        endinf_case @a c s a_id b_id ac bc

    -- Cases 7-9: Node vs Node (A is from Dc, so uses @Dc@ inference when positionA > positionB)
    applyDcA' c s a@(a_id, Node positionA pos_childA neg_childA)  b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB =
            let c_ = traverse_dc @a "pos child" c pos_childA pos_childB
                (c', (pos_result, _)) = applyDcA @a c_ s pos_childA pos_childB

                c_' = traverse_dc @a "neg child" (reset_stack_bin c' c) neg_childA neg_childB
                (c'', (neg_result, _)) = applyDcA @a c_' s neg_childA neg_childB
            in withCache c (a, b, (s ++ "Dc")) $ applyElimRule @a (reset_stack_bin c'' c) (Node positionA pos_result neg_result)
        | positionA < positionB = uncurry (applyElimRule @a) (inferNodeB' @a (applyDcA' @a) c s a b)
        | positionA > positionB = uncurry (applyElimRule @a) (inferNodeA' @Dc (applyDcA' @a) c s a b)  -- A is Dc, use @Dc@ inference

    -- Cases 10-15: InfNodes vs Node/InfNodes/EndInfNode (similar to apply', but A uses @Dc@ when wrapping)
    applyDcA' c s a@(a_id, InfNodes positionA _ _ _) b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB = withCache c (a, b, (s ++ "Dc")) $
                uncurry (applyElimRule @a) (inferNodeA' @Dc (applyDcA' @a) c s a b)  -- A is Dc
    applyDcA' c s a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA < positionB = withCache c (a, b, (s ++ "Dc")) $
                uncurry (applyElimRule @a) (inferNodeB' @a (applyDcA' @a) c s a b)
    applyDcA' c s a@(a_id, InfNodes positionA _ _ _)  b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = applyInf @a c s a b
        | positionA < positionB = applyInfB @a c s a b
        | positionA > positionB = applyInfA @Dc c s a b  -- A is Dc, use @Dc@ when wrapping
    applyDcA' c s a@(a_id, EndInfNode _) b@(b_id, InfNodes{}) = withCache c (a, b, (s ++ "Dc")) $ applyInfA @Dc c s a b  -- A is Dc
    applyDcA' c s a@(a_id, InfNodes{}) b@(b_id, EndInfNode _) = withCache c (a, b, (s ++ "Dc")) $ applyInfB @a c s a b

    dcA_leaf_cases c s a@(_, Leaf _) b@(_, Node{}) = withCache c (a, b, s ++ "Dc") $ uncurry (applyElimRule @a) (inferNodeA' @Dc (applyDcA' @a) c s a b )  -- A is Dc
    dcA_leaf_cases c s a@(_, Node{}) b@(_, Leaf _) = withCache c (a, b, s ++ "Dc") $ uncurry (applyElimRule @a) (inferNodeB' @a (applyDcA' @a) c s a b)
    dcA_leaf_cases c s a@(a_id, Leaf True) b@(b_id, EndInfNode bc) = withCache c (a, b, s ++ "Dc") $
        endinf_case @a c s a_id b_id (1,0) bc
    dcA_leaf_cases c s a@(a_id, EndInfNode ac) b@(b_id, Leaf True) = withCache c (a, b, s ++ "Dc") $
        endinf_case @a c s a_id b_id ac (1,0)
    dcA_leaf_cases c s a@(a_id, Leaf False) b@(b_id, EndInfNode bc) = withCache c (a, b, s ++ "Dc") $
        endinf_case @a c s a_id b_id (2,0) bc
    dcA_leaf_cases c s a@(a_id, EndInfNode ac) b@(b_id, Leaf False) = withCache c (a, b, s ++ "Dc") $
        endinf_case @a c s a_id b_id ac (2,0)
    dcA_leaf_cases c s a@(a_id, Leaf _) b@(b_id, InfNodes{}) = withCache c (a, b, s ++ "Dc") $
        applyInfA @Dc c s a b  -- A is Dc
    dcA_leaf_cases c s a@(a_id, InfNodes {}) b@(b_id, Leaf _) = withCache c (a, b, s ++ "Dc") $
        applyInfB @a c s a b

    -- Unknown resolution: if A is Unknown, resolve it by popping dcA from stack
    -- If B is Unknown, return it as-is (it will resolve to dcB elsewhere)
    dcA_leaf_cases c s a@(_, Unknown) b =  -- A is Unknown, resolve from dcA
        let (c', dcA) = pop_dcA'' c
        in applyDcA' @a c' s dcA b
    dcA_leaf_cases c s a b@(_, Unknown) = (c, b)  -- B is Unknown, return as-is
    dcA_leaf_cases c "union" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then absorb @a (c, a) else absorb @a (c, b)
    dcA_leaf_cases c "inter" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then absorb @a (c, b) else absorb @a (c, a)

    -- | Handles the case when both arguments are EndInfNodes (both exiting their class hierarchies).
    -- | This function:
    -- |   1. Pops the inference type stack to determine which inference contexts (Dc/Neg/Pos) were used
    -- |   2. Applies the appropriate binary operation based on the combination of inference types
    -- |   3. Wraps the result in an EndInfNode to maintain the class hierarchy structure
    -- | The inference type combinations determine which version of apply to use

    endinf_case c s a_id b_id ac bc = let
        -- Pop the inference type stack to get the inference contexts for A and B
        (c_, (infA, infB)) = pop_stack' c
        -- Synchronize dc_stack traversal for the EndInfNode case
        c' = traverse_dc @a "endinf" c_ a_id b_id
        -- Apply operation based on inference type combination
        (c'', (r, _)) = case (infA, infB) of
            (Dc, Dc) -> apply @Dc c' s ac bc  -- Both continuous (don't-care inference)
            (Neg, Neg) -> apply @Neg c' s ac bc  -- Both using negative literal inference rule
            (Pos, Pos) -> apply @Pos c' s ac bc  -- Both using positive literal inference rule
            (Neg, Dc) -> applyDcB @Neg c' s ac bc  -- Negative literal inference vs continuous
            (Pos, Dc) -> applyDcB @Pos c' s ac bc  -- Positive literal inference vs continuous
            (Dc, Neg) -> applyDcA @Neg c' s ac bc  -- Continuous vs negative literal inference
            (Dc, Pos) -> applyDcA @Pos c' s ac bc  -- Continuous vs positive literal inference
            r'@(_, _) -> error ("weird combination after pop stack: " ++ show r')
        -- Absorb redundant branches, then apply elimination rule and wrap in EndInfNode
        in absorb @a $ applyElimRule @a (reset_stack_bin c'' c) (EndInfNode r)

-- | ======================== InfNode Application Logic ========================
-- |
-- | These functions handle binary operations when at least one argument is an InfNodes (class-defining node).
-- |
-- | The algorithm:
-- |   1. First compute dcR (the resulting continuous branch using the don't-care literal inference/elimination rule) by applying operation to dcA and dcB
-- |   2. Then compute nR (branch using negative literal inference/elimination rule) using dcR as the continuous background
-- |   3. Then compute pR (branch using positive literal inference/elimination rule) using dcR as the continuous background
-- |   4. Combine results into a new InfNodes with the three computed branches
-- |
-- | The dc_stack is updated at each step:
-- |   - For dc branch: Push Unknown placeholders (dcR not yet computed)
-- |   - For neg/pos branches: Push the computed dcR as the continuous background
-- |
-- | Note: The actual exception type (neg1/neg0 or pos1/pos0) depends on what dcR evaluates to.
applyInf :: forall a. (Dd1 a, DdF3 a, Dd1_helper a) => BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
applyInf c s a@(a_id, InfNodes positionA dcA pA nA) b@(b_id, InfNodes positionB dcB pB nB)
    | positionA == positionB =
        let
            -- Step 1: Compute the continuous (dc) branch result using don't-care inference rule
            -- Push Unknown placeholders for dcA, dcB, dcR (dcR not yet known)
            c_ = add_to_stack (positionA, Dc) (((0, 0), Unknown), ((0, 0), Unknown), ((0, 0), Unknown)) c
            (c1, dcR) = apply @Dc (traverse_dc @a "inf dc" c_ dcA dcB) s dcA dcB

            -- Step 2: Compute the branch using negative literal inference rule
            -- Push the computed dc branches and dcR as the continuous background
            c2_ = add_to_stack (positionA, Neg) (getNode c1 dcA, getNode c1 dcB, dcR) (reset_stack_bin c1 c)
            (c2, nR) = apply @Neg (traverse_dc @a "inf neg" c2_ nA nB) s nA nB

            -- Step 3: Compute the branch using positive literal inference rule
            -- Push the computed dc branches and dcR as the continuous background
            c3_ = add_to_stack (positionA, Pos) (getNode c1 dcA, getNode c1 dcB, dcR) (reset_stack_bin c2 c)
            (c3, pR) = apply @Pos (traverse_dc @a "inf pos" c3_ pA pB) s pA pB

            -- Step 4: Reset stack and combine results into new InfNodes
            c4 = reset_stack_bin c3 c
        in applyElimRule @a c4 $ InfNodes positionA (fst dcR) (fst pR) (fst nR)
    | positionA > positionB = applyInfA @a c s a b  -- A's class comes after, wrap A
    | positionA < positionB = applyInfB @a c s a b  -- B's class comes after, wrap B
applyInf c s a@(_, InfNodes {}) b@(_, Leaf _) = applyInfB @a c s a b  -- Wrap Leaf in InfNode's class
applyInf c s a@(_, InfNodes {}) b@(_, EndInfNode _) = applyInfB @a c s a b  -- Wrap EndInfNode in InfNode's class
applyInf c s a@(_, Leaf _) b@(_, InfNodes{}) = applyInfA @a c s a b  -- Wrap Leaf in InfNode's class
applyInf c s a@(_, EndInfNode _) b@(_, InfNodes{}) = applyInfA @a c s a b  -- Wrap EndInfNode in InfNode's class
applyInf c s a b = error ("apply inf error: " ++ s)


applyInfA :: forall a. (DdF3 a) => BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
applyInfA c s (a_id, _) b@(_, InfNodes positionB _ _ _) = let
        (c', r) = insert c (EndInfNode a_id)
        (c'', r') = inferInfNode @a c' positionB r
    in applyInf @a c'' s r' b
applyInfA _ _ _ _ = error "should not be possible"

applyInfB :: forall a. (DdF3 a) => BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
applyInfB c s a@(_, InfNodes positionA _ _ _) b@(b_id, _) = let
        (c', r) = insert c (EndInfNode b_id)
        (c'', r') = inferInfNode @a c' positionA r
    in applyInf @a c'' s a r'
applyInfB _ _ _ _ = error "should not be possible"

-- | Helper wrapper for inferred node recursive calls.
-- | These functions bridge between the Dd1 typeclass (which works with Nodes) and the DdF3
-- | typeclass (which works with Dd and handles inference rules).
inferNodeA' :: forall a. DdF3 a => (BiOpContext -> String -> Node -> Node -> (BiOpContext, Node))
            -> BiOpContext -> String -> Node -> Node -> (BiOpContext, Dd)
inferNodeA' f c s a b = inferNodeA @a f c s a b

inferNodeB' :: forall a. DdF3 a => (BiOpContext -> String -> Node -> Node -> (BiOpContext, Node))
            -> BiOpContext -> String -> Node -> Node -> (BiOpContext, Dd)
inferNodeB' f c s a b = inferNodeB @a f c s a b