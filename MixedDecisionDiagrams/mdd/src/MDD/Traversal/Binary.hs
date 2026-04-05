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

module MDD.Traversal.Binary where

import MDD.Types
import MDD.Traversal.Context
import MDD.NodeLookup
import MDD.Traversal.Stack
import MDD.Traversal.Support
import MDD.Extra.Draw (Show_setting (..), debug_manipulation, debug_manipulation_inf, debug, show_dd, show_node, settings)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Map as Map
import Data.Kind (Constraint)


-- | refactored with use of AI


-- * Binary Caching Helper


-- | A higher-order function for handling cache lookup and update.
-- |
-- | The cache prevents redundant computations during binary operations (union, intersection, etc.).
-- | It uses a two-level structure:
-- |   - First level: Maps function names (e.g., "union", "inter") to their caches
-- |   - Second level: Maps (NodeId A, NodeId B, dc_stack state) to previously computed results
-- |
-- | The dc_stack is included in the cache key because the same node pair can produce different
-- | results depending on the hierarchical context (which ClassNode layers we're currently in).
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




-- * Binary Operation Typeclass (Dd1)


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
    endclass_case :: BiOpContext -> String -> NodeId -> NodeId -> NodeId -> NodeId -> (BiOpContext, Node)

instance (DdF3 a, Dd1_helper a) => Dd1 a where
    -- | Main entry point: converts NodeIds to Nodes, wraps with debug output
    apply c s a b
        | a == b    = (c, getNode c a)
        | otherwise = debug_manipulation (apply' @a c s (getNode c a) (getNode c b)) s (s ++ to_str @a) c (getNode c a) (getNode c b)

    -- | Main binary operation dispatcher. Handles all combinations of node types.
    -- | Pattern matches are ordered from most specific to most general.

    -- Cases 1-4: At least one argument is a terminal (Leaf or Unknown)
    --   -> Delegate to leaf_cases for terminal handling
    apply' c s a@(_, Leaf _) b = leaf_cases @a c s a b
    apply' c s a b@(_, Leaf _) = leaf_cases @a c s a b
    apply' c s a@(_, Unknown) b = leaf_cases @a c s a b
    apply' c s a b@(_, Unknown) = leaf_cases @a c s a b

    -- Case 5: Both arguments are EndClassNode (both exiting their respective classes)
    --   -> Pop the inference type stack to determine which inference context to use
    --   -> Then apply operation in the parent class context
    apply' c s a@(a_id, EndClassNode ac) b@(b_id, EndClassNode bc) = withCache c (a, b, s) $
        endclass_case @a c s a_id b_id ac bc

    -- Cases 6-8: Both arguments are regular Nodes (variable nodes)
    --   -> Compare positions to determine traversal strategy
    apply' c s a@(a_id, Node positionA pos_childA neg_childA)  b@(b_id, Node positionB pos_childB neg_childB)
        -- Case 6: Positions match (same variable)
        --   -> Traverse both positive and negative branches in parallel
        --   -> traverse_dc synchronizes dc_stack traversal with main traversal (handles "catch-up")
        --   -> reset_stack_bin restores original stack state between branches
        | positionA == positionB =
            let c_ = traverse_dc @a "pos child" c a_id b_id
                (c', (pos_result, _)) = apply @a c_ s pos_childA pos_childB

                c_' = traverse_dc @a "neg child" (reset_stack_bin c' c) a_id b_id
                (c'', (neg_result, _)) = apply @a c_' s neg_childA neg_childB
            in withCache c (a, b, s) $ applyElimRule @a (reset_stack_bin c'' c) (Node positionA pos_result neg_result)
        -- Case 7: positionA < positionB (A's variable comes before B's in ordering)
        | positionA < positionB = uncurry (applyElimRule @a) (inferNodeB' @a (apply' @a) c s a b)
        -- Case 8: positionA > positionB (B's variable comes before A's)
        | positionA > positionB = uncurry (applyElimRule @a) (inferNodeA' @a (apply' @a) c s a b)

    -- Cases 9-12: ClassNode vs Node (entering/exiting class hierarchy)
    apply' c s a@(a_id, ClassNode positionA _ _ _) b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        -- Case 9: positionA > positionB (ClassNode's class comes after Node's variable)
        | positionA > positionB = withCache c (a, b, s) $
                uncurry (applyElimRule @a) (inferNodeA' @a (apply' @a) c s a b)
        -- Case 10: positionA < positionB (ClassNode's class comes before Node's variable)
        --   -> Need to enter the class hierarchy: applyClassB wraps Node in the class context
        | positionA < positionB = withCache c (a, b, s) $
                applyClassB @a c s a b
    apply' c s a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, ClassNode positionB _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB = withCache c (a, b, s) $
                applyClassA @a c s a b
        -- Case 12: positionA < positionB (Node's variable comes before ClassNode's class)
        | positionA < positionB = withCache c (a, b, s) $
                uncurry (applyElimRule @a) (inferNodeB' @a (apply' @a) c s a b)

    -- Cases 13-15: Both arguments are ClassNode (class hierarchy operations)
    apply' c s a@(a_id, ClassNode positionA _ _ _)  b@(b_id, ClassNode positionB _ _ _)
        -- Case 13: Positions match (same class)
        | positionA == positionB = withCache c (a, b, s) $ applyClass @a c s a b
        | positionA < positionB = withCache c (a, b, s) $ applyClassB @a c s a b
        | positionA > positionB = withCache c (a, b, s) $ applyClassA @a c s a b

    -- Cases 16-19: EndClassNode vs Node (hierarchy mismatch)
    --   -> EndClassNode means we're exiting a class, but Node / ClassNode means we're still in that class
    --   -> Need to infer what the EndClassNode's argument should be at the Node's position
    apply' c s a@(a_id, EndClassNode _) b@(b_id, Node idx _ _) = withCache c (a, b, s) $ uncurry (applyElimRule @a) (inferNodeA' @a (apply' @a) c s a b)
    apply' c s a@(a_id, Node{}) b@(b_id, EndClassNode _) = withCache c (a, b, s) $ uncurry (applyElimRule @a) (inferNodeB' @a (apply' @a) c s a b)

    apply' c s a@(_, EndClassNode _) b@(_, ClassNode{}) = withCache c (a, b, s) $
        applyClassA @a c s a b
    apply' c s a@(_, ClassNode{}) b@(_, EndClassNode _) = withCache c (a, b, s) $
        applyClassB @a c s a b

    -- | Handles all cases where at least one argument is a terminal value (Leaf, Unknown).
    -- | This function dispatches to specialized handlers based on the combination of terminal types.
    leaf_cases c s a@(_, Leaf _) b@(_, Node{}) = withCache c (a, b, s) $ uncurry (applyElimRule @a) (inferNodeA' @a (apply' @a) c s a b)
    leaf_cases c s a@(_, Node{}) b@(_, Leaf _) = withCache c (a, b, s) $ uncurry (applyElimRule @a) (inferNodeB' @a (apply' @a) c s a b )
    leaf_cases c s a@(a_id, Leaf True) b@(b_id, EndClassNode bc) = withCache c (a, b, s) $
        endclass_case @a c s a_id b_id (1,0) bc
    leaf_cases c s a@(a_id, EndClassNode ac) b@(b_id, Leaf True) = withCache c (a, b, s) $
        endclass_case @a c s a_id b_id ac (1,0)
    leaf_cases c s a@(a_id, Leaf False) b@(b_id, EndClassNode bc) = withCache c (a, b, s) $
        endclass_case @a c s a_id b_id (2,0) bc
    leaf_cases c s a@(a_id, EndClassNode ac) b@(b_id, Leaf False) = withCache c (a, b, s) $
        endclass_case @a c s a_id b_id ac (2,0)
    leaf_cases c s a@(a_id, Leaf _) b@(b_id, ClassNode{}) = withCache c (a, b, s) $
        applyClassA @a c s a b
    leaf_cases c s a@(a_id, ClassNode {}) b@(b_id, Leaf _) = withCache c (a, b, s) $
        applyClassB @a c s a b

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
    leaf_cases c "union" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then (c, a) else (c, b)
    leaf_cases c "inter" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then (c, b) else (c, a)

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

    -- Cases 5-6: EndClassNode vs Node (note: B uses @Dc@ inference when inferring)
    applyDcB' c s a@(a_id, EndClassNode _) b@(b_id, Node idx _ _) = withCache c (a, b, (s ++ "Dc")) $ uncurry (applyElimRule @a) (inferNodeA' @a (applyDcB' @a) c s a b)
    applyDcB' c s a@(a_id, Node{}) b@(b_id, EndClassNode _) = withCache c (a, b, (s ++ "Dc")) $ uncurry (applyElimRule @a) (inferNodeB' @Dc (applyDcB' @a) c s a b)
    applyDcB' c s a@(a_id, EndClassNode ac) b@(b_id, EndClassNode bc) = withCache c (a, b, (s ++ "Dc")) $
        endclass_case @a c s a_id b_id ac bc

    -- Cases 7-9: Node vs Node (B is from Dc, so uses @Dc@ inference when positionA < positionB)
    applyDcB' c s a@(a_id, Node positionA pos_childA neg_childA)  b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB =
            let c_ = traverse_dc @a "pos child" c a_id b_id
                (c', (pos_result, _)) = applyDcB @a c_ s pos_childA pos_childB

                c_' = traverse_dc @a "neg child" (reset_stack_bin c' c) a_id b_id
                (c'', (neg_result, _)) = applyDcB @a c_' s neg_childA neg_childB
            in withCache c (a, b, (s ++ "Dc")) $ applyElimRule @a (reset_stack_bin c'' c) (Node positionA pos_result neg_result)
        | positionA < positionB = uncurry (applyElimRule @a) (inferNodeB' @Dc (applyDcB' @a) c s a b)  -- B is Dc, use @Dc@ inference
        | positionA > positionB = uncurry (applyElimRule @a) (inferNodeA' @a (applyDcB' @a) c s a b)

    -- Cases 10-15: ClassNode vs Node/ClassNode/EndClassNode (similar to apply', but B uses @Dc@ when wrapping)
    applyDcB' c s a@(a_id, ClassNode positionA _ _ _) b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB = withCache c (a, b, (s ++ "Dc")) $
                uncurry (applyElimRule @a) (inferNodeA' @a (applyDcB' @a) c s a b)
        | positionA < positionB = withCache c (a, b, (s ++ "Dc")) $
                applyClassBAs @Dc @a c s a b  -- B is Dc
    applyDcB' c s a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, ClassNode positionB _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA < positionB = withCache c (a, b, (s ++ "Dc")) $
                uncurry (applyElimRule @a) (inferNodeB' @Dc (applyDcB' @a) c s a b)  -- B is Dc
        | positionA > positionB = withCache c (a, b, (s ++ "Dc")) $
                applyClassA @a c s a b
    applyDcB' c s a@(a_id, ClassNode positionA _ _ _)  b@(b_id, ClassNode positionB _ _ _)
        | positionA == positionB = applyClass @a c s a b
        | positionA < positionB = applyClassBAs @Dc @a c s a b  -- wrap B as Dc, process with outer context @a
        | positionA > positionB = applyClassA @a c s a b
    applyDcB' c s a@(_, EndClassNode _) b@(_, ClassNode{}) = withCache c (a, b, (s ++ "Dc")) $ applyClassA @a c s a b
    applyDcB' c s a@(_, ClassNode{}) b@(_, EndClassNode _) = withCache c (a, b, (s ++ "Dc")) $ applyClassBAs @Dc @a c s a b


    dcB_leaf_cases c s a@(_, Leaf _) b@(_, Node{}) = withCache c (a, b, s ++ "Dc") $ uncurry (applyElimRule @a) (inferNodeA' @a (applyDcB' @a) c s a b )
    dcB_leaf_cases c s a@(_, Node{}) b@(_, Leaf _) = withCache c (a, b, s ++ "Dc") $ uncurry (applyElimRule @a) (inferNodeB' @Dc (applyDcB' @a) c s a b)  -- B is Dc
    dcB_leaf_cases c s a@(a_id, Leaf True) b@(b_id, EndClassNode bc) = withCache c (a, b, s ++ "Dc") $
        endclass_case @a c s a_id b_id (1,0) bc
    dcB_leaf_cases c s a@(a_id, EndClassNode ac) b@(b_id, Leaf True) = withCache c (a, b, s ++ "Dc") $
        endclass_case @a c s a_id b_id ac (1,0)
    dcB_leaf_cases c s a@(a_id, Leaf False) b@(b_id, EndClassNode bc) = withCache c (a, b, s ++ "Dc") $
        endclass_case @a c s a_id b_id (2,0) bc
    dcB_leaf_cases c s a@(a_id, EndClassNode ac) b@(b_id, Leaf False) = withCache c (a, b, s ++ "Dc") $
        endclass_case @a c s a_id b_id ac (2,0)
    dcB_leaf_cases c s a@(a_id, Leaf _) b@(b_id, ClassNode{}) = withCache c (a, b, s ++ "Dc") $
        applyClassA @a c s a b
    dcB_leaf_cases c s a@(a_id, ClassNode {}) b@(b_id, Leaf _) = withCache c (a, b, s ++ "Dc") $
        applyClassBAs @Dc @a c s a b  -- wrap B as Dc, process with outer context @a

    -- Unknown resolution: if A is Unknown, return it (it will resolve to dcA elsewhere)
    -- If B is Unknown, resolve it by popping dcB from stack
    dcB_leaf_cases c s a@(_, Unknown) b = (c, a)  -- A is Unknown, return as-is
    dcB_leaf_cases c s a b@(_, Unknown) =  -- B is Unknown, resolve from dcB
        let (c', dcB) = pop_dcB'' c
        in applyDcB' @a c' s a dcB
    dcB_leaf_cases c "union" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then (c, a) else (c, b)
    dcB_leaf_cases c "inter" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then (c, b) else (c, a)

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

    -- Cases 5-6: EndClassNode vs Node (note: A uses @Dc@ inference when inferring)
    applyDcA' c s a@(a_id, EndClassNode _) b@(b_id, Node idx _ _) = withCache c (a, b, (s ++ "Dc")) $ uncurry (applyElimRule @a) (inferNodeA' @Dc (applyDcA' @a) c s a b)   -- A is Dc
    applyDcA' c s a@(a_id, Node{}) b@(b_id, EndClassNode _) = (withCache c (a, b, (s ++ "Dc")) $ uncurry (applyElimRule @a) (inferNodeB' @a (applyDcA' @a) c s a b))
    applyDcA' c s a@(a_id, EndClassNode ac) b@(b_id, EndClassNode bc) = withCache c (a, b, (s ++ "Dc")) $
        endclass_case @a c s a_id b_id ac bc

    -- Cases 7-9: Node vs Node (A is from Dc, so uses @Dc@ inference when positionA > positionB)
    applyDcA' c s a@(a_id, Node positionA pos_childA neg_childA)  b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB =
            let c_ = traverse_dc @a "pos child" c a_id b_id
                (c', (pos_result, _)) = applyDcA @a c_ s pos_childA pos_childB

                c_' = traverse_dc @a "neg child" (reset_stack_bin c' c) a_id b_id
                (c'', (neg_result, _)) = applyDcA @a c_' s neg_childA neg_childB
            in withCache c (a, b, (s ++ "Dc")) $ applyElimRule @a (reset_stack_bin c'' c) (Node positionA pos_result neg_result)
        | positionA < positionB = uncurry (applyElimRule @a) (inferNodeB' @a (applyDcA' @a) c s a b)
        | positionA > positionB = uncurry (applyElimRule @a) (inferNodeA' @Dc (applyDcA' @a) c s a b)  -- A is Dc, use @Dc@ inference

    -- Cases 10-15: ClassNode vs Node/ClassNode/EndClassNode (similar to apply', but A uses @Dc@ when wrapping)
    applyDcA' c s a@(a_id, ClassNode positionA _ _ _) b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB = withCache c (a, b, (s ++ "Dc")) $
                uncurry (applyElimRule @a) (inferNodeA' @Dc (applyDcA' @a) c s a b)  -- A is Dc
        | positionA < positionB = withCache c (a, b, (s ++ "Dc")) $
                applyClassB @a c s a b
    applyDcA' c s a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, ClassNode positionB _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA < positionB = withCache c (a, b, (s ++ "Dc")) $
                uncurry (applyElimRule @a) (inferNodeB' @a (applyDcA' @a) c s a b)
        | positionA > positionB = withCache c (a, b, (s ++ "Dc")) $
                applyClassAAs @Dc @a c s a b  -- A is Dc
    applyDcA' c s a@(a_id, ClassNode positionA _ _ _)  b@(b_id, ClassNode positionB _ _ _)
        | positionA == positionB = applyClass @a c s a b
        | positionA < positionB = applyClassB @a c s a b
        | positionA > positionB = applyClassAAs @Dc @a c s a b  -- wrap A as Dc, process with outer context @a
    applyDcA' c s a@(_, EndClassNode _) b@(_, ClassNode{}) = withCache c (a, b, (s ++ "Dc")) $ applyClassAAs @Dc @a c s a b
    applyDcA' c s a@(_, ClassNode{}) b@(_, EndClassNode _) = withCache c (a, b, (s ++ "Dc")) $ applyClassB @a c s a b

    dcA_leaf_cases c s a@(_, Leaf _) b@(_, Node{}) = withCache c (a, b, s ++ "Dc") $ uncurry (applyElimRule @a) (inferNodeA' @Dc (applyDcA' @a) c s a b )  -- A is Dc
    dcA_leaf_cases c s a@(_, Node{}) b@(_, Leaf _) = withCache c (a, b, s ++ "Dc") $ uncurry (applyElimRule @a) (inferNodeB' @a (applyDcA' @a) c s a b)
    dcA_leaf_cases c s a@(a_id, Leaf True) b@(b_id, EndClassNode bc) = withCache c (a, b, s ++ "Dc") $
        endclass_case @a c s a_id b_id (1,0) bc
    dcA_leaf_cases c s a@(a_id, EndClassNode ac) b@(b_id, Leaf True) = withCache c (a, b, s ++ "Dc") $
        endclass_case @a c s a_id b_id ac (1,0)
    dcA_leaf_cases c s a@(a_id, Leaf False) b@(b_id, EndClassNode bc) = withCache c (a, b, s ++ "Dc") $
        endclass_case @a c s a_id b_id (2,0) bc
    dcA_leaf_cases c s a@(a_id, EndClassNode ac) b@(b_id, Leaf False) = withCache c (a, b, s ++ "Dc") $
        endclass_case @a c s a_id b_id ac (2,0)
    dcA_leaf_cases c s a@(a_id, Leaf _) b@(b_id, ClassNode{}) = withCache c (a, b, s ++ "Dc") $
        applyClassAAs @Dc @a c s a b  -- wrap A as Dc, process with outer context @a
    dcA_leaf_cases c s a@(a_id, ClassNode {}) b@(b_id, Leaf _) = withCache c (a, b, s ++ "Dc") $
        applyClassB @a c s a b

    -- Unknown resolution: if A is Unknown, resolve it by popping dcA from stack
    -- If B is Unknown, return it as-is (it will resolve to dcB elsewhere)
    dcA_leaf_cases c s a@(_, Unknown) b =  -- A is Unknown, resolve from dcA
        let (c', dcA) = pop_dcA'' c
        in applyDcA' @a c' s dcA b
    dcA_leaf_cases c s a b@(_, Unknown) = (c, b)  -- B is Unknown, return as-is
    dcA_leaf_cases c "union" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then (c, a) else (c, b)
    dcA_leaf_cases c "inter" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then (c, b) else (c, a)

    -- | Handles the case when both arguments are EndClassNode (both exiting their class hierarchies).
    -- | This function:
    -- |   1. Pops the inference type stack to determine which inference contexts (Dc/Neg/Pos) were used
    -- |   2. Applies the appropriate binary operation based on the combination of inference types
    -- |   3. Wraps the result in an EndClassNode to maintain the class hierarchy structure
    -- | The inference type combinations determine which version of apply to use

    endclass_case c s a_id b_id ac bc = let
        (c_, (infA, infB)) = pop_stack' c
        c' = traverse_dc @a "endclass" c_ a_id b_id
        (c'', (r, _)) = case (infA, infB) of
            (Dc, Dc) -> apply @Dc c' s ac bc
            (Neg, Neg) -> apply @Neg c' s ac bc
            (Pos, Pos) -> apply @Pos c' s ac bc
            (Neg, Dc) -> applyDcB @Neg c' s ac bc
            (Pos, Dc) -> applyDcB @Pos c' s ac bc
            (Dc, Neg) -> applyDcA @Neg c' s ac bc
            (Dc, Pos) -> applyDcA @Pos c' s ac bc
            r'@(_, _) -> error ("weird combination after pop stack: " ++ show r')
        in applyElimRule @a (reset_stack_bin c'' c) (EndClassNode r)

-- | ======================== ClassNode Application Logic ========================
-- |
-- | These functions handle binary operations when at least one argument is an ClassNode (class-defining node).
-- |
-- | The algorithm:
-- |   1. First compute dcR (the resulting continuous branch using the don't-care literal inference/elimination rule) by applying operation to dcA and dcB
-- |   2. Then compute nR (branch using negative literal inference/elimination rule) using dcR as the continuous background
-- |   3. Then compute pR (branch using positive literal inference/elimination rule) using dcR as the continuous background
-- |   4. Combine results into a new ClassNode with the three computed branches
-- |
-- | The dc_stack is updated at each step:
-- |   - For dc branch: Push Unknown placeholders (dcR not yet computed)
-- |   - For neg/pos branches: Push the computed dcR as the continuous background
-- |
-- | Note: The actual exception type (neg1/neg0 or pos1/pos0) depends on what dcR evaluates to.
applyClass :: forall a. (DdF3 a) => BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
applyClass c s a b = debug_manipulation_inf (applyClass' @a c s a b) s (s ++ to_str @a) c a b

applyClass' :: forall a. (DdF3 a) => BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
applyClass' c s a@(a_id, ClassNode positionA dcA pA nA) b@(b_id, ClassNode positionB dcB pB nB)
    | positionA == positionB =
        let
            c_ = add_to_stack (positionA, Dc) (((0, 0), Unknown), ((0, 0), Unknown), ((0, 0), Unknown)) (traverse_dc @a "class dc" c a_id b_id)
            (c1, dcR) = apply @Dc c_ s dcA dcB
            (c1', dcR') = absorb_dc @Dc c1 positionA dcR

            c2_ = add_to_stack (positionA, Neg) (getNode c dcA, getNode c dcB, dcR) (traverse_dc @a "class neg" (reset_stack_bin c1' c) a_id b_id)
            (c2, nR) = apply @Neg c2_ s nA nB
            (c2', nR') = absorb @Neg c2 positionA dcR' nR

            c3_ = add_to_stack (positionA, Pos) (getNode c dcA, getNode c dcB, dcR) (traverse_dc @a "class pos" (reset_stack_bin c2' c) a_id b_id)
            (c3, pR) = apply @Pos c3_ s pA pB
            (c3', pR') = absorb @Pos c3 positionA dcR' pR

            c4 = reset_stack_bin c3' c

        in applyElimRule @a c4 $ ClassNode positionA (fst dcR') (fst pR') (fst nR')
    | positionA > positionB = applyClassA @a c s a b  -- A's class comes after, wrap A
    | positionA < positionB = applyClassB @a c s a b  -- B's class comes after, wrap B
applyClass' c s a@(_, ClassNode {}) b@(_, Leaf _) = applyClassB @a c s a b  -- Wrap Leaf in ClassNode's class
applyClass' c s a@(_, ClassNode{}) b@(_, EndClassNode _) = applyClassB @a c s a b
applyClass' c s a@(_, Leaf _) b@(_, ClassNode{}) = applyClassA @a c s a b  -- Wrap Leaf in ClassNode's class
applyClass' c s a@(_, EndClassNode _) b@(_, ClassNode{}) = applyClassA @a c s a b
applyClass' _ s _ _ = error ("apply class error: " ++ s)


applyClassA :: forall a. (DdF3 a) => BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
applyClassA c s (a_id, _) b@(_, ClassNode positionB _ _ _) = let
        (c', r) = insert c (EndClassNode a_id)
        (c'', r') = inferClassNode @a c' positionB r
    in applyClass @a c'' s r' b
applyClassA _ _ _ _ = error "should not be possible"

-- | Like applyClassA, but wraps A using inference type @w@ while processing with inference type @a@.
applyClassAAs :: forall w a. (DdF3 w, DdF3 a) => BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
applyClassAAs c s (a_id, _) b@(_, ClassNode positionB _ _ _) = let
        (c', r) = insert c (EndClassNode a_id)
        (c'', r') = inferClassNode @w c' positionB r
    in applyClass @a c'' s r' b
applyClassAAs _ _ _ _ = error "should not be possible"

applyClassB :: forall a. (DdF3 a) => BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
applyClassB c s a@(_, ClassNode positionA _ _ _) b@(b_id, _) = let
        (c', r) = insert c (EndClassNode b_id)
        (c'', r') = inferClassNode @a c' positionA r
    in applyClass @a c'' s a r'
applyClassB _ _ _ _ = error "should not be possible"

-- | Like applyClassB, but wraps B using inference type @w@ while processing with inference type @a@.
-- Used when B comes from a Dc branch (wrap as Dc) but the result lives in a different context.
applyClassBAs :: forall w a. (DdF3 w, DdF3 a) => BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
applyClassBAs c s a@(_, ClassNode positionA _ _ _) b@(b_id, _) = let
        (c', r) = insert c (EndClassNode b_id)
        (c'', r') = inferClassNode @w c' positionA r
    in applyClass @a c'' s a r'
applyClassBAs _ _ _ _ = error "should not be possible"


-- | Helper wrapper for inferred node recursive calls.
-- | These functions bridge between the Dd1 typeclass (which works with Nodes) and the DdF3
-- | typeclass (which works with Dd and handles inference rules).
inferNodeA' :: forall a. DdF3 a => (BiOpContext -> String -> Node -> Node -> (BiOpContext, Node))
            -> BiOpContext -> String -> Node -> Node -> (BiOpContext, Dd)
inferNodeA' f c s a b = inferNodeA @a f c s a b

inferNodeB' :: forall a. DdF3 a => (BiOpContext -> String -> Node -> Node -> (BiOpContext, Node))
            -> BiOpContext -> String -> Node -> Node -> (BiOpContext, Dd)
inferNodeB' f c s a b = inferNodeB @a f c s a b