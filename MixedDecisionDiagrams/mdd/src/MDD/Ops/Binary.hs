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
import MDD.Draw (debug_manipulation, debug_dc_traverse)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Map as Map
import Data.Kind (Constraint)

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
-- |
-- | Case 1: Function cache exists, and this exact (nodeA, nodeB, dc_stack) combination was seen before
-- |   -> Return cached result immediately
-- | Case 2: Function cache exists, but this combination is new
-- |   -> Execute the computation, then store result with updated dc_stack in cache
-- | Case 3: Function not in cache (shouldn't happen with proper initialization)
-- |   -> Error
withCache :: BinaryOperatorContext -> (Node, Node, String) -> (BinaryOperatorContext, Node) -> (BinaryOperatorContext, Node)
withCache c@BinaryOperatorContext{bin_cache = nc, bin_dc_stack = dck} ((keyA, _), (keyB, _), keyFunc) func_with_args =
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
-- * Redundancy Elimination (absorb)
-- ==========================================================================================================

-- | Main entry point for the absorb function.
-- | The absorb function maintains canonical representation by eliminating redundant branches.
-- | If a discrete branch (Pos or Neg) evaluates to the same result as the continuous background (dcR),
-- | that branch is redundant and can be replaced with Unknown (which will resolve to dcR during evaluation).
absorb :: (BinaryOperatorContext, Node) -> (BinaryOperatorContext, Node)
absorb (c, n) = absorb' (c, n)

-- | Recursively checks if a node's evaluation matches the continuous background (dcR) at the current level.
-- | If it matches, the node is "absorbed" (replaced with Unknown) to maintain minimal graph representation.
-- |
-- | Case 1: dcR is Unknown (lazy evaluation from deeper layer)
-- |   -> Pop the Unknown from stack and recurse on remaining layers
-- | Case 2: Node a is Unknown
-- |   -> Cannot compare, return as-is (Unknown will resolve during evaluation)
-- | Case 3: Both a and dcR are Leaf values
-- |   -> If they match, replace a with Unknown (absorbed into continuous background)
-- |   -> Otherwise, keep a as discrete exception
-- | Case 4: dcR is Leaf, a is InfNodes
-- |   -> Recursively check all three branches (dc, pos, neg) of the InfNode
-- |   -> If all three branches match dcR, the entire InfNode is redundant -> replace with Unknown
-- |   -> Otherwise, keep the InfNode (it represents exceptions to the continuous background)
-- | Case 5: dcR is Leaf, a is EndInfNode
-- |   -> Check if the child of EndInfNode matches dcR
-- |   -> If yes, absorb (replace with Unknown); otherwise keep
-- | Case 6: Both dcR and a are EndInfNodes
-- |   -> Compare their child nodes; if equal, absorb
-- | Case 7: Generic comparison (dcR is a Node or other structure)
-- |   -> If a structurally equals dcR, absorb; otherwise keep
-- | Case 8: Empty dc_stack (top level, no continuous background to compare against)
-- |   -> Return as-is (no absorption possible)
absorb' :: (BinaryOperatorContext, Node) -> (BinaryOperatorContext, Node)
-- | given a dcR and a pos or ng results, sets sub-paths in the local inf-domain which agree with the dcR to unknown ("absorbing them")
absorb' (c@BinaryOperatorContext{bin_dc_stack = (dcA, dcB, dc@(_, Unknown) : fs) }, a)  =
    let (c', r) = absorb' (c{bin_dc_stack = (dcA, dcB, fs)}, a) in (c, r)
absorb' (c@BinaryOperatorContext{bin_dc_stack = (_, _, dc : fs) }, a@(_, Unknown)) = (c, a)
absorb' (c@BinaryOperatorContext{bin_dc_stack = (_, _, dc : fs) }, a@(_, Leaf _))
    | a == dc = (c, ((0,0), Unknown))  -- Leaf matches dcR: absorb into continuous background
    | otherwise = (c,a)  -- Leaf differs: keep as discrete exception
absorb' (c@BinaryOperatorContext{bin_dc_stack = (_, _, dc@(_, Leaf _)  : fs) }, a@(_, InfNodes _ d p n))  =  let
    (_, r1) = absorb' (c, getNode c d)  -- Check dc branch
    (_, r2) = absorb' (c, getNode c p)  -- Check pos branch
    (_, r3) = absorb' (c, getNode c n)  -- Check neg branch
    in if r1 == r2 && r2 == r3 then (c, ((0,0), Unknown)) else (c, a)  -- All branches match: absorb entire InfNode
absorb' (c@BinaryOperatorContext{bin_dc_stack = (_, _, dc@(_, Leaf _)  : fs) }, a@(_, EndInfNode a_child)) = if getNode c a_child == dc then (c, ((0,0), Unknown)) else (c, a)
absorb' (c@BinaryOperatorContext{bin_dc_stack = (_, _, dc@(_, EndInfNode dc') : fs) }, a@(_, EndInfNode a'))
    | a' == dc' = (c, ((0,0), Unknown))  -- EndInfNode children match: absorb
    | otherwise = (c,a)
absorb' (c@BinaryOperatorContext{bin_dc_stack = (_, _, dc : fs) }, a)
    | a == dc = (c, ((0,0), Unknown))  -- Generic structural match: absorb
    | otherwise = (c,a)
absorb' (c@BinaryOperatorContext{bin_dc_stack = (_, _, []) }, a) = (c, a)  -- Top level: no dcR to compare against

-- ==========================================================================================================
-- * Binary Operation Typeclass (Dd1)
-- ==========================================================================================================

-- | The Dd1 typeclass defines binary operations (union, intersection, etc.) parameterized by
-- | the inference type @a@ (Dc, Neg, or Pos). The inference type determines which elimination
-- | rules are applied during traversal (see DdF3 in MDD.Traversal).
-- |
-- | Key methods:
-- |   - apply/apply': Main binary operation on two nodes
-- |   - applyDcB/applyDcB': Binary operation where argument B is from a Dc (continuous) branch
-- |   - applyDcA/applyDcA': Binary operation where argument A is from a Dc (continuous) branch
-- |   - leaf_cases/dcB_leaf_cases/dcA_leaf_cases: Handle terminal cases (Leaf, Unknown, etc.)
-- |   - endinf_case: Handle EndInfNode encounters (moving up the class hierarchy)
type Dd1 :: Inf -> Constraint
class Dd1 a where
    leaf_cases :: BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node)
    dcB_leaf_cases :: BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node)
    dcA_leaf_cases :: BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node)
    apply :: BinaryOperatorContext -> String -> NodeId -> NodeId -> (BinaryOperatorContext, Node)
    apply'' :: BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node)
    applyDcB :: BinaryOperatorContext -> String -> NodeId -> NodeId -> (BinaryOperatorContext, Node)
    applyDcB'' :: BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node)
    applyDcA :: BinaryOperatorContext -> String -> NodeId -> NodeId -> (BinaryOperatorContext, Node)
    applyDcA'' :: BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node)

    apply' :: BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node)
    applyDcB' :: BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node)
    applyDcA' :: BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node)
    endinf_case :: BinaryOperatorContext -> String -> NodeId -> NodeId -> NodeId -> NodeId -> (BinaryOperatorContext, Node)

instance (DdF3 a, Dd1_helper a) => Dd1 a where
    -- | Main entry point: converts NodeIds to Nodes and wraps with debug output
    apply c s a b = debug_manipulation (apply' @a c s (getNode c a) (getNode c b)) s (s ++ to_str @a) c (getNode c a) (getNode c b)
    -- | Internal version without debug wrapper (used to avoid double printing in recursive calls)
    apply'' c s a b = apply' @a c s a b

    -- | Main binary operation dispatcher. Handles all combinations of node types.
    -- | Pattern matches are ordered from most specific to most general.

    -- Cases 1-4: At least one argument is a terminal (Leaf or Unknown)
    --   -> Delegate to leaf_cases for terminal handling
    apply' c s a@(_, Leaf _) b = leaf_cases @a c s a b
    apply' c s a b@(_, Leaf _) = leaf_cases @a c s a b
    apply' c s a@(_, Unknown) b = leaf_cases @a c s a b
    apply' c s a b@(_, Unknown) = leaf_cases @a c s a b

    -- Cases 5-6: EndInfNode vs Node (hierarchy mismatch)
    --   -> EndInfNode means we're exiting a class, but Node means we're still in that class
    --   -> Need to infer what the EndInfNode's argument should be at the Node's position
    --   -> Uses inference rules (DdF3) to create missing nodes
    apply' c s a@(a_id, EndInfNode _) b@(b_id, Node idx _ _) = withCache c (a, b, s) $ uncurry (applyElimRule @a) (inferNodeA' @a (apply'' @a) c s a b)
    apply' c s a@(a_id, Node{}) b@(b_id, EndInfNode _) = withCache c (a, b, s) $ uncurry (applyElimRule @a) (inferNodeB' @a (apply'' @a) c s a b)

    -- Case 7: Both arguments are EndInfNodes (both exiting their respective classes)
    --   -> Pop the inference type stack to determine which inference context to use
    --   -> Then apply operation in the parent class context
    apply' c s a@(a_id, EndInfNode ac) b@(b_id, EndInfNode bc) = withCache c (a, b, s) $
        endinf_case @a c s a_id b_id ac bc

    -- Cases 8-10: Both arguments are regular Nodes (variable nodes)
    --   -> Compare positions to determine traversal strategy
    apply' c s a@(a_id, Node positionA pos_childA neg_childA)  b@(b_id, Node positionB pos_childB neg_childB)
        -- Case 8: Positions match (same variable)
        --   -> Traverse both positive and negative branches in parallel
        --   -> traverse_dc synchronizes dc_stack traversal with main traversal (handles "catch-up")
        --   -> reset_stack_bin restores original stack state between branches
        | positionA == positionB =
            let c_ = traverse_dc @a "pos child" c pos_childA pos_childB  -- Sync dc_stack for pos branch
                (c', (pos_result, _)) = apply @a c_ s pos_childA pos_childB

                c_' = traverse_dc @a "neg child" (reset_stack_bin c' c) neg_childA neg_childB  -- Sync dc_stack for neg branch
                (c'', (neg_result, _)) = apply @a c_' s neg_childA neg_childB
            in withCache c (a, b, s) $ applyElimRule @a (reset_stack_bin c'' c) (Node positionA pos_result neg_result)
        -- Case 9: positionA < positionB (A's variable comes before B's in ordering)
        --   -> B is missing variable at positionA, so infer B's value at that position
        --   -> Uses inference rules to create a node for B at positionA
        | positionA < positionB = uncurry (applyElimRule @a) (inferNodeB' @a (apply'' @a) c s a b)
        -- Case 10: positionA > positionB (B's variable comes before A's)
        --   -> A is missing variable at positionB, so infer A's value at that position
        | positionA > positionB = uncurry (applyElimRule @a) (inferNodeA' @a (apply'' @a) c s a b)

    -- Cases 11-13: InfNodes vs Node (entering/exiting class hierarchy)
    --   -> InfNodes represents a class-defining node (with dc, pos, neg branches)
    --   -> Node represents a regular variable node
    apply' c s a@(a_id, InfNodes positionA _ _ _) b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        -- Case 11: positionA > positionB (InfNode's class comes after Node's variable)
        --   -> Node is missing the class context, infer Node's value in the class context
        | positionA > positionB = withCache c (a, b, s) $
                uncurry (applyElimRule @a) (inferNodeA' @a (apply'' @a) c s a b)
        -- Case 12: positionA < positionB (InfNode's class comes before Node's variable)
        --   -> Need to enter the class hierarchy: applyInfB wraps Node in the class context
        --   -> absorb eliminates redundant branches after entering class
        | positionA < positionB = withCache c (a, b, s) $
                absorb $ applyInfB @a c s a b
    apply' c s a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        -- Case 13: positionA > positionB (Node's variable comes after InfNode's class)
        --   -> Need to enter class hierarchy: applyInfA wraps Node in the class context
        | positionA > positionB = withCache c (a, b, s) $
                absorb $ applyInfA @a c s a b
        -- Case 14: positionA < positionB (Node's variable comes before InfNode's class)
        --   -> InfNode is missing the variable, infer InfNode's value at that variable position
        | positionA < positionB = withCache c (a, b, s) $
                uncurry (applyElimRule @a) (inferNodeB' @a (apply'' @a) c s a b)

    -- Cases 15-17: Both arguments are InfNodes (class hierarchy operations)
    --   -> When positions match, apply operation within the class (applyInf)
    --   -> When positions differ, one needs to be wrapped in the other's class context
    apply' c s a@(a_id, InfNodes positionA _ _ _)  b@(b_id, InfNodes positionB _ _ _)
        -- Case 15: Positions match (same class)
        --   -> Apply operation within the class: compute dc, pos, and neg branches separately
        | positionA == positionB = withCache c (a, b, s) $ absorb $ applyInf @a c s a b
        -- Case 16: positionA < positionB (A's class comes before B's)
        --   -> Wrap B in A's class context
        | positionA < positionB = withCache c (a, b, s) $ absorb $ applyInfB @a c s a b
        -- Case 17: positionA > positionB (A's class comes after B's)
        --   -> Wrap A in B's class context
        | positionA > positionB = withCache c (a, b, s) $ absorb $ applyInfA @a c s a b

    -- Cases 18-19: EndInfNode vs InfNodes (exiting one class while entering another)
    --   -> EndInfNode means exiting a class, InfNodes means entering a class
    --   -> Wrap the EndInfNode's result in the InfNode's class context
    apply' c s a@(a_id, EndInfNode _) b@(b_id, InfNodes{}) = withCache c (a, b, s) $ absorb $ applyInfA @a c s a b
    apply' c s a@(a_id, InfNodes{}) b@(b_id, EndInfNode _) = withCache c (a, b, s) $ absorb $ applyInfB @a c s a b

    -- | Handles all cases where at least one argument is a terminal value (Leaf, Unknown, EndInfNode, InfNodes).
    -- | This function dispatches to specialized handlers based on the combination of terminal types.

    -- Cases 1-2: Leaf vs Node (terminal vs non-terminal)
    --   -> Leaf is a constant, Node needs to be evaluated at all positions
    --   -> Infer what the Node should evaluate to given the Leaf constant
    leaf_cases c s a@(_, Leaf _) b@(_, Node{}) = withCache c (a, b, s) $ uncurry (applyElimRule @a) (inferNodeA' @a (apply'' @a) c s a b)
    leaf_cases c s a@(_, Node{}) b@(_, Leaf _) = withCache c (a, b, s) $ uncurry (applyElimRule @a) (inferNodeB' @a (apply'' @a) c s a b )

    -- Cases 3-6: Leaf vs EndInfNode (constant vs class exit)
    --   -> EndInfNode means we're exiting a class hierarchy
    --   -> Leaf True maps to NodeId (1,0) = top, Leaf False maps to (2,0) = bot
    --   -> Use endinf_case to handle the class exit properly
    leaf_cases c s a@(a_id, Leaf True) b@(b_id, EndInfNode bc) = withCache c (a, b, s) $
        endinf_case @a c s a_id b_id (1,0) bc
    leaf_cases c s a@(a_id, EndInfNode ac) b@(b_id, Leaf True) = withCache c (a, b, s) $
        endinf_case @a c s a_id b_id ac (1,0)
    leaf_cases c s a@(a_id, Leaf False) b@(b_id, EndInfNode bc) = withCache c (a, b, s) $
        endinf_case @a c s a_id b_id (2,0) bc
    leaf_cases c s a@(a_id, EndInfNode ac) b@(b_id, Leaf False) = withCache c (a, b, s) $
        endinf_case @a c s a_id b_id ac (2,0)

    -- Cases 7-8: Leaf vs InfNodes (constant vs class entry)
    --   -> InfNodes represents entering a class hierarchy
    --   -> Wrap the Leaf constant in the class context (applyInfA/applyInfB)
    leaf_cases c s a@(a_id, Leaf _) b@(b_id, InfNodes{}) = withCache c (a, b, s) $
        applyInfA @a c s a b
    leaf_cases c s a@(a_id, InfNodes {}) b@(b_id, Leaf _) = withCache c (a, b, s) $
        applyInfB @a c s a b

    -- Cases 9-11: Unknown resolution
    --   -> Unknown is a lazy leaf that resolves to the continuous background (dc branch)
    --   -> When Unknown is encountered, we need to look up the dc branch from the dc_stack
    --   -> dcA and dcB are the continuous branches for arguments A and B respectively
    leaf_cases c s a@(_, Unknown) b@(_, Unknown) = (c , a)  -- Both Unknown: return first (they'll resolve the same)
    leaf_cases c s a@(_, Unknown) b = -- Resolve Unknown in argument A
        -- Pop dcA from stack (the continuous branch for argument A at current/previous layer)
        -- Then apply operation with dcA instead of Unknown
        let (c', dcA) = pop_dcA' c
        in applyDcA'' @a c' s dcA b
    leaf_cases c s a b@(_, Unknown) = -- Resolve Unknown in argument B
        -- Pop dcB from stack (the continuous branch for argument B at current/previous layer)
        let (c', dcB) = pop_dcB' c
        in applyDcB'' @a c' s a dcB

    -- Cases 12-13: Union/Intersection specific logic for Leaf vs Leaf
    --   -> These are the base cases for boolean operations
    --   -> Union: if A is True, result is True (A); otherwise result is B
    --   -> Intersection: if A is True, result is B; otherwise result is False (A)
    --   -> absorb ensures result is canonical (may replace with Unknown if redundant)
    leaf_cases c "union" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then absorb (c, a) else absorb (c, b)
    leaf_cases c "inter" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then absorb (c, b) else absorb (c, a)

    -- Fallback: should not happen with proper type handling
    leaf_cases c s a b = error ("leaf case: " ++ s)

-- | ======================== DC versions (Argument B is DC type) ========================
-- |
-- | These functions handle binary operations where argument B comes from a Dc (continuous/don't-care) branch.
-- | The key difference is that when inferring nodes for B, we use @Dc@ inference rules instead of @a@.
-- | This is because B represents the continuous background, so its elimination rules follow Dc semantics.

    -- | Entry point for applyDcB: converts NodeIds to Nodes and wraps with debug
    applyDcB c s a b = debug_manipulation (applyDcB' @a c s (getNode c a) (getNode c b)) s (s ++ "DcB " ++ to_str @a) c (getNode c a) (getNode c b)
    -- | Internal version without debug wrapper
    applyDcB'' c s a b = applyDcB' @a c s a b

    -- | Binary operation where B is from Dc branch. Similar structure to apply', but:
    -- |   - When inferring nodes for B, uses @Dc@ inference rules (inferNodeB' @Dc)
    -- |   - Cache key includes "Dc" suffix to distinguish from regular operations
    -- |   - All cases mirror apply' but with Dc-specific inference for argument B

    -- Cases 1-4: Terminal values -> delegate to dcB_leaf_cases
    applyDcB' c s a@(_, Leaf _) b = dcB_leaf_cases @a c s a b
    applyDcB' c s a b@(_, Leaf _) = dcB_leaf_cases @a c s a b
    applyDcB' c s a@(_, Unknown) b = dcB_leaf_cases @a c s a b
    applyDcB' c s a b@(_, Unknown) = dcB_leaf_cases @a c s a b

    -- Cases 5-6: EndInfNode vs Node (note: B uses @Dc@ inference when inferring)
    applyDcB' c s a@(a_id, EndInfNode _) b@(b_id, Node idx _ _) = withCache c (a, b, (s ++ "Dc")) $ uncurry (applyElimRule @a) (inferNodeA' @a (applyDcB'' @a) c s a b)
    applyDcB' c s a@(a_id, Node{}) b@(b_id, EndInfNode _) = withCache c (a, b, (s ++ "Dc")) $ uncurry (applyElimRule @a) (inferNodeB' @Dc (applyDcB'' @a) c s a b)
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
        | positionA < positionB = uncurry (applyElimRule @a) (inferNodeB' @Dc (applyDcB'' @a) c s a b)  -- B is Dc, use @Dc@ inference
        | positionA > positionB = uncurry (applyElimRule @a) (inferNodeA' @a (applyDcB'' @a) c s a b)

    -- Cases 10-15: InfNodes vs Node/InfNodes/EndInfNode (similar to apply', but B uses @Dc@ when wrapping)
    applyDcB' c s a@(a_id, InfNodes positionA _ _ _) b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB = withCache c (a, b, (s ++ "Dc")) $
                uncurry (applyElimRule @a) (inferNodeA' @a (applyDcB'' @a) c s a b)
    applyDcB' c s a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA < positionB = withCache c (a, b, (s ++ "Dc")) $
                uncurry (applyElimRule @a) (inferNodeB' @Dc (applyDcB'' @a) c s a b)  -- B is Dc
    applyDcB' c s a@(a_id, InfNodes positionA _ _ _)  b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = applyInf @a c s a b
        | positionA < positionB = applyInfB @Dc c s a b  -- B is Dc, use @Dc@ when wrapping
        | positionA > positionB = applyInfA @a c s a b
    applyDcB' c s a@(a_id, EndInfNode _) b@(b_id, InfNodes{}) = withCache c (a, b, (s ++ "Dc")) $ applyInfA @a c s a b
    applyDcB' c s a@(a_id, InfNodes{}) b@(b_id, EndInfNode _) = withCache c (a, b, (s ++ "Dc")) $ applyInfB @Dc c s a b  -- B is Dc

    -- | Leaf cases for applyDcB. Similar to leaf_cases, but:
    -- |   - When inferring nodes for B, uses @Dc@ inference rules
    -- |   - When B is Unknown, it resolves to dcB (the continuous branch for B)
    dcB_leaf_cases c s a@(_, Leaf _) b@(_, Node{}) = withCache c (a, b, s ++ "Dc") $ uncurry (applyElimRule @a) (inferNodeA' @a (applyDcB'' @a) c s a b )
    dcB_leaf_cases c s a@(_, Node{}) b@(_, Leaf _) = withCache c (a, b, s ++ "Dc") $ uncurry (applyElimRule @a) (inferNodeB' @Dc (applyDcB'' @a) c s a b)  -- B is Dc
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
        in applyDcB'' @a c' s a dcB
    dcB_leaf_cases c "union" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then absorb (c, a) else absorb (c, b)
    dcB_leaf_cases c "inter" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then absorb (c, b) else absorb (c, a)

-- | ======================== DcA versions (Argument A is DC type) ========================
-- |
-- | These functions handle binary operations where argument A comes from a Dc (continuous/don't-care) branch.
-- | The key difference is that when inferring nodes for A, we use @Dc@ inference rules instead of @a@.
-- | This is the mirror of applyDcB, but for argument A.

    -- | Entry point for applyDcA: converts NodeIds to Nodes and wraps with debug
    applyDcA c s a b = debug_manipulation (applyDcA' @a c s (getNode c a) (getNode c b)) s (s ++ "DcA " ++ to_str @a) c (getNode c a) (getNode c b)
    -- | Internal version without debug wrapper
    applyDcA'' c s a b = applyDcA' @a c s a b

    -- | Binary operation where A is from Dc branch. Similar structure to apply', but:
    -- |   - When inferring nodes for A, uses @Dc@ inference rules (inferNodeA' @Dc)
    -- |   - Cache key includes "Dc" suffix to distinguish from regular operations
    -- |   - All cases mirror apply' but with Dc-specific inference for argument A

    -- Cases 1-4: Terminal values -> delegate to dcA_leaf_cases
    applyDcA' c s a@(_, Leaf _) b = dcA_leaf_cases @a c s a b
    applyDcA' c s a b@(_, Leaf _) = dcA_leaf_cases @a c s a b
    applyDcA' c s a@(_, Unknown) b = dcA_leaf_cases @a c s a b
    applyDcA' c s a b@(_, Unknown) = dcA_leaf_cases @a c s a b

    -- Cases 5-6: EndInfNode vs Node (note: A uses @Dc@ inference when inferring)
    applyDcA' c s a@(a_id, EndInfNode _) b@(b_id, Node idx _ _) = withCache c (a, b, (s ++ "Dc")) $ uncurry (applyElimRule @a) (inferNodeA' @Dc (applyDcA'' @a) c s a b)  -- A is Dc
    applyDcA' c s a@(a_id, Node{}) b@(b_id, EndInfNode _) = withCache c (a, b, (s ++ "Dc")) $ uncurry (applyElimRule @a) (inferNodeB' @a (applyDcA'' @a) c s a b)
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
        | positionA < positionB = uncurry (applyElimRule @a) (inferNodeB' @a (applyDcA'' @a) c s a b)
        | positionA > positionB = uncurry (applyElimRule @a) (inferNodeA' @Dc (applyDcA'' @a) c s a b)  -- A is Dc, use @Dc@ inference

    -- Cases 10-15: InfNodes vs Node/InfNodes/EndInfNode (similar to apply', but A uses @Dc@ when wrapping)
    applyDcA' c s a@(a_id, InfNodes positionA _ _ _) b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB = withCache c (a, b, (s ++ "Dc")) $
                uncurry (applyElimRule @a) (inferNodeA' @Dc (applyDcA'' @a) c s a b)  -- A is Dc
    applyDcA' c s a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA < positionB = withCache c (a, b, (s ++ "Dc")) $
                uncurry (applyElimRule @a) (inferNodeB' @a (applyDcA'' @a) c s a b)
    applyDcA' c s a@(a_id, InfNodes positionA _ _ _)  b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = applyInf @a c s a b
        | positionA < positionB = applyInfB @a c s a b
        | positionA > positionB = applyInfA @Dc c s a b  -- A is Dc, use @Dc@ when wrapping
    applyDcA' c s a@(a_id, EndInfNode _) b@(b_id, InfNodes{}) = withCache c (a, b, (s ++ "Dc")) $ applyInfA @Dc c s a b  -- A is Dc
    applyDcA' c s a@(a_id, InfNodes{}) b@(b_id, EndInfNode _) = withCache c (a, b, (s ++ "Dc")) $ applyInfB @a c s a b

    -- | Leaf cases for applyDcA. Similar to leaf_cases, but:
    -- |   - When inferring nodes for A, uses @Dc@ inference rules
    -- |   - When A is Unknown, it resolves to dcA (the continuous branch for A)
    dcA_leaf_cases c s a@(_, Leaf _) b@(_, Node{}) = withCache c (a, b, s ++ "Dc") $ uncurry (applyElimRule @a) (inferNodeA' @Dc (applyDcA'' @a) c s a b )  -- A is Dc
    dcA_leaf_cases c s a@(_, Node{}) b@(_, Leaf _) = withCache c (a, b, s ++ "Dc") $ uncurry (applyElimRule @a) (inferNodeB' @a (applyDcA'' @a) c s a b)
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
        in applyDcA'' @a c' s dcA b
    dcA_leaf_cases c s a b@(_, Unknown) = (c, b)  -- B is Unknown, return as-is
    dcA_leaf_cases c "union" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then absorb (c, a) else absorb (c, b)
    dcA_leaf_cases c "inter" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then absorb (c, b) else absorb (c, a)

    -- | Handles the case when both arguments are EndInfNodes (both exiting their class hierarchies).
    -- | This function:
    -- |   1. Pops the inference type stack to determine which inference contexts (Dc/Neg/Pos) were used
    -- |   2. Applies the appropriate binary operation based on the combination of inference types
    -- |   3. Wraps the result in an EndInfNode to maintain the class hierarchy structure
    -- |
    -- | The inference type combinations determine which version of apply to use:
    -- |   - (Dc, Dc): Both from continuous branches (don't-care inference rule) -> use apply @Dc
    -- |   - (Neg, Neg): Both from branches using negative literal inference rule -> use apply @Neg
    -- |   - (Pos, Pos): Both from branches using positive literal inference rule -> use apply @Pos
    -- |   - (Neg, Dc) or (Pos, Dc): One using literal inference rule, one continuous -> use applyDcB (B is Dc)
    -- |   - (Dc, Neg) or (Dc, Pos): One continuous, one using literal inference rule -> use applyDcA (A is Dc)
    -- |
    -- | After computing the result, absorb eliminates redundant branches, then applyElimRule
    -- | applies the appropriate elimination rule based on the current inference type @a@.
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
        in absorb $ applyElimRule @a (reset_stack_bin c'' c) (EndInfNode r)

-- | ======================== InfNode Application Logic ========================
-- |
-- | These functions handle binary operations when at least one argument is an InfNodes
-- | (class-defining node). InfNodes have three branches:
-- |   - dc: Uses the don't-care literal inference/elimination rule (continuous background)
-- |   - neg: Uses the negative literal inference/elimination rule
-- |   - pos: Uses the positive literal inference/elimination rule
-- | The operation must be applied to all three branches separately.

-- | Applies a binary operation to two InfNodes (or InfNode + terminal).
-- | When both arguments are InfNodes with matching positions, the operation is applied
-- | separately to each of the three branch pairs (dc, pos, neg).
-- |
-- | The algorithm:
-- |   1. First compute dcR (the resulting continuous branch) by applying operation to dcA and dcB
-- |   2. Then compute nR (branch using negative literal inference rule) using dcR as the continuous background
-- |   3. Then compute pR (branch using positive literal inference rule) using dcR as the continuous background
-- |   4. Combine results into a new InfNodes with the three computed branches
-- |
-- | The dc_stack is updated at each step:
-- |   - For dc branch: Push Unknown placeholders (dcR not yet computed)
-- |   - For neg/pos branches: Push the computed dcR as the continuous background
-- |
-- | Note: The actual exception type (neg1/neg0 or pos1/pos0) depends on what dcR evaluates to.
-- | If dcR is False, then neg/pos branches represent neg1/pos1 exceptions (exceptions to False).
-- | If dcR is True, then neg/pos branches represent neg0/pos0 exceptions (exceptions to True).
-- | Using the absorb function, branches that end in the same evaluation as dcR are eliminated
-- | which keeps the MDD's canonical and minimal
-- |
-- | Case 1: Both are InfNodes with matching positions
-- |   -> Apply operation to all three branch pairs, compute dcR first, then neg/pos branches
-- | Case 2: positionA > positionB (A's class comes after B's)
-- |   -> Wrap A in B's class context (applyInfA)
-- | Case 3: positionA < positionB (A's class comes before B's)
-- |   -> Wrap B in A's class context (applyInfB)
-- | Cases 4-7: One argument is InfNodes, other is terminal (Leaf/EndInfNode)
-- |   -> Wrap the terminal in the InfNode's class context
applyInf :: forall a. (Dd1 a, DdF3 a, Dd1_helper a) => BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node)
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

-- | Wraps argument A in the class context of argument B (which is an InfNodes).
-- | This is used when A needs to be evaluated within B's class hierarchy.
-- | The function:
-- |   1. Applies elimination rule to A (which may be an EndInfNode exiting a class)
-- |   2. Creates a new InfNodes with A's result as the dc branch, empty pos/neg branches
-- |   3. Recursively applies applyInf to combine the wrapped A with B
applyInfA :: forall a. (Dd1 a, DdF3 a, Dd1_helper a) => BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node)
applyInfA c s a@(a_id, _) b@(_, InfNodes positionB _ _ _) = let
        -- Apply elimination rule to A (handles EndInfNode if present)
        (c', (r_id, _)) = applyElimRule @a c (EndInfNode a_id)
        -- Create new InfNodes wrapping A's result in B's class context
        -- Empty pos/neg branches (0,0) will be filled by applyInf
        (c'', r') = insert c' $ InfNodes positionB r_id (0,0) (0,0)
    in applyInf @a c'' s r' b

-- | Wraps argument B in the class context of argument A (which is an InfNodes).
-- | This is the mirror of applyInfA. Used when B needs to be evaluated within A's class hierarchy.
applyInfB :: forall a. (Dd1 a, DdF3 a, Dd1_helper a) => BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node)
applyInfB c s a@(_, InfNodes positionA _ _ _) b@(b_id, _) = let
        -- Apply elimination rule to B (handles EndInfNode if present)
        (c', (r_id, _)) = applyElimRule @a c (EndInfNode b_id)
        -- Create new InfNodes wrapping B's result in A's class context
        (c'', r') = insert c' $ InfNodes positionA r_id (0,0) (0,0)
    in applyInf @a c'' s a r'

-- | Helper wrapper for inferred node recursive calls.
-- | These functions bridge between the Dd1 typeclass (which works with Nodes) and the DdF3
-- | typeclass (which works with Dd and handles inference rules).
-- |
-- | When a node is "missing" a variable (e.g., node A at position 5 when node B is at position 3),
-- | we need to infer what A should evaluate to at position 3. The DdF3 typeclass provides
-- | the inference rules (Dc, Neg, Pos) that determine how to create the missing node.
-- |
-- | inferNodeA': Infers a node for argument A when A is missing a variable that B has.
-- | inferNodeB': Infers a node for argument B when B is missing a variable that A has.
inferNodeA' :: forall a. DdF3 a => (BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node))
            -> BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Dd)
inferNodeA' f c s a b = inferNodeA @a f c s a b

inferNodeB' :: forall a. DdF3 a => (BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node))
            -> BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Dd)
inferNodeB' f c s a b = inferNodeB @a f c s a b