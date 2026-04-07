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
-- | the inference type @a@ (any of Dc, Neg, Pos, NegDc, DcNeg, PosDc, DcPos).
-- | Compound types encode asymmetric traversal where one operand is in Dc role.
-- | See TraversalMode in MDD.Traversal.Support for per-mode method implementations.

apply :: TraversalMode -> BiOpContext -> String -> NodeId -> NodeId -> (BiOpContext, Node)
apply' :: TraversalMode -> BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
leaf_cases :: TraversalMode -> BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
endclass_case :: TraversalMode -> BiOpContext -> String -> NodeId -> NodeId -> NodeId -> NodeId -> (BiOpContext, Node)

    -- | Main entry point: converts NodeIds to Nodes, wraps with debug output
apply tm c s a b
    | a == b    = (c, getNode c a)
    | otherwise = debug_manipulation (apply' tm c s (getNode c a) (getNode c b)) s (s ++ tmName tm) c (getNode c a) (getNode c b)

    -- | Unified binary operation dispatcher for all seven Inf modes.
    -- | Compound modes (NegDc, DcNeg, PosDc, DcPos) behave identically to the simple
    -- | modes structurally; the asymmetry is captured by TraversalMode method dispatch
    -- | (tmInferNodeA/B, tmApplyElimRule, tmInferClassNodeForA/B).

    -- Cases 1-4: At least one argument is a terminal (Leaf or Unknown)
apply' tm c s a@(a_id, a_dd) b@(b_id, b_dd)
        -- 1. Unknowns are placeholders and must be resolved before positioning is evaluated.
        | a_dd == Unknown || b_dd == Unknown = leaf_cases tm c s a b
        
        -- 2. Positional Comparison
        | posA == posB = case (a_dd, b_dd) of
            (Node _ pos_childA neg_childA, Node _ pos_childB neg_childB) ->
                let c_ = traverse_dc tm MvPos c a_id b_id
                    (c', (pos_result, _)) = apply tm c_ s pos_childA pos_childB

                    c_' = traverse_dc tm MvNeg (reset_stack_bin c' c) a_id b_id
                    (c'', (neg_result, _)) = apply tm c_' s neg_childA neg_childB
                in withCache c (a, b, s) $ tmApplyElimRule tm (reset_stack_bin c'' c) (Node posA pos_result neg_result)
            (ClassNode{}, ClassNode{}) -> withCache c (a, b, s) $ applyClass tm c s a b
            (EndClassNode ac, EndClassNode bc) -> withCache c (a, b, s) $ endclass_case tm c s a_id b_id ac bc
            (Leaf _, Leaf _) -> leaf_cases tm c s a b
            _ -> error "apply': Same position but mismatched constructors!"
            
        -- 3. Asymmetric Inference
        | posA > posB = matchAndInferA b_dd
        | posA < posB = matchAndInferB a_dd
    | otherwise   = error "apply': Unreachable position comparison"
      where
        posA = nodePosition a_dd
        posB = nodePosition b_dd
        
        -- Match on the "smaller" node (B) to infer structure for the "larger" node (A)
        matchAndInferA (Node{})       = withCache c (a, b, s) $ uncurry (tmApplyElimRule tm) (tmInferNodeA tm (apply' tm) c s a b)
        matchAndInferA (ClassNode{})  = withCache c (a, b, s) $ applyClassA tm c s a b
        matchAndInferA (EndClassNode bc) = 
            -- If B is EndClassNode, A must be a Leaf (since posA > posB). 
            -- Convert Leaf A to EndClassNode representation (l_1 / l_0) and exit class.
            let ac = case a_dd of
                        Leaf True  -> l_1
                        Leaf False -> l_0
                        _          -> error "apply': expected Leaf for EndClassNode inference"
            in withCache c (a, b, s) $ endclass_case tm c s a_id b_id ac bc
        matchAndInferA _ = error "apply': Unexpected node type for matchAndInferA"
            
        -- Match on the "smaller" node (A) to infer structure for the "larger" node (B)
        matchAndInferB (Node{})       = withCache c (a, b, s) $ uncurry (tmApplyElimRule tm) (tmInferNodeB tm (apply' tm) c s a b)
        matchAndInferB (ClassNode{})  = withCache c (a, b, s) $ applyClassB tm c s a b
        matchAndInferB (EndClassNode ac) = 
            let bc = case b_dd of
                        Leaf True  -> l_1
                        Leaf False -> l_0
                        _          -> error "apply': expected Leaf for EndClassNode inference"
            in withCache c (a, b, s) $ endclass_case tm c s a_id b_id ac bc
        matchAndInferB _ = error "apply': Unexpected node type for matchAndInferB"

    -- | Unified leaf/terminal handler for all seven Inf modes.
    -- | Unknown resolution uses TraversalMode methods (tmAUnknownReturn, tmBUnknownReturn, tmDcAMode, tmDcBMode,
    -- | tmPopADropLevel, tmPopBDropLevel) so compound modes inherit the correct Dc-asymmetric behavior.
    
    -- Unknown resolution (unified across all Inf modes via TraversalMode methods)
leaf_cases tm c s a@(_, Unknown) b@(_, Unknown) = (c, a)
leaf_cases tm c s a@(_, Unknown) b
        | tmAUnknownReturn tm = (c, a)
    | otherwise =
            let (c', dcA) = pop_dc_stack DcA (tmPopADropLevel tm) c
            in apply' (tmDcAMode tm) c' s dcA b
leaf_cases tm c s a b@(_, Unknown)
        | tmBUnknownReturn tm = (c, b)
    | otherwise =
            let (c', dcB) = pop_dc_stack DcB (tmPopBDropLevel tm) c
            in apply' (tmDcBMode tm) c' s a dcB

    -- Leaf vs Leaf base cases
leaf_cases tm c "union" a@(_, Leaf boolA) b@(_, Leaf _) = if boolA then (c, a) else (c, b)
leaf_cases tm c "inter" a@(_, Leaf boolA) b@(_, Leaf _) = if boolA then (c, b) else (c, a)

leaf_cases tm c s a b = error ("leaf case: " ++ s)

    -- | Pops the level stack, maps (infA, infB) to the appropriate Inf mode,
    -- | and re-dispatches via apply. Compound pairs produced by applyClass'
    -- | (e.g. NegDc, NegDc) now round-trip correctly back into compound apply.
endclass_case tm c s a_id b_id ac bc =
        let (c_, (infA, infB)) = pop_stack' c
            c' = traverse_dc tm ExitClass c_ a_id b_id
            (c'', (r, _)) = apply (infToMode (pairToInf infA infB)) c' s ac bc
        in tmApplyElimRule tm (reset_stack_bin c'' c) (EndClassNode r)





-- | ======================== ClassNode Application Logic ========================
-- |
-- | Algorithm:
-- |   1. Compute dcR via apply modeDc on the two dc children.
-- |   2. Compute nR via apply (tmNegClassInf tm) on the neg children.
-- |      Under compound modes (e.g. NegDc) this stays in the compound mode,
-- |      so the Dc-asymmetry is preserved across nested class boundaries.
-- |   3. Compute pR via apply (tmPosClassInf tm) on the pos children.
-- |   4. Absorb nR and pR against dcR; combine into ClassNode.
-- |
-- | Level stack: negClassInf/posClassInf are pushed (not plain Neg/Pos) so that
-- | endclass_case sees compound pairs and dispatches back to the correct mode.
applyClass :: TraversalMode -> BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
applyClass tm c s a b = debug_manipulation_inf (applyClass' tm c s a b) s (s ++ tmName tm) c a b

applyClass' :: TraversalMode -> BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
applyClass' tm c s a@(a_id, ClassNode positionA dcA pA nA) b@(b_id, ClassNode positionB dcB pB nB)
    | positionA == positionB =
        let
            c_ = add_to_stack (positionA, Dc) (((0, 0), Unknown), ((0, 0), Unknown), ((0, 0), Unknown)) (traverse_dc tm MvClassDc c a_id b_id)
            (c1, dcR) = apply modeDc c_ s dcA dcB
            (c1', dcR') = absorb_dc modeDc c1 positionA dcR

            -- Helper function for pos/neg branches. Note that we must use applyElimRule's
            -- typeclass method application, but `absorb` also needs type application.
            -- To avoid rank-N polymorphism issues, we keep the calls explicit but 
            -- share the structural boilerplate via a let-binding.
            
            nInf = tmNegClassInf tm
            c2_ = add_to_stack (positionA, tmToInf nInf) (getNode c dcA, getNode c dcB, dcR) (traverse_dc tm MvClassNeg (reset_stack_bin c1' c) a_id b_id)
            (c2, nR) = apply nInf c2_ s nA nB
            (c2', nR') = absorb modeNeg c2 positionA dcR' nR

            pInf = tmPosClassInf tm
            c3_ = add_to_stack (positionA, tmToInf pInf) (getNode c dcA, getNode c dcB, dcR) (traverse_dc tm MvClassPos (reset_stack_bin c2' c) a_id b_id)
            (c3, pR) = apply pInf c3_ s pA pB
            (c3', pR') = absorb modePos c3 positionA dcR' pR

        in tmApplyElimRule tm (reset_stack_bin c3' c) $ ClassNode positionA (fst dcR') (fst pR') (fst nR')
    | positionA > positionB = applyClassA tm c s a b
    | positionA < positionB = applyClassB tm c s a b
applyClass' tm c s a@(_, ClassNode{}) b@(_, Leaf _)        = applyClassB tm c s a b
applyClass' tm c s a@(_, ClassNode{}) b@(_, EndClassNode _) = applyClassB tm c s a b
applyClass' tm c s a@(_, Leaf _)        b@(_, ClassNode{}) = applyClassA tm c s a b
applyClass' tm c s a@(_, EndClassNode _) b@(_, ClassNode{}) = applyClassA tm c s a b
applyClass' _ _ s _ _ = error ("apply class error: " ++ s)


-- | Wrap the non-ClassNode A-side using A's inference projection (tmInferClassNodeForA tm),
-- | then enter applyClass tm.  For compound modes (e.g. NegDc) this uses @Neg for A
-- | instead of the compound type itself, preserving correct class-node structure.
applyClassA :: TraversalMode -> BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
applyClassA tm c s (a_id, _) b@(_, ClassNode positionB _ _ _) =
    let (c', r)   = insert c (EndClassNode a_id)
        (c'', r') = tmInferClassNodeForA tm c' positionB r
    in applyClass tm c'' s r' b
applyClassA _ _ _ _ _ = error "applyClassA: B must be a ClassNode"

-- | Wrap the non-ClassNode B-side using B's inference projection (tmInferClassNodeForB tm).
applyClassB :: TraversalMode -> BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
applyClassB tm c s a@(_, ClassNode positionA _ _ _) (b_id, _) =
    let (c', r)   = insert c (EndClassNode b_id)
        (c'', r') = tmInferClassNodeForB tm c' positionA r
    in applyClass tm c'' s a r'
applyClassB _ _ _ _ _ = error "applyClassB: A must be a ClassNode"