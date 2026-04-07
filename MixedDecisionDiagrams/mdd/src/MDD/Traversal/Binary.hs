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
-- | See DdF3 in MDD.Traversal.Support for per-mode method implementations.

type Dd1 :: Inf -> Constraint
class Dd1 a where
    -- | Unified leaf/terminal dispatcher (handles all seven Inf modes).
    leaf_cases :: BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
    apply :: BiOpContext -> String -> NodeId -> NodeId -> (BiOpContext, Node)
    apply' :: BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
    endclass_case :: BiOpContext -> String -> NodeId -> NodeId -> NodeId -> NodeId -> (BiOpContext, Node)

instance (DdF3 a, Dd1_helper a) => Dd1 a where
    -- | Main entry point: converts NodeIds to Nodes, wraps with debug output
    apply c s a b
        | a == b    = (c, getNode c a)
        | otherwise = debug_manipulation (apply' @a c s (getNode c a) (getNode c b)) s (s ++ to_str @a) c (getNode c a) (getNode c b)

    -- | Unified binary operation dispatcher for all seven Inf modes.
    -- | Compound modes (NegDc, DcNeg, PosDc, DcPos) behave identically to the simple
    -- | modes structurally; the asymmetry is captured by DdF3 method dispatch
    -- | (inferNodeA/B, applyElimRule, inferClassNodeForA/B).

    -- Cases 1-4: At least one argument is a terminal (Leaf or Unknown)
    apply' c s a@(a_id, a_dd) b@(b_id, b_dd)
        -- 1. Unknowns are placeholders and must be resolved before positioning is evaluated.
        | a_dd == Unknown || b_dd == Unknown = leaf_cases @a c s a b
        
        -- 2. Positional Comparison
        | posA == posB = case (a_dd, b_dd) of
            (Node _ pos_childA neg_childA, Node _ pos_childB neg_childB) ->
                let c_ = traverse_dc @a MvPos c a_id b_id
                    (c', (pos_result, _)) = apply @a c_ s pos_childA pos_childB

                    c_' = traverse_dc @a MvNeg (reset_stack_bin c' c) a_id b_id
                    (c'', (neg_result, _)) = apply @a c_' s neg_childA neg_childB
                in withCache c (a, b, s) $ applyElimRule @a (reset_stack_bin c'' c) (Node posA pos_result neg_result)
            (ClassNode{}, ClassNode{}) -> withCache c (a, b, s) $ applyClass @a c s a b
            (EndClassNode ac, EndClassNode bc) -> withCache c (a, b, s) $ endclass_case @a c s a_id b_id ac bc
            (Leaf _, Leaf _) -> leaf_cases @a c s a b
            _ -> error "apply': Same position but mismatched constructors!"
            
        -- 3. Asymmetric Inference
        | posA > posB = matchAndInferA b_dd
        | posA < posB = matchAndInferB a_dd
        | otherwise   = error "apply': Unreachable position comparison"
      where
        posA = nodePosition a_dd
        posB = nodePosition b_dd
        
        -- Match on the "smaller" node (B) to infer structure for the "larger" node (A)
        matchAndInferA (Node{})       = withCache c (a, b, s) $ uncurry (applyElimRule @a) (inferNodeA @a (apply' @a) c s a b)
        matchAndInferA (ClassNode{})  = withCache c (a, b, s) $ applyClassA @a c s a b
        matchAndInferA (EndClassNode bc) = 
            -- If B is EndClassNode, A must be a Leaf (since posA > posB). 
            -- Convert Leaf A to EndClassNode representation (l_1 / l_0) and exit class.
            let ac = case a_dd of
                        Leaf True  -> l_1
                        Leaf False -> l_0
                        _          -> error "apply': expected Leaf for EndClassNode inference"
            in withCache c (a, b, s) $ endclass_case @a c s a_id b_id ac bc
        matchAndInferA _ = error "apply': Unexpected node type for matchAndInferA"
            
        -- Match on the "smaller" node (A) to infer structure for the "larger" node (B)
        matchAndInferB (Node{})       = withCache c (a, b, s) $ uncurry (applyElimRule @a) (inferNodeB @a (apply' @a) c s a b)
        matchAndInferB (ClassNode{})  = withCache c (a, b, s) $ applyClassB @a c s a b
        matchAndInferB (EndClassNode ac) = 
            let bc = case b_dd of
                        Leaf True  -> l_1
                        Leaf False -> l_0
                        _          -> error "apply': expected Leaf for EndClassNode inference"
            in withCache c (a, b, s) $ endclass_case @a c s a_id b_id ac bc
        matchAndInferB _ = error "apply': Unexpected node type for matchAndInferB"

    -- | Unified leaf/terminal handler for all seven Inf modes.
    -- | Unknown resolution uses DdF3 methods (aUnknownReturn, bUnknownReturn, dcAMode, dcBMode,
    -- | popADropLevel, popBDropLevel) so compound modes inherit the correct Dc-asymmetric behavior.
    
    -- Unknown resolution (unified across all Inf modes via DdF3 methods)
    leaf_cases c s a@(_, Unknown) b@(_, Unknown) = (c, a)
    leaf_cases c s a@(_, Unknown) b
        | aUnknownReturn @a = (c, a)
        | otherwise =
            let (c', dcA) = pop_dc_stack DcA (popADropLevel @a) c
            in apply'_with (dcAMode @a) c' s dcA b
    leaf_cases c s a b@(_, Unknown)
        | bUnknownReturn @a = (c, b)
        | otherwise =
            let (c', dcB) = pop_dc_stack DcB (popBDropLevel @a) c
            in apply'_with (dcBMode @a) c' s a dcB

    -- Leaf vs Leaf base cases
    leaf_cases c "union" a@(_, Leaf boolA) b@(_, Leaf _) = if boolA then (c, a) else (c, b)
    leaf_cases c "inter" a@(_, Leaf boolA) b@(_, Leaf _) = if boolA then (c, b) else (c, a)

    leaf_cases c s a b = error ("leaf case: " ++ s)

    -- | Pops the level stack, maps (infA, infB) to the appropriate Inf mode,
    -- | and re-dispatches via apply_with. Compound pairs produced by applyClass'
    -- | (e.g. NegDc, NegDc) now round-trip correctly back into compound apply.
    endclass_case c s a_id b_id ac bc =
        let (c_, (infA, infB)) = pop_stack' c
            c' = traverse_dc @a ExitClass c_ a_id b_id
            (c'', (r, _)) = apply_with (pairToInf infA infB) c' s ac bc
        in applyElimRule @a (reset_stack_bin c'' c) (EndClassNode r)


-- | Map a (infA, infB) level-stack pair to the unified Inf mode for apply_with.
-- | Symmetric pairs map to the simple mode; asymmetric / compound pairs map to
-- | the corresponding compound constructor.  Legacy (Neg,Dc) etc. arise when
-- | pop_dcA'/pop_dcB' mutate the level entry before endclass_case is reached.
pairToInf :: Inf -> Inf -> Inf
pairToInf Dc    Dc    = Dc
pairToInf Neg   Neg   = Neg
pairToInf Pos   Pos   = Pos
pairToInf NegDc NegDc = NegDc
pairToInf DcNeg DcNeg = DcNeg
pairToInf PosDc PosDc = PosDc
pairToInf DcPos DcPos = DcPos
pairToInf DcDcA DcDcA = DcDcA
pairToInf DcDcB DcDcB = DcDcB
-- Legacy asymmetric primitive pairs (pop_dcA'/pop_dcB' mutated a simple level entry to Dc):
pairToInf Neg   Dc    = NegDc
pairToInf Pos   Dc    = PosDc
pairToInf Dc    Neg   = DcNeg
pairToInf Dc    Pos   = DcPos
-- Compound level vs bare Dc (pop_dc_stack dropLevel in a compound context promotes the parent
-- entry to Dc, while the other side still holds the compound entry from one level up):
pairToInf NegDc Dc    = NegDc  -- B resolved Unknown; A-side compound context unchanged
pairToInf PosDc Dc    = PosDc
pairToInf Dc    DcNeg = DcNeg  -- A resolved Unknown; B-side compound context unchanged
pairToInf Dc    DcPos = DcPos
pairToInf DcDcA Dc    = DcDcA
pairToInf Dc    DcDcB = DcDcB
pairToInf a     b     = error ("pairToInf: unexpected level-stack pair: " ++ show a ++ ", " ++ show b)


-- | Runtime dispatch on Inf to select the appropriate apply entry point.
-- | Used by leaf_cases for Unknown resolution and by applyClass' for inner branches.
apply_with :: Inf -> BiOpContext -> String -> NodeId -> NodeId -> (BiOpContext, Node)
apply_with Dc    = apply @Dc
apply_with Neg   = apply @Neg
apply_with Pos   = apply @Pos
apply_with NegDc = apply @NegDc
apply_with DcNeg = apply @DcNeg
apply_with PosDc = apply @PosDc
apply_with DcPos = apply @DcPos
apply_with DcDcA = apply @DcDcA
apply_with DcDcB = apply @DcDcB

-- | Runtime dispatch on Inf to select the appropriate apply' entry point.
apply'_with :: Inf -> BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
apply'_with Dc    = apply' @Dc
apply'_with Neg   = apply' @Neg
apply'_with Pos   = apply' @Pos
apply'_with NegDc = apply' @NegDc
apply'_with DcNeg = apply' @DcNeg
apply'_with PosDc = apply' @PosDc
apply'_with DcPos = apply' @DcPos
apply'_with DcDcA = apply' @DcDcA
apply'_with DcDcB = apply' @DcDcB


-- | ======================== ClassNode Application Logic ========================
-- |
-- | Algorithm:
-- |   1. Compute dcR via apply @Dc on the two dc children.
-- |   2. Compute nR via apply_with (negClassInf @a) on the neg children.
-- |      Under compound modes (e.g. NegDc) this stays in the compound mode,
-- |      so the Dc-asymmetry is preserved across nested class boundaries.
-- |   3. Compute pR via apply_with (posClassInf @a) on the pos children.
-- |   4. Absorb nR and pR against dcR; combine into ClassNode.
-- |
-- | Level stack: negClassInf/posClassInf are pushed (not plain Neg/Pos) so that
-- | endclass_case sees compound pairs and dispatches back to the correct mode.
applyClass :: forall a. (DdF3 a) => BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
applyClass c s a b = debug_manipulation_inf (applyClass' @a c s a b) s (s ++ to_str @a) c a b

applyClass' :: forall a. (DdF3 a) => BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
applyClass' c s a@(a_id, ClassNode positionA dcA pA nA) b@(b_id, ClassNode positionB dcB pB nB)
    | positionA == positionB =
        let
            c_ = add_to_stack (positionA, Dc) (((0, 0), Unknown), ((0, 0), Unknown), ((0, 0), Unknown)) (traverse_dc @a MvClassDc c a_id b_id)
            (c1, dcR) = apply @Dc c_ s dcA dcB
            (c1', dcR') = absorb_dc @Dc c1 positionA dcR

            -- Helper function for pos/neg branches. Note that we must use applyElimRule's
            -- typeclass method application, but `absorb` also needs type application.
            -- To avoid rank-N polymorphism issues, we keep the calls explicit but 
            -- share the structural boilerplate via a let-binding.
            
            nInf = negClassInf @a
            c2_ = add_to_stack (positionA, nInf) (getNode c dcA, getNode c dcB, dcR) (traverse_dc @a MvClassNeg (reset_stack_bin c1' c) a_id b_id)
            (c2, nR) = apply_with nInf c2_ s nA nB
            (c2', nR') = absorb @Neg c2 positionA dcR' nR

            pInf = posClassInf @a
            c3_ = add_to_stack (positionA, pInf) (getNode c dcA, getNode c dcB, dcR) (traverse_dc @a MvClassPos (reset_stack_bin c2' c) a_id b_id)
            (c3, pR) = apply_with pInf c3_ s pA pB
            (c3', pR') = absorb @Pos c3 positionA dcR' pR

        in applyElimRule @a (reset_stack_bin c3' c) $ ClassNode positionA (fst dcR') (fst pR') (fst nR')
    | positionA > positionB = applyClassA @a c s a b
    | positionA < positionB = applyClassB @a c s a b
applyClass' c s a@(_, ClassNode{}) b@(_, Leaf _)        = applyClassB @a c s a b
applyClass' c s a@(_, ClassNode{}) b@(_, EndClassNode _) = applyClassB @a c s a b
applyClass' c s a@(_, Leaf _)        b@(_, ClassNode{}) = applyClassA @a c s a b
applyClass' c s a@(_, EndClassNode _) b@(_, ClassNode{}) = applyClassA @a c s a b
applyClass' _ s _ _ = error ("apply class error: " ++ s)


-- | Wrap the non-ClassNode A-side using A's inference projection (inferClassNodeForA @a),
-- | then enter applyClass @a.  For compound modes (e.g. NegDc) this uses @Neg for A
-- | instead of the compound type itself, preserving correct class-node structure.
applyClassA :: forall a. (DdF3 a) => BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
applyClassA c s (a_id, _) b@(_, ClassNode positionB _ _ _) =
    let (c', r)   = insert c (EndClassNode a_id)
        (c'', r') = inferClassNodeForA @a c' positionB r
    in applyClass @a c'' s r' b
applyClassA _ _ _ _ = error "applyClassA: B must be a ClassNode"

-- | Wrap the non-ClassNode B-side using B's inference projection (inferClassNodeForB @a).
applyClassB :: forall a. (DdF3 a) => BiOpContext -> String -> Node -> Node -> (BiOpContext, Node)
applyClassB c s a@(_, ClassNode positionA _ _ _) (b_id, _) =
    let (c', r)   = insert c (EndClassNode b_id)
        (c'', r') = inferClassNodeForB @a c' positionA r
    in applyClass @a c'' s a r'
applyClassB _ _ _ _ = error "applyClassB: A must be a ClassNode"