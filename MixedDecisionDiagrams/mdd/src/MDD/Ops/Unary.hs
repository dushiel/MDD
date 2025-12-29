{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Move brackets to avoid $" #-}
{-# HLINT ignore "Use second" #-}

module MDD.Ops.Unary where

import MDD.Types
import MDD.Context
import MDD.Manager
import MDD.Stack
import MDD.Traversal
import MDD.Draw (debug_manipulation_unary)

import Data.Hashable
import qualified Data.HashMap.Strict as HashMap
import Data.Kind (Constraint)
import Debug.Trace (trace)

-- ==========================================================================================================
-- * Unary Caching Helper
-- ==========================================================================================================

-- | A higher-order function for handling cache lookup and update for unary operations.
-- |
-- | The cache prevents redundant computations during unary operations (negation, restriction, etc.).
-- | Unlike binary operations which cache (NodeId A, NodeId B, dc_stack), unary operations only
-- | cache by NodeId since there's only one argument.
withCache_ :: UnaryOperatorContext -> Node -> (UnaryOperatorContext, Node) -> (UnaryOperatorContext, Node)
withCache_ c@UnaryOperatorContext { un_cache = nc } (key, _) func_with_args =
  case HashMap.lookup key nc of
    Just result -> (c, (result, getDd c result))  -- Cache hit: return previously computed result
    Nothing -> let
      (updatedContext, result@(nodeid, _)) = func_with_args
      updatedCache = HashMap.insert key nodeid nc
      in (updatedContext { un_cache = updatedCache }, result)  -- Cache miss: compute and store result

-- | Debug wrapper for restrict_node_set operations.
-- | Similar to debug_manipulation for binary operations, but adapted for unary operations.
withDebug_restrict :: forall a. (DdF3 a) =>
    UnaryOperatorContext -> [Position] -> Bool -> Node ->
    (UnaryOperatorContext -> [Position] -> Bool -> Node -> (UnaryOperatorContext, Node)) ->
    (UnaryOperatorContext, Node)
withDebug_restrict c nas b d restrict_func =
    let func_key = "restrict"
        func_name = "restrict " ++ to_str @a
        result = restrict_func c nas b d
    in debug_manipulation_unary result func_key func_name c d nas b

-- ==========================================================================================================
-- * Unary Elimination Rules
-- ==========================================================================================================

-- | Apply elimination rules for unary operations (similar to binary but for UnaryOperatorContext).
-- |
-- | This function applies the same elimination rules as binary operations (see DdF3 in MDD.Traversal),
-- | but works directly with UnaryOperatorContext without needing a binary context workaround.
-- |
-- | The elimination rules are:
-- |   - Dc: Eliminate nodes where pos and neg branches are equal
-- |   - Pos: Eliminate nodes where neg branch is Unknown (only pos is valid)
-- |   - Neg: Eliminate nodes where pos branch is Unknown (only neg is valid)
-- |
-- | This is a dedicated implementation that mirrors the logic from DdF3 instances but works
-- | directly with UnaryOperatorContext, avoiding the need for context conversions.
applyElimRule_unary :: forall a. (DdF3 a) => UnaryOperatorContext -> Dd -> (UnaryOperatorContext, Node)
applyElimRule_unary c d = case to_str @a of
    "Dc" -> applyElimRule_dc c d
    "Pos" -> applyElimRule_pos c d
    "Neg" -> applyElimRule_neg c d
    _ -> insert c d
  where
    -- Dc elimination rule: Eliminate nodes where pos and neg branches are equal
    applyElimRule_dc :: UnaryOperatorContext -> Dd -> (UnaryOperatorContext, Node)
    applyElimRule_dc c' d'@(Node _ p n) = if p == n then (c', getNode c' p) else insert c' d'
    applyElimRule_dc c' (InfNodes _ (1,0) (0,0) (0,0)) = (c', ((1,0), Leaf True))
    applyElimRule_dc c' (InfNodes _ (2,0) (0,0) (0,0)) = (c', ((2,0), Leaf False))
    applyElimRule_dc c' (InfNodes _ (0,0) (0,0) (0,0)) = (c', ((0,0), Unknown))
    applyElimRule_dc c' (EndInfNode (1,0)) = (c', ((1,0), Leaf True))
    applyElimRule_dc c' (EndInfNode (2,0)) = (c', ((2,0), Leaf False))
    applyElimRule_dc c' (EndInfNode (0,0)) = (c', ((0,0), Unknown))
    applyElimRule_dc c' d'@(EndInfNode r) = case getDd c' r of
        Leaf _ -> (c', getNode c' r)
        Unknown -> (c', getNode c' r)
        _ -> insert c' d'
    applyElimRule_dc c' d'@(InfNodes _ consq (0,0) (0,0)) = case getDd c' consq of
        EndInfNode d'' -> (c', getNode c' d'')
        _ -> insert c' d'
    applyElimRule_dc c' d' = insert c' d'

    -- Pos elimination rule: Eliminate nodes where neg branch is Unknown (only pos is valid)
    applyElimRule_pos :: UnaryOperatorContext -> Dd -> (UnaryOperatorContext, Node)
    applyElimRule_pos c' (Node _ posC (0, 0)) = (c', getNode c' posC)
    applyElimRule_pos c' (InfNodes _ (0,0) (1,0) (0,0)) = (c', ((1,0), Leaf True))
    applyElimRule_pos c' (InfNodes _ (0,0) (2,0) (0,0)) = (c', ((2,0), Leaf False))
    applyElimRule_pos c' d'@(EndInfNode r) = case getDd c' r of
        Leaf _ -> (c', getNode c' r)
        Unknown -> (c', getNode c' r)
        _ -> insert c' d'
    applyElimRule_pos c' d' = insert c' d'

    -- Neg elimination rule: Eliminate nodes where pos branch is Unknown (only neg is valid)
    applyElimRule_neg :: UnaryOperatorContext -> Dd -> (UnaryOperatorContext, Node)
    applyElimRule_neg c' (Node _ (0, 0) negC) = (c', getNode c' negC)
    applyElimRule_neg c' (InfNodes _ (0,0) (0,0) (1,0)) = (c', ((1,0), Leaf True))
    applyElimRule_neg c' (InfNodes _ (0,0) (0,0) (2,0)) = (c', ((2,0), Leaf False))
    applyElimRule_neg c' d'@(EndInfNode r) = case getDd c' r of
        Leaf _ -> (c', getNode c' r)
        Unknown -> (c', getNode c' r)
        _ -> insert c' d'
    applyElimRule_neg c' d' = insert c' d'

-- | Apply elimination rules for unary operations (takes tuple form).
-- | Convenience wrapper that unpacks the tuple and calls `applyElimRule_unary`.
applyElimRule'_unary :: forall a. (DdF3 a) => (UnaryOperatorContext, Dd) -> (UnaryOperatorContext, Node)
applyElimRule'_unary (c, d) = applyElimRule_unary @a c d

-- ==========================================================================================================
-- * Redundancy Elimination (absorb) for Unary
-- ==========================================================================================================

-- | Main entry point for the absorb function for unary operations.
-- | The absorb function maintains canonical representation by eliminating redundant branches.
-- | If a discrete branch (Pos or Neg) evaluates to the same result as the continuous background (dcR),
-- | that branch is redundant and can be replaced with Unknown (which will resolve to dcR during evaluation).
absorb_unary :: (UnaryOperatorContext, Node) -> (UnaryOperatorContext, Node)
absorb_unary (c, n) = absorb'_unary (c, n)

-- | Recursively checks if a node's evaluation matches the continuous background (dcR) at the current level.
-- | If it matches, the node is "absorbed" (replaced with Unknown) to maintain minimal graph representation.
-- |
-- | **Note**: The unary dc_stack structure is `[Node]` (dcRs only), containing:
-- |   - `dcRs`: List of resulting continuous branches (for absorption comparison)
-- | Unlike binary operations which track both input dc branches (dcA, dcB) for Unknown resolution,
-- | unary operations don't need to track the original input's dc branches since Unknown is
-- | returned as-is in unary operations (no resolution needed).
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
absorb'_unary :: (UnaryOperatorContext, Node) -> (UnaryOperatorContext, Node)
-- | given a dcR and a pos or ng results, sets sub-paths in the local inf-domain which agree with the dcR to unknown ("absorbing them")
absorb'_unary (c@UnaryOperatorContext{un_dc_stack = dc@(_, Unknown) : fs }, a)  =
    let (c', r) = absorb'_unary (c{un_dc_stack = fs}, a) in (c, r)
absorb'_unary (c@UnaryOperatorContext{un_dc_stack = dc : fs }, a@(_, Unknown)) = (c, a)
absorb'_unary (c@UnaryOperatorContext{un_dc_stack = dc : fs }, a@(_, Leaf _))
    | a == dc = (c, ((0,0), Unknown))
    | otherwise = (c,a)
absorb'_unary (c@UnaryOperatorContext{un_dc_stack = dc@(_, Leaf _)  : fs }, a@(_, InfNodes _ d p n))  =  let
    (_, r1) = absorb'_unary (c, getNode c d)
    (_, r2) = absorb'_unary (c, getNode c p)
    (_, r3) = absorb'_unary (c, getNode c n)
    in if r1 == r2 && r2 == r3 then (c, ((0,0), Unknown)) else (c, a)
absorb'_unary (c@UnaryOperatorContext{un_dc_stack = dc@(_, Leaf _)  : fs }, a@(_, EndInfNode a_child)) = if getNode c a_child == dc then (c, ((0,0), Unknown)) else (c, a)
absorb'_unary (c@UnaryOperatorContext{un_dc_stack = dc@(_, EndInfNode dc') : fs }, a@(_, EndInfNode a'))
    | a' == dc' = (c, ((0,0), Unknown))
    | otherwise = (c,a)
absorb'_unary (c@UnaryOperatorContext{un_dc_stack = dc : fs }, a)
    | a == dc = (c, ((0,0), Unknown))
    | otherwise = (c,a)
absorb'_unary (c@UnaryOperatorContext{un_dc_stack = [] }, a) = (c, a)

-- ==========================================================================================================
-- * Negation Logic
-- ==========================================================================================================

negation :: UnaryOperatorContext -> Node -> (UnaryOperatorContext, Node)
negation = negation'

negation' :: UnaryOperatorContext -> Node -> (UnaryOperatorContext, Node)
negation' c d@(node_id, Node position pos_child neg_child)  = withCache_ c d $ let
    (c1, (posR, _)) = negation' c (getNode c pos_child)
    (c2, (negR, _)) = negation' c1 (getNode c1 neg_child)
    in insert c2 $ Node position posR negR
negation' c d@(node_id, InfNodes position dc p n) = withCache_ c d $ let
    (c1, (r_dc, _)) = negation' c (getNode c dc)
    (c2, (r_n, _)) = negation' c1 (getNode c1 n)
    (c3, (r_p, _)) = negation' c2 (getNode c2 p)
        in insert c3 $ InfNodes position r_dc r_p r_n
negation' c d@(node_id, EndInfNode a) = withCache_ c  d $ let
    (c1, (result, _)) = negation' c (getNode c a)
    in insert c1 $ EndInfNode result
negation' c (_, Leaf b) = (c, ((hash $ Leaf (not b), 0), Leaf (not b)))
negation' c u@(_, Unknown) = (c, u)

-- ==========================================================================================================
-- * Unary Operation Typeclass and Instances
-- ==========================================================================================================

-- | The DdUnary typeclass defines unary operations (restriction, quantification) parameterized by
-- | the inference type @a@ (Dc, Neg, or Pos). The inference type determines which elimination
-- | rules are applied during traversal (see DdF3 in MDD.Traversal).
-- |
-- | Key methods:
-- |   - restrict_node_set: Restricts/quantifies variables in an MDD (universal/existential quantification)
-- |   - traverse_dc_unary: Synchronizes dc_stack traversal with main traversal (similar to binary's traverse_dc)
type DdUnary :: Inf -> Constraint
class DdUnary a where
    restrict_node_set :: UnaryOperatorContext -> [Position] -> Bool -> Node -> (UnaryOperatorContext, Node)
    traverse_dc_unary :: String -> UnaryOperatorContext -> NodeId -> UnaryOperatorContext

instance (DdF3 a) => DdUnary a where
    -- | Synchronizes the dc_stack with the main traversal for unary operations.
    -- | Similar to binary's `traverse_dc`, but for unary context.
    -- |
    -- | Synchronizes the dc_stack with the main traversal for unary operations.
    -- | Similar to binary's `traverse_dc`, but for unary context.
    -- |
    -- | **Potential Issue**: This implementation uses a dummy binary context (`dummyBin`) to call
    -- | `traverse_dc_generic`, which expects a BinaryOperatorContext. This is a workaround that
    -- | may not correctly handle all cases, as the binary and unary contexts have different
    -- | stack structures. The unary stack is `[Node]` (dcRs only) while binary is `(dcA, dcB, dcR)`.
    -- |
    -- | Case 1: Inference type is Dc (don't-care)
    -- |   -> No synchronization needed (both branches valid, no catchup required)
    -- | Case 2: Inference type is Neg or Pos
    -- |   -> Update all dcR branches in the stack using traverse_dc_generic
    -- |   -> Uses the inference rule @a@ to catch up when positions don't match
    traverse_dc_unary s c@UnaryOperatorContext{un_dc_stack = dcRs, un_current_level = lv} d =
        if to_str @a == "Dc" then c
            else let
                -- Logic depends on which context is being used (unary/binary)
                -- **Note**: Using dummyBin is a workaround - may not handle all cases correctly
                new_dcRs = map (traverse_dc_generic @a s (dummyBin c) (getNode c d)) dcRs  -- Update dcR branches
            in c{un_dc_stack = new_dcRs, un_current_level=lv}
      where
        -- Helper to satisfy traverse_dc_generic signature which expects Binary context
        -- **Potential Issue**: This creates a binary context with only the nodelookup, missing
        -- the binary-specific stack structure. This may cause issues if traverse_dc_generic
        -- accesses binary-specific stack fields.
        dummyBin u = init_binary_context (getLookup u)

    -- | Restricts/quantifies variables in a Node (variable node).
    -- |
    -- | This function implements universal/existential quantification by restricting variables
    -- | to specific boolean values. The `nas` parameter is a list of positions to restrict,
    -- | and `b` determines whether to restrict to True (universal) or False (existential).
    -- | The position matching logic `(reverse $ map fst $ un_current_level c) ++ [position] == na`  compares the current path with the target position. This is by design.
    -- |
    -- | Algorithm:
    -- |   1. Check if we need to infer nodes (current path is less than target position)
    -- |   2. If inference needed: infer nodes until we reach the target position
    -- |   3. Check if current position matches the first restriction target (`na`)
    -- |   4. If match: set `b' = True` and remove `na` from remaining restrictions
    -- |   5. If no match: set `b' = False` and keep `na` in remaining restrictions
    -- |   6. Recursively restrict pos and neg children
    -- |   7. If position matched (`b' = True`):
    -- |      - If `b = True`: take pos branch (both pos and neg point to posR)
    -- |      - If `b = False`: take neg branch (both pos and neg point to negR)
    -- |   8. If position didn't match: keep both branches (posR and negR)
    restrict_node_set c (na : nas) b d@(node_id, Node position pos_child neg_child)  =
        withDebug_restrict @a c (na : nas) b d $ \c' nas' b' d' -> restrict_node_set_internal c' nas' b' d'
      where
        restrict_node_set_internal c (na : nas) b d@(node_id, Node position pos_child neg_child)  =
            -- Check if we need to infer nodes (if we've passed the target position)
            let current_path = (reverse $ map fst $ un_current_level c) ++ [position]
            in trace ("current: " ++ show current_path ++ ", na : " ++ show na) (if current_path > na
                then -- We've passed the target position, need to infer a node at the target
                    let (c', d') = inferNode @a c (last na) d
                    in restrict_node_set @a c' (na : nas) b d'
                else let
                    (b', nas') = if current_path == na
                        then (True, nas)
                        else (False, na : nas)

                    (c1, posR) = if nas' /= []
                        then (fst traverse_pos, fst $ snd traverse_pos)
                        else (c, pos_child) -- terminal case, all vars have been replaced
                    traverse_pos = restrict_node_set @a c_ nas' b (getNode c pos_child)
                    c_ = traverse_dc_unary @a "pos child" c pos_child

                    (c2, negR) = if nas' /= []
                        then (fst traverse_neg, fst $ snd traverse_neg)
                        else (c, neg_child) -- terminal case, all vars have been replaced
                    traverse_neg = restrict_node_set @a c1_ nas' b (getNode c1 neg_child)
                    c1_ = traverse_dc_unary @a "neg child" (reset_stack_un c1 c) neg_child

                    in if b'  -- hit, so remove na from nas
                        then if b  -- depending on b, take positive or negative evaluation
                            then applyElimRule_unary @a c2 $ Node position posR posR
                            else applyElimRule_unary @a c2 $ Node position negR negR
                        else applyElimRule_unary @a c2 $ Node position posR negR)  -- otherwise continue with original nas and no quantification
    restrict_node_set c [] b d@(node_id, Node position pos_child neg_child) =
        withDebug_restrict @a c [] b d $ \c' _nas' _b' d' -> restrict_node_set_internal c' [] _b' d'
      where
        restrict_node_set_internal c [] b d@(node_id, Node position pos_child neg_child) =
            -- No more restrictions to apply, return as-is
            absorb_unary (c, d)

    -- | Restricts/quantifies variables in an InfNodes (class-defining node).
    -- |
    -- | This function handles restriction when entering a class hierarchy. Similar to binary's
    -- | `applyInf`, it processes all three branches (dc, pos, neg) separately.
    -- |
    -- | Algorithm:
    -- |   1. Check if we need to infer InfNodes to reach the target position
    -- |   2. If inference needed: infer InfNodes until we reach the target position
    -- |   3. First compute dcR (the resulting continuous branch) using @Dc@ inference rule
    -- |   4. Then compute nR (branch using negative literal inference rule) using dcR as background
    -- |   5. Then compute pR (branch using positive literal inference rule) using dcR as background
    -- |   6. Combine results into a new InfNodes with the three computed branches
    -- |
    -- | The dc_stack is updated at each step:
    -- |   - For dc branch: Push Unknown placeholders (dcR not yet computed)
    -- |   - For neg/pos branches: Push the computed dcR as the continuous background
    -- |
    -- | **Note**: This follows the same pattern as binary's `applyInf`, which is good for consistency.
    restrict_node_set c (na : nas) b d@(node_id, InfNodes position dc p n) =
        withDebug_restrict @a c (na : nas) b d $ \c' nas' b' d' -> restrict_node_set_internal c' nas' b' d'
      where
        restrict_node_set_internal c (na : nas) b d@(node_id, InfNodes position dc p n) =
            -- Check if we need to infer InfNodes (if we've passed the target position)
            let current_path = (reverse $ map fst $ un_current_level c) ++ [position]
            in if current_path > na
                then -- We've passed the target position, need to infer an InfNode at the target
                    let (c', d') = inferInfNode @a c (last na) d
                    in restrict_node_set @a c' (na : nas) b d'
                else let
                    c_ = add_to_stack_ (position, Dc) (((0, 0), Unknown), ((0, 0), Unknown)) c  -- Push Unknown for dc, Unknown for dcR (dcR not yet computed)
                    (c1, dcR) = restrict_node_set @Dc (traverse_dc_unary @a "inf dc" c_ dc) (na : nas) b (getNode c dc)
                    c2_ = add_to_stack_ (position, Neg) (getNode c1 dc, dcR) (reset_stack_un c1 c)
                    (c2, nR) = trace "inf neg" ( restrict_node_set @Neg (traverse_dc_unary @a "inf neg" c2_ n) (na : nas) b (getNode c1 n))
                    c3_ = add_to_stack_ (position, Pos) (getNode c2 dc, dcR) (reset_stack_un c2 c)
                    (c3, pR) = trace "inf pos" (restrict_node_set @Pos (traverse_dc_unary @a "inf pos" c3_ p) (na : nas) b (getNode c2 p))

                    in absorb_unary $ applyElimRule_unary @a (reset_stack_un c3 c) $ InfNodes position (fst dcR) (fst pR) (fst nR)
    restrict_node_set c [] b d@(node_id, InfNodes position dc p n) =
        withDebug_restrict @a c [] b d $ \c' _nas' _b' d' -> restrict_node_set_internal c' [] _b' d'
      where
        restrict_node_set_internal c [] b d@(node_id, InfNodes position dc p n) =
            -- No more restrictions to apply, return as-is
            absorb_unary (c, d)

    -- | Restricts/quantifies variables in an EndInfNode (class exit marker).
    -- |
    -- | This function handles restriction when exiting a class hierarchy. Similar to binary's
    -- | `endinf_case`, it pops the inference type stack to determine which inference context
    -- | (Dc/Neg/Pos) was used, then applies the appropriate restriction operation.
    -- |
    -- | Algorithm:
    -- |   1. Pop the inference type stack to get the inference context for the current class
    -- |   2. Synchronize dc_stack traversal for the EndInfNode case
    -- |   3. Check if we need to continue traversal (if there are remaining restrictions)
    -- |   4. If restrictions remain: continue with child node (may need inference)
    -- |   5. Apply restriction based on the inference type (Dc, Neg, or Pos)
    -- |   6. Wrap result in EndInfNode to maintain class hierarchy structure
    -- |   7. Absorb redundant branches
    restrict_node_set c nas b d@(node_id, EndInfNode child) =
        withDebug_restrict @a c nas b d $ \c' nas' b' d' -> restrict_node_set_internal c' nas' b' d'
      where
        restrict_node_set_internal c nas b d@(node_id, EndInfNode child) =  let
            -- Pop the inference type stack to get the inference context for the current class
            (c_, inf) = pop_stack_ c
            -- Synchronize dc_stack traversal for the EndInfNode case
            c' = traverse_dc_unary @a "endinf" c_ node_id
            (c'', (r, _)) = case inf of
                 Dc -> restrict_node_set @Dc c' nas b (getNode c child)
                 Pos -> restrict_node_set @Pos c' nas b (getNode c child)
                 Neg -> restrict_node_set @Neg c' nas b (getNode c child)
            in absorb_unary $ applyElimRule'_unary @a (reset_stack_un c'' c, EndInfNode r)

    -- | Restricts/quantifies variables when encountering a Leaf (terminal value).
    -- |
    -- | When we encounter a Leaf but there are still restrictions to apply, we need to
    -- | infer nodes to continue traversal until we reach the target position.
    -- | Once all restrictions are applied, we return the Leaf as-is.
    restrict_node_set c (na : nas) b d@(_, Leaf _) =
        withDebug_restrict @a c (na : nas) b d $ \c' nas' b' d' -> restrict_node_set_internal c' nas' b' d'
      where
        restrict_node_set_internal c (na : nas) b d@(_, Leaf _) =
            -- Need to infer nodes to reach target position, then continue restriction
            -- Infer a node at the target position, then recursively restrict
            let (c', inferred_node) = inferNode @a c (last na) d
            in restrict_node_set @a c' (na : nas) b inferred_node
    restrict_node_set c [] b d@(_, Leaf _) =
        withDebug_restrict @a c [] b d $ \c' _nas' _b' d' -> restrict_node_set_internal c' [] _b' d'
      where
        restrict_node_set_internal c [] _ d@(_, Leaf _) = absorb_unary (c, d)  -- No more restrictions, return Leaf

    -- | Restricts/quantifies variables when encountering Unknown.
    -- |
    -- | When we encounter Unknown but there are still restrictions to apply, we need to
    -- | infer nodes to continue traversal until we reach the target position.
    -- | Unknown is returned as-is when there are no restrictions remaining.
    restrict_node_set c (na : nas) b d@(_, Unknown) =
        withDebug_restrict @a c (na : nas) b d $ \c' nas' b' d' -> restrict_node_set_internal c' nas' b' d'
      where
        restrict_node_set_internal c (na : nas) b d@(_, Unknown) =
            -- Need to infer nodes to reach target position, then continue restriction
            -- Infer a node at the target position, then recursively restrict
            let (c', inferred_node) = inferNode @a c (last na) d
            in restrict_node_set @a c' (na : nas) b inferred_node
    restrict_node_set c [] b d@(_, Unknown) =
        withDebug_restrict @a c [] b d $ \c' _nas' _b' d' -> restrict_node_set_internal c' [] _b' d'
      where
        restrict_node_set_internal c [] _ d@(_, Unknown) = (c, d)  -- No more restrictions, return Unknown

    -- Fallback: should not happen with proper type handling
    restrict_node_set c nas b d = error ("nonexhaustive restrict_node_set: " ++ "\n c: \n" ++ show (getLookup c) ++ "\n nas: \n" ++ show nas ++ "\n b: \n" ++ show b ++ "\n d: \n" ++ show d)