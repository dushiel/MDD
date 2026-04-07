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
{-# HLINT ignore "Use camelCase" #-}

module MDD.Ops.Unary where

import MDD.Types
import MDD.Context
import MDD.Manager
import MDD.Stack
import MDD.Traversal
import MDD.Draw (debug_manipulation_unary, show_node)

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
withCache_ :: UnOpContext -> Node -> (UnOpContext, Node) -> (UnOpContext, Node)
withCache_ c@UCxt { un_cache = nc } (key, _) func_with_args =
  case HashMap.lookup key nc of
    Just result -> (c, (result, getDd c result))  -- Cache hit: return previously computed result
    Nothing -> let
      (updatedContext, result@(nodeid, _)) = func_with_args
      updatedCache = HashMap.insert key nodeid nc
      in (updatedContext { un_cache = updatedCache }, result)  -- Cache miss: compute and store result

-- | Debug wrapper for restrict_node_set operations.
-- | Similar to debug_manipulation for binary operations, but adapted for unary operations.
withDebug_restrict :: forall a. (DdF3 a) =>
    UnOpContext -> [Position] -> Bool -> Node ->
    (UnOpContext -> [Position] -> Bool -> Node -> (UnOpContext, Node)) ->
    (UnOpContext, Node)
withDebug_restrict c nas b d restrict_func =
    let func_key = "restrict"
        func_name = "restrict " ++ to_str @a
        result = restrict_func c nas b d
    in debug_manipulation_unary result func_key func_name c d nas b

-- ==========================================================================================================
-- * Unary DC Traversal Helper
-- ==========================================================================================================

-- | Synchronizes a single dc branch node with a reference node for unary operations.
traverse_dc_generic_unary :: forall a. (DdF3 a) => String -> UnOpContext -> Node -> Node -> Node
traverse_dc_generic_unary s c refNode dcNode =
    case (dcNode, refNode) of
        ( tNode@(_, Node position _ _), rNode@(_, Node idx _ _) ) ->
            if | position > idx -> dcNode  -- dcNode ahead: no catchup needed
                | position == idx -> move_dc c s dcNode  -- Positions match: move down
                | position < idx -> move_dc c s (catchup @a s c dcNode idx)  -- dcNode behind: catch up
        ( (_, Node{}), (_, Leaf _) ) -> move_dc c s (catchup @a s c dcNode (-1))  -- Catch up to terminal
        ( (_, Node{}), (_, EndInfNode{}) ) -> move_dc c s (catchup @a s c dcNode (-1))  -- Catch up to terminal
        ( (_, EndInfNode{}), (_, EndInfNode{}) ) -> move_dc c s dcNode  -- Both EndInfNodes: move down
        ( _, (_, Unknown) ) -> move_dc c s dcNode  -- refNode Unknown: move down dcNode
        ( (_, Unknown), _ ) -> dcNode  -- dcNode Unknown: return as-is (resolves from stack)
        ( (_, InfNodes position _ _ _), (_, InfNodes idx _ _ _) ) ->
            if | position > idx -> dcNode  -- dcNode ahead: no catchup
                | position == idx -> move_dc c s dcNode  -- Positions match: move down
                | position < idx -> dcNode  -- dcNode behind: no catchup (InfNodes handled separately)
        _ -> dcNode  -- Default: return as-is


-- ==========================================================================================================
-- * Negation Logic
-- ==========================================================================================================

negation :: UnOpContext -> Node -> (UnOpContext, Node)
negation = negation'

negation' :: UnOpContext -> Node -> (UnOpContext, Node)
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
    restrict_node_set :: UnOpContext -> [Position] -> Bool -> Node -> (UnOpContext, Node)
    traverse_dc_unary :: String -> UnOpContext -> NodeId -> UnOpContext

instance (DdF3 a) => DdUnary a where
    -- | Synchronizes the dc_stack with the main traversal for unary operations.
    traverse_dc_unary s c@UCxt{un_dc_stack = dcRs, un_current_level = lv} d =
        if to_str @a == "Dc" then c
            else let
                new_dcRs = map (traverse_dc_generic_unary @a s c (getNode c d)) dcRs
            in c{un_dc_stack = new_dcRs, un_current_level=lv}

    -- | Restricts/quantifies variables in a Node (variable node).
    -- |
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
            -- Use compare_current_target_positions to determine the appropriate action
            let current_path = (reverse $ map fst $ un_current_level c) ++ [position]
                case_code = --trace ("comparing path: " ++ show current_path ++ " with na " ++ show na ++ " = case " ++ show (compare_current_target_positions current_path na))
                    (compare_current_target_positions current_path na)
            in case case_code of
                1 -> -- Hit: exact match, apply restrict and continue with leftover list
                    let
                        (c1, posR) = (fst traverse_pos, fst $ snd traverse_pos)
                        traverse_pos = restrict_node_set @a c_ nas b (getNode c pos_child)
                        c_ = traverse_dc_unary @a "pos child" c pos_child

                        (c2, negR) = (fst traverse_neg, fst $ snd traverse_neg)
                        traverse_neg = restrict_node_set @a c1_ nas b (getNode c1 neg_child)
                        c1_ = traverse_dc_unary @a "neg child" (reset_stack_un c1 c) neg_child

                        in if b  -- depending on b, take positive or negative evaluation
                            then applyElimRule @a c2 $ Node position posR posR
                            else applyElimRule @a c2 $ Node position negR negR
                2 -> -- Not yet reached: continue traversing MDD
                    let
                        (c1, posR) = (fst traverse_pos, fst $ snd traverse_pos)
                        traverse_pos = -- trace ("\npos: " ++ show_node c (getNode c pos_child))
                            (restrict_node_set @a c_ (na : nas) b (getNode c pos_child))
                        c_ = traverse_dc_unary @a "pos child" c pos_child

                        (c2, negR) = (fst traverse_neg, fst $ snd traverse_neg)
                        traverse_neg = -- trace ("\nneg: " ++ show_node c1 (getNode c1 neg_child))
                            (restrict_node_set @a c1_ (na : nas) b (getNode c1 neg_child))
                        c1_ = traverse_dc_unary @a "neg child" (reset_stack_un c1 c) neg_child

                        in applyElimRule @a c2 $ Node position posR negR
                3 -> -- Same class: infer normal node at target position
                    let (c', d') = inferNode @a c (last na) d
                    in restrict_node_set @a c' (na : nas) b d'
                4 -> -- Previous layer: infer EndInfNode to exit current class
                    let (c1, endinf_wrapped) = insert c (EndInfNode (fst d))
                    in restrict_node_set @a c1 (na : nas) b endinf_wrapped
                5 -> -- Deeper layer: infer InfNode at the appropriate position
                    let
                        infnode_position = na !! length (init current_path)
                        (c1, d1) = insert c (EndInfNode (fst d))
                        (c2, d2) = inferInfNode @a c1 infnode_position d1
                    in restrict_node_set @a c2 (na : nas) b d2
                _ -> error ("compare_current_target_positions returned unexpected case: " ++ show case_code)

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
                cp = -- trace ("infnode!!! comparing path: " ++ show current_path ++ " with na " ++ show na ++ " = case " ++ show (compare_current_target_positions current_path na))
                    current_path
            in if cp > na
                then -- We've passed the target position, need to infer an InfNode at the target
                    let infnode_position = na !! length (init current_path)
                        (c1, d1) = insert c (EndInfNode (fst d))
                        (c2, d2) = inferInfNode @a c1 infnode_position d1
                    in restrict_node_set @a c2 (na : nas) b d2
                else let
                    c_ = add_to_stack_ (position, Dc) (((0, 0), Unknown), ((0, 0), Unknown)) c  -- Push Unknown for dc, Unknown for dcR (dcR not yet computed)
                    (c1, dcR) = restrict_node_set @Dc (traverse_dc_unary @a "inf dc" c_ dc) (na : nas) b (getNode c dc)
                    c2_ = add_to_stack_ (position, Neg) (getNode c1 dc, dcR) (reset_stack_un c1 c)
                    (c2, nR) = ( restrict_node_set @Neg (traverse_dc_unary @a "inf neg" c2_ n) (na : nas) b (getNode c1 n))
                    c3_ = add_to_stack_ (position, Pos) (getNode c2 dc, dcR) (reset_stack_un c2 c)
                    (c3, pR) = restrict_node_set @Pos (traverse_dc_unary @a "inf pos" c3_ p) (na : nas) b (getNode c2 p)

                    in absorb_unary @a $ applyElimRule @a (reset_stack_un c3 c) $ InfNodes position (fst dcR) (fst pR) (fst nR)

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
    restrict_node_set c (na : nas) b d@(node_id, EndInfNode child) =
        withDebug_restrict @a c (na : nas) b d $ \c' nas' b' d' -> restrict_node_set_internal c' nas' b' d'
      where
        restrict_node_set_internal c (na : nas) b d@(node_id, EndInfNode child) =
            -- For EndInfNode, current_path is just the current level (no position to append)
            let current_path = reverse $ map fst $ un_current_level c
                case_code = -- trace ("comparing path: " ++ show current_path ++ " with na " ++ show na ++ " = case " ++ show (determine_inference_type current_path na))
                    (determine_inference_type current_path na)
            in case case_code of
                3 -> -- Same class: infer normal node at target position
                    let (c', d') = inferNode @a c (last na) d
                    in restrict_node_set @a c' (na : nas) b d'
                4 -> -- Previous layer: handle EndInfNode (pop stack and continue with child)
                    let
                        -- Pop the inference type stack to get the inference context for the current class
                        (c_, inf) = pop_stack_ c
                        -- Synchronize dc_stack traversal for the EndInfNode case
                        c' = traverse_dc_unary @a "endinf" c_ node_id
                        (c'', (r, _)) = case inf of
                             Dc -> restrict_node_set @Dc c' (na : nas) b (getNode c child)
                             Pos -> restrict_node_set @Pos c' (na : nas) b (getNode c child)
                             Neg -> restrict_node_set @Neg c' (na : nas) b (getNode c child)
                    in absorb_unary @a $ applyElimRule' @a (reset_stack_un c'' c, EndInfNode r)
                5 -> -- Deeper layer: infer InfNode at the appropriate position
                    let
                        current_lv = current_path
                        infnode_position = na !! length current_lv  -- int at index (length current_path) in na
                        (c1, d1) = insert c (EndInfNode (fst d))
                        (c2, d2) = inferInfNode @a c1 infnode_position d1
                    in restrict_node_set @a c2 (na : nas) b d2
                _ -> error ("determine_inference_type returned unexpected case: " ++ show case_code)

    -- | Restricts/quantifies variables when encountering a Leaf (terminal value).
    -- |
    -- | When we encounter a Leaf but there are still restrictions to apply, we need to
    -- | infer nodes to continue traversal until we reach the target position.
    -- | Once all restrictions are applied, we return the Leaf as-is.
    restrict_node_set c (na : nas) b d@(_, Leaf _) =
        withDebug_restrict @a c (na : nas) b d $ \c' nas' b' d' -> restrict_node_set_internal c' nas' b' d'
      where
        restrict_node_set_internal c (na : nas) b d@(_, Leaf _) =
            -- For Leaf nodes, current_path is just the current level (no position to append)
            let current_path = reverse $ map fst $ un_current_level c
                case_code = --trace ("comparing path: " ++ show current_path ++ " with na " ++ show na ++ " = case " ++ show (determine_inference_type current_path na))
                    (determine_inference_type current_path na)
            in case case_code of
                3 -> -- Same class: infer normal node at target position
                    let (c', d') = inferNode @a c (last na) d
                    in restrict_node_set @a c' (na : nas) b d'
                4 -> -- Previous layer: infer EndInfNode to exit current class
                    let (c1, endinf_wrapped) = insert c (EndInfNode (fst d))
                    in restrict_node_set @a c1 (na : nas) b endinf_wrapped
                5 -> -- Deeper layer: infer InfNode at the appropriate position
                    let
                        current_lv = current_path
                        infnode_position = na !! length current_lv  -- int at index (length current_path) in na
                        (c1, d1) = insert c (EndInfNode (fst d))
                        (c2, d2) = inferInfNode @a c1 infnode_position d1
                    in (restrict_node_set @a c2 (na : nas) b d2)
                _ -> error ("compare_current_target_positions returned unexpected case: " ++ show case_code)

    -- | Restricts/quantifies variables when encountering Unknown.
    -- |
    -- | When we encounter Unknown but there are still restrictions to apply, we need to
    -- | infer nodes to continue traversal until we reach the target position.
    -- | Unknown is returned as-is when there are no restrictions remaining.
    restrict_node_set c (na : nas) b d@(_, Unknown) =
        withDebug_restrict @a c (na : nas) b d $ \c' nas' b' d' -> restrict_node_set_internal c' nas' b' d'
      where
        restrict_node_set_internal c (na : nas) b d@(_, Unknown) =
            -- For Unknown nodes, current_path is just the current level (no position to append)
            let current_path = reverse $ map fst $ un_current_level c
                case_code = --trace ("comparing path: " ++ show current_path ++ " with na " ++ show na ++ " = case " ++ show (determine_inference_type current_path na))
                    (determine_inference_type current_path na)
            in case case_code of
                3 -> -- Same class: infer normal node at target position
                    let (c', d') = inferNode @a c (last na) d
                    in restrict_node_set @a c' (na : nas) b d'
                4 -> -- Previous layer: infer EndInfNode to exit current class
                    let (c1, endinf_wrapped) = insert c (EndInfNode (fst d))
                    in restrict_node_set @a c1 (na : nas) b endinf_wrapped
                5 -> -- Deeper layer: infer InfNode at the appropriate position
                    let
                        current_lv = current_path
                        infnode_position = na !! length current_lv  -- int at index (length current_path) in na
                        (c', d') = inferInfNode @a c infnode_position d
                    in (restrict_node_set @a c' (na : nas) b d')
                _ -> error ("determine_inference_type returned unexpected case: " ++ show case_code)

    -- base case, finished restricting, perform absorb and return result.
    restrict_node_set c _ b d =
        withDebug_restrict @a c [] b d $ \c' _nas' _b' d' -> absorb_unary @a (c', d')

    -- Fallback: should not happen with proper type handling
    restrict_node_set c nas b d = error ("nonexhaustive restrict_node_set: " ++ "\n c: \n" ++ show (getLookup c) ++ "\n nas: \n" ++ show nas ++ "\n b: \n" ++ show b ++ "\n d: \n" ++ show d)



-- ==========================================================================================================
-- * Position Comparison and Inference Type Determination
-- ==========================================================================================================

-- | Compares the current path with the target position and returns a case code (1-5).
-- |
-- | Cases:
-- |   1: Hit - current_path == na, apply restrict and continue with leftover list of positions
-- |   2: Not yet reached - current_path < na, continue traversing MDD
-- |   3-5: Passed the target - current_path > na, need to infer a node at the target
-- |
-- | When case 3-5 is returned, use `determine_inference_type` to determine the specific inference type.
compare_current_target_positions :: Position -> Position -> Int
compare_current_target_positions current_path na
    | current_path == na = 1  -- Hit: exact match
    | current_path < na = 2   -- Not yet reached: continue traversal
    | current_path > na = determine_inference_type (init current_path) na  -- Passed: need inference
    | otherwise = error "compare_current_target_positions: unexpected comparison result"

-- | Determines what kind of inference needs to be done when we've passed the target position.
-- |
-- | This function is only called when current_path > na (case 3-5).
-- |
-- | Returns:
-- |   3: Target is in the same class (current_lv and init na match), infer normal node
-- |   4: Target is on a previous layer class progression (current_lv and init na differ), infer endinf node
-- |   5: Target requires entering a deeper class layer (init na is longer than current_level and they share a prefix), infer infnode
determine_inference_type :: Position -> Position -> Int
determine_inference_type current_level na
    | null current_level || null na = error "determine_inference_type: empty position"
    | current_level == init na = 3  -- Same class: infer normal node, with position last na
    | length (init na) > length current_level && sharesPrefix = 5  -- Deeper layer: infer infnode
    | otherwise = 4  -- Previous layer: infer endinf node
  where
    -- Check if current_level and na share a common prefix (up to the length of current_level)
    sharesPrefix = and (zipWith (==) current_level (take (length current_level) na))