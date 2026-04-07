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

module MDD.Traversal.Unary where

import MDD.Types
import MDD.Traversal.Context
import MDD.NodeLookup
import MDD.Traversal.Stack
import MDD.Traversal.Support
import MDD.Extra.Draw (debug_manipulation_unary, show_node)

import Data.Hashable
import qualified Data.HashMap.Strict as HashMap
import Data.Kind (Constraint)
import Debug.Trace (trace)

-- | refactored with use of AI


-- * Restriction: passed-target inference (shared across @Dd@ shapes)

-- | When the current path has passed the next restriction coordinate (@current_path > na@),
-- 'passedTargetKind' distinguishes three actions.
data PassedTargetKind
  = -- | Target lies in the same class layer: infer a standard 'Node'.
    PassedSameClass
  | -- | Target lies on a shallower layer: exit toward it (simple case — not 'EndClassNode').
    PassedPreviousLayer
  | -- | Target needs a deeper 'ClassNode': infer class structure at @infnode_position@.
    PassedDeeperLayer
  deriving (Eq, Show)

-- | Result of comparing the traversal path to the next restriction coordinate @na@.
data RestrictPathVsTarget
  = -- | @current_path == na@: apply restriction here, then continue with @nas@.
    RestrictHit
  | -- | @current_path < na@: descend further before consuming @na@.
    RestrictNotYetReached
  | -- | @current_path > na@: synthesize missing structure; see 'PassedTargetKind'.
    RestrictPassed PassedTargetKind
  deriving (Eq, Show)

-- | Staging before 'inferClassNode' in the deeper-layer case: either insert an 'EndClassNode'
-- wrapper for the current root, or continue with the root unchanged (e.g. 'Unknown').
type RestrictDeeperLayerStage = UnOpContext -> Node -> (UnOpContext, Node)

wrapCurrentRootAsEndClass :: RestrictDeeperLayerStage
wrapCurrentRootAsEndClass c d = insert c (EndClassNode (fst d))

restrictDeeperLayerBare :: RestrictDeeperLayerStage
restrictDeeperLayerBare c d = (c, d)

-- | 'PassedSameClass': infer a normal node at @last na@ and recurse.
restrictPassedSameClass :: TraversalMode -> UnOpContext -> [Position] -> Bool -> Node -> (UnOpContext, Node)
restrictPassedSameClass tm c (na : nas) b d =
  let (c', d') = tmInferNode tm c (last na) d
  in restrict_node_set tm c' (na : nas) b d'
restrictPassedSameClass _ _ [] _ _ = error "restrictPassedSameClass: empty position list"

-- | 'PassedPreviousLayer' (simple): wrap current root as 'EndClassNode' and recurse.
restrictPassedPreviousLayerSimple :: TraversalMode -> UnOpContext -> [Position] -> Bool -> Node -> (UnOpContext, Node)
restrictPassedPreviousLayerSimple tm c (na : nas) b d =
  let (c1, endclass_wrapped) = insert c (EndClassNode (fst d))
  in restrict_node_set tm c1 (na : nas) b endclass_wrapped
restrictPassedPreviousLayerSimple _ _ [] _ _ = error "restrictPassedPreviousLayerSimple: empty position list"

-- | 'PassedDeeperLayer': stage, 'inferClassNode' at @infnode_position@, recurse.
restrictPassedDeeperLayer :: TraversalMode -> UnOpContext -> [Position] -> Bool -> Node -> Int -> RestrictDeeperLayerStage -> (UnOpContext, Node)
restrictPassedDeeperLayer tm c (na : nas) b d infnode_position stage =
  let (c1, d1) = stage c d
      (c2, d2) = tmInferClassNode tm c1 infnode_position d1
  in restrict_node_set tm c2 (na : nas) b d2
restrictPassedDeeperLayer _ _ [] _ _ _ _ = error "restrictPassedDeeperLayer: empty position list"


-- * Unary Caching Helper


-- | A higher-order function for handling cache lookup and update for unary operations.
-- | The cache prevents redundant computations during unary operations (negation, restriction, etc.).
withCache_ :: UnOpContext -> Node -> (UnOpContext, Node) -> (UnOpContext, Node)
withCache_ c@UCxt { un_cache = nc } (key, _) func_with_args =
  case HashMap.lookup key nc of
    Just result -> (c, (result, getDd c result))  -- Cache hit: return previously computed result
    Nothing -> let
      (updatedContext, result@(nodeid, _)) = func_with_args
      updatedCache = HashMap.insert key nodeid nc
      in (updatedContext { un_cache = updatedCache }, result)  -- Cache miss: compute and store result


withDebug_restrict :: TraversalMode -> UnOpContext -> [Position] -> Bool -> Node -> (UnOpContext -> [Position] -> Bool -> Node -> (UnOpContext, Node)) -> (UnOpContext, Node)
withDebug_restrict tm c nas b d restrict_func =
    let func_key = "restrict"
        func_name = "restrict " ++ tmName tm
        result = restrict_func c nas b d
    in debug_manipulation_unary result func_key func_name c d nas b


-- * Negation Logic


negation :: UnOpContext -> Node -> (UnOpContext, Node)
negation = negation'

negation' :: UnOpContext -> Node -> (UnOpContext, Node)
negation' c d@(node_id, Node position pos_child neg_child)  = withCache_ c d $ let
    (c1, (posR, _)) = negation' c (getNode c pos_child)
    (c2, (negR, _)) = negation' c1 (getNode c1 neg_child)
    in insert c2 $ Node position posR negR
negation' c d@(node_id, ClassNode position dc p n) = withCache_ c d $ let
    (c1, (r_dc, _)) = negation' c (getNode c dc)
    (c2, (r_n, _)) = negation' c1 (getNode c1 n)
    (c3, (r_p, _)) = negation' c2 (getNode c2 p)
        in insert c3 $ ClassNode position r_dc r_p r_n
negation' c d@(node_id, EndClassNode a) = withCache_ c  d $ let
    (c1, (result, _)) = negation' c (getNode c a)
    in insert c1 $ EndClassNode result
negation' c (_, Leaf b) = (c, ((hash $ Leaf (not b), 0), Leaf (not b)))
negation' c u@(_, Unknown) = (c, u)





restrict_node_set :: TraversalMode -> UnOpContext -> [Position] -> Bool -> Node -> (UnOpContext, Node)
restrict_node_set tm c (na : nas) b d@(node_id, Node position pos_child neg_child)  =
    withDebug_restrict tm c (na : nas) b d $ \c' nas' b' d' -> restrict_node_set_internal c' nas' b' d'
  where
    restrict_node_set_internal c (na : nas) b d@(node_id, Node position pos_child neg_child)  =
        let current_path = (reverse $ map fst $ un_current_level c) ++ [position]
            pathCmp = --trace ("comparing path: " ++ show current_path ++ " with na " ++ show na ++ " = " ++ show (compare_current_target_positions current_path na))
                compare_current_target_positions current_path na
        in case pathCmp of
            RestrictHit ->
                let
                    (c1, posR) = (fst traverse_pos, fst $ snd traverse_pos)
                    traverse_pos = restrict_node_set tm c_ nas b (getNode c pos_child)
                    c_ = traverse_dc_unary tm MvPos c node_id

                    (c2, negR) = (fst traverse_neg, fst $ snd traverse_neg)
                    traverse_neg = restrict_node_set tm c1_ nas b (getNode c1 neg_child)
                    c1_ = traverse_dc_unary tm MvNeg (reset_stack_un c1 c) node_id

                    in if b  -- depending on b, take positive or negative evaluation
                        then tmApplyElimRule tm c2 $ Node position posR posR
                        else tmApplyElimRule tm c2 $ Node position negR negR
            RestrictNotYetReached ->
                let
                    (c1, posR) = (fst traverse_pos, fst $ snd traverse_pos)
                    traverse_pos = -- trace ("\npos: " ++ show_node c (getNode c pos_child))
                        (restrict_node_set tm c_ (na : nas) b (getNode c pos_child))
                    c_ = traverse_dc_unary tm MvPos c node_id

                    (c2, negR) = (fst traverse_neg, fst $ snd traverse_neg)
                    traverse_neg = -- trace ("\nneg: " ++ show_node c1 (getNode c1 neg_child))
                        (restrict_node_set tm c1_ (na : nas) b (getNode c1 neg_child))
                    c1_ = traverse_dc_unary tm MvNeg (reset_stack_un c1 c) node_id

                    in tmApplyElimRule tm c2 $ Node position posR negR
            RestrictPassed PassedSameClass -> restrictPassedSameClass tm c (na : nas) b d
            RestrictPassed PassedPreviousLayer -> restrictPassedPreviousLayerSimple tm c (na : nas) b d
            RestrictPassed PassedDeeperLayer ->
                restrictPassedDeeperLayer tm c (na : nas) b d
                    (na !! length (init current_path))
                    wrapCurrentRootAsEndClass


restrict_node_set tm c (na : nas) b d@(node_id, ClassNode position dc p n) =
    withDebug_restrict tm c (na : nas) b d $ \c' nas' b' d' -> restrict_node_set_internal c' nas' b' d'
  where
    restrict_node_set_internal c (na : nas) b d@(node_id, ClassNode position dc p n) =
        -- Check if we need to infer ClassNode (if we've passed the target position)
        let current_path = (reverse $ map fst $ un_current_level c) ++ [position]
            cp = -- trace ("infnode!!! comparing path: " ++ show current_path ++ " with na " ++ show na ++ " = case " ++ show (compare_current_target_positions current_path na))
                current_path
        in if cp > na
            then -- We've passed the target position, need to infer an ClassNode at the target
                restrictPassedDeeperLayer tm c (na : nas) b d
                    (na !! length (init current_path))
                    wrapCurrentRootAsEndClass
            else let
                c_ = add_to_stack_ (position, Dc) (((0, 0), Unknown), ((0, 0), Unknown)) (traverse_dc_unary tm MvClassDc c node_id)
                (c1, dcR) = restrict_node_set modeDc c_ (na : nas) b (getNode c dc)
                (c1', dcR') = absorb_dc_unary modeDc c1 dcR

                c2_ = add_to_stack_ (position, Neg) (getNode c1' dc, dcR') (traverse_dc_unary tm MvClassNeg (reset_stack_un c1' c) node_id)
                (c2, nR) = restrict_node_set modeNeg c2_ (na : nas) b (getNode c1' n)
                (c2', nR') = absorb_unary modeNeg c2 dcR' nR

                c3_ = add_to_stack_ (position, Pos) (getNode c2' dc, dcR') (traverse_dc_unary tm MvClassPos (reset_stack_un c2' c) node_id)
                (c3, pR) = restrict_node_set modePos c3_ (na : nas) b (getNode c2' p)
                (c3', pR') = absorb_unary modePos c3 dcR' pR

                in tmApplyElimRule tm (reset_stack_un c3' c) $ ClassNode position (fst dcR') (fst pR') (fst nR')

-- | Restricts/quantifies variables in an EndClassNode (class exit marker).
-- |
-- | This function handles restriction when exiting a class hierarchy. Similar to binary's
-- | `endclass_case`, it pops the inference type stack to determine which inference context
-- | (Dc/Neg/Pos) was used in the previous class, then applies the appropriate restriction operation.
restrict_node_set tm c (na : nas) b d@(node_id, EndClassNode child) =
    withDebug_restrict tm c (na : nas) b d $ \c' nas' b' d' -> restrict_node_set_internal c' nas' b' d'
  where
    restrict_node_set_internal c (na : nas) b d@(node_id, EndClassNode child) =
        -- For EndClassNode, current_path is just the current level (no position to append)
        let current_path = reverse $ map fst $ un_current_level c
            infkind = -- trace ("comparing path: " ++ show current_path ++ " with na " ++ show na ++ " = " ++ show (passedTargetKind current_path na))
                passedTargetKind current_path na
        in case infkind of
            PassedSameClass -> restrictPassedSameClass tm c (na : nas) b d
            PassedPreviousLayer ->
                -- Pop stack, sync dc traversal, recurse into child (not the simple wrap+recurse path)
                let
                    (c_, inf) = pop_stack_ c
                    c' = traverse_dc_unary tm ExitClass c_ node_id
                    (c'', (r, _)) = case inf of
                         Dc -> restrict_node_set modeDc c' (na : nas) b (getNode c child)
                         Pos -> restrict_node_set modePos c' (na : nas) b (getNode c child)
                         Neg -> restrict_node_set modeNeg c' (na : nas) b (getNode c child)
                in let (c3, endNode) = tmApplyElimRule tm (reset_stack_un c'' c) (EndClassNode r)
                   in case un_dc_stack c3 of
                       (dcR : _) -> absorb_unary tm c3 dcR endNode
                       []        -> (c3, endNode)
            PassedDeeperLayer ->
                let current_lv = current_path
                    infnode_position = na !! length current_lv
                in restrictPassedDeeperLayer tm c (na : nas) b d infnode_position wrapCurrentRootAsEndClass

restrict_node_set tm c (na : nas) b d@(_, Leaf _) =
    withDebug_restrict tm c (na : nas) b d $ \c' nas' b' d' -> restrict_node_set_internal c' nas' b' d'
  where
    restrict_node_set_internal c (na : nas) b d@(_, Leaf _) =
        -- For Leaf nodes, current_path is just the current level (no position to append)
        let current_path = reverse $ map fst $ un_current_level c
            infkind = --trace ("comparing path: " ++ show current_path ++ " with na " ++ show na ++ " = " ++ show (passedTargetKind current_path na))
                passedTargetKind current_path na
        in case infkind of
            PassedSameClass -> restrictPassedSameClass tm c (na : nas) b d
            PassedPreviousLayer -> restrictPassedPreviousLayerSimple tm c (na : nas) b d
            PassedDeeperLayer ->
                let current_lv = current_path
                    infnode_position = na !! length current_lv
                in restrictPassedDeeperLayer tm c (na : nas) b d infnode_position wrapCurrentRootAsEndClass
restrict_node_set tm c (na : nas) b d@(_, Unknown) =
    withDebug_restrict tm c (na : nas) b d $ \c' nas' b' d' -> restrict_node_set_internal c' nas' b' d'
  where
    restrict_node_set_internal c (na : nas) b d@(_, Unknown) =
        -- For Unknown nodes, current_path is just the current level (no position to append)
        let current_path = reverse $ map fst $ un_current_level c
            infkind = --trace ("comparing path: " ++ show current_path ++ " with na " ++ show na ++ " = " ++ show (passedTargetKind current_path na))
                passedTargetKind current_path na
        in case infkind of
            PassedSameClass -> restrictPassedSameClass tm c (na : nas) b d
            PassedPreviousLayer -> restrictPassedPreviousLayerSimple tm c (na : nas) b d
            PassedDeeperLayer ->
                let current_lv = current_path
                    infnode_position = na !! length current_lv
                in restrictPassedDeeperLayer tm c (na : nas) b d infnode_position restrictDeeperLayerBare

-- base case, finished restricting, perform absorb and return result.
restrict_node_set tm c _ b d =
    withDebug_restrict tm c [] b d $ \c' _nas' _b' d' ->
        case un_dc_stack c' of
            (dcR : _) -> absorb_unary tm c' dcR d'
            []        -> (c', d')

-- Fallback: should not happen with proper type handling
restrict_node_set tm c nas b d = error ("nonexhaustive restrict_node_set: " ++ "\n c: \n" ++ show (getLookup c) ++ "\n nas: \n" ++ show nas ++ "\n b: \n" ++ show b ++ "\n d: \n" ++ show d)




-- * Position Comparison and Inference Type Determination


-- | Compares the current path with the next restriction coordinate @na@.
compare_current_target_positions :: Position -> Position -> RestrictPathVsTarget
compare_current_target_positions current_path na
    | current_path == na = RestrictHit
    | current_path < na = RestrictNotYetReached
    | current_path > na = RestrictPassed (passedTargetKind (init current_path) na)
    | otherwise = error "compare_current_target_positions: unexpected comparison result"

-- | When @current_path > na@, classifies which structure to synthesize. The @current_level@
-- argument is the relevant prefix (e.g. @init current_path@ from 'compare_current_target_positions'
-- at a 'Node', or @current_path@ at 'Leaf' / 'Unknown' / 'EndClassNode').
passedTargetKind :: Position -> Position -> PassedTargetKind
passedTargetKind current_level na
    | null current_level || null na = error "passedTargetKind: empty position"
    | current_level == init na = PassedSameClass
    | length (init na) > length current_level && sharesPrefix = PassedDeeperLayer
    | otherwise = PassedPreviousLayer
  where
    sharesPrefix = and (zipWith (==) current_level (take (length current_level) na))