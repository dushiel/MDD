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
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Map as Map
import Data.Kind (Constraint)

-- ==========================================================================================================
-- * Binary Caching Helper
-- ==========================================================================================================

-- A higher-order function for handling cache lookup and update
withCache :: BinaryOperatorContext -> (Node, Node, String) -> (BinaryOperatorContext, Node) -> (BinaryOperatorContext, Node)
withCache c@BinaryOperatorContext{bin_cache = nc, bin_dc_stack = dck} ((keyA, _), (keyB, _), keyFunc) func_with_args =
  case Map.lookup keyFunc nc of
    Just nc' -> case HashMap.lookup (keyA, keyB, dck) nc' of
      Just result -> (c, getNode c result) --`debug` (col Vivid Green "func cache:" ++ " found previous result for " ++ show (keyA, keyB))
      Nothing -> let
        (updatedContext, r@(result, _)) = func_with_args
        new_dck = bin_dc_stack updatedContext
        updatedCache = Map.insert keyFunc (HashMap.insert (keyA, keyB, new_dck) result nc') nc
        in (updatedContext { bin_cache = updatedCache }, r) -- `debug` (col Vivid Green "func cache:" ++ " adding new key`` " ++ show (keyA, keyB))
    Nothing -> error ("function not in map, bad initialisation?: " ++ show keyFunc)

-- ==========================================================================================================
-- * Redundancy Elimination (absorb)
-- ==========================================================================================================

absorb :: (BinaryOperatorContext, Node) -> (BinaryOperatorContext, Node)
absorb (c, n) = absorb' (c, n)

absorb' :: (BinaryOperatorContext, Node) -> (BinaryOperatorContext, Node)
-- | given a dcR and a pos or ng results, sets sub-paths in the local inf-domain which agree with the dcR to unknown ("absorbing them")
absorb' (c@BinaryOperatorContext{bin_dc_stack = (dcA, dcB, dc@(_, Unknown) : fs) }, a)  =
    let (c', r) = absorb' (c{bin_dc_stack = (dcA, dcB, fs)}, a) in (c, r)
absorb' (c@BinaryOperatorContext{bin_dc_stack = (_, _, dc : fs) }, a@(_, Unknown)) = (c, a)
absorb' (c@BinaryOperatorContext{bin_dc_stack = (_, _, dc : fs) }, a@(_, Leaf _))
    | a == dc = (c, ((0,0), Unknown))
    | otherwise = (c,a)
absorb' (c@BinaryOperatorContext{bin_dc_stack = (_, _, dc@(_, Leaf _)  : fs) }, a@(_, InfNodes _ d p n))  =  let
    (_, r1) = absorb' (c, getNode c d)
    (_, r2) = absorb' (c, getNode c p)
    (_, r3) = absorb' (c, getNode c n)
    in if r1 == r2 && r2 == r3 then (c, ((0,0), Unknown)) else (c, a)
absorb' (c@BinaryOperatorContext{bin_dc_stack = (_, _, dc@(_, Leaf _)  : fs) }, a@(_, EndInfNode a_child)) = if getNode c a_child == dc then (c, ((0,0), Unknown)) else (c, a)
absorb' (c@BinaryOperatorContext{bin_dc_stack = (_, _, dc@(_, EndInfNode dc') : fs) }, a@(_, EndInfNode a'))
    | a' == dc' = (c, ((0,0), Unknown))
    | otherwise = (c,a)
absorb' (c@BinaryOperatorContext{bin_dc_stack = (_, _, dc : fs) }, a)
    | a == dc = (c, ((0,0), Unknown))
    | otherwise = (c,a)
absorb' (c@BinaryOperatorContext{bin_dc_stack = (_, _, []) }, a) = (c, a)

-- ==========================================================================================================
-- * Binary Operation Typeclass (Dd1)
-- ==========================================================================================================

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
    apply c s a b = apply' @a c s (getNode c a) (getNode c b)
    apply'' c s a b = apply' @a c s a b

    apply' c s a@(_, Leaf _) b = leaf_cases @a c s a b
    apply' c s a b@(_, Leaf _) = leaf_cases @a c s a b
    apply' c s a@(_, Unknown) b = leaf_cases @a c s a b
    apply' c s a b@(_, Unknown) = leaf_cases @a c s a b

    apply' c s a@(a_id, EndInfNode _) b@(b_id, Node idx _ _) = withCache c (a, b, s) $ uncurry (applyElimRule @a) (inferNodeA' @a (apply'' @a) c s a b)
    apply' c s a@(a_id, Node{}) b@(b_id, EndInfNode _) = withCache c (a, b, s) $ uncurry (applyElimRule @a) (inferNodeB' @a (apply'' @a) c s a b)
    -- Inferred node for Arguments when EndInfNode is encountered
    apply' c s a@(a_id, EndInfNode ac) b@(b_id, EndInfNode bc) = withCache c (a, b, s) $
        endinf_case @a c s a_id b_id ac bc

    apply' c s a@(a_id, Node positionA pos_childA neg_childA)  b@(b_id, Node positionB pos_childB neg_childB)
        -- Match
        | positionA == positionB =
            let c_ = traverse_dc @a "pos child" c pos_childA pos_childB
                (c', (pos_result, _)) = apply @a c_ s pos_childA pos_childB

                c_' = traverse_dc @a "neg child" (reset_stack_bin c' c) neg_childA neg_childB
                (c'', (neg_result, _)) = apply @a c_' s neg_childA neg_childB
            in withCache c (a, b, s) $ applyElimRule @a (reset_stack_bin c'' c) (Node positionA pos_result neg_result)
        -- Mismatch, highest position gets an inferred node at position of the lowest
        | positionA < positionB = uncurry (applyElimRule @a) (inferNodeB' @a (apply'' @a) c s a b)
        | positionA > positionB = uncurry (applyElimRule @a) (inferNodeA' @a (apply'' @a) c s a b)

    -- -- entering new domains (InfNodes logic)
    apply' c s a@(a_id, InfNodes positionA _ _ _) b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB = withCache c (a, b, s) $
                uncurry (applyElimRule @a) (inferNodeA' @a (apply'' @a) c s a b)
        | positionA < positionB = withCache c (a, b, s) $
                absorb $ applyInfB @a c s a b
    apply' c s a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB = withCache c (a, b, s) $
                absorb $ applyInfA @a c s a b
        | positionA < positionB = withCache c (a, b, s) $
                uncurry (applyElimRule @a) (inferNodeB' @a (apply'' @a) c s a b)
    apply' c s a@(a_id, InfNodes positionA _ _ _)  b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = withCache c (a, b, s) $ absorb $ applyInf @a c s a b
        | positionA < positionB = withCache c (a, b, s) $ absorb $ applyInfB @a c s a b
        | positionA > positionB = withCache c (a, b, s) $ absorb $ applyInfA @a c s a b
    apply' c s a@(a_id, EndInfNode _) b@(b_id, InfNodes{}) = withCache c (a, b, s) $ absorb $ applyInfA @a c s a b
    apply' c s a@(a_id, InfNodes{}) b@(b_id, EndInfNode _) = withCache c (a, b, s) $ absorb $ applyInfB @a c s a b

    -- leaf cases for terminal values (0, 1) or Unknown
    leaf_cases c s a@(_, Leaf _) b@(_, Node{}) = withCache c (a, b, s) $ uncurry (applyElimRule @a) (inferNodeA' @a (apply'' @a) c s a b)
    leaf_cases c s a@(_, Node{}) b@(_, Leaf _) = withCache c (a, b, s) $ uncurry (applyElimRule @a) (inferNodeB' @a (apply'' @a) c s a b )
    -- leaf vs endinfnode cases
    leaf_cases c s a@(a_id, Leaf True) b@(b_id, EndInfNode bc) = withCache c (a, b, s) $
        endinf_case @a c s a_id b_id (1,0) bc
    leaf_cases c s a@(a_id, EndInfNode ac) b@(b_id, Leaf True) = withCache c (a, b, s) $
        endinf_case @a c s a_id b_id ac (1,0)
    leaf_cases c s a@(a_id, Leaf False) b@(b_id, EndInfNode bc) = withCache c (a, b, s) $
        endinf_case @a c s a_id b_id (2,0) bc
    leaf_cases c s a@(a_id, EndInfNode ac) b@(b_id, Leaf False) = withCache c (a, b, s) $
        endinf_case @a c s a_id b_id ac (2,0)
    -- leaf vs infnode cases
    leaf_cases c s a@(a_id, Leaf _) b@(b_id, InfNodes{}) = withCache c (a, b, s) $
        applyInfA @a c s a b
    leaf_cases c s a@(a_id, InfNodes {}) b@(b_id, Leaf _) = withCache c (a, b, s) $
        applyInfB @a c s a b

    leaf_cases c s a@(_, Unknown) b@(_, Unknown) = (c , a)
    leaf_cases c s a@(_, Unknown) b = -- resolve Unknown to see if it is a True or False or a dd
        let (c', dcA) = pop_dcA' c
        in applyDcA'' @a c' s dcA b
    leaf_cases c s a b@(_, Unknown) =
        let (c', dcB) = pop_dcB' c
        in applyDcB'' @a c' s a dcB
    -- Logic for Union/Intersection specific leaf handling
    leaf_cases c "union" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then absorb (c, a) else absorb (c, b)
    leaf_cases c "inter" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then absorb (c, b) else absorb (c, a)
    leaf_cases c s a b = error ("leaf case: " ++ s)

-- | ======================== DC versions (Argument B is DC type) ========================

    applyDcB c s a b = applyDcB' @a c s (getNode c a) (getNode c b)
    applyDcB'' c s a b = applyDcB' @a c s a b

    applyDcB' c s a@(_, Leaf _) b = dcB_leaf_cases @a c s a b
    applyDcB' c s a b@(_, Leaf _) = dcB_leaf_cases @a c s a b
    applyDcB' c s a@(_, Unknown) b = dcB_leaf_cases @a c s a b
    applyDcB' c s a b@(_, Unknown) = dcB_leaf_cases @a c s a b

    applyDcB' c s a@(a_id, EndInfNode _) b@(b_id, Node idx _ _) = withCache c (a, b, (s ++ "Dc")) $ uncurry (applyElimRule @a) (inferNodeA' @a (applyDcB'' @a) c s a b)
    applyDcB' c s a@(a_id, Node{}) b@(b_id, EndInfNode _) = withCache c (a, b, (s ++ "Dc")) $ uncurry (applyElimRule @a) (inferNodeB' @Dc (applyDcB'' @a) c s a b)
    applyDcB' c s a@(a_id, EndInfNode ac) b@(b_id, EndInfNode bc) = withCache c (a, b, (s ++ "Dc")) $
        endinf_case @a c s a_id b_id ac bc

    applyDcB' c s a@(a_id, Node positionA pos_childA neg_childA)  b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB =
            let c_ = traverse_dc @a "pos child" c pos_childA pos_childB
                (c', (pos_result, _)) = applyDcB @a c_ s pos_childA pos_childB

                c_' = traverse_dc @a "neg child" (reset_stack_bin c' c) neg_childA neg_childB
                (c'', (neg_result, _)) = applyDcB @a c_' s neg_childA neg_childB
            in withCache c (a, b, (s ++ "Dc")) $ applyElimRule @a (reset_stack_bin c'' c) (Node positionA pos_result neg_result)
        | positionA < positionB = uncurry (applyElimRule @a) (inferNodeB' @Dc (applyDcB'' @a) c s a b)
        | positionA > positionB = uncurry (applyElimRule @a) (inferNodeA' @a (applyDcB'' @a) c s a b)

    applyDcB' c s a@(a_id, InfNodes positionA _ _ _) b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB = withCache c (a, b, (s ++ "Dc")) $
                uncurry (applyElimRule @a) (inferNodeA' @a (applyDcB'' @a) c s a b)
    applyDcB' c s a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA < positionB = withCache c (a, b, (s ++ "Dc")) $
                uncurry (applyElimRule @a) (inferNodeB' @Dc (applyDcB'' @a) c s a b)
    applyDcB' c s a@(a_id, InfNodes positionA _ _ _)  b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = applyInf @a c s a b
        | positionA < positionB = applyInfB @Dc c s a b
        | positionA > positionB = applyInfA @a c s a b
    applyDcB' c s a@(a_id, EndInfNode _) b@(b_id, InfNodes{}) = withCache c (a, b, (s ++ "Dc")) $ applyInfA @a c s a b
    applyDcB' c s a@(a_id, InfNodes{}) b@(b_id, EndInfNode _) = withCache c (a, b, (s ++ "Dc")) $ applyInfB @Dc c s a b

    dcB_leaf_cases c s a@(_, Leaf _) b@(_, Node{}) = withCache c (a, b, s ++ "Dc") $ uncurry (applyElimRule @a) (inferNodeA' @a (applyDcB'' @a) c s a b )
    dcB_leaf_cases c s a@(_, Node{}) b@(_, Leaf _) = withCache c (a, b, s ++ "Dc") $ uncurry (applyElimRule @a) (inferNodeB' @Dc (applyDcB'' @a) c s a b)
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
        applyInfB @Dc c s a b

    dcB_leaf_cases c s a@(_, Unknown) b = (c, a)
    dcB_leaf_cases c s a b@(_, Unknown) =
        let (c', dcB) = pop_dcB'' c
        in applyDcB'' @a c' s a dcB
    dcB_leaf_cases c "union" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then absorb (c, a) else absorb (c, b)
    dcB_leaf_cases c "inter" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then absorb (c, b) else absorb (c, a)

-- | ======================== DcA versions (Argument A is DC type) ========================

    applyDcA c s a b = applyDcA' @a c s (getNode c a) (getNode c b)
    applyDcA'' c s a b = applyDcA' @a c s a b

    applyDcA' c s a@(_, Leaf _) b = dcA_leaf_cases @a c s a b
    applyDcA' c s a b@(_, Leaf _) = dcA_leaf_cases @a c s a b
    applyDcA' c s a@(_, Unknown) b = dcA_leaf_cases @a c s a b
    applyDcA' c s a b@(_, Unknown) = dcA_leaf_cases @a c s a b

    applyDcA' c s a@(a_id, EndInfNode _) b@(b_id, Node idx _ _) = withCache c (a, b, (s ++ "Dc")) $ uncurry (applyElimRule @a) (inferNodeA' @Dc (applyDcA'' @a) c s a b)
    applyDcA' c s a@(a_id, Node{}) b@(b_id, EndInfNode _) = withCache c (a, b, (s ++ "Dc")) $ uncurry (applyElimRule @a) (inferNodeB' @a (applyDcA'' @a) c s a b)
    applyDcA' c s a@(a_id, EndInfNode ac) b@(b_id, EndInfNode bc) = withCache c (a, b, (s ++ "Dc")) $
        endinf_case @a c s a_id b_id ac bc

    applyDcA' c s a@(a_id, Node positionA pos_childA neg_childA)  b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB =
            let c_ = traverse_dc @a "pos child" c pos_childA pos_childB
                (c', (pos_result, _)) = applyDcA @a c_ s pos_childA pos_childB

                c_' = traverse_dc @a "neg child" (reset_stack_bin c' c) neg_childA neg_childB
                (c'', (neg_result, _)) = applyDcA @a c_' s neg_childA neg_childB
            in withCache c (a, b, (s ++ "Dc")) $ applyElimRule @a (reset_stack_bin c'' c) (Node positionA pos_result neg_result)
        | positionA < positionB = uncurry (applyElimRule @a) (inferNodeB' @a (applyDcA'' @a) c s a b)
        | positionA > positionB = uncurry (applyElimRule @a) (inferNodeA' @Dc (applyDcA'' @a) c s a b)

    applyDcA' c s a@(a_id, InfNodes positionA _ _ _) b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB = withCache c (a, b, (s ++ "Dc")) $
                uncurry (applyElimRule @a) (inferNodeA' @Dc (applyDcA'' @a) c s a b)
    applyDcA' c s a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA < positionB = withCache c (a, b, (s ++ "Dc")) $
                uncurry (applyElimRule @a) (inferNodeB' @a (applyDcA'' @a) c s a b)
    applyDcA' c s a@(a_id, InfNodes positionA _ _ _)  b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = applyInf @a c s a b
        | positionA < positionB = applyInfB @a c s a b
        | positionA > positionB = applyInfA @Dc c s a b
    applyDcA' c s a@(a_id, EndInfNode _) b@(b_id, InfNodes{}) = withCache c (a, b, (s ++ "Dc")) $ applyInfA @Dc c s a b
    applyDcA' c s a@(a_id, InfNodes{}) b@(b_id, EndInfNode _) = withCache c (a, b, (s ++ "Dc")) $ applyInfB @a c s a b

    dcA_leaf_cases c s a@(_, Leaf _) b@(_, Node{}) = withCache c (a, b, s ++ "Dc") $ uncurry (applyElimRule @a) (inferNodeA' @Dc (applyDcA'' @a) c s a b )
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
        applyInfA @Dc c s a b
    dcA_leaf_cases c s a@(a_id, InfNodes {}) b@(b_id, Leaf _) = withCache c (a, b, s ++ "Dc") $
        applyInfB @a c s a b

    dcA_leaf_cases c s a@(_, Unknown) b =
        let (c', dcA) = pop_dcA'' c
        in applyDcA'' @a c' s dcA b
    dcA_leaf_cases c s a b@(_, Unknown) = (c, b)
    dcA_leaf_cases c "union" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then absorb (c, a) else absorb (c, b)
    dcA_leaf_cases c "inter" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then absorb (c, b) else absorb (c, a)

    -- Case logic for EndInfNode encountered during binary operations
    endinf_case c s a_id b_id ac bc = let
        (c_, (infA, infB)) = pop_stack' c
        c' = traverse_dc @a "endinf" c_ a_id b_id
        (c'', (r, _)) = case (infA, infB) of
            (Dc, Dc) -> apply @Dc c' s ac bc
            (Neg, Neg) -> apply @Neg c' s ac bc
            (Pos, Pos) -> apply @Pos c' s ac bc
            (Neg, Dc) -> applyDcB @Neg c' s ac bc
            (Pos, Dc) -> applyDcB @Pos c' s ac bc
            (Dc, Neg) -> applyDcA @Neg c' s ac bc
            (Dc, Pos) -> applyDcA @Pos c' s ac bc
            r'@(_, _) -> error ("weird combination after pop stack: " ++ show r')
        in absorb $ applyElimRule @a (reset_stack_bin c'' c) (EndInfNode r)

-- | ======================== InfNode Application Logic ========================

applyInf :: forall a. (Dd1 a, DdF3 a, Dd1_helper a) => BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node)
applyInf c s a@(a_id, InfNodes positionA dcA pA nA) b@(b_id, InfNodes positionB dcB pB nB)
    | positionA == positionB =
        let
            -- Context update for descending into the class hierarchy
            c_ = add_to_stack (positionA, Dc) (((0, 0), Unknown), ((0, 0), Unknown), ((0, 0), Unknown)) c
            (c1, dcR) = apply @Dc (traverse_dc @a "inf dc" c_ dcA dcB) s dcA dcB

            -- Negative branch application
            c2_ = add_to_stack (positionA, Neg) (getNode c1 dcA, getNode c1 dcB, dcR) (reset_stack_bin c1 c)
            (c2, nR) = apply @Neg (traverse_dc @a "inf neg" c2_ nA nB) s nA nB

            -- Positive branch application
            c3_ = add_to_stack (positionA, Pos) (getNode c1 dcA, getNode c1 dcB, dcR) (reset_stack_bin c2 c)
            (c3, pR) = apply @Pos (traverse_dc @a "inf pos" c3_ pA pB) s pA pB

            c4 = reset_stack_bin c3 c
        in applyElimRule @a c4 $ InfNodes positionA (fst dcR) (fst pR) (fst nR)
    | positionA > positionB = applyInfA @a c s a b
    | positionA < positionB = applyInfB @a c s a b
applyInf c s a@(_, InfNodes {}) b@(_, Leaf _) = applyInfB @a c s a b
applyInf c s a@(_, InfNodes {}) b@(_, EndInfNode _) = applyInfB @a c s a b
applyInf c s a@(_, Leaf _) b@(_, InfNodes{}) = applyInfA @a c s a b
applyInf c s a@(_, EndInfNode _) b@(_, InfNodes{}) = applyInfA @a c s a b
applyInf c s a b = error ("apply inf error: " ++ s)

applyInfA :: forall a. (Dd1 a, DdF3 a, Dd1_helper a) => BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node)
applyInfA c s a@(a_id, _) b@(_, InfNodes positionB _ _ _) = let
        (c', (r_id, _)) = applyElimRule @a c (EndInfNode a_id)
        (c'', r') = insert c' $ InfNodes positionB r_id (0,0) (0,0)
    in applyInf @a c'' s r' b

applyInfB :: forall a. (Dd1 a, DdF3 a, Dd1_helper a) => BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node)
applyInfB c s a@(_, InfNodes positionA _ _ _) b@(b_id, _) = let
        (c', (r_id, _)) = applyElimRule @a c (EndInfNode b_id)
        (c'', r') = insert c' $ InfNodes positionA (0,0) (0,0) r_id
    in applyInf @a c'' s a r'

-- | Helper wrapper for inferred node recursive calls
inferNodeA' :: forall a. DdF3 a => (BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node))
            -> BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Dd)
inferNodeA' f c s a b = inferNodeA @a f c s a b

inferNodeB' :: forall a. DdF3 a => (BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node))
            -> BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Dd)
inferNodeB' f c s a b = inferNodeB @a f c s a b