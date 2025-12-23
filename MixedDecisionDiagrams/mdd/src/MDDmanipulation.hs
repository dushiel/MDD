{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes, KindSignatures #-}
{-# HLINT ignore "Use notElem" #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# HLINT ignore "Eta reduce" #-}
{-# HLINT ignore "Move brackets to avoid $" #-}
{-# HLINT ignore "Use guards" #-}
{-# LANGUAGE MultiWayIf #-}

module SODDmanipulation where
-- future : explore {-# UNPACK #-} !Int
--SPECIALIZE pragma
import MDD
import MDD (Dd)
import SupportMDD
import Data.Kind


import DrawMDD (debug_manipulation, debug_dc_traverse)
import Data.Bimap ()
import Debug.Trace (trace)

type DdManipulation = BinaryOperatorContext -> Node -> Node -> (BinaryOperatorContext, Node)
type DdManipulation' = BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node)


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
negation' c (_, Leaf b) = (c, leaf $ not b)
negation' c u@(_, Unknown) = (c, u)



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



instance (DdF3 a) => Dd1 a where
    apply c s a b = debug_manipulation  (apply' @a c s (getNode c a) (getNode c b)) s (s ++ to_str @a) c (getNode c a) (getNode c b)
    apply'' c s a b = debug_manipulation  (apply' @a c s a b) s (s ++ "==" ++ to_str @a) c a b

    apply' c s a@(_, Leaf _) b = leaf_cases @a c s a b
    apply' c s a b@(_, Leaf _) = leaf_cases @a c s a b
    apply' c s a@(_, Unknown) b = leaf_cases @a c s a b
    apply' c s a b@(_, Unknown) = leaf_cases @a c s a b

    apply' c s a@(a_id, EndInfNode _) b@(b_id, Node idx _ _) = withCache c (a, b, s) $ applyElimRule' @a (inferNodeA' @a (apply'' @a) c s a b)
    apply' c s a@(a_id, Node{}) b@(b_id, EndInfNode _) = withCache c (a, b, s) $ applyElimRule' @a (inferNodeB' @a (apply'' @a) c s a b)
    apply' c s a@(a_id, EndInfNode ac) b@(b_id, EndInfNode bc) = withCache c (a, b, s) $
        endinf_case @a c s a_id b_id ac bc

    apply' c s a@(a_id, Node positionA pos_childA neg_childA)  b@(b_id, Node positionB pos_childB neg_childB)
        -- Match
        | positionA == positionB =
            let c_ = traverse_dc @a "pos child" c pos_childA pos_childB
                (c', (pos_result, _)) = apply @a c_ s pos_childA pos_childB

                c_' = traverse_dc @a "neg child" (reset_stack c' c) neg_childA neg_childB
                (c'', (neg_result, _)) = apply @a c_' s neg_childA neg_childB
            in withCache c (a, b, s) $ applyElimRule @a (reset_stack c'' c) (Node positionA pos_result neg_result) --`debug` ("apply noide node = " ++ show (Node positionA pos_result neg_result) ++ " .... " ++ show positionA ++ "\n for type elim " ++ to_str @a ++ " ,  elimed: " ++ show (snd $ applyElimRule @a (reset_stack c'' c) (Node positionA pos_result neg_result)))
        -- Mismatch, highest position gets an inferred node at position of the lowest
        | positionA < positionB = applyElimRule' @a (inferNodeB' @a (apply'' @a) c s a b)
        | positionA > positionB = applyElimRule' @a (inferNodeA' @a (apply'' @a) c s a b)

    -- -- entering new domains
    apply' c s a@(a_id, InfNodes positionA _ _ _) b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB = withCache c (a, b, s) $
                applyElimRule' @a (inferNodeA' @a (apply'' @a) c s a b)
        | positionA < positionB = withCache c (a, b, s) $
                absorb $ applyInfB @a c s a b
    apply' c s a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB = withCache c (a, b, s) $
                absorb $ applyInfA @a c s a b
        | positionA < positionB = withCache c (a, b, s) $
                applyElimRule' @a (inferNodeB' @a (apply'' @a) c s a b)
    apply' c s a@(a_id, InfNodes positionA _ _ _)  b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = withCache c (a, b, s) $ absorb $ applyInf @a c s a b
        | positionA < positionB = withCache c (a, b, s) $ absorb $ applyInfB @a c s a b
        | positionA > positionB = withCache c (a, b, s) $ absorb $ applyInfA @a c s a b
    apply' c s a@(a_id, EndInfNode _) b@(b_id, InfNodes{}) = withCache c (a, b, s) $ absorb $ applyInfA @a c s a b
    apply' c s a@(a_id, InfNodes{}) b@(b_id, EndInfNode _) = withCache c (a, b, s) $ absorb $ applyInfB @a c s a b

    -- union node cases
    leaf_cases c s a@(_, Leaf _) b@(_, Node{}) = withCache c (a, b, s) $ applyElimRule' @a (inferNodeA' @a (apply'' @a) c s a b)
    leaf_cases c s a@(_, Node{}) b@(_, Leaf _) = withCache c (a, b, s) $ applyElimRule' @a (inferNodeB' @a (apply'' @a) c s a b )
    -- add endinfnode
    leaf_cases c s a@(a_id, Leaf True) b@(b_id, EndInfNode bc) = withCache c (a, b, s) $
        endinf_case @a c s a_id b_id (1,0) bc
    leaf_cases c s a@(a_id, EndInfNode ac) b@(b_id, Leaf True) = withCache c (a, b, s) $
        endinf_case @a c s a_id b_id ac (1,0)
    leaf_cases c s a@(a_id, Leaf False) b@(b_id, EndInfNode bc) = withCache c (a, b, s) $
        endinf_case @a c s a_id b_id (2,0) bc
    leaf_cases c s a@(a_id, EndInfNode ac) b@(b_id, Leaf False) = withCache c (a, b, s) $
        endinf_case @a c s a_id b_id ac (2,0)
    -- add infnode
    leaf_cases c s a@(a_id, Leaf _) b@(b_id, InfNodes{}) = withCache c (a, b, s) $
        applyInfA @a c s a b -- todo: by going in here we are "forgetting" we are processing a Dc at the moment, so when we pop back we need to continue with unionDc
    leaf_cases c s a@(a_id, InfNodes {}) b@(b_id, Leaf _) = withCache c (a, b, s) $
        applyInfB @a c s a b

    leaf_cases c s a@(_, Unknown) b@(_, Unknown) = (c , a)
    leaf_cases c s a@(_, Unknown) b = -- resolve Unknown to see if it is a True or False or a dd, then do the above or continue with the dd
        let (c', dcA) = pop_dcA' c -- `debug` "dca dc"
        in applyDcA'' @a c' s dcA b   -- `debug` ("using dcA to replace Unknown : " ++ show dcA)
    leaf_cases c s a b@(_, Unknown) =
        let (c', dcB) = pop_dcB' c -- `debug` "dcb dc"
        in applyDcB'' @a c' s a dcB  -- `debug` ("using dcB to replace Unknown : " ++ show dcB)
    --  Unknown is stronger than True in finite + union context
    leaf_cases c "union" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then absorb (c, a) else absorb (c, b) -- True might be absorbed, then return Unknown
    leaf_cases c "inter" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then absorb (c, b) else absorb (c, a) -- True might be absorbed, then return Unknown
    leaf_cases c s a b = error ("leaf case: " ++ s)



-- | ======================== DC versions ========================
    -- b is of dc type

    applyDcB c s a b = debug_manipulation  (applyDcB' @a c s (getNode c a) (getNode c b)) s (s ++ "DcB " ++ to_str @a) c (getNode c a) (getNode c b)
    applyDcB'' c s a b = debug_manipulation  (applyDcB' @a c s a b) s (s ++ "DcB ==" ++ to_str @a) c a b

    applyDcB' c s a@(_, Leaf _) b = dcB_leaf_cases @a c s a b
    applyDcB' c s a b@(_, Leaf _) = dcB_leaf_cases @a c s a b
    applyDcB' c s a@(_, Unknown) b = dcB_leaf_cases @a c s a b
    applyDcB' c s a b@(_, Unknown) = dcB_leaf_cases @a c s a b

    applyDcB' c s a@(a_id, EndInfNode _) b@(b_id, Node idx _ _) = withCache c (a, b, (s ++ "Dc")) $ applyElimRule' @a (inferNodeA' @a (applyDcB'' @a) c s a b)
    applyDcB' c s a@(a_id, Node{}) b@(b_id, EndInfNode _) = withCache c (a, b, (s ++ "Dc")) $ applyElimRule' @a (inferNodeB' @Dc (applyDcB'' @a) c s a b)
    applyDcB' c s a@(a_id, EndInfNode ac) b@(b_id, EndInfNode bc) = withCache c (a, b, (s ++ "Dc")) $
        endinf_case @a c s a_id b_id ac bc

    applyDcB' c s a@(a_id, Node positionA pos_childA neg_childA)  b@(b_id, Node positionB pos_childB neg_childB)
        -- Match
        | positionA == positionB =
            let c_ = traverse_dc @a "pos child" c pos_childA pos_childB
                (c', (pos_result, _)) = applyDcB @a c_ s pos_childA pos_childB

                c_' = traverse_dc @a "neg child" (reset_stack c' c) neg_childA neg_childB
                (c'', (neg_result, _)) = applyDcB @a c_' s neg_childA neg_childB
            in withCache c (a, b, (s ++ "Dc")) $ applyElimRule @a (reset_stack c'' c) (Node positionA pos_result neg_result)
        -- Mismatch, highest position gets an inferred node at position of the lowest
        | positionA < positionB = applyElimRule' @a (inferNodeB' @Dc (applyDcB'' @a) c s a b)
        | positionA > positionB = applyElimRule' @a (inferNodeA' @a (applyDcB'' @a) c s a b)

    -- -- entering new domains
    applyDcB' c s a@(a_id, InfNodes positionA _ _ _) b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB = withCache c (a, b, (s ++ "Dc")) $
                applyElimRule' @a (inferNodeA' @a (applyDcB'' @a) c s a b)
        -- | positionA < positionB = withCache c (a, b, (s ++ "Dc")) $
        --         applyElimRule @a $ applyInfB a b
    applyDcB' c s a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
    --     | positionA > positionB = withCache c (a, b, (s ++ "Dc")) $
    --             applyElimRule @a $ applyInfA a b
        | positionA < positionB = withCache c (a, b, (s ++ "Dc")) $
                applyElimRule' @a (inferNodeB' @Dc (applyDcB'' @a) c s a b)
    applyDcB' c s a@(a_id, InfNodes positionA _ _ _)  b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = applyInf @a c s a b
        | positionA < positionB = applyInfB @Dc c s a b
        | positionA > positionB = applyInfA @a c s a b
    applyDcB' c s a@(a_id, EndInfNode _) b@(b_id, InfNodes{}) = withCache c (a, b, (s ++ "Dc")) $ applyInfA @a c s a b
    applyDcB' c s a@(a_id, InfNodes{}) b@(b_id, EndInfNode _) = withCache c (a, b, (s ++ "Dc")) $ applyInfB @Dc c s a b

    -- infer node cases
    dcB_leaf_cases c s a@(_, Leaf _) b@(_, Node{}) = withCache c (a, b, s ++ "Dc") $ applyElimRule' @a (inferNodeA' @a (applyDcB'' @a) c s a b )
    dcB_leaf_cases c s a@(_, Node{}) b@(_, Leaf _) = withCache c (a, b, s ++ "Dc") $ applyElimRule' @a (inferNodeB' @Dc (applyDcB'' @a) c s a b)
    -- endinfnode
    -- perform original apply again since we are going out of the Dc environment
    -- todo: even if we do double substitution?? probably not
    dcB_leaf_cases c s a@(a_id, Leaf True) b@(b_id, EndInfNode bc) = withCache c (a, b, s ++ "Dc") $
        endinf_case @a c s a_id b_id (1,0) bc
    dcB_leaf_cases c s a@(a_id, EndInfNode ac) b@(b_id, Leaf True) = withCache c (a, b, s ++ "Dc") $
        endinf_case @a c s a_id b_id ac (1,0)
    dcB_leaf_cases c s a@(a_id, Leaf False) b@(b_id, EndInfNode bc) = withCache c (a, b, s ++ "Dc") $
        endinf_case @a c s a_id b_id (2,0) bc
    dcB_leaf_cases c s a@(a_id, EndInfNode ac) b@(b_id, Leaf False) = withCache c (a, b, s ++ "Dc") $
        endinf_case @a c s a_id b_id ac (2,0)
    -- add infnode
    dcB_leaf_cases c s a@(a_id, Leaf _) b@(b_id, InfNodes{}) = withCache c (a, b, s ++ "Dc") $
        applyInfA @a c s a b -- todo: by going in here we are "forgetting" we are processing a Dc at the moment, so when we pop back we need to continue with interDc
    dcB_leaf_cases c s a@(a_id, InfNodes {}) b@(b_id, Leaf _) = withCache c (a, b, s ++ "Dc") $
        applyInfB @Dc c s a b

    --  Unknown is stronger than True in finite + intersectionDc context
    dcB_leaf_cases c s a@(_, Unknown) b = (c, a) -- when having to replace a Unknown when already in a Dc traversal we will be comparing a DcA branch with a DcB branch.. which has already been calculated in dcR, therefor we known for sure it will be absorbed by dcR
    dcB_leaf_cases c s a b@(_, Unknown) =
        let (c', dcB) = pop_dcB'' c --`debug` "dcb pop"
        in applyDcB'' @a c' s a dcB -- unknown on dc side means that it should be replaced with a dc from an outer level
    -- if the result is
    dcB_leaf_cases c "union" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then absorb (c, a) else absorb (c, b) -- True might be absorbed, then return Unknown
    dcB_leaf_cases c "inter" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then absorb (c, b) else absorb (c, a) -- True might be absorbed, then return Unknown

-- | ======================== DcA versions (Arguments switched) ========================
    ---
     -- a is of dc type

    applyDcA c s a b = debug_manipulation  (applyDcA' @a c s (getNode c a) (getNode c b)) s (s ++ "DcA " ++ to_str @a) c (getNode c a) (getNode c b)
    applyDcA'' c s a b = debug_manipulation  (applyDcA' @a c s a b) s (s ++ "DcA ==" ++ to_str @a) c a b

    applyDcA' c s a@(_, Leaf _) b = dcA_leaf_cases @a c s a b
    applyDcA' c s a b@(_, Leaf _) = dcA_leaf_cases @a c s a b
    applyDcA' c s a@(_, Unknown) b = dcA_leaf_cases @a c s a b
    applyDcA' c s a b@(_, Unknown) = dcA_leaf_cases @a c s a b

    applyDcA' c s a@(a_id, EndInfNode _) b@(b_id, Node idx _ _) = withCache c (a, b, (s ++ "Dc")) $ applyElimRule' @a (inferNodeA' @Dc (applyDcA'' @a) c s a b)
    applyDcA' c s a@(a_id, Node{}) b@(b_id, EndInfNode _) = withCache c (a, b, (s ++ "Dc")) $ applyElimRule' @a (inferNodeB' @a (applyDcA'' @a) c s a b)
    applyDcA' c s a@(a_id, EndInfNode ac) b@(b_id, EndInfNode bc) = withCache c (a, b, (s ++ "Dc")) $
        endinf_case @a c s a_id b_id ac bc

    applyDcA' c s a@(a_id, Node positionA pos_childA neg_childA)  b@(b_id, Node positionB pos_childB neg_childB)
        -- Match
        | positionA == positionB =
            let c_ = traverse_dc @a "pos child" c pos_childA pos_childB
                (c', (pos_result, _)) = applyDcA @a c_ s pos_childA pos_childB

                c_' = traverse_dc @a "neg child" (reset_stack c' c) neg_childA neg_childB
                (c'', (neg_result, _)) = applyDcA @a c_' s neg_childA neg_childB
            in withCache c (a, b, (s ++ "Dc")) $ applyElimRule @a (reset_stack c'' c) (Node positionA pos_result neg_result)
        -- Mismatch, highest position gets an inferred node at position of the lowest
        | positionA < positionB = applyElimRule' @a (inferNodeB' @a (applyDcA'' @a) c s a b)
        | positionA > positionB = applyElimRule' @a (inferNodeA' @Dc (applyDcA'' @a) c s a b)

    -- -- entering new domains
    applyDcA' c s a@(a_id, InfNodes positionA _ _ _) b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB = withCache c (a, b, (s ++ "Dc")) $
                applyElimRule' @a (inferNodeA' @Dc (applyDcA'' @a) c s a b)
        -- | positionA < positionB = withCache c (a, b, (s ++ "Dc")) $
        --         applyElimRule @a $ applyInfB a b
    applyDcA' c s a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
    --     | positionA > positionB = withCache c (a, b, (s ++ "Dc")) $
    --             applyElimRule @a $ applyInfA a b
        | positionA < positionB = withCache c (a, b, (s ++ "Dc")) $
                applyElimRule' @a (inferNodeB' @a (applyDcA'' @a) c s a b)
    applyDcA' c s a@(a_id, InfNodes positionA _ _ _)  b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = applyInf @a c s a b
        | positionA < positionB = applyInfB @a c s a b
        | positionA > positionB = applyInfA @Dc c s a b
    applyDcA' c s a@(a_id, EndInfNode _) b@(b_id, InfNodes{}) = withCache c (a, b, (s ++ "Dc")) $ applyInfA @Dc c s a b
    applyDcA' c s a@(a_id, InfNodes{}) b@(b_id, EndInfNode _) = withCache c (a, b, (s ++ "Dc")) $ applyInfB @a c s a b

    -- infer node cases
    dcA_leaf_cases c s a@(_, Leaf _) b@(_, Node{}) = withCache c (a, b, s ++ "Dc") $ applyElimRule' @a (inferNodeA' @Dc (applyDcA'' @a) c s a b )
    dcA_leaf_cases c s a@(_, Node{}) b@(_, Leaf _) = withCache c (a, b, s ++ "Dc") $ applyElimRule' @a (inferNodeB' @a (applyDcA'' @a) c s a b)
    -- endinfnode
    -- perform original apply again since we are going out of the Dc environment
    -- todo: even if we do double substitution?? probably not
    dcA_leaf_cases c s a@(a_id, Leaf True) b@(b_id, EndInfNode bc) = withCache c (a, b, s ++ "Dc") $
        endinf_case @a c s a_id b_id (1,0) bc
    dcA_leaf_cases c s a@(a_id, EndInfNode ac) b@(b_id, Leaf True) = withCache c (a, b, s ++ "Dc") $
        endinf_case @a c s a_id b_id ac (1,0)
    dcA_leaf_cases c s a@(a_id, Leaf False) b@(b_id, EndInfNode bc) = withCache c (a, b, s ++ "Dc") $
        endinf_case @a c s a_id b_id (2,0) bc
    dcA_leaf_cases c s a@(a_id, EndInfNode ac) b@(b_id, Leaf False) = withCache c (a, b, s ++ "Dc") $
        endinf_case @a c s a_id b_id ac (2,0)
    -- add infnode
    dcA_leaf_cases c s a@(a_id, Leaf _) b@(b_id, InfNodes{}) = withCache c (a, b, s ++ "Dc") $
        applyInfA @Dc c s a b -- todo: by going in here we are "forgetting" we are processing a Dc at the moment, so when we pop back we need to continue with interDc
    dcA_leaf_cases c s a@(a_id, InfNodes {}) b@(b_id, Leaf _) = withCache c (a, b, s ++ "Dc") $
        applyInfB @a c s a b

    --  Unknown is stronger than True in finite + intersectionDcA context
    dcA_leaf_cases c s a@(_, Unknown) b =
        let (c', dcA) = pop_dcA'' c --`debug` "dca pop"
        in applyDcA'' @a c' s dcA b -- unknown on dc side means that it should be replaced with a dc from an outer level
    dcA_leaf_cases c s a b@(_, Unknown) = (c, b)
    -- if the result is
    dcA_leaf_cases c "union" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then absorb (c, a) else absorb (c, b)
    dcA_leaf_cases c "inter" a@(_, Leaf boolA) b@(_, Leaf boolB) = if boolA then absorb (c, b) else absorb (c, a)
    endinf_case c s a_id b_id ac bc = let
        (c_, (infA, infB)) = pop_stack' c
        c' = traverse_dc @a "endinf" c_ a_id b_id -- `debug` (show $ dc_stack c_)
        (c'', (r, _)) = case (infA, infB) of
            (Dc, Dc) -> apply @Dc c' s ac bc --`debug` ("dc ")
            (Neg, Neg) -> apply @Neg c' s ac bc `debug` ("neg ")
            (Pos, Pos) -> apply @Pos c' s ac bc `debug` ("pos ")
            (Neg, Dc) -> applyDcB @Neg c' s ac bc `debug` ("neg dc")
            (Pos, Dc) -> applyDcB @Pos c' s ac bc `debug` ("pos dc")
            (Dc, Neg) -> applyDcA @Neg c' s ac bc `debug` ("dc neg ")
            (Dc, Pos) -> applyDcA @Pos c' s ac bc `debug` ("dc pos ")
            r'@(_, _) -> error ("weird combination after pop stack: " ++ show r')
        in absorb $ applyElimRule' @a $ (reset_stack c'' c, EndInfNode r) -- todo remove reset stack by removing stack in leaf cases on other places




type DdF3 :: Inf -> Constraint
type Dd1 :: Inf -> Constraint

class DdF3 a where
    inferNodeA :: DdManipulation -> BinaryOperatorContext -> Node -> Node -> (BinaryOperatorContext, Dd)
    inferNodeB :: DdManipulation -> BinaryOperatorContext -> Node -> Node -> (BinaryOperatorContext, Dd)
    inferNodeB' :: DdManipulation' -> BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Dd)
    inferNodeA' :: DdManipulation' -> BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Dd)
    applyElimRule :: BinaryOperatorContext -> Dd -> (BinaryOperatorContext, Node)
    applyElimRule' :: (BinaryOperatorContext, Dd) -> (BinaryOperatorContext, Node)
    applyInfA :: BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node)
    applyInfB :: BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node)
    to_str :: String
    catchup :: (HasNodeLookup c) => String -> c -> Node -> Int -> Node

    inferNode :: (HasNodeLookup c) => c -> Int -> Node -> (c, Node)
    inferInfNode :: (HasNodeLookup c) => c -> Int -> Node -> (c, Node)


instance DdF3 Dc where
    inferNodeA f c a (b_id, b@(Node positionB pos_childB neg_childB)) =
        let (c', (pos_result, _)) = f c a (getNode c pos_childB)
            (c'', (neg_result, _)) = f c' a (getNode c neg_childB)
        in (c'', ( Node positionB pos_result neg_result))
    inferNodeB f c (a_id, Node positionA pos_childA neg_childA) b =
        let (c', (pos_result, _)) = f c (getNode c pos_childA) b
            (c'', (neg_result, _)) = f c' (getNode c neg_childA) b
        in (c'', ( Node positionA pos_result neg_result))

    inferNodeA' f c s a (b_id, b@(Node positionB pos_childB neg_childB)) =
        let (c', (pos_result, _)) = f c s a (getNode c pos_childB)
            (c'', (neg_result, _)) = f c' s a (getNode c neg_childB)
        in (c'', ( Node positionB pos_result neg_result))
    inferNodeB' f c s (a_id, Node positionA pos_childA neg_childA) b =
        let (c', (pos_result, _)) = f c s (getNode c pos_childA) b
            (c'', (neg_result, _)) = f c' s (getNode c neg_childA) b
        in (c'', ( Node positionA pos_result neg_result))

    applyElimRule c (InfNodes _ (1,0) (0,0) (0,0)) = (c, ((1,0), Leaf True))
    applyElimRule c (InfNodes _ (2,0) (0,0) (0,0)) = (c, ((2,0), Leaf False))
    applyElimRule c (InfNodes _ (0,0) (0,0) (0,0)) = (c, ((0,0), Unknown))
    applyElimRule c d@(Node _ p n) = if p == n then (c, getNode c p) else insert c d
    applyElimRule c d@(InfNodes _ consq (0,0) (0,0)) = case getDd c consq of
        EndInfNode d' -> (c, getNode c d')
        _ -> applyElimRule_general c d
    applyElimRule c d = applyElimRule_general c d

    applyElimRule' (c, d@(Node _ p n)) = if p == n then (c, getNode c p) else insert c d
    applyElimRule' (c, d@(InfNodes _ consq (0,0) (0,0))) = case getDd c consq of
        EndInfNode d' -> (c, getNode c d')
        _ -> applyElimRule_general c d
    applyElimRule' (c, d) = applyElimRule'_general (c, d)

    applyInfA c s a@(a_id, _) b@(_, InfNodes positionB _ _ _) = let
            (c', (r_id, _)) = applyElimRule @Dc c (EndInfNode  a_id)
            (c'', r') = insert c' $ InfNodes positionB r_id (0,0) (0,0)
        in applyInf @Dc c'' s r' b
    applyInfB c s a@(_, InfNodes positionA _ _ _) b@(b_id, _) = let
            (c', (r_id, _)) = applyElimRule @Dc c $ EndInfNode b_id
            (c'', r') = insert c' $ InfNodes positionA r_id (0,0) (0,0)
        in applyInf @Dc c'' s a r'

    inferNode c position (n_id, n) = insert c (Node position n_id n_id)
    inferInfNode c position (n_id, n) = insert c $ InfNodes position n_id (0,0) (0,0)
    -- i think we can implement a "do nothing" version of catchup for Dc
    catchup s c n _ = n

    to_str = "Dc"

instance DdF3 Pos where
    inferNodeA f c a@(a_id, _) b@(b_id, Node positionB pos_childB neg_childB) =
        let
            (c', r) = insert c (Node positionB a_id (0,0))
            (c'', r'@(r_id, r_dd)) = f c' r b
        in (c'', r_dd)
    inferNodeB f c a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, _) =
        let
            (c', r) = insert c (Node positionA b_id (0,0))
            (c'', r'@(r_id, r_dd)) = f c' a r
        in (c'', r_dd)

    inferNodeA' f c s a@(a_id, _) b@(b_id, Node positionB pos_childB neg_childB) =
        let
            (c', r) = insert c (Node positionB a_id (0,0))
            (c'', r'@(r_id, r_dd)) = f c' s r b
        in (c'', r_dd)
    inferNodeB' f c s a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, _) =
        let
            (c', r) = insert c (Node positionA b_id (0,0))
            (c'', r'@(r_id, r_dd)) = f c' s a r
        in (c'', r_dd)

    applyElimRule c (InfNodes _ (0,0) (1,0) (0,0)) = (c, ((1,0), Leaf True))
    applyElimRule c (InfNodes _ (0,0) (2,0) (0,0)) = (c, ((2,0), Leaf False))
    applyElimRule c (InfNodes _ (0,0) (0,0) (0,0)) = (c, ((0,0), Unknown))
    applyElimRule c d@(Node _ posC (0, 0)) = (c, getNode c posC)
    applyElimRule c d = applyElimRule_general c d

    applyElimRule' (c, d@(Node _ posC (0, 0))) = (c, getNode c posC)
    applyElimRule' (c, d) = applyElimRule'_general (c, d)

    applyInfA c s a@(a_id, _) b@(_, InfNodes positionB _ _ _) = let
            (c', (r_id, _)) = applyElimRule @Pos c $ EndInfNode  a_id
            (c'', r') = insert c' $ InfNodes positionB (0,0) r_id (0,0)
        in applyInf @Pos c'' s r' b
    applyInfB c s a@(_, InfNodes positionA _ _ _) b@(b_id, _) = let
            (c', (r_id, _)) = applyElimRule @Pos c $ EndInfNode b_id
            (c'', r') = insert c' $ InfNodes positionA (0,0) r_id (0,0)
        in applyInf @Pos c'' s a r'

    inferNode c position (n_id, n) = insert c (Node position n_id (0,0))
    inferInfNode c position (n_id, n) = insert c $ InfNodes position (0,0) n_id (0,0)

    catchup s c n@(_, Node positionA pos_child _) idx
        -- special case to go until the end
        | idx == -1 = catchup @Pos s c (move_dc c s n ) idx
        -- catchup
        | idx > positionA = catchup @Pos s c (move_dc c s n ) idx
        -- ending criteria
        | idx < positionA = n
        | idx == positionA = n
    -- todo case infnode
    -- in case of leaf, endinfnode
    catchup s c n idx = n
    -- unknown should not be possible

    to_str = "Pos"

instance DdF3 Neg where
    inferNodeA f c a@(a_id, _) b@(b_id, Node positionB pos_childB neg_childB) =
        let
            (c', r) = insert c (Node positionB (0,0) a_id)
            (c'', r'@(r_id, r_dd)) = f c' r b
        in (c'', r_dd)
    inferNodeB f c a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, _) =
        let
            (c', r) = insert c (Node positionA (0,0) b_id)
            (c'', r'@(r_id, r_dd)) = f c' a r
        in (c'', r_dd)

    inferNodeA' f c s a@(a_id, _) b@(b_id, Node positionB pos_childB neg_childB) =
        let
            (c', r) = insert c (Node positionB (0,0) a_id)
            (c'', r'@(r_id, r_dd)) = f c' s r b
        in (c'', r_dd)
    inferNodeB' f c s a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, _) =
        let
            (c', r) = insert c (Node positionA (0,0) b_id)
            (c'', r'@(r_id, r_dd)) = f c' s a r
        in (c'', r_dd)

    applyInfA c s a@(a_id, _) b@(_, InfNodes positionB _ _ _) = let
            (c', (r_id, _)) = applyElimRule @Neg c $ EndInfNode  a_id
            (c'', r') = insert c' $ InfNodes positionB (0,0) (0,0) r_id
        in applyInf @Neg c'' s r' b
    applyInfB c s a@(_, InfNodes positionA _ _ _) b@(b_id, _) = let
            (c', (r_id, _)) = applyElimRule @Neg c $ EndInfNode b_id
            (c'', r') = insert c' $ InfNodes positionA (0,0) (0,0) r_id
        in applyInf @Neg c'' s a r'

    applyElimRule c (InfNodes _ (0,0) (0,0) (1,0)) = (c, ((1,0), Leaf True))
    applyElimRule c (InfNodes _ (0,0) (0,0) (2,0)) = (c, ((2,0), Leaf False))
    applyElimRule c (InfNodes _ (0,0) (0,0) (0,0)) = (c, ((0,0), Unknown))
    applyElimRule c d@(Node _ (0, 0) negC) = (c, (negC, getDd c negC))
    applyElimRule c d = applyElimRule_general c d

    applyElimRule' (c, d@(Node _ (0, 0) negC)) = (c, (negC, getDd c negC))
    applyElimRule' (c, d) = applyElimRule'_general (c, d)

    inferNode c position (n_id, n) = insert c (Node position (0,0) n_id)
    inferInfNode c position (n_id, n) = insert c $ InfNodes position (0,0) (0,0) n_id

    catchup s c n@(_, Node positionA pos_child _) idx
        -- special case to go until the end
        | idx == -1 = catchup @Neg s c (move_dc c s n) idx
        -- catchup
        | idx > positionA = catchup @Neg s c (move_dc c s n) idx
        -- ending criteria
        | idx < positionA = n
        | idx == positionA = n
    -- todo case infnode
    -- in case of leaf, endinfnode
    catchup s c n idx = n
    -- unknown should not be possible

    to_str = "Neg"

applyElimRule_general :: (HasNodeLookup c) => c -> Dd -> (c, Node)
applyElimRule_general c (EndInfNode (1,0)) = (c, ((1,0), Leaf True))
applyElimRule_general c (EndInfNode (2,0)) = (c, ((2,0), Leaf False))
applyElimRule_general c (EndInfNode (0,0)) = (c, ((0,0), Unknown))
applyElimRule_general c d = insert c d

applyElimRule'_general :: (HasNodeLookup c) => (c, Dd) -> (c, Node)
applyElimRule'_general (c, EndInfNode (1,0)) = (c, ((1,0), Leaf True))
applyElimRule'_general (c, EndInfNode (2,0)) = (c, ((2,0), Leaf False))
applyElimRule'_general (c, EndInfNode (0,0)) = (c, ((0,0), Unknown))
applyElimRule'_general (c, d) = insert c d

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






data Component = CompA | CompB | CompR


class Dd1_helper a where
    traverse_dc :: String -> BinaryOperatorContext -> NodeId -> NodeId -> BinaryOperatorContext
    traverse_dc_ :: String -> (HasNodeLookup c) => c -> NodeId -> c -- This is ambiguous, will need specialized versions or careful type handling
    getComponentFuncs :: Dd1 a => Component -> ( (Inf, (Node, Node, Node)) -> Node -- getter
                                           , BinaryOperatorContext -> String -> BinaryOperatorContext -- mover
                                           , BinaryOperatorContext -> Int -> BinaryOperatorContext -- catchuper
                                           , String -- component string label
                                           )
    traverse_dc_generic :: String -> (HasNodeLookup c) => c -> Node -> Node -> Node
    applyInf :: BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node)
    applyInf' :: BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node)




instance (DdF3 a) => Dd1_helper a where
    -- apply traversal
    applyInf :: BinaryOperatorContext -> String ->  Node -> Node -> (BinaryOperatorContext, Node)
    applyInf c s a@(a_id, a_d) b = debug_manipulation (applyInf' @a c s a b) s ("applyInf " ++ to_str @a ++ " " ++ s) c a b
    applyInf' :: BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node)
    applyInf' c s a@(a_id, InfNodes positionA dcA pA nA) b@(b_id, InfNodes positionB dcB pB nB)
        | positionA == positionB =
            let
                -- if there is an above layer
                -- update func stack so its dc's are on the same level as a and b (if not in dc context)
                c_ = add_to_stack (positionA, Dc) (((0, 0), Unknown), ((0, 0), Unknown), ((0, 0), Unknown)) c

                (c1, dcR) = apply @Dc (traverse_dc @a "inf dc" c_ dcA dcB) s dcA dcB

                -- to remeber the dcA and dcB specifically for this neg apply call, we place them on the func stack
                -- whenever, in this call, encountering (endinfnode) it should be taken off the func stack
                c2_ = add_to_stack (positionA, Neg) (getNode c1 dcA, getNode c1 dcB, dcR) (reset_stack c1 c)
                (c2, nR) = apply @Neg (traverse_dc @a "inf neg" c2_ nA nB) s nA nB

                c3_ = add_to_stack (positionA, Pos) (getNode c1 dcA, getNode c1 dcB, dcR) (reset_stack c2 c)
                (c3, pR) = apply @Pos (traverse_dc @a "inf pos" c3_ pA pB) s pA pB

                c4 = reset_stack c3 c
            in applyElimRule @a c4 $ InfNodes positionA (fst dcR) (fst pR) (fst nR)

        | positionA > positionB = applyInfA @a c s a b
        | positionA < positionB = applyInfB @a c s a b
    applyInf' c s a@(_, InfNodes {}) b@(_, Leaf _) = applyInfB @a c s a b
    applyInf' c s a@(_, InfNodes {}) b@(_, EndInfNode _) = applyInfB @a c s a b
    applyInf' c s a@(_, Leaf _) b@(_, InfNodes{}) = applyInfA @a c s a b
    applyInf' c s a@(_, EndInfNode _) b@(_, InfNodes{}) = applyInfA @a c s a b
    applyInf' c s a b = error_display "apply inf" c a b


    traverse_dc s c@BinaryOperatorContext{bin_dc_stack = dcs@(dcAs', dcBs', dcRs'), bin_current_level = lv} a b = debug_dc_traverse s c a b
        (if to_str @a == "Dc" then c
            else let
                -- lv' = if s == "endinf" then init lv else lv
                -- (dcAs, dcBs, dcRs) = if s == "endinf" then (init dcAs', init dcBs', init dcRs') else dcs
                new_dcAs = map (traverse_dc_generic @a s c (getNode c a)) dcAs'
                new_dcBs = map (traverse_dc_generic @a s c (getNode c b)) dcBs'
                new_dcRs = map (traverse_dc_generic @a s c (getNode c a)) dcRs' -- assumption, dcA and dcB are always at the same position when calling traverse_dc. if in the future this changes then we should take the highest / smallest to compare to dcR
                new_dcs = (new_dcAs, new_dcBs, new_dcRs)
            in c{bin_dc_stack = new_dcs, bin_current_level=lv})


    traverse_dc_generic s c refNode dcNode =
            case (dcNode, refNode) of
                -- Dc Node vs Ref Node comparison logic
                -- ! Ref node has already performed move !
                ( tNode@(_, Node position _ _), rNode@(_, Node idx _ _) ) ->
                    if | position > idx -> dcNode -- dc is ahead, do nothing
                        | position == idx -> move_dc c s dcNode -- Positions match, move
                        | position < idx -> move_dc c s (catchup @a s c dcNode idx)-- dc behind, catchup then move

                -- dc Node vs Leaf/EndInfNode (dc needs to catch up fully)
                ( (_, Node{}), (_, Leaf _) )         -> move_dc c s (catchup @a s c dcNode (-1)) -- Use -1 to signify catch up fully, then move
                ( (_, Node{}), (_, EndInfNode{}) ) -> move_dc c s (catchup @a s c dcNode (-1))  -- Catch up fully, then move

                -- Both EndInfNode
                ( (_, EndInfNode{}), (_, EndInfNode{}) ) -> move_dc c s dcNode

                -- Base cases where dc is already at EndInfNode or Leaf (usually no-op for traversal)
                ( (_, EndInfNode{}), (_, Leaf{}) )      -> dcNode -- todo for absorb; we should infer nodes for zdd side until an absorbable state has been reached..
                ( (_, Leaf{}),       (_, Leaf{}) )      -> dcNode
                ( (_, Leaf{}),       (_, EndInfNode{}) ) -> dcNode
                ( (_, Leaf{}),       (_, InfNodes{}) ) -> dcNode

                -- Base cases where dc is EndInfNode/Leaf and refNode is Node (dc is "ahead")
                ( (_, EndInfNode{}), (_, Node idx _ _) ) -> dcNode
                ( (_, Leaf _),       (_, Node idx _ _) ) -> dcNode

                -- Handle Unknown reference node
                ( _, (_, Unknown) ) -> move_dc c s dcNode
                ( (_, Unknown), _ ) -> dcNode -- !!!! todo think about what should be right here !!!!

                -- Handle InfNodes (using placeholder undefined for logic - needs careful implementation)
                ( (_, InfNodes position _ _ _), (_, InfNodes idx _ _ _) ) ->
                    if | position > idx -> dcNode -- dc is ahead, do nothing
                        | position == idx -> move_dc c s dcNode -- Positions match, move
                        | position < idx -> undefined-- dc behind, catchup then move
                ( (_, InfNodes position _ _ _), rNode@(_, Node idx _ _) )  ->
                    if | position > idx -> dcNode -- dc is ahead, do nothing
                        | position == idx -> move_dc c s dcNode -- Positions match, move
                        | position < idx -> undefined-- dc behind, catchup then move
                ( (_, EndInfNode{}), (_, InfNodes idx dc p n) ) -> dcNode
                ( (_, InfNodes{}), (_, Leaf{}) )           -> dcNode -- todo for absorb; we should infer nodes for zdd side until an absorbable state has been reached..
                ( (_, InfNodes{}), (_, EndInfNode{}) )     -> dcNode -- todo for absorb; we should infer nodes for zdd side until an absorbable state has been reached..

                -- Error case for unhandled patterns
                ( t, r ) -> error $ "traverse_dc_generic unhandled. dcNode=" ++ show t ++ " refNode=" ++ show r ++ " c=" ++ show (getLookup c) ++ " s=" ++ s


    traverse_dc_ s c d =  -- debug_dc_traverse s c d
        -- Need specialized implementations for different contexts if using traverse_dc_ generically
        undefined -- Logic depends on which context is being used (unary/binary)



type DdUnary :: Inf -> Constraint

class DdUnary a where
    swap_node_set :: UnaryOperatorContext -> [Position] -> Node -> (UnaryOperatorContext, Node)
    swap_node_set' :: UnaryOperatorContext -> [Position] -> Node -> (UnaryOperatorContext, Node)
    restrict_node_set :: UnaryOperatorContext -> [Position] -> Bool -> Node -> (UnaryOperatorContext, Node)
    restrict_node_set' :: UnaryOperatorContext -> [Position] -> Bool -> Node -> (UnaryOperatorContext, Node)
    traverse_dc_unary :: String -> UnaryOperatorContext -> NodeId -> UnaryOperatorContext



instance (DdF3 a) => DdUnary a where
    traverse_dc_unary s c@UnaryOperatorContext{un_dc_stack = dcs@(dcs', dcRs'), un_current_level = lv} d =
        if to_str @a == "Dc" then c
            else let
                new_dcs' = map (traverse_dc_generic @a s c (getNode c d)) dcs'
                new_dcRs = map (traverse_dc_generic @a s c (getNode c d)) dcRs'
                new_dcs = (new_dcs', new_dcRs)
            in c{un_dc_stack = new_dcs, un_current_level=lv}

    swap_node_set c (na : nas) d@(node_id, Node position pos_child neg_child)  = let
        (b, nas') = if (reverse $ map fst $ un_current_level c) ++ [position] == na
            then (True, nas)
            else (False, na : nas)

        (c1, posR) = if nas' /= []
            then (fst traverse_pos, fst $ snd traverse_pos)
            else (c, pos_child) -- terminal case, all vars have been replaced
        traverse_pos = swap_node_set @a c_ nas' (getNode c pos_child)
        c_ = traverse_dc_unary @a "pos child" c pos_child


        (c2, negR) = if nas' /= []
            then (fst traverse_neg, fst $ snd traverse_neg)
            else (c, neg_child) -- terminal case, all vars have been replaced
        traverse_neg = swap_node_set @a c1_ nas' (getNode c1 neg_child)
        c1_ = traverse_dc_unary @a "neg child" (reset_stack c1 c) neg_child

        -- Use a dummy BinaryOperatorContext to perform elimination since it's shared logic
        -- Alternatively, refactor applyElimRule to take HasNodeLookup
        in if b
            then undefined -- Placeholder: need to handle Binary logic calls from Unary context
            else undefined


    swap_node_set c nas d@(node_id, InfNodes position dc p n) =  let
        c_ = add_to_stack_ (position, Dc) (((0, 0), Unknown), ((0, 0), Unknown)) c
        (c1, dcR) = swap_node_set @Dc (traverse_dc_unary @a "inf dc" c_ dc) nas (getNode c dc)
        c2_ = add_to_stack_ (position, Neg) (getNode c1 dc, dcR) (reset_stack c1 c)
        (c2, nR) = swap_node_set @Neg (traverse_dc_unary @a "inf neg" c2_ n) nas (getNode c1 n)
        c3_ = add_to_stack_ (position, Pos) (getNode c2 dc, dcR) (reset_stack c2 c)
        (c3, pR) = swap_node_set @Pos (traverse_dc_unary @a "inf pos" c3_ p) nas (getNode c2 p)

        in undefined -- Placeholder: handle absorb in Unary context


    swap_node_set c nas d@(node_id, EndInfNode child) =  let
        (c_, inf) = pop_stack_ c
        c' = traverse_dc_unary @a "endinf" c_ node_id
        (c'', (r, _)) = case inf of
             Dc -> swap_node_set @Dc c' nas (getNode c child)
             Pos -> swap_node_set @Pos c' nas (getNode c child)
             Neg -> swap_node_set @Neg c' nas (getNode c child)
        in undefined -- Placeholder

    swap_node_set c nas b@(_, Leaf _) = (c, b) -- Placeholder
    swap_node_set c nas u@(_, Unknown) = (c, u)

    -- do inference whenever the node which should be swapped is eliminated
    swap_node_set' c (na : nas) d@(node_id, Node position pos_child neg_child) = if (reverse $ map fst $ un_current_level c) ++ [position] > na
        then let (c', d') = inferNode @a c (last na) d
            in swap_node_set @a c' (na : nas) d'
        else swap_node_set @a c (na : nas) d
    swap_node_set' c (na : nas) d@(node_id, InfNodes position dc p n) = if (reverse $ map fst $ un_current_level c) ++ [position] > na
        -- todo! infer the infnode which is needed to reach the flip node
        then let (c', d') = inferInfNode @a c (last na) d
            in swap_node_set @a c' (na : nas) d'
        else swap_node_set @a c (na : nas) d
    swap_node_set' c (na : nas) d = swap_node_set @a c (na : nas) d

    restrict_node_set c (na : nas) b d@(node_id, Node position pos_child neg_child)  = let
        (b', nas') = if (reverse $ map fst $ un_current_level c) ++ [position] == na
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
        c1_ = traverse_dc_unary @a "neg child" (reset_stack c1 c) neg_child

        in undefined

    restrict_node_set c nas b d@(node_id, InfNodes position dc p n) =
        let
        c_ = add_to_stack_ (position, Dc) (((0, 0), Unknown), ((0, 0), Unknown)) c
        (c1, dcR) = restrict_node_set @Dc (traverse_dc_unary @a "inf dc" c_ dc) nas b (getNode c dc)
        c2_ = add_to_stack_ (position, Neg) (getNode c1 dc, dcR) (reset_stack c1 c)
        (c2, nR) = restrict_node_set @Neg (traverse_dc_unary @a "inf neg" c2_ n) nas b (getNode c1 n)
        c3_ = add_to_stack_ (position, Pos) (getNode c2 dc, dcR) (reset_stack c2 c)
        (c3, pR) = restrict_node_set @Pos (traverse_dc_unary @a "inf pos" c3_ p) nas b (getNode c2 p)

        in undefined

    restrict_node_set c nas b d@(node_id, EndInfNode child) =  let
        (c_, inf) = pop_stack_ c
        c' = traverse_dc_unary @a "endinf" c_ node_id
        (c'', (r, _)) = case inf of
             Dc -> restrict_node_set @Dc c' nas b (getNode c child)
             Pos -> restrict_node_set @Pos c' nas b (getNode c child)
             Neg -> restrict_node_set @Neg c' nas b (getNode c child)
        in undefined

    restrict_node_set c nas _ b@(_, Leaf _) = (c, b)
    restrict_node_set c nas _ u@(_, Unknown) = (c, u)

    restrict_node_set c n a b = error ("nonexhaustive " ++ "\n c: \n" ++ show (getLookup c) ++ "\n n: \n" ++ show n ++ "\n a: \n" ++ show a ++ "\n b: \n" ++ show b)
    -- do inference whenever the node which should be restricted is eliminated
    restrict_node_set' c (na : nas) b d@(node_id, Node position pos_child neg_child) = if (reverse $ map fst $ un_current_level c) ++ [position] > na
        then let (c', d') = inferNode @a c (last na) d
            in restrict_node_set @a c' (na : nas) b d'
        else restrict_node_set @a c (na : nas) b d
    restrict_node_set' c (na : nas) b d@(node_id, InfNodes position dc p n) = if (reverse $ map fst $ un_current_level c) ++ [position] > na
        -- todo! infer the infnode which is needed to reach the flip node
        then let (c', d') = inferInfNode @a c (last na) d
            in restrict_node_set @a c' (na : nas) b d'
        else restrict_node_set @a c (na : nas) b d
    restrict_node_set' c (na : nas) b d = restrict_node_set @a c (na : nas) b d
