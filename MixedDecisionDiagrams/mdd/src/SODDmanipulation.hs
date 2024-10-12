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

module SODDmanipulation where
-- todo-future : explore {-# UNPACK #-} !Int
--SPECIALIZE pragma
import MDD hiding (debug)
import Debug.Trace (trace)
import DrawMDD
import Data.Kind

import GHC.IO (unsafePerformIO)
import DrawMDD (debug_manipulation)
import MDD (Dd(EndInfNode, InfNodes))
import Data.Bimap (insert)
type Node = (NodeId, Dd)
type DdManipulation = Context -> Node -> Node -> (Context, Node)

negation :: Context -> Node -> (Context, Node)
negation c d = debug_manipulation (negation' c d)

negation' :: Context -> Node -> (Context, Node)
negation' c (node_id, Node position pos_child neg_child)  = withCache_ c node_id $ let
    (c1, posR) = negation' c pos_child  --`debug` ("negation' pos child: " ++ show_dd settings c pos_child ++ " , " ++ " -> " ++ show (getDd c pos_child) )
    (c2, negR) = negation' c1 neg_child  --`debug` ("negation' neg child: " ++ show_dd settings c neg_child ++ " , " ++ "-> " ++ show (getDd c' neg_child))
    in insert c2 $ Node position posR negR -- `debug` (" inserted: " ++ show (insert c'' $ Node position posR negR))
negation' c (node_id, InfNodes position dc n p) = withCache_ c  node_id $ let
    (c1, r_dc) = negation' c dc
    (c2, r_n) = negation' c1 n
    (c3, r_p) = negation' c2 p
        in insert c3 $ InfNodes position r_dc r_n r_p
negation' c (node_id, EndInfNode a) = withCache_ c  node_id $ let
    (c1, result) = negation' c a (getDd c a) --`debug` ("negation' endinf child: " ++ show_dd settings c a )
    in insert c1 $ EndInfNode result
negation' c (_, Leaf b) = (c, leaf $ not b) --`debug` ("returning : " ++ show (c, leaf $ not b))
negation' c u@(_, Unknown) = (c, u)

intersection :: Context -> Node -> Node -> (Context, Node)
intersection c a b = debug_manipulation (intersection'  c a b)
    -- `debug` ("intersection: \n" ++ show_dd settings c a ++ " \n; "  ++ show_dd settings c b)

intersection' :: Context -> Node -> Node -> (Context, Node)
intersection' c Unknown b = insert c b -- build up the resulting cache by inserting all results
intersection' c a Unknown = insert c a
intersection' c a@(_, Leaf False) b = (c, a) -- no insert needed for Leafs
intersection' c a b@(_, Leaf False) = (c, b)
intersection' c a@(_, Leaf True) b = insert c b -- no cache lookup needed
intersection' c a b@(_, Leaf True) = insert c a

intersection' c a@(a_id, EndInfNode _) b@(b_id, Node{}) = withCache c (a_id, b_id, "inter") $ inferNodeA c a b
intersection' c a@(a_id, Node{}) b@(b_id, EndInfNode _) = withCache c (a_id, b_id, "inter") $ inferNodeB c a b
intersection' c a@(a_id, EndInfNode ac) b@(b_id, EndInfNode bc) = withCache c (a_id, b_id, "inter") $
    let (c', r) = intersection c ac bc
    in insert c' EndInfNode r
intersection' c a@(a_id, EndInfNode _) b@(b_id, InfNodes{}) = withCache c (a_id, b_id, "inter") $ inferInfNodeA c a b
intersection' c a@(a_id, InfNodes{}) b@(b_id, EndInfNode _) = withCache c (a_id, b_id, "inter") $ inferInfNodeB c a b

intersection' c a@(a_id, Node positionA pos_childA neg_childA)  b@(b_id, Node positionB pos_childB neg_childB)
    -- Match
    | positionA == positionB =
        let (c', pos_result) = intersection @a c pos_childA pos_childB
            (c'', neg_result) = intersection @a c' neg_childA neg_childB
        in withCache c (a_id, b_id, "inter") $ applyElimRule @a c'' (Node positionA pos_result neg_result)
    -- Mismatch, highest position gets an inferred node at position of the lowest
    | positionA < positionB = inferNodeB @a (intersection @a) c a b
    | positionA > positionB = inferNodeA @a (intersection @a) c a b

-- entering new domains
intersection' c a@(a_id, InfNodes positionA _ _ _ _ _) b@(b_id, Node positionB pos_childB neg_childB)
    | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
    | positionA > positionB = withCache c (a_id, b_id, "inter") $
            inferNodeA @a c a b
    | positionA < positionB = withCache c (a_id, b_id, "inter") $
            applyElimRule @a $ applyInfB a b -- there is a special elimination rule for the InfNodes case
intersection' c a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, InfNodes positionB _ _ _ _ _)
    | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
    | positionA > positionB = withCache c (a_id, b_id, "inter") $
            applyElimRule @a $ applyInfA a b
    | positionA < positionB = withCache c (a_id, b_id, "inter") $
            inferNodeB @a c a b
intersection' c a@(a_id, InfNodes positionA _ _ _ _ _)  b@(b_id, InfNodes positionB _ _ _ _ _)
    | positionA == positionB = applyInf a b
    | positionA < positionB = applyInfB @a a b
    | positionA > positionB = applyInfA @a a b
intersection' c a@(a_id, InfNodes positionA _ _ _ _ _) b@(b_id, EndInfNode _) = applyInfB @a a_id b_id a b
intersection' c a@(a_id, EndInfNode _) b@(b_id, InfNodes positionB _ _ _ _ _) = applyInfA @a a_id b_id a b

applyInf :: Context -> NodeId -> NodeId -> (Context, NodeId)
applyInf c a b = debug_manipulation (applyInf' c a b)
    "intersection" "applyInf"

applyInf' :: DdManipulation -> DdManipulation
applyInf' b c a@(InfNodes positionA dcA nA pA) b@(InfNodes positionB dcB nB pB)

    | positionA == positionB = let
            operator = if b then intersection else union

            (c1, dcR) = operator @Dc c dcA dcB
            (c2, nR) =
                let (c2', r') = operator @Neg c2 nA nB
                in absorb @Neg c2' r' cR
            (c3, pR) =
                let (c3', r') = operator @Pos c3 pA pB
                in absorb @Pos c3' r' cR

            apply_elimRule (_, InfNodes _ (Leaf True) Unknown Unknown) = Leaf True
            apply_elimRule (_, InfNodes _ (Leaf False) Unknown Unknown) = Leaf False
            apply_elimRule (_, InfNodes _ Unknown Unknown Unknown) = Unknown
            apply_elimRule d = insert c3 d

        in apply_elimRule $ InfNodes positionA dcR nR pR

    | otherwise = error_display c a b
applyInf' c a_id b_id a b = error_display c a b



class DdF4 a where
    inferNodeA :: DdManipulation -> DdManipulation
    inferNodeB :: DdManipulation -> DdManipulation
    applyElimRule :: Context -> Node -> (Context, Node)


instance DdF4 Dc where
    inferNodeA f c a (b_id, b@(Node positionB pos_childB neg_childB)) =
        let (c', pos_result) = f c a pos_childB
            (c'', neg_result) = f c' a neg_childB
        in applyElimRule @Dc c'' (Node positionB pos_result neg_result)
    inferNodeA _ c a b = error_display "inferNodeA dc"
    inferNodeB f c (a_id, Node positionA pos_childA neg_childA) b =
        let (c', pos_result) = f c pos_childA b
            (c'', neg_result) = f c' neg_childA b
        in applyElimRule @Dc c'' (Node positionA pos_result neg_result)
    inferNodeB _ c a b = error_display "infernodeB dc"

    applyElimRule c (d_id, EndInfNode l@(Leaf _)) = (c, l)
    applyElimRule c d@(d_id, Node _ a b) = (c, a)
    applyElimRule c d = (c, d)

    applyInfB a@(_, InfNodes positionA _ _ _) b =
        insert c $ applyElimRule @Dc $ applyInf c (InfNodes positionA b Unknown Unknown)


instance DdF4 Pos where
    inferNodeA f c a (b_id, b@(Node positionB pos_childB _)) =
        let (c', pos_result) = f c a pos_childB
        in applyElimRule @Pos c' pos_result
    inferNodeA _ c a b = error_display "inferNodeA pos"
    inferNodeB f c (a_id, Node positionA pos_childA _) b =
        let (c', pos_result) = f c pos_childA b
        in applyElimRule @Pos c' pos_result
    inferNodeB _ c a b = error_display "infernodeB pos"

    applyElimRule c (d_id, EndInfNode l@(Leaf _)) = (c, l)
    applyElimRule c d@(d_id, Node _ posC (_, Unknown)) = (c, posC)
    applyElimRule c d = (c, d)

instance DdF4 Neg where
    inferNodeA f c a (b_id, b@(Node positionB _ neg_childB)) =
        let (c', neg_result) = f c a neg_childB
        in applyElimRule @Pos c' neg_result
    inferNodeA _ c a b = error_display "inferNodeA neg"
    inferNodeB f c (a_id, Node positionA _ neg_childA) b =
        let (c', neg_result) = f c neg_childA b
        in applyElimRule @Pos c' neg_result
    inferNodeB _ c a b = error_display "infernodeB neg"

    applyElimRule c (d_id, EndInfNode l@(Leaf _)) = (c, l)
    applyElimRule c d@(d_id, Node _ (_, Unknown) negC) = (c, negC)
    applyElimRule c d = (c, d)

error_display :: String -> Context -> Node -> Node -> ()
error_display s c (a_id, a) (b_id, b) = error (show s ++ " : " ++ show c ++ ", " ++ show a ++ ", " ++ show_dd settings c b_id)
