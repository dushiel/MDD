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

module SODDmanipulation where
-- todo-future : explore {-# UNPACK #-} !Int
--SPECIALIZE pragma
import MDD
import Data.Kind

import DrawMDD (debug_manipulation)
import Data.Bimap ()

type DdManipulation = Context -> Node -> Node -> (Context, Node)

negation :: Context -> Node -> (Context, Node)
negation = negation'

negation' :: Context -> Node -> (Context, Node)
negation' c d@(node_id, Node position pos_child neg_child)  = withCache_ c d $ let
    (c1, (posR, _)) = negation' c (pos_child, getDd c pos_child)  --`debug` ("negation' pos child: " ++ show_dd settings c pos_child ++ " , " ++ " -> " ++ show (getDd c pos_child) )
    (c2, (negR, _)) = negation' c1 (neg_child, getDd c1 neg_child)  --`debug` ("negation' neg child: " ++ show_dd settings c neg_child ++ " , " ++ "-> " ++ show (getDd c' neg_child))
    in insert c2 $ Node position posR negR -- `debug` (" inserted: " ++ show (insert c'' $ Node position posR negR))
negation' c d@(node_id, InfNodes position dc p n) = withCache_ c d $ let
    (c1, (r_dc, _)) = negation' c (dc, getDd c dc)
    (c2, (r_n, _)) = negation' c1 (n, getDd c n)
    (c3, (r_p, _)) = negation' c2 (p, getDd c p)
        in insert c3 $ InfNodes position r_dc r_p r_n
negation' c d@(node_id, EndInfNode a) = withCache_ c  d $ let
    (c1, (result, _)) = negation' c (a, getDd c a) --`debug` ("negation' endinf child: " ++ show_dd settings c a )
    in insert c1 $ EndInfNode result
negation' c (_, Leaf b) = (c, leaf $ not b) --`debug` ("returning : " ++ show (c, leaf $ not b))
negation' c u@(_, Unknown) = (c, u)

class Dd1 a where
    intersection :: Context -> NodeId -> NodeId -> (Context, Node)
    intersection' :: Context -> Node -> Node -> (Context, Node)
    intersection'' :: Context -> Node -> Node -> (Context, Node)
    absorb :: Context -> NodeId -> NodeId -> (Context, Node)
    absorb' :: Context -> Node -> Node -> (Context, Node)
    absorb'' :: Context -> Node -> Node -> (Context, Node)


instance (DdF3 a) => Dd1 a where

    intersection c a b = debug_manipulation  (intersection' @a c (getNode c a) (getNode c b)) "intersection" ("intersection" ++ to_str @a) c (getNode c a) (getNode c b)
        --  `debug` ("intersection: \n" ++ show a ++ " \n; "  ++ show b)
    intersection'' c a b = debug_manipulation  (intersection' @a c a b) "intersection" ("intersection" ++ to_str @a) c a b


    intersection' c a@(_, Leaf False) b = interLeaf @a c a b -- `debug` "LEa Fasle inter" -- no insert needed for Leafs
    intersection' c a b@(_, Leaf False) = interLeaf @a c a b
    intersection' c a@(_, Leaf True) b = interLeaf @a c a b -- `debug` "LEa True inter" -- no cache lookup needed
    intersection' c a b@(_, Leaf True) = interLeaf @a c a b
    intersection' c a@(_, Unknown) b@(_, Unknown) = (c , a)

    intersection' c a@(_, Unknown) b@(b_id, Node positionB pos_childB neg_childB) = 
        let (c', (pos_result, _)) = intersection @a c (0,0) pos_childB `debug` "node node"
            (c'', (neg_result, _)) = intersection @a c' (0,0) neg_childB
        in withCache c (a, b, "inter") $ applyElimRule @a c'' (Node positionB pos_result neg_result)

    intersection' c a@(a_id, Node positionA pos_childA neg_childA) b@(_, Unknown) = 
        let (c', (pos_result, _)) = intersection @a c (0,0) pos_childA `debug` "node node"
            (c'', (neg_result, _)) = intersection @a c' (0,0) neg_childA
        in withCache c (a, b, "inter") $ applyElimRule @a c'' (Node positionA pos_result neg_result)

    intersection' c a@(a_id, EndInfNode _) b@(b_id, Node{}) = withCache c (a, b, "inter") $ inferNodeA @a (intersection'' @a) c a b
    intersection' c a@(a_id, Node{}) b@(b_id, EndInfNode _) = withCache c (a, b, "inter") $ inferNodeB @a (intersection'' @a) c a b
    intersection' c a@(a_id, EndInfNode ac) b@(b_id, EndInfNode bc) = withCache c (a, b, "inter") $
        let (c', (r, _)) = intersection @a c ac bc
        in insert c' $ EndInfNode r

    intersection' c a@(a_id, Node positionA pos_childA neg_childA)  b@(b_id, Node positionB pos_childB neg_childB)
        -- Match
        | positionA == positionB =
            let (c', (pos_result, _)) = intersection @a c pos_childA pos_childB `debug` "node node"
                (c'', (neg_result, _)) = intersection @a c' neg_childA neg_childB
            in withCache c (a, b, "inter") $ applyElimRule @a c'' (Node positionA pos_result neg_result)
        -- Mismatch, highest position gets an inferred node at position of the lowest
        | positionA < positionB = inferNodeB @a (intersection'' @a) c a b `debug` "intersection-inferNodeB"
        | positionA > positionB = inferNodeA @a (intersection'' @a) c a b `debug` "intersection-inferNodeA" 

    -- -- entering new domains
    intersection' c a@(a_id, InfNodes positionA _ _ _) b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB = withCache c (a, b, "inter") $
                inferNodeA @a (intersection'' @a) c a b
        -- | positionA < positionB = withCache c (a, b, "inter") $
        --         applyElimRule @a $ applyInfB a b -- there is a special elimination rule for the InfNodes case
    intersection' c a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
    --     | positionA > positionB = withCache c (a, b, "inter") $
    --             applyElimRule @a $ applyInfA a b
        | positionA < positionB = withCache c (a, b, "inter") $
                inferNodeB @a (intersection'' @a) c a b
    intersection' c a@(a_id, InfNodes positionA _ _ _)  b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = applyInf c a b
        | positionA < positionB = applyInfB @a c a b
        | positionA > positionB = applyInfA @a c a b
    intersection' c a@(a_id, EndInfNode _) b@(b_id, InfNodes{}) = withCache c (a, b, "inter") $ applyInfA @a c a b
    intersection' c a@(a_id, InfNodes{}) b@(b_id, EndInfNode _) = withCache c (a, b, "inter") $ applyInfB @a c a b

    --todo add endinfnode (0,0) /(1,0) removal on leaf cases
    absorb c a b = debug_manipulation  (absorb' @a c (getNode c a) (getNode c b)) "absorb" ("absorb" ++ to_str @a) c (getNode c a) (getNode c b)
    absorb'' c a b = debug_manipulation  (absorb' @a c a b) "absorb" ("absorb" ++ to_str @a) c a b
    absorb' :: Context -> Node -> Node -> (Context, Node)
    absorb' c a dc@(_, Unknown) = (c, a)
    absorb' c a@(_, Unknown) dc = (c, ((0,0), Unknown))
    absorb' c a@(_, Leaf _) dc = if a == dc then (c, ((0,0), Unknown)) else (c, a)
    absorb' c a@(_, EndInfNode _) dc@(_, Node positionD pos_childD neg_childD)  = inferNodeA @a (absorb' @a) c a dc
    absorb' c a@(_, EndInfNode a_child) dc@(_, Leaf _)  = if getNode c a_child == dc then (c, ((0,0), Unknown)) else (c, a)
    absorb' c a@(_, InfNodes {}) dc@(_, Leaf _)  = (c, a)
    absorb' c a@(_, Node positionA pos_childA neg_childA) dc@(dc_id, EndInfNode _)  = --infere Dc node
        let (c', (pos_result, _)) = absorb @a c pos_childA dc_id
            (c'', (neg_result, _)) = absorb @a c' neg_childA dc_id
        in withCache c (a, dc, "absorb") $ applyElimRule @a c'' (Node positionA pos_result neg_result)
    absorb' c a@(_, EndInfNode a') dc@(_, EndInfNode dc') = if a' == dc' then (c, ((0,0), Unknown)) else (c, a)
    absorb' c a@(_, Node positionA pos_childA neg_childA) dc@(dc_id, Leaf _) =
        let (c', (pos_result, _)) = absorb @a c pos_childA dc_id
            (c'', (neg_result, _)) = absorb @a c' neg_childA dc_id
        in withCache c (a, dc, "absorb") $ applyElimRule @a c'' (Node positionA pos_result neg_result) `debug` ("absorb " ++ to_str @a ++ show (Node positionA pos_result neg_result))

    absorb' c a@(_, Node positionA pos_childA neg_childA)  dc@(dc_id, Node positionD pos_childD neg_childD)
        -- No mismatch
        | positionA == positionD =
            let (c', (pos_result, _)) = absorb @a c pos_childA pos_childD
                (c'', (neg_result, _)) = absorb @a c' neg_childA neg_childD
            in withCache c (a, dc, "absorb") $ applyElimRule @a c'' (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionD = inferNodeA @a (absorb' @a) c a dc
        | positionA < positionD =
            let (c', (pos_result, _)) = absorb @a c pos_childA dc_id
                (c'', (neg_result, _)) = absorb @a c' neg_childA dc_id
            in withCache c (a, dc, "absorb") $ applyElimRule @a c'' (Node positionA pos_result neg_result)

    -- absorb' c a@(_, InfNodes {}) b@(_, InfNodes {}) = case to_constr @a of
    --     Dc -> error "absorb with a dc as first argument should not be possible"
    --     Neg -> f True
    --     Pos -> f True
    --     where
    --         f b' = apply @a Absorb c "absorb" (t_and_rMain b') a b
    -- absorb' c a@(_, InfNodes positionA dcA n1A n0A p1A p0A) dc@(_, Node positionD pos_childD neg_childD)
    --     | positionA > positionD = inferNodeA @a (absorb @a) c a dc
    --     | positionA < positionD = case to_constr @a of
    --         Dc -> error "absorb with a dc as first argument should not be possible"
    --         Neg -> f True
    --         Pos -> f True
    --     | otherwise = undefined
    --         where
    --             f b' = apply @Dc Absorb c "absorb" (t_and_rInferB b') a dc
    -- -- add posB == posA, then we consider node to be AllNegs -> [1]
    -- absorb' c a@(_, Node positionA pos_childA neg_childA) dc@(_, InfNodes positionD dcA n1A n0A p1A p0A)
    --     | positionA > positionD =  case to_constr @a of
    --             Dc -> error "absorb with a dc as first argument should not be possible"
    --             Neg -> f True
    --             Pos -> f True
    --     | positionA < positionD =
    --         let (c', (pos_result, _)) = absorb @a c pos_childA b_id (getDd c pos_childA) dc
    --             (c'', (neg_result, _)) = absorb @a c' pos_childA b_id (getDd c neg_childA) dc
    --         in withCache c (a_id, b_id, "absorb") $ applyElimRule @a c'' (Node positionD pos_result neg_result)
    --     | otherwise = undefined
    --         where
    --             f b' = apply @a Absorb c "absorb" (t_and_rInferA b') a dc

    absorb' c a b = error $ "absorb , " ++ "a = " ++ show a ++ "  \n  b = " ++ show b

applyInf :: Context -> Node -> Node -> (Context, Node)
applyInf c a b = debug_manipulation (applyInf' c a b) "intersection" "applyInf" c a b



applyInf' :: Context -> Node -> Node -> (Context, Node)
applyInf' c a@(a_id, InfNodes positionA dcA pA nA) b@(b_id, InfNodes positionB dcB pB nB)
    | positionA == positionB = -- if b then
        let
            (c1, dcR) = intersection @Dc c dcA dcB
            (c2, nR) =
                let (c2', r2') = intersection @Neg c1 nA nB
                in absorb'' @Neg c2' r2' dcR
            (c3, pR) =
                let (c3', r3') = intersection @Pos c2 pA pB
                in absorb'' @Pos c3' r3' dcR

            apply_elimRule (InfNodes _ (1,0) (0,0) (0,0)) = (c3, ((1,0), Leaf True))
            apply_elimRule (InfNodes _ (2,0) (0,0) (0,0)) = (c3, ((2,0), Leaf False))
            apply_elimRule (InfNodes _ (0,0) (0,0) (0,0)) = (c3, ((0,0), Unknown))
            apply_elimRule d = insert c3 d
        in apply_elimRule $ InfNodes positionA (fst dcR) (fst pR) (fst nR)
        -- else let
            -- (c1, dcR) = union @Dc c dcA dcB
            -- (c2, nR) =
            --     let (c2', r') = union @Neg c2 nA nB
            --     in absorb @Neg c2' r' cR
            -- (c3, pR) =
            --     let (c3', r') = union @Pos c3 pA pB
            --     in absorb @Pos c3' r' cR

        --     apply_elimRule (InfNodes _ (1,0) (0,0) (0,0)) = (c1, ((1,0), Leaf True))
        --     apply_elimRule (InfNodes _ (2,0) (0,0) (0,0)) = (c1, ((2,0), Leaf False))
        --     apply_elimRule (InfNodes _ (0,0) (0,0) (0,0)) = (c1, ((0,0), Unknown))
        --     apply_elimRule d = insert c1 d
        -- in apply_elimRule $ InfNodes positionA dcR nR pR

    | positionA > positionB = applyInfA @Dc c a b
    | positionA < positionB = applyInfB @Dc c a b
applyInf' c a b = error_display "apply inf" c a b


type DdF3 :: Inf -> Constraint
type Dd1 :: Inf -> Constraint

class DdF3 a where
    inferNodeA :: DdManipulation -> DdManipulation
    inferNodeB :: DdManipulation -> DdManipulation
    applyElimRule :: Context -> Dd -> (Context, Node)
    applyInfA :: Context -> Node -> Node -> (Context, Node)
    applyInfB :: Context -> Node -> Node -> (Context, Node)
    to_str :: String
    interLeaf :: Context -> Node -> Node -> (Context, Node)


instance DdF3 Dc where
    inferNodeA f c a (b_id, b@(Node positionB pos_childB neg_childB)) =
        let (c', (pos_result, _)) = f c a (getNode c pos_childB)
            (c'', (neg_result, _)) = f c' a (getNode c neg_childB)
        in applyElimRule @Dc c'' ( Node positionB pos_result neg_result)
    inferNodeA _ c a b = error_display "inferNodeA dc" c a b
    inferNodeB f c (a_id, Node positionA pos_childA neg_childA) b =
        let (c', (pos_result, _)) = f c (getNode c pos_childA) b
            (c'', (neg_result, _)) = f c' (getNode c neg_childA) b
        in applyElimRule @Dc c'' ( Node positionA pos_result neg_result)
    inferNodeB _ c a b = error_display "infernodeB dc" c a b

    applyElimRule c (EndInfNode (1,0)) = (c, ((1,0), Leaf True))
    applyElimRule c (EndInfNode (2,0)) = (c, ((2,0), Leaf False))
    applyElimRule c d@(Node _ p n) = if p == n then (c, getNode c p) else insert c d
    applyElimRule c d = insert c d

    applyInfA c a@(a_id, _) b@(_, InfNodes positionB _ _ _) = let
            (c', r) = insert c $ InfNodes positionB a_id (0,0) (0,0)
        in applyInf c' r b
    applyInfB c a@(_, InfNodes positionA _ _ _) b@(b_id, _) = let
            (c', r) = insert c $ InfNodes positionA b_id (0,0) (0,0)
        in applyInf c' a r

    --  True is stronger than Unknown in dc + intersection context, so unknown comes before true
    interLeaf c a@(_, Leaf False) b = (c, a) -- `debug` "LEa Fasle inter" -- no insert needed for Leafs
    interLeaf c a b@(_, Leaf False) = (c, b)
    interLeaf c a@(_, Unknown) b = (c, b) -- build up the resulting cache by inserting all results
    interLeaf c a b@(_, Unknown) = (c, a) 
    interLeaf c a@(_, Leaf True) b = (c, b) -- `debug` "LEa True inter" -- no cache lookup needed
    interLeaf c a b@(_, Leaf True) = (c, a)
    interLeaf _ _ _ = error "wrong arguments for inter leaf case"

    to_str = "Dc"

instance DdF3 Pos where
    inferNodeA f c a@(a_id, _) b@(b_id, Node positionB pos_childB neg_childB) = 
        let 
            (c', r) = insert c (Node positionB a_id (0,0))
            (c'', r'@(r_id, r_dd)) = f c' r b
        in applyElimRule @Pos c'' r_dd `debug` ("inferNodeA neg : " ++ show r')
    inferNodeA _ c a b = error_display "inferNodeA pos" c a b
    inferNodeB f c a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, _) =
        let 
            (c', r) = insert c (Node positionA b_id (0,0))
            (c'', r'@(r_id, r_dd)) = f c' r a
        in applyElimRule @Neg c'' r_dd `debug` ("inferNodeB neg : " ++ show r')
    inferNodeB _ c a b = error_display "infernodeB pos" c a b

    applyElimRule c (EndInfNode (1,0)) = (c, ((1,0), Leaf True))
    applyElimRule c (EndInfNode (2,0)) = (c, ((2,0), Leaf False))
    applyElimRule c d@(Node _ posC (0, 0)) = (c, getNode c posC) `debug` ("eimrule" ++ show posC)
    applyElimRule c d = insert c d

    --  Unknown is stronger than True in finite + intersection context
    interLeaf c a@(_, Leaf False) b = (c, a) -- `debug` "LEa Fasle inter" -- no insert needed for Leafs
    interLeaf c a b@(_, Leaf False) = (c, b)
    interLeaf c a@(_, Leaf True) b = (c, b) -- `debug` "LEa True inter" -- no cache lookup needed
    interLeaf c a b@(_, Leaf True) = (c, a)
    interLeaf c a@(_, Unknown) b = (c, b) -- build up the resulting cache by inserting all results
    interLeaf c a b@(_, Unknown) = (c, a) 
    interLeaf _ _ _ = error "wrong arguments for inter leaf case"

    to_str = "Pos"

instance DdF3 Neg where
    inferNodeA f c a@(a_id, _) b@(b_id, Node positionB pos_childB neg_childB) =
        let 
            (c', r) = insert c (Node positionB (0,0) a_id)
            (c'', r'@(r_id, r_dd)) = f c' r b
        in applyElimRule @Neg c'' r_dd `debug` ("inferNodeA neg : " ++ show r')
    inferNodeA _ c a b = error_display "inferNodeA neg" c a b
    inferNodeB f c a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, _) =
        let 
            (c', r) = insert c (Node positionA (0,0) b_id)
            (c'', r'@(r_id, r_dd)) = f c' r a
        in applyElimRule @Neg c'' r_dd `debug` ("inferNodeB neg : " ++ show r')
    inferNodeB _ c a b = error_display "infernodeB neg" c a b

    applyElimRule c (EndInfNode (1,0)) = (c, ((1,0), Leaf True))
    applyElimRule c (EndInfNode (2,0)) = (c, ((2,0), Leaf False))
    applyElimRule c d@(Node _ (0, 0) negC) = (c, (negC, getDd c negC))
    applyElimRule c d = insert c d

    interLeaf c a@(_, Leaf False) b = (c, a) -- `debug` "LEa Fasle inter" -- no insert needed for Leafs
    interLeaf c a b@(_, Leaf False) = (c, b)
    interLeaf c a@(_, Leaf True) b = (c, b) -- `debug` "LEa True inter" -- no cache lookup needed
    interLeaf c a b@(_, Leaf True) = (c, a)
    interLeaf c a@(_, Unknown) b = (c, b) -- build up the resulting cache by inserting all results
    interLeaf c a b@(_, Unknown) = (c, a) 
    interLeaf _ _ _ = error "wrong arguments for inter leaf case"
    to_str = "Neg"

class All a where
    error_display :: String -> Context -> Node -> Node -> a
    error_display s c (a_id, a) (b_id, b) = error (show s ++ " : " ++ show c ++ ", " ++ show a ++ ", " ++ show b)

instance All (Context, Node)