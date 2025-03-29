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
    intersection'' :: Context -> Node -> Node -> (Context, Node)
    union :: Context -> NodeId -> NodeId -> (Context, Node)
    union'' :: Context -> Node -> Node -> (Context, Node)
    intersection' :: Context -> Node -> Node -> (Context, Node)
    union' :: Context -> Node -> Node -> (Context, Node)
    absorb :: Context -> NodeId -> NodeId -> (Context, Node)
    absorb' :: Context -> Node -> Node -> (Context, Node)
    absorb'' :: Context -> Node -> Node -> (Context, Node)





instance (DdF3 a) => Dd1 a where
    union c a b = debug_manipulation  (union' @a c (getNode c a) (getNode c b)) "union" ("union" ++ to_str @a) c (getNode c a) (getNode c b)
    union'' c a b = debug_manipulation  (union' @a c a b) "union" ("union==" ++ to_str @a) c a b

    union' c a@(_, Leaf False) b = unionLeaf @a c a b
    union' c a b@(_, Leaf False) = unionLeaf @a c a b
    union' c a@(_, Leaf True) b = unionLeaf @a c a b
    union' c a b@(_, Leaf True) = unionLeaf @a c a b
    union' c a@(_, Unknown) b@(_, Unknown) = (c , a)
    union' c a b@(_, Unknown) = unionLeaf @a c a b
    union' c a@(_, Unknown) b = unionLeaf @a c a b

    union' c a@(a_id, EndInfNode _) b@(b_id, Node idx _ _) = withCache c (a, b, "union") $ inferNodeA @a (union'' @a) c a b
    union' c a@(a_id, Node{}) b@(b_id, EndInfNode _) = withCache c (a, b, "union") $ inferNodeB @a (union'' @a) c a b
    union' c a@(a_id, EndInfNode ac) b@(b_id, EndInfNode bc) = withCache c (a, b, "union") $ 
        let c' = traverse_dc @a "endinf" c a_id b_id 
            (c'', (r, _)) = union @a c' ac bc
        in insert c'' $ EndInfNode r

    union' c a@(a_id, Node positionA pos_childA neg_childA)  b@(b_id, Node positionB pos_childB neg_childB)
        -- Match
        | positionA == positionB =
            let current_fs = head $ func_stack c
                c_ = traverse_dc @a "pos child" c pos_childA pos_childB 
                (c', (pos_result, _)) = union @a c_ pos_childA pos_childB

                c_' = traverse_dc @a "neg child" (func_alt (to_str @a) c' current_fs) neg_childA neg_childB -- todo: catch more cases where child is some random type..
                (c'', (neg_result, _)) = union @a c_' neg_childA neg_childB 
            in withCache c (a, b, "union") $ applyElimRule @a c'' (Node positionA pos_result neg_result)
        -- Mismatch, highest position gets an inferred node at position of the lowest
        | positionA < positionB = inferNodeB @a (union'' @a) c a b
        | positionA > positionB = inferNodeA @a (union'' @a) c a b

    -- -- entering new domains
    union' c a@(a_id, InfNodes positionA _ _ _) b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB = withCache c (a, b, "union") $
                inferNodeA @a (union'' @a) c a b
        -- | positionA < positionB = withCache c (a, b, "union") $
        --         applyElimRule @a $ applyInfB a b -- there is a special elimination rule for the InfNodes case
    union' c a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
    --     | positionA > positionB = withCache c (a, b, "union") $
    --             applyElimRule @a $ applyInfA a b
        | positionA < positionB = withCache c (a, b, "union") $
                inferNodeB @a (union'' @a) c a b
    union' c a@(a_id, InfNodes positionA _ _ _)  b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = applyInf @a c "union" a b
        | positionA < positionB = applyInfB @a c "union" a b
        | positionA > positionB = applyInfA @a c "union" a b
    union' c a@(a_id, EndInfNode _) b@(b_id, InfNodes{}) = withCache c (a, b, "union") $ applyInfA @a c "union" a b
    union' c a@(a_id, InfNodes{}) b@(b_id, EndInfNode _) = withCache c (a, b, "union") $ applyInfB @a c "union" a b

    intersection c a b = debug_manipulation  (intersection' @a c (getNode c a) (getNode c b)) "intersection" ("intersection" ++ to_str @a) c (getNode c a) (getNode c b)
    intersection'' c a b = debug_manipulation  (intersection' @a c a b) "intersection" ("intersection==" ++ to_str @a) c a b

    intersection' c a@(_, Leaf False) b = interLeaf @a c a b -- `debug` "inter False @a"
    intersection' c a b@(_, Leaf False) = interLeaf @a c a b -- `debug` "inter False @b"
    intersection' c a@(_, Leaf True) b = interLeaf @a c a b -- `debug` "inter True @a"
    intersection' c a b@(_, Leaf True) = interLeaf @a c a b -- `debug` "inter True @b"
    intersection' c a@(_, Unknown) b@(_, Unknown) = (c , a)
    intersection' c a b@(_, Unknown) = interLeaf @a c a b
    intersection' c a@(_, Unknown) b = interLeaf @a c a b

    intersection' c a@(a_id, EndInfNode _) b@(b_id, Node idx _ _) = withCache c (a, b, "inter") $ inferNodeA @a (intersection'' @a) c a b
    intersection' c a@(a_id, Node{}) b@(b_id, EndInfNode _) = withCache c (a, b, "inter") $ inferNodeB @a (intersection'' @a) c a b
    intersection' c a@(a_id, EndInfNode ac) b@(b_id, EndInfNode bc) = withCache c (a, b, "inter") $ 
        let c' = traverse_dc @a "endinf" c a_id b_id 
            (c'', (r, _)) = intersection @a c' ac bc
        in insert c'' $ EndInfNode r

    intersection' c a@(a_id, Node positionA pos_childA neg_childA)  b@(b_id, Node positionB pos_childB neg_childB)
        -- Match
        | positionA == positionB =
            let current_fs = head $ func_stack c
                c_ = traverse_dc @a "pos child" c pos_childA pos_childB 
                (c', (pos_result, _)) = intersection @a c_ pos_childA pos_childB

                c_' = traverse_dc @a "neg child" (func_alt (to_str @a) c' current_fs) neg_childA neg_childB -- todo: catch more cases where child is some random type..
                (c'', (neg_result, _)) = intersection @a c_' neg_childA neg_childB 
            in withCache c (a, b, "inter") $ applyElimRule @a c'' (Node positionA pos_result neg_result)
        -- Mismatch, highest position gets an inferred node at position of the lowest
        | positionA < positionB = inferNodeB @a (intersection'' @a) c a b
        | positionA > positionB = inferNodeA @a (intersection'' @a) c a b

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
        | positionA == positionB = applyInf @a c "intersection" a b
        | positionA < positionB = applyInfB @a c "intersection" a b
        | positionA > positionB = applyInfA @a c "intersection" a b
    intersection' c a@(a_id, EndInfNode _) b@(b_id, InfNodes{}) = withCache c (a, b, "inter") $ applyInfA @a c "intersection" a b
    intersection' c a@(a_id, InfNodes{}) b@(b_id, EndInfNode _) = withCache c (a, b, "inter") $ applyInfB @a c "intersection" a b


    --todo add endinfnode (0,0) /(1,0) removal on leaf cases
    absorb c a b = debug_manipulation  (absorb' @a c (getNode c a) (getNode c b)) "absorb" ("absorb" ++ to_str @a) c (getNode c a) (getNode c b)
    absorb'' c a b = debug_manipulation  (absorb' @a c a b) "absorb" ("absorb" ++ to_str @a) c a b
    absorb' :: Context -> Node -> Node -> (Context, Node)
    -- | given a dcR and a pos or ng results, sets sub-paths in the local inf-domain which agree with the dcR to unknown ("absorbing them")   
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
        in withCache c (a, dc, "absorb") $ applyElimRule @a c'' (Node positionA pos_result neg_result) -- `debug` ("absorb " ++ to_str @a ++ show (Node positionA pos_result neg_result))

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







type DdF3 :: Inf -> Constraint
type Dd1 :: Inf -> Constraint

class DdF3 a where
    inferNodeA :: DdManipulation -> DdManipulation
    inferNodeB :: DdManipulation -> DdManipulation
    applyElimRule :: Context -> Dd -> (Context, Node)
    applyInfA :: Context -> String -> Node -> Node -> (Context, Node)
    applyInfB :: Context -> String -> Node -> Node -> (Context, Node)
    to_str :: String
    interLeaf :: Context -> Node -> Node -> (Context, Node)
    unionLeaf :: Context -> Node -> Node -> (Context, Node)
    catchupA :: Context -> Int -> Context
    catchupB :: Context -> Int -> Context
    catchupR :: Context -> Int -> Context


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

    applyInfA c s a@(a_id, _) b@(_, InfNodes positionB _ _ _) = let
            (c', (r_id, _)) = insert c $ EndInfNode  a_id
            (c'', r') = insert c' $ InfNodes positionB r_id (0,0) (0,0)
        in applyInf @Dc c'' s r' b
    applyInfB c s a@(_, InfNodes positionA _ _ _) b@(b_id, _) = let
            (c', (r_id, _)) = insert c $ EndInfNode b_id 
            (c'', r') = insert c' $ InfNodes positionA r_id (0,0) (0,0)
        in applyInf @Dc c'' s a r'

    --  True is stronger than Unknown in dc + intersection context, so unknown comes before true
    interLeaf c a@(_, Leaf False) b = (c, a) -- no insert needed for Leafs
    interLeaf c a b@(_, Leaf False) = (c, b)
    interLeaf c a@(_, Unknown) b = (c, b) -- build up the resulting cache by inserting all results
    interLeaf c a b@(_, Unknown) = (c, a)
    interLeaf c a@(_, Leaf True) b = (c, b) -- no cache lookup needed
    interLeaf c a b@(_, Leaf True) = (c, a)
    interLeaf _ _ _ = error "wrong arguments for inter leaf case"

    --  False is stronger than Unknown in dc + intersection context, so unknown comes before false
    unionLeaf c a@(_, Leaf True) b = (c, a) -- no insert needed for Leafs
    unionLeaf c a b@(_, Leaf True) = (c, b)
    unionLeaf c a@(_, Unknown) b = (c, b) -- build up the resulting cache by inserting all results
    unionLeaf c a b@(_, Unknown) = (c, a)
    unionLeaf c a@(_, Leaf False) b = (c, b) -- no cache lookup needed
    unionLeaf c a b@(_, Leaf False) = (c, a)
    unionLeaf _ _ _ = error "wrong arguments for inter leaf case"

    -- i think we can implement a "do nothing" version of catchup for Dc
    catchupA c _ = c
    catchupB c _ = c
    catchupR c _ = c 

    to_str = "Dc"

instance DdF3 Pos where
    inferNodeA f c a@(a_id, _) b@(b_id, Node positionB pos_childB neg_childB) =
        let
            (c', r) = insert c (Node positionB a_id (0,0))
            (c'', r'@(r_id, r_dd)) = f c' r b
        in applyElimRule @Pos c'' r_dd --`debug` ("inferNodeA pos : " ++ show r' ++ "\n" ++ show a ++ "\n" ++ show b)
    inferNodeA _ c a b = error_display "inferNodeA pos" c a b
    inferNodeB f c a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, _) =
        let
            (c', r) = insert c (Node positionA b_id (0,0))
            (c'', r'@(r_id, r_dd)) = f c' a r
        in applyElimRule @Pos c'' r_dd --`debug` ("inferNodeB pos : " ++ show r' ++ "\n" ++ show a ++ "\n" ++ show b)
    inferNodeB _ c a b = error_display "infernodeB pos" c a b

    applyElimRule c (EndInfNode (1,0)) = (c, ((1,0), Leaf True))
    applyElimRule c (EndInfNode (2,0)) = (c, ((2,0), Leaf False))
    applyElimRule c d@(Node _ posC (0, 0)) = (c, getNode c posC) --`debug` ("eimrule" ++ show posC)
    applyElimRule c d = insert c d

    --  Unknown is stronger than True in finite + intersection context
    -- if the result is 
    interLeaf c a@(_, Leaf False) b = (c, a) -- False might be absorbed, then return Unknown
    interLeaf c a b@(_, Leaf False) = (c, b)
    interLeaf c a@(_, Leaf True) b = (c, b) -- check if b needs to be absorbed, if b == dcA? or b == dcR at this point?
    interLeaf c a b@(_, Leaf True) = (c, a)
    interLeaf c a@(_, Unknown) b = -- resolve Unknown to see if it is a True or False or a dd, then do the above or continue with the dd 
        -- todo! if b is a node (or infnode o.O') perform dc : pos intersection 
        let (_, (dcA, _, _)) = head $ func_stack c
        in intersection'' @Pos c dcA b  --`debug` ("using dcA in interLeaf pos: " ++ show dcA)
    interLeaf c a b@(_, Unknown) =
        let (_, (_, dcB, _)) = head $ func_stack c
        in intersection'' @Pos c a dcB --`debug` ("using dcB in interLeaf pos: " ++ show dcB)
    interLeaf _ _ _ = error "wrong arguments for inter leaf case"

    --  Unknown is stronger than True in finite + union context
    -- if the result is 
    unionLeaf c a@(_, Leaf True) b = (c, a) -- True might be absorbed, then return Unknown
    unionLeaf c a b@(_, Leaf True) = (c, b)
    unionLeaf c a@(_, Leaf False) b = (c, b) -- check if b needs to be absorbed, if b == dcA? or b == dcR at this point?
    unionLeaf c a b@(_, Leaf False) = (c, a)
    unionLeaf c a@(_, Unknown) b = -- resolve Unknown to see if it is a True or False or a dd, then do the above or continue with the dd 
        -- todo! if b is a node (or infnode o.O') perform dc : pos union 
        let (_, (dcA, _, _)) = head $ func_stack c
        in union'' @Pos c dcA b  --`debug` ("using dcA in unionLeaf pos: " ++ show dcA)
    unionLeaf c a b@(_, Unknown) =
        let (_, (_, dcB, _)) = head $ func_stack c
        in union'' @Pos c a dcB --`debug` ("using dcB in unionLeaf pos: " ++ show dcB)
    unionLeaf _ _ _ = error "wrong arguments for union leaf case"

    catchupA c@Context{func_stack = (inf, ((_, Node positionA pos_childA _), b, dcR))  : fs } idx
        -- special case to go until the end
        | idx == -1 = catchupA @Pos (moveA c "pos child" "pos") idx
        -- catchup
        | idx > positionA = catchupA @Pos (moveA c "pos child" "pos") idx
        -- ending criteria
        | idx < positionA = c
        | idx == positionA = c
    -- todo case infnode
    -- in case of leaf, endinfnode  
    catchupA c@Context{func_stack = _  : fs } idx = c
    -- unknown should not be possible

    catchupB c@Context{func_stack = (inf, (a, (_, Node positionB pos_childB _ ), dcR))  : fs } idx
        | idx == -1 = catchupB @Pos (moveB c "pos child" "pos") idx
        -- catchup
        | idx > positionB = catchupB @Pos (moveB c "pos child" "pos") idx
        -- ending criteria
        | idx < positionB = c
        | idx == positionB = c
    -- todo case infnode
    -- in case of leaf, endinfnode  
    catchupB c@Context{func_stack = _  : fs } idx = c
    -- unknown should not be possible

    catchupR c@Context{func_stack = (inf, (a, (_, Node positionR pos_childR _ ), dcR))  : fs } idx
        | idx == -1 = catchupR @Pos (moveR c "pos child" "pos") idx
        -- catchup
        | idx > positionR = catchupR @Pos (moveR c "pos child" "pos") idx
        -- ending criteria
        | idx < positionR = c
        | idx == positionR = c
    -- todo case infnode
    -- in case of leaf, endinfnode  
    catchupR c@Context{func_stack = _  : fs } idx = c
    -- unknown should not be possible

    to_str = "Pos"

instance DdF3 Neg where
    inferNodeA f c a@(a_id, _) b@(b_id, Node positionB pos_childB neg_childB) =
        let
            (c', r) = insert c (Node positionB (0,0) a_id)
            (c'', r'@(r_id, r_dd)) = f c' r b
        in applyElimRule @Neg c'' r_dd --`debug` ("inferNodeA neg : " ++ show r' ++ "\n" ++ show a ++ "\n" ++ show b)
    inferNodeA _ c a b = error_display "inferNodeA neg" c a b
    inferNodeB f c a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, _) =
        let
            (c', r) = insert c (Node positionA (0,0) b_id)
            (c'', r'@(r_id, r_dd)) = f c' a r
        in applyElimRule @Neg c'' r_dd --`debug` ("inferNodeB neg : " ++ show r'++ "\n" ++ show a ++ "\n" ++ show b)
    inferNodeB _ c a b = error_display "infernodeB neg" c a b

    applyElimRule c (EndInfNode (1,0)) = (c, ((1,0), Leaf True))
    applyElimRule c (EndInfNode (2,0)) = (c, ((2,0), Leaf False))
    applyElimRule c d@(Node _ (0, 0) negC) = (c, (negC, getDd c negC))
    applyElimRule c d = insert c d

    interLeaf c a@(_, Leaf False) b = (c, a) -- (future if i want to remove absorb) False might be absorbed, then return Unknown
    interLeaf c a b@(_, Leaf False) = (c, b)
    interLeaf c a@(_, Leaf True) b = (c, b) -- (future if i want to remove absorb) check if b needs to be absorbed, if b == dcA? or b == dcR at this point?
    interLeaf c a b@(_, Leaf True) = (c, a)
    interLeaf c a@(_, Unknown) b = -- resolve Unknown to see if it is a True or False or a dd, then do the above or continue with the dd 
        let (_, (dcA, _, _)) = head $ func_stack c
        in intersection'' @Neg c dcA b  --`debug` ("using dcA in interLeaf neg: " ++ show dcA)
    interLeaf c a b@(_, Unknown) =
        let (_, (_, dcB, _)) = head $ func_stack c
        in intersection'' @Neg c a dcB  --`debug` ("using dcB in interLeaf neg: " ++ show dcB)
    interLeaf _ _ _ = error "wrong arguments for inter leaf case"

    unionLeaf c a@(_, Leaf True) b = (c, a) -- (future if i want to remove absorb) True might be absorbed, then return Unknown
    unionLeaf c a b@(_, Leaf True) = (c, b)
    unionLeaf c a@(_, Leaf False) b = (c, b) -- (future if i want to remove absorb) check if b needs to be absorbed, if b == dcA? or b == _ at this point?
    unionLeaf c a b@(_, Leaf False) = (c, a)
    unionLeaf c a@(_, Unknown) b = -- resolve Unknown to see if it is a False or True or a dd, then do the above or continue with the dd 
        let (_, (dcA, _, _)) = head $ func_stack c
        in union'' @Neg c dcA b  --`debug` ("using dcA in unionLeaf neg: " ++ show dcA)
    unionLeaf c a b@(_, Unknown) =
        let (_, (_, dcB, _)) = head $ func_stack c
        in union'' @Neg c a dcB  --`debug` ("using dcB in unionLeaf neg: " ++ show dcB)
    unionLeaf _ _ _ = error "wrong arguments for union leaf case"

    catchupA c@Context{func_stack = (inf, ((_, Node positionA _ neg_childA), b, dcR))  : fs } idx
        | idx == -1 = catchupA @Neg (moveA c "neg child" "neg") idx
        -- catchup
        | idx > positionA = catchupA @Neg (moveA c "neg child" "neg") idx
        -- ending criteria
        | idx < positionA = c
        | idx == positionA = c
    -- todo case infnode
    -- in case of leaf, endinfnode  
    catchupA c@Context{func_stack = _  : fs } idx = c
    -- unknown should not be possible

    catchupB c@Context{func_stack = (inf, (a, (_, Node positionB _ neg_childB), dcR))  : fs } idx
        | idx == -1 = catchupB @Neg (moveB c "neg child" "neg") idx
        -- catchup
        | idx > positionB = catchupB @Neg (moveB c "neg child" "neg") idx
        -- ending criteria
        | idx < positionB = c
        | idx == positionB = c
    -- todo case infnode
    -- in case of leaf, endinfnode  
    catchupB c@Context{func_stack = _  : fs } idx = c
    -- unknown should not be possible

    catchupR c@Context{func_stack = (inf, (a, (_, Node positionR _ neg_childR), dcR))  : fs } idx
        | idx == -1 = catchupR @Neg (moveR c "neg child" "neg") idx
        -- catchup
        | idx > positionR = catchupR @Neg (moveR c "neg child" "neg") idx
        -- ending criteria
        | idx < positionR = c
        | idx == positionR = c
    -- todo case infnode
    -- in case of leaf, endinfnode  
    catchupR c@Context{func_stack = _  : fs } idx = c
    -- unknown should not be possible

    to_str = "Neg"

class All a where
    error_display :: String -> Context -> Node -> Node -> a
    error_display s c (a_id, a) (b_id, b) = error (show s ++ " : " ++ show c ++ ", " ++ show a ++ ", " ++ show b)

instance All (Context, Node)

func_tail :: String -> Context -> Context
func_tail s c@Context{func_stack = _ : fs } =
    if s == "Dc" then c else c{func_stack = fs} --`debug` "applying func_tail"
func_tail s c@Context{func_stack = [] } = 
    if s == "Dc" then c else error "func_tail should not be called on an empty func_stack"

func_alt :: String -> Context -> (Inf, (Node,Node, Node)) -> Context
func_alt s c@Context{func_stack = _ : fs } alt_head =
    if s == "Dc" then c else c{func_stack = alt_head : fs} --`debug` "applying func_alt"
func_alt s c@Context{func_stack = [] } alt_head = 
    if s == "Dc" then c else c{func_stack = [alt_head]} --`debug` "applying func_alt"

-- Combined helper function: Processes a single Node based on the move string.
-- Takes the specific node to process and returns the new Node resulting from the move.
processStackElement :: Context -> String -> String -> Node -> Node
processStackElement c m t node =
    case node of -- Pattern match directly on the Node structure passed in
        (_, Node position pos_child neg_child) -> -- Use generic pattern variable names
            if m == "pos child" then getNode c pos_child
            else if m == "neg child" then getNode c neg_child
            -- Add conditions for "neginf", "posinf" if needed
            else error $ "processStackElement: undefined move '" ++ m ++ "' for Node pattern: " ++ show node

        (_, EndInfNode child) ->
            if m == "endinf" then getNode c child
            else error $ "processStackElement: undefined move '" ++ m ++ "' for EndInfNode pattern: " ++ show node

        (_, InfNodes position dc p n) ->
            if m == "inf pos" then getNode c p
            else if m == "inf ned" then getNode c n
            else if m == "inf dc" then getNode c dc
            else error $ "processStackElement: undefined move '" ++ m ++ "' for InfNodes pattern: " ++ show node

        -- Add cases for any other constructors of Node if they exist
        _ -> error $ "processStackElement: Unhandled Node pattern: " ++ show node


moveA :: Context -> String -> String -> Context
moveA c m t
  | null (func_stack c) = c -- Nothing to do if the stack is empty
  | otherwise =
      let
          -- This function is applied to each element of the func_stack
          updateElementForA :: (Inf, (Node, Node, Node)) -> (Inf, (Node, Node, Node))
          updateElementForA (inf, (a, b, r)) =
              let new_a = processStackElement c m t a -- Call the common helper on 'a'
              in (inf, (new_a, b, r)) -- Construct the result tuple with the modified 'a'
          
          new_func_stack = map updateElementForA (func_stack c)
      in c { func_stack = new_func_stack }
      -- Optional trace: trace ("moveA processed stack...") $ ...


moveB :: Context -> String -> String -> Context
moveB c m t
  | null (func_stack c) = c -- Nothing to do if the stack is empty
  | otherwise =
      let
          -- This function is applied to each element of the func_stack
          updateElementForB :: (Inf, (Node, Node, Node)) -> (Inf, (Node, Node, Node))
          updateElementForB (inf, (a, b, r)) =
              let new_b = processStackElement c m t b -- Call the common helper on 'b'
              in (inf, (a, new_b, r)) -- Construct the result tuple with the modified 'b'

          new_func_stack = map updateElementForB (func_stack c)
      in c { func_stack = new_func_stack }
      -- Optional trace: trace ("moveB processed stack...") $ ...

moveR :: Context -> String -> String -> Context
moveR c m t
  | null (func_stack c) = c -- Nothing to do if the stack is empty
  | otherwise =
      let
          -- This function is applied to each element of the func_stack
          updateElementForB :: (Inf, (Node, Node, Node)) -> (Inf, (Node, Node, Node))
          updateElementForB (inf, (a, b, r)) =
              let new_r = processStackElement c m t r -- Call the common helper on 'b'
              in (inf, (a, b, new_r)) -- Construct the result tuple with the modified 'b'

          new_func_stack = map updateElementForB (func_stack c)
      in c { func_stack = new_func_stack }
      -- Optional trace: trace ("moveB processed stack...") $ ...

-- update_func_stack :: String -> Int -> Context -> Context
-- update_func_stack s idx c@Context{func_stack = fl} = traverse_dcB s idx (traverse_dcA s idx c)
-- todo map over full func_stack


data Component = CompA | CompB | CompR


class Dd1_helper a where
    traverse_dc :: String -> Context -> NodeId -> NodeId -> Context
    getComponentFuncs :: Dd1 a => Component -> ( (Inf, (Node, Node, Node)) -> Node -- getter
                                           , Context -> String -> String -> Context -- mover
                                           , Context -> Int -> Context -- catchuper
                                           , String -- component string label
                                           )
    traverse_dc_generic :: Component -> String -> Context -> Node -> Context
    applyInf :: Context -> String -> Node -> Node -> (Context, Node)
    applyInf' :: Context -> String -> Node -> Node -> (Context, Node)


instance (DdF3 a) => Dd1_helper a where
    -- apply traversal
    applyInf :: Context -> String ->  Node -> Node -> (Context, Node)
    applyInf c s a b = debug_manipulation (applyInf' @a c s a b) s "applyInf" c a b

    applyInf' :: Context -> String -> Node -> Node -> (Context, Node)
    applyInf' c s a@(a_id, InfNodes positionA dcA pA nA) b@(b_id, InfNodes positionB dcB pB nB)
        | positionA == positionB =  if s == "intersection" then
            let
                -- if there is an above layer
                -- update func stack so its dc's are on the same level as a and b (if not in dc context) 
                c_ = if func_stack c == [] then c else 
                    traverse_dc @a "inf" c a_id b_id
                
                (c1, dcR) = intersection @Dc c_ dcA dcB

                -- to remeber the dcA and dcB specifically for this neg intersection call, we place them on the func stack
                -- whenever, in this call, encountering (endinfnode) it should be taken off the func stack
                c2_ = c1{func_stack = (Neg, (getNode c1 dcA, getNode c1 dcB, dcR)) : func_stack c1}  
                (c2, nR) =
                    let (c2', r2') = intersection @Neg c2_ nA nB
                    in absorb'' @Neg c2' r2' dcR

                -- todo ugly type specification from func_tail here, inside intersection we wan to skip on Dc.. 
                c3_ = c2{func_stack = (Pos, (getNode c1 dcA, getNode c1 dcB, dcR)) : func_stack (func_tail "" c2)}
                (c3, pR) =
                    let (c3', r3') = intersection @Pos c3_ pA pB
                    in absorb'' @Pos c3' r3' dcR

                c4 = func_tail (to_str @a) c3 --remove the func_stack layer
            in apply_elimRule c4 $ InfNodes positionA (fst dcR) (fst pR) (fst nR)

            else let
                -- if there is an above layer
                -- update func stack so its dc's are on the same level as a and b (if not in dc context) 
                c_ = if func_stack c == [] then c else 
                    traverse_dc @a "inf" c a_id b_id
                
                (c1, dcR) = union @Dc c_ dcA dcB

                -- to remeber the dcA and dcB specifically for this neg union call, we place them on the func stack
                -- whenever, in this call, encountering (endinfnode) it should be taken off the func stack
                c2_ = c1{func_stack = (Neg, (getNode c1 dcA, getNode c1 dcB, dcR)) : func_stack c1}  
                (c2, nR) =
                    let (c2', r2') = union @Neg c2_ nA nB
                    in absorb'' @Neg c2' r2' dcR

                -- todo ugly type specification from func_tail here, inside union we wan to skip on Dc.. 
                c3_ = c2{func_stack = (Pos, (getNode c1 dcA, getNode c1 dcB, dcR)) : func_stack (func_tail "" c2)}
                (c3, pR) =
                    let (c3', r3') = union @Pos c3_ pA pB
                    in absorb'' @Pos c3' r3' dcR

                c4 = func_tail (to_str @a) c3 --remove the func_stack layer
            in apply_elimRule c4 $ InfNodes positionA (fst dcR) (fst pR) (fst nR)

        | positionA > positionB = applyInfA @a c s a b
        | positionA < positionB = applyInfB @a c s a b
        where
            apply_elimRule c' (InfNodes _ (1,0) (0,0) (0,0)) = (c', ((1,0), Leaf True))
            apply_elimRule c' (InfNodes _ (2,0) (0,0) (0,0)) = (c', ((2,0), Leaf False))
            apply_elimRule c' (InfNodes _ (0,0) (0,0) (0,0)) = (c', ((0,0), Unknown))
            apply_elimRule c' d@(InfNodes _ consq (0,0) (0,0)) = case getDd c' consq of 
                EndInfNode d' -> (c', getNode c' d')
                _ -> insert c' d
            apply_elimRule c' d = insert c' d
    applyInf' c s a b = error_display "apply inf" c a b

    traverse_dc s c a b = if to_str @a == "Dc" then c else traverse_dc_generic @a CompB s (traverse_dc_generic @a CompA s c (getNode c a)) (getNode c b)

    
    traverse_dc_generic component s c refNode
        | null (func_stack c) = c -- Should not happen if called from A/B/R defaults, but good practice
        | otherwise =
            let headElement@(inf, _) = head (func_stack c)
                fs = tail (func_stack c)
                (getter, mover, catchuper, compStr) = getComponentFuncs @a component -- Get functions for A, B, or R
                targetNode = getter headElement -- Get the Node (a, b, or r) we are currently traversing
            in
            case (targetNode, refNode) of
                -- Main Node vs Node comparison logic
                ( tNode@(_, Node position _ _), rNode@(_, Node idx _ _) ) ->
                    if | position > idx -> c -- Target is ahead, do nothing
                        | position == idx -> mover c s (to_str @a) -- Positions match, move
                        | position < idx -> traverse_dc_generic @a component s (catchuper c idx) refNode -- Target behind, catchup then recurse

                -- Target Node vs Leaf/EndInfNode (Target needs to catch up fully)
                ( (_, Node{}), (_, Leaf _) )         -> catchuper c (-1) -- Use -1 to signify catch up fully
                ( (_, Node{}), rNode@(_, EndInfNode{}) ) -> traverse_dc_generic @a component s (catchuper c (-1)) rNode -- Catch up fully, then re-evaluate with EndInfNode

                -- Both EndInfNode
                ( (_, EndInfNode{}), (_, EndInfNode{}) ) ->
                    if s == "endinf" then mover c "endinf" (to_str @a) else c -- Perform endinf move or no-op

                -- Base cases where target is already at EndInfNode or Leaf (usually no-op for traversal)
                ( (_, EndInfNode{}), (_, Leaf{}) )      -> c
                ( (_, Leaf{}),       (_, Leaf{}) )      -> c
                ( (_, Leaf{}),       (_, EndInfNode{}) ) -> c

                -- Base cases where target is EndInfNode/Leaf and refNode is Node (target is "ahead")
                ( (_, EndInfNode{}), (_, Node idx _ _) ) -> c
                ( (_, Leaf _),       (_, Node idx _ _) ) -> c

                -- Handle Unknown reference node
                ( _, (_, Unknown) ) -> c

                -- Handle InfNodes (using placeholder undefined for logic - needs careful implementation)
                ( (_, InfNodes{}), (_, InfNodes idx dc p n) ) -> undefined -- Add specific logic using mover/catchuper
                ( (_, InfNodes{}), rNode@(_, Node idx _ _) )  -> undefined -- Add specific logic
                ( (_, EndInfNode{}), (_, InfNodes idx dc p n) ) -> undefined -- Add specific logic
                ( (_, InfNodes{}), (_, Leaf{}) )           -> undefined -- Add specific logic

                -- Error case for unhandled patterns
                ( t, r ) -> error $ "traverse_dc_generic (" ++ compStr ++ ") unhandled. targetNode=" ++ show t ++ " refNode=" ++ show r ++ " c=" ++ show (func_stack c) ++ " s=" ++ s

    getComponentFuncs :: Component -> ( (Inf, (Node, Node, Node)) -> Node -- getter
                                           , Context -> String -> String -> Context -- mover
                                           , Context -> Int -> Context -- catchuper
                                           , String -- component string label
                                           )
    getComponentFuncs CompA = ( (\(_, (a, _, _)) -> a), moveA, catchupA @a, "A" )
    getComponentFuncs CompB = ( (\(_, (_, b, _)) -> b), moveB, catchupB @a, "B" )
    getComponentFuncs CompR = ( (\(_, (_, _, r)) -> r), moveR, catchupR @a, "R" ) -- Requires catchupR @a
