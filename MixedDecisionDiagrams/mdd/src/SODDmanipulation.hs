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

import DrawMDD (debug_manipulation, debug_dc_traverse)
import Data.Bimap ()

type DdManipulation = Context -> Node -> Node -> (Context, Node)
type DdManipulation' = Context -> String -> Node -> Node -> (Context, Node)

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
    intersection_leaf_cases :: Context -> Node -> Node -> (Context, Node)
    union_leaf_cases :: Context -> Node -> Node -> (Context, Node)
    apply :: Context -> String -> NodeId -> NodeId -> (Context, Node)
    apply'' :: Context -> String -> Node -> Node -> (Context, Node)
    intersectionDc :: Context -> NodeId -> NodeId -> (Context, Node)
    intersectionDc'' :: Context -> Node -> Node -> (Context, Node)
    unionDc :: Context -> NodeId -> NodeId -> (Context, Node)
    unionDc'' :: Context -> Node -> Node -> (Context, Node)

    apply' :: Context -> String -> Node -> Node -> (Context, Node)
    intersectionDc' :: Context -> Node -> Node -> (Context, Node)
    unionDc' :: Context -> Node -> Node -> (Context, Node)



instance (DdF3 a) => Dd1 a where
    apply c s a b = debug_manipulation  (apply' @a c s (getNode c a) (getNode c b)) s (s ++ to_str @a) c (getNode c a) (getNode c b)
    apply'' c s a b = debug_manipulation  (apply' @a c s a b) s (s ++ "==" ++ to_str @a) c a b

    apply' c s a@(_, Leaf _) b = if s == "union" 
        then union_leaf_cases @a c a b
        else intersection_leaf_cases @a c a b
    apply' c s a b@(_, Leaf _) = if s == "union" 
        then union_leaf_cases @a c a b
        else intersection_leaf_cases @a c a b
    apply' c s a@(_, Unknown) b = if s == "union" 
        then union_leaf_cases @a c a b
        else intersection_leaf_cases @a c a b
    apply' c s a b@(_, Unknown) = if s == "union" 
        then union_leaf_cases @a c a b
        else intersection_leaf_cases @a c a b

    apply' c s a@(a_id, EndInfNode _) b@(b_id, Node idx _ _) = withCache c (a, b, s) $ applyElimRule' @a (inferNodeA' @a (apply'' @a) c s a b)
    apply' c s a@(a_id, Node{}) b@(b_id, EndInfNode _) = withCache c (a, b, s) $ applyElimRule' @a (inferNodeB' @a (apply'' @a) c s a b)
    apply' c@Context{func_stack = current : prev@(inf, n) : fs} s a@(a_id, EndInfNode ac) b@(b_id, EndInfNode bc) = withCache c (a, b, s) $
        let c' = traverse_dc @a "endinf" c a_id b_id
            (c'', (r, _)) = case inf of
                Dc -> apply @Dc c' s ac bc
                Neg -> apply @Neg c' s ac bc
                Pos -> apply @Pos c' s ac bc
        in absorb $ insert c''{func_stack = prev : fs} $ EndInfNode r -- context passback manners?

    apply' c@Context{func_stack = fs} s a@(a_id, Node positionA pos_childA neg_childA)  b@(b_id, Node positionB pos_childB neg_childB)
        -- Match
        | positionA == positionB =
            let c_ = traverse_dc @a "pos child" c pos_childA pos_childB
                (c', (pos_result, _)) = apply @a c_ s pos_childA pos_childB

                c_' = traverse_dc @a "neg child" c'{func_stack = fs} neg_childA neg_childB
                (c'', (neg_result, _)) = apply @a c_' s neg_childA neg_childB
            in withCache c (a, b, s) $ applyElimRule @a c''{func_stack = fs} (Node positionA pos_result neg_result)
        -- Mismatch, highest position gets an inferred node at position of the lowest
        | positionA < positionB = applyElimRule' @a (inferNodeB' @a (apply'' @a) c s a b)
        | positionA > positionB = applyElimRule' @a (inferNodeA' @a (apply'' @a) c s a b)

    -- -- entering new domains
    apply' c s a@(a_id, InfNodes positionA _ _ _) b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB = withCache c (a, b, s) $
                applyElimRule' @a (inferNodeA' @a (apply'' @a) c s a b)
        -- | positionA < positionB = withCache c (a, b, s) $
        --         applyInfB c s a b 
    apply' c s a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
    --     | positionA > positionB = withCache c (a, b, s) $
    --             applyInfA s a b
        | positionA < positionB = withCache c (a, b, s) $
                applyElimRule' @a (inferNodeB' @a (apply'' @a) c s a b)
    apply' c s a@(a_id, InfNodes positionA _ _ _)  b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = applyInf @a c s a b
        | positionA < positionB = applyInfB @a c s a b
        | positionA > positionB = applyInfA @a c s a b
    apply' c s a@(a_id, EndInfNode _) b@(b_id, InfNodes{}) = withCache c (a, b, s) $ applyInfA @a c s a b
    apply' c s a@(a_id, InfNodes{}) b@(b_id, EndInfNode _) = withCache c (a, b, s) $ applyInfB @a c s a b

-- | ======================== DC versions ========================
    -- b is of dc type
    -- thus applyElimRule' @a (inferNodeB has Dc
    -- this version is designed not to be working with recursion yet (generalized refactored version needed)
    -- Unknown handeling should be different. 

    unionDc c a b = debug_manipulation  (unionDc' @a c (getNode c a) (getNode c b)) "unionDc" ("unionDc" ++ to_str @a) c (getNode c a) (getNode c b)
    unionDc'' c a b = debug_manipulation  (unionDc' @a c a b) "unionDc" ("unionDc==" ++ to_str @a) c a b

    -- unionDc node cases
    unionDc' c a@(_, Leaf True) b@(_, Node{}) = withCache c (a, b, "unionDc") $ applyElimRule' @a (inferNodeA @a (unionDc'' @a) c a b )
    unionDc' c a@(_, Node{}) b@(_, Leaf True) = withCache c (a, b, "unionDc") $ applyElimRule' @a (inferNodeB @Dc (unionDc'' @a) c a b )
    unionDc' c a@(_, Leaf False) b@(_, Node{}) = withCache c (a, b, "unionDc") $ applyElimRule' @a (inferNodeA @a (unionDc'' @a) c a b )
    unionDc' c a@(_, Node{}) b@(_, Leaf False) = withCache c (a, b, "unionDc") $ applyElimRule' @a (inferNodeB @Dc (unionDc'' @a) c a b )
    -- todo add endinfnode 
    -- todo add infnode 

    --  Unknown is stronger than True in finite + unionDc context    
    unionDc' c a@(_, Leaf True) b = absorb (c, a) -- True might be absorbed, then return Unknown
    unionDc' c a b@(_, Leaf True) = absorb (c, b)
    unionDc' c a@(_, Leaf False) b = absorb (c, b) -- check if b needs to be absorbed, if b == dcA? or b == dcR at this point?
    unionDc' c a b@(_, Leaf False) = absorb (c, a)
    unionDc' c a@(_, Unknown) b@(_, Unknown) = (c , a)
    unionDc' c a@(_, Unknown) b = (c, a) -- when having to replace a Unknown when already in a Dc traversal we will be comparing a DcA branch with a DcB branch.. which has already been calculated in dcR, therefor we known for sure it will be absorbed by dcR
    unionDc' c a b@(_, Unknown) = undefined

    unionDc' c a@(a_id, EndInfNode _) b@(b_id, Node idx _ _) = withCache c (a, b, "unionDc") $ applyElimRule' @a (inferNodeA @a (unionDc'' @a) c a b)
    unionDc' c a@(a_id, Node{}) b@(b_id, EndInfNode _) = withCache c (a, b, "unionDc") $ applyElimRule' @a (inferNodeB @Dc (unionDc'' @a) c a b)
    unionDc' c@Context{func_stack = f : fs} a@(a_id, EndInfNode ac) b@(b_id, EndInfNode bc) = withCache c (a, b, "unionDc") $
        let c' = traverse_dc @a "endinf" c a_id b_id
            -- at the end of local dc - pos/neg traversal, continue with the non dc traversal
            (c'', (r, _)) = apply @a c'{func_stack = fs} "union" ac bc
        in absorb $ insert c''{func_stack = f:fs} $ EndInfNode r

    unionDc' c@Context{func_stack = fs} a@(a_id, Node positionA pos_childA neg_childA)  b@(b_id, Node positionB pos_childB neg_childB)
        -- Match
        | positionA == positionB =
            let c_ = traverse_dc @a "pos child" c pos_childA pos_childB
                (c', (pos_result, _)) = unionDc @a c_ pos_childA pos_childB

                c_' = traverse_dc @a "neg child" c'{func_stack = fs} neg_childA neg_childB
                (c'', (neg_result, _)) = unionDc @a c_' neg_childA neg_childB
            in withCache c (a, b, "unionDc") $ applyElimRule @a c''{func_stack = fs} (Node positionA pos_result neg_result)
        -- Mismatch, highest position gets an inferred node at position of the lowest
        | positionA < positionB = applyElimRule' @a (inferNodeB @Dc (unionDc'' @a) c a b)
        | positionA > positionB = applyElimRule' @a (inferNodeA @a (unionDc'' @a) c a b)

    -- -- entering new domains
    unionDc' c a@(a_id, InfNodes positionA _ _ _) b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB = withCache c (a, b, "unionDc") $
                applyElimRule' @a (inferNodeA @a (unionDc'' @a) c a b)
        -- | positionA < positionB = withCache c (a, b, "unionDc") $
        --         applyElimRule @a $ applyInfB a b 
    unionDc' c a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
    --     | positionA > positionB = withCache c (a, b, "unionDc") $
    --             applyElimRule @a $ applyInfA a b
        | positionA < positionB = withCache c (a, b, "unionDc") $
                applyElimRule' @a (inferNodeB @Dc (unionDc'' @a) c a b)
    unionDc' c a@(a_id, InfNodes positionA _ _ _)  b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = applyInf @a c "unionDc" a b
        | positionA < positionB = applyInfB @a c "unionDc" a b
        | positionA > positionB = applyInfA @a c "unionDc" a b
    unionDc' c a@(a_id, EndInfNode _) b@(b_id, InfNodes{}) = withCache c (a, b, "unionDc") $ applyInfA @a c "unionDc" a b
    unionDc' c a@(a_id, InfNodes{}) b@(b_id, EndInfNode _) = withCache c (a, b, "unionDc") $ applyInfB @a c "unionDc" a b

    intersectionDc c a b = debug_manipulation  (intersectionDc' @a c (getNode c a) (getNode c b)) "interDc" ("interDc" ++ to_str @a) c (getNode c a) (getNode c b)
    intersectionDc'' c a b = debug_manipulation  (intersectionDc' @a c a b) "interDc" ("intersectionDc==" ++ to_str @a) c a b

        -- infer node cases
    intersectionDc' c a@(_, Leaf False) b@(_, Node{}) = withCache c (a, b, "interDc") $ applyElimRule' @a (inferNodeA @a (intersectionDc'' @a) c a b )
    intersectionDc' c a@(_, Node{}) b@(_, Leaf False) = withCache c (a, b, "interDc") $ applyElimRule' @a (inferNodeB @Dc (intersectionDc'' @a) c a b )
    intersectionDc' c a@(_, Leaf True) b@(_, Node{}) = withCache c (a, b, "interDc") $ applyElimRule' @a (inferNodeA @a (intersectionDc'' @a) c a b )
    intersectionDc' c a@(_, Node{}) b@(_, Leaf True) = withCache c (a, b, "interDc") $ applyElimRule' @a (inferNodeB @Dc (intersectionDc'' @a) c a b) `debug` "infer dc node? "
    -- todo add endinfnode 
    -- todo add infnode 

    --  Unknown is stronger than True in finite + intersectionDc context
    -- if the result is 
    intersectionDc' c a@(_, Leaf False) b = absorb (c, a) -- False might be absorbed, then return Unknown
    intersectionDc' c a b@(_, Leaf False) = absorb (c, b)
    intersectionDc' c a@(_, Leaf True) b = absorb (c, b) -- check if b needs to be absorbed, if b == dcA? or b == dcR at this point?
    intersectionDc' c a b@(_, Leaf True) = absorb (c, a)
    intersectionDc' c a@(_, Unknown) b@(_, Unknown) = (c , a)
    intersectionDc' c a@(_, Unknown) b = (c, a) -- when having to replace a Unknown when already in a Dc traversal we will be comparing a DcA branch with a DcB branch.. which has already been calculated in dcR, therefor we known for sure it will be absorbed by dcR
    intersectionDc' c a b@(_, Unknown) = undefined

    intersectionDc' c a@(a_id, EndInfNode _) b@(b_id, Node idx _ _) = withCache c (a, b, "interDc") $ applyElimRule' @a (inferNodeA @a (intersectionDc'' @a) c a b)
    intersectionDc' c a@(a_id, Node{}) b@(b_id, EndInfNode _) = withCache c (a, b, "interDc") $ applyElimRule' @a (inferNodeB @Dc (intersectionDc'' @a) c a b)
    intersectionDc' c@Context{func_stack = f : fs} a@(a_id, EndInfNode ac) b@(b_id, EndInfNode bc) = withCache c (a, b, "interDc") $
        let c' = traverse_dc @a "endinf" c a_id b_id
            (c'', (r, _)) = apply @a c'{func_stack = fs} "inter" ac bc
        in absorb $ insert c''{func_stack = f:fs} $ EndInfNode r

    intersectionDc' c@Context{func_stack = fs} a@(a_id, Node positionA pos_childA neg_childA)  b@(b_id, Node positionB pos_childB neg_childB)
        -- Match
        | positionA == positionB =
            let c_ = traverse_dc @a "pos child" c pos_childA pos_childB
                (c', (pos_result, _)) = intersectionDc @a c_ pos_childA pos_childB

                c_' = traverse_dc @a "neg child" c'{func_stack = fs} neg_childA neg_childB
                (c'', (neg_result, _)) = intersectionDc @a c_' neg_childA neg_childB
            in withCache c (a, b, "interDc") $ applyElimRule @a c''{func_stack = fs} (Node positionA pos_result neg_result) --`debug` ("pos: " ++ (show pos_result) ++ ", neg : "  ++ (show neg_result) ++ " \n prefinal:  " ++ (show $ (Node positionA pos_result neg_result)) ++ " \n final:  " ++ (show $ applyElimRule @a c'' (Node positionA pos_result neg_result)))
        -- Mismatch, highest position gets an inferred node at position of the lowest
        | positionA < positionB = applyElimRule' @a (inferNodeB @Dc (intersectionDc'' @a) c a b)
        | positionA > positionB = applyElimRule' @a (inferNodeA @a (intersectionDc'' @a) c a b)

    -- -- entering new domains
    intersectionDc' c a@(a_id, InfNodes positionA _ _ _) b@(b_id, Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB = withCache c (a, b, "interDc") $
                applyElimRule' @a (inferNodeA @a (intersectionDc'' @a) c a b)
        -- | positionA < positionB = withCache c (a, b, "interDc") $
        --         applyElimRule @a $ applyInfB a b 
    intersectionDc' c a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
    --     | positionA > positionB = withCache c (a, b, "interDc") $
    --             applyElimRule @a $ applyInfA a b
        | positionA < positionB = withCache c (a, b, "interDc") $
                applyElimRule' @a (inferNodeB @Dc (intersectionDc'' @a) c a b)
    intersectionDc' c a@(a_id, InfNodes positionA _ _ _)  b@(b_id, InfNodes positionB _ _ _)
        | positionA == positionB = applyInf @a c "intersectionDc" a b
        | positionA < positionB = applyInfB @a c "intersectionDc" a b
        | positionA > positionB = applyInfA @a c "intersectionDc" a b
    intersectionDc' c a@(a_id, EndInfNode _) b@(b_id, InfNodes{}) = withCache c (a, b, "interDc") $ applyInfA @a c "intersectionDc" a b
    intersectionDc' c a@(a_id, InfNodes{}) b@(b_id, EndInfNode _) = withCache c (a, b, "interDc") $ applyInfB @a c "intersectionDc" a b



    -- infer node cases
    intersection_leaf_cases c a@(_, Leaf False) b@(_, Node{}) = withCache c (a, b, "inter") $ applyElimRule' @a (inferNodeA' @a (apply'' @a) c "inter" a b )
    intersection_leaf_cases c a@(_, Node{}) b@(_, Leaf False) = withCache c (a, b, "inter") $ applyElimRule' @a (inferNodeB' @a (apply'' @a) c "inter" a b )
    intersection_leaf_cases c a@(_, Leaf True) b@(_, Node{}) = withCache c (a, b, "inter") $ applyElimRule' @a (inferNodeA' @a (apply'' @a) c "inter" a b )
    intersection_leaf_cases c a@(_, Node{}) b@(_, Leaf True) = withCache c (a, b, "inter") $ applyElimRule' @a (inferNodeB' @a (apply'' @a) c "inter" a b )
    -- todo add endinfnode 
    -- todo add infnode 

    --  Unknown is stronger than True in finite + intersection context
    -- if the result is 
    intersection_leaf_cases c a@(_, Leaf False) b = absorb (c, a) -- False might be absorbed, then return Unknown
    intersection_leaf_cases c a b@(_, Leaf False) = absorb (c, b)
    intersection_leaf_cases c a@(_, Leaf True) b = absorb (c, b) -- check if b needs to be absorbed, if b == dcA? or b == dcR at this point?
    intersection_leaf_cases c a b@(_, Leaf True) = absorb (c, a)
    intersection_leaf_cases c a@(_, Unknown) b@(_, Unknown) = (c , a)
    intersection_leaf_cases c a@(_, Unknown) b = -- resolve Unknown to see if it is a True or False or a dd, then do the above or continue with the dd 
        -- todo! if b is a node (or infnode o.O') perform dc : pos intersection 
        let (_, (dcA, _, _)) = head $ func_stack c
        in intersectionDc'' @a c b dcA  --`debug` ("using dcA to replace Unknown: " ++ show dcA)
    intersection_leaf_cases c a b@(_, Unknown) =
        let (_, (_, dcB, _)) = head $ func_stack c
        in intersectionDc'' @a c a dcB -- `debug` ("using dcB to replace Unknown: " ++ show dcB)


    -- union node cases
    union_leaf_cases c a@(_, Leaf True) b@(_, Node{}) = withCache c (a, b, "union") $ applyElimRule' @a (inferNodeA' @a (apply'' @a) c "union" a b)
    union_leaf_cases c a@(_, Node{}) b@(_, Leaf True) = withCache c (a, b, "union") $ applyElimRule' @a (inferNodeB' @a (apply'' @a) c "union" a b )
    union_leaf_cases c a@(_, Leaf False) b@(_, Node{}) = withCache c (a, b, "union") $ applyElimRule' @a (inferNodeA' @a (apply'' @a) c "union" a b )
    union_leaf_cases c a@(_, Node{}) b@(_, Leaf False) = withCache c (a, b, "union") $ applyElimRule' @a (inferNodeB' @a (apply'' @a) c "union" a b )
    -- todo add endinfnode 
    -- todo add infnode 

    --  Unknown is stronger than True in finite + union context    
    union_leaf_cases c a@(_, Leaf True) b = absorb (c, a) -- True might be absorbed, then return Unknown
    union_leaf_cases c a b@(_, Leaf True) = absorb (c, b)
    union_leaf_cases c a@(_, Leaf False) b = absorb (c, b) -- check if b needs to be absorbed, if b == dcA? or b == dcR at this point?
    union_leaf_cases c a b@(_, Leaf False) = absorb (c, a)
    union_leaf_cases c a@(_, Unknown) b@(_, Unknown) = (c , a)
    union_leaf_cases c a@(_, Unknown) b = -- resolve Unknown to see if it is a True or False or a dd, then do the above or continue with the dd 
        -- todo! if b is a node (or infnode o.O') perform dc : pos union 
        let (_, (dcA, _, _)) = head $ func_stack c
        in unionDc'' @a c b dcA  -- `debug` ("using dcA to replace Unknown : " ++ show dcA)
    union_leaf_cases c a b@(_, Unknown) =
        let (_, (_, dcB, _)) = head $ func_stack c
        in unionDc'' @a c a dcB -- `debug` ("using dcB to replace Unknown : " ++ show dcB)


type DdF3 :: Inf -> Constraint
type Dd1 :: Inf -> Constraint

class DdF3 a where
    inferNodeA :: DdManipulation -> Context -> Node -> Node -> (Context, Dd)
    inferNodeB :: DdManipulation -> Context -> Node -> Node -> (Context, Dd)
    inferNodeB' :: DdManipulation' -> Context -> String -> Node -> Node -> (Context, Dd)
    inferNodeA' :: DdManipulation' -> Context -> String -> Node -> Node -> (Context, Dd)
    applyElimRule :: Context -> Dd -> (Context, Node)
    applyElimRule' :: (Context, Dd) -> (Context, Node)
    applyInfA :: Context -> String -> Node -> Node -> (Context, Node)
    applyInfB :: Context -> String -> Node -> Node -> (Context, Node)
    to_str :: String
    -- interLeaf :: Context -> Node -> Node -> (Context, Node)
    -- unionLeaf :: Context -> Node -> Node -> (Context, Node)
    catchup :: String -> Context -> Node -> Int -> Node


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
            (c', (r_id, _)) = insert c $ EndInfNode  a_id
            (c'', r') = insert c' $ InfNodes positionB r_id (0,0) (0,0)
        in applyInf @Dc c'' s r' b
    applyInfB c s a@(_, InfNodes positionA _ _ _) b@(b_id, _) = let
            (c', (r_id, _)) = insert c $ EndInfNode b_id
            (c'', r') = insert c' $ InfNodes positionA r_id (0,0) (0,0)
        in applyInf @Dc c'' s a r'

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
            (c', r) = insert c (Node positionB (0,0) a_id)
            (c'', r'@(r_id, r_dd)) = f c' s r b
        in (c'', r_dd) 
    inferNodeB' f c s a@(a_id, Node positionA pos_childA neg_childA) b@(b_id, _) =
        let
            (c', r) = insert c (Node positionA (0,0) b_id)
            (c'', r'@(r_id, r_dd)) = f c' s a r
        in (c'', r_dd)
    
    applyElimRule c d@(Node _ posC (0, 0)) = (c, getNode c posC) 
    applyElimRule c d = applyElimRule_general c d

    applyElimRule' (c, d@(Node _ posC (0, 0))) = (c, getNode c posC) 
    applyElimRule' (c, d) = applyElimRule'_general (c, d)

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

    applyElimRule c d@(Node _ (0, 0) negC) = (c, (negC, getDd c negC))
    applyElimRule c d = applyElimRule_general c d

    applyElimRule' (c, d@(Node _ (0, 0) negC)) = (c, (negC, getDd c negC))
    applyElimRule' (c, d) = applyElimRule'_general (c, d)

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

applyElimRule_general :: Context -> Dd -> (Context, Node)
applyElimRule_general c (EndInfNode (1,0)) = (c, ((1,0), Leaf True))
applyElimRule_general c (EndInfNode (2,0)) = (c, ((2,0), Leaf False))
applyElimRule_general c (InfNodes _ (1,0) (0,0) (0,0)) = (c, ((1,0), Leaf True))
applyElimRule_general c (InfNodes _ (2,0) (0,0) (0,0)) = (c, ((2,0), Leaf False))
applyElimRule_general c (InfNodes _ (0,0) (0,0) (0,0)) = (c, ((0,0), Unknown))
applyElimRule_general c d = insert c d

applyElimRule'_general :: (Context, Dd) -> (Context, Node)
applyElimRule'_general (c, (EndInfNode (1,0))) = (c, ((1,0), Leaf True))
applyElimRule'_general (c, (EndInfNode (2,0))) = (c, ((2,0), Leaf False))
applyElimRule'_general (c, d) = insert c d

absorb :: (Context, Node) -> (Context, Node)
absorb (c@Context{func_stack = (inf, (_, _, dcR))  : fs }, n@(id, d)) = absorb' (c, n) -- `debug` ("absorb check on node : " ++ (show n) ++ "\n with dcR :" ++ (show dcR) ++ "\n fs tail : " ++ show fs)
absorb (c, n) = absorb' (c, n)

absorb' :: (Context, Node) -> (Context, Node)
-- | given a dcR and a pos or ng results, sets sub-paths in the local inf-domain which agree with the dcR to unknown ("absorbing them")   
absorb' (c@Context{func_stack = (inf, (_, _, dc@(_, Unknown)))  : fs }, a)  = (c, a)
absorb' (c@Context{func_stack = (inf, (_, _, dc))  : fs }, a@(_, Unknown)) = (c, a)
absorb' (c@Context{func_stack = (inf, (_, _, dc))  : fs }, a@(_, Leaf _))
    | a == dc = (c, ((0,0), Unknown))
    | otherwise = (c,a)
absorb' (c@Context{func_stack = (inf, (_, _, dc@(_, Leaf _)))  : fs }, a@(_, InfNodes {}))  = (c, a)
absorb' (c@Context{func_stack = (inf, (_, _, dc@(_, Leaf _)))  : fs }, a@(_, EndInfNode a_child))   = if getNode c a_child == dc then (c, ((0,0), Unknown)) else (c, a)
absorb' (c@Context{func_stack = (inf, (_, _, dc@(_, EndInfNode dc')))  : fs }, a@(_, EndInfNode a'))
    | a' == dc' = (c, ((0,0), Unknown))
    | otherwise = (c,a)
absorb' (c@Context{func_stack = (inf, (_, _, dc))  : fs }, a)
    | a == dc = (c, ((0,0), Unknown))
    | otherwise = (c,a)
absorb' (c@Context{func_stack = [] }, a) = (c, a)
-- absorb' (c@Context{func_stack = fs }, a) = error ("fs = " ++ (show fs) ++ ", node = " ++ (show a))



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
move_dc :: Context -> String -> Node -> Node
move_dc c m node =
    case node of -- Pattern match directly on the Node structure passed in
        (_, Node position pos_child neg_child) -> -- Use generic pattern variable names
            if m == "pos child" then getNode c pos_child -- `debug` ("node pos move : " ++ (show node))
            else if m == "neg child" then getNode c neg_child -- `debug` ("node neg move : " ++ (show node))
            -- Add conditions for "neginf", "posinf" if needed
            else error $ "processStackElement: undefined move '" ++ m ++ "' for Node pattern: " ++ show node

        (_, EndInfNode child) ->
            if m == "endinf" then getNode c child --`debug` ("endinf " ++ show (EndInfNode child) )
            else (if (m == "pos child") || (m == "neg child") then node 
            else error $ "processStackElement: undefined move '" ++ m ++ "' for EndInfNode pattern: " ++ show node)

        (_, InfNodes position dc p n) ->
            if m == "inf pos" then getNode c p
            else if m == "inf neg" then getNode c n
            else if m == "inf dc" then getNode c dc
            else error $ "processStackElement: undefined move '" ++ m ++ "' for InfNodes pattern: " ++ show node

        (_, Leaf _) ->
            node
        (_, Unknown) ->
            node
        -- Add cases for any other constructors of Node if they exist
        _ -> error $ "processStackElement: Unhandled Node pattern: " ++ show node ++ ", move: " ++ m


-- update_func_stack :: String -> Int -> Context -> Context
-- update_func_stack s idx c@Context{func_stack = fl} = traverse_dcB s idx (traverse_dcA s idx c)
-- todo map over full func_stack


data Component = CompA | CompB | CompR


class Dd1_helper a where
    traverse_dc :: String -> Context -> NodeId -> NodeId -> Context
    getComponentFuncs :: Dd1 a => Component -> ( (Inf, (Node, Node, Node)) -> Node -- getter
                                           , Context -> String -> Context -- mover
                                           , Context -> Int -> Context -- catchuper
                                           , String -- component string label
                                           )
    traverse_dc_generic :: String -> Context -> Node -> Node -> Node
    applyInf :: Context -> String -> Node -> Node -> (Context, Node)
    applyInf' :: Context -> String -> Node -> Node -> (Context, Node)


instance (DdF3 a) => Dd1_helper a where
    -- apply traversal
    applyInf :: Context -> String ->  Node -> Node -> (Context, Node)
    applyInf c s a b = debug_manipulation (applyInf' @a c s a b) s "applyInf" c a b

    applyInf' :: Context -> String -> Node -> Node -> (Context, Node)
    applyInf' c@Context{func_stack = fs} s a@(a_id, InfNodes positionA dcA pA nA) b@(b_id, InfNodes positionB dcB pB nB)
        | positionA == positionB =  
            let
                -- if there is an above layer
                -- update func stack so its dc's are on the same level as a and b (if not in dc context) 
                c_ = c{func_stack = (Dc, ((u, Unknown),(u, Unknown),(u, Unknown))) : func_stack c}

                (c1, dcR) = apply @Dc (traverse_dc @a "inf dc" c_ dcA dcB) s dcA dcB

                -- to remeber the dcA and dcB specifically for this neg apply call, we place them on the func stack
                -- whenever, in this call, encountering (endinfnode) it should be taken off the func stack
                c2_ = c1{func_stack = (Neg, (getNode c1 dcA, getNode c1 dcB, dcR)) : func_stack c1}
                (c2, nR) = apply @Neg (traverse_dc @a "inf neg" c2_ nA nB) s nA nB


                -- todo ugly type specification from func_tail here, inside apply we wan to skip on Dc.. 
                c3_ = c2{func_stack = (Pos, (getNode c1 dcA, getNode c1 dcB, dcR)) : func_stack (func_tail "" c2)}
                (c3, pR) = apply @Pos (traverse_dc @a "inf pos" c3_ pA pB) s pA pB

                c4 = func_tail (to_str @a) c3 --remove the func_stack layer
            in applyElimRule @a c4 $ InfNodes positionA (fst dcR) (fst pR) (fst nR)

        | positionA > positionB = applyInfA @a c s a b
        | positionA < positionB = applyInfB @a c s a b
    applyInf' c s a b = error_display "apply inf" c a b


    traverse_dc s c@Context{func_stack = fs} a b = debug_dc_traverse s c a b
        (if to_str @a == "Dc" then c
            else let
                (infs, dcs) = if s == "endinf" then unzip $ init fs else unzip fs
                (dcAs, dcBs, dcRs) = if s == "endinf" then unzip3 $ init dcs else unzip3 dcs
                new_dcAs = map (traverse_dc_generic @a s c (getNode c a)) dcAs
                new_dcBs = map (traverse_dc_generic @a s c (getNode c b)) dcBs
                new_dcRs = map (traverse_dc_generic @a s c (getNode c a)) dcRs -- assumption, dcA and dcB are always at the same position when calling traverse_dc. if in the future this changes then we should take the highest / smallest to compare to dcR
                new_fs = zip infs $ zip3 new_dcAs new_dcBs new_dcRs
            in c{func_stack = new_fs})




    traverse_dc_generic s c refNode dcNode
        | null (func_stack c) = error "Should not happen if called from A/B/R defaults"
        | otherwise =
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
                ( (_, EndInfNode{}), (_, Leaf{}) )      -> dcNode -- todo check if makes sense, probably need to catchup with dc 
                ( (_, Leaf{}),       (_, Leaf{}) )      -> dcNode
                ( (_, Leaf{}),       (_, EndInfNode{}) ) -> dcNode

                -- Base cases where dc is EndInfNode/Leaf and refNode is Node (dc is "ahead")
                ( (_, EndInfNode{}), (_, Node idx _ _) ) -> dcNode
                ( (_, Leaf _),       (_, Node idx _ _) ) -> dcNode

                -- Handle Unknown reference node
                ( _, (_, Unknown) ) -> move_dc c s dcNode
                ( (_, Unknown), _ ) -> dcNode -- !!!! todo think about what should be right here !!!! 

                -- Handle InfNodes (using placeholder undefined for logic - needs careful implementation)
                ( (_, InfNodes{}), (_, InfNodes idx dc p n) ) -> undefined -- Add specific logic using mover/catchuper
                ( (_, InfNodes{}), rNode@(_, Node idx _ _) )  -> undefined -- Add specific logic
                ( (_, EndInfNode{}), (_, InfNodes idx dc p n) ) -> undefined -- Add specific logic
                ( (_, InfNodes{}), (_, Leaf{}) )           -> undefined -- Add specific logic

                -- Error case for unhandled patterns
                ( t, r ) -> error $ "traverse_dc_generic unhandled. dcNode=" ++ show t ++ " refNode=" ++ show r ++ " c=" ++ show (func_stack c) ++ " s=" ++ s



