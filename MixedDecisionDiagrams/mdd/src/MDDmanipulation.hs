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



module MDDmanipulation where
-- todo-future : explore {-# UNPACK #-} !Int
--SPECIALIZE pragma
import MDD hiding (debug)
import Debug.Trace (trace)
import DrawMDD
import Data.Kind

import Data.Map (Map)
import Data.Hashable
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.Map as Map
import GHC.IO (unsafePerformIO)



-- todo parser from debug show output to DD
-- todo add levels to the hashing
-- todo add dereferencing in the nodelookup
-- -- | !! 2 design decisions, either the finite typ[e recopy the infinite types consequences (which means we need to constantly check for absorbs after each change) or the finite types have the add on


-- -- create stack also for function calls: only mixed and absorb can be added
-- -- add additional context types: mixed and absorb

-- -- | This module describes functions that manipulate MDDs.

-- -- For the usual Binary Decision Diagrams there are 4 patterns (3 combinations) to account for:
-- -- Leaf | Leaf
-- -- Node | Leaf
-- -- Node | Node

-- -- For MDDs (with four types of nodes) there are additional patterns (10 combinations total):

-- -- InfS | InfS
-- -- InfS | InfE
-- -- InfE | InfE

-- -- Leaf | InfS
-- -- infer Top for InfS
-- -- Leaf | InfE
-- -- pop local context,
-- -- there should be a infEnd for every InfStart thus we loose Leaf inference:

-- -- Node | InfS
-- -- Node | InfE
-- -- continue local node recursion until InfE or InfS is reached

-- -- absorb decing choice: make 2, union and intersection, if the 0 and 1 zdds are never constructed to be smalleer and larger (respectively) then we could have only 1 absorb. evenmore so we could combine the absorb with the mixed intersection / mixed union, which is probably best for perfornace
-- -- the aborb needs not perform an intersection or union after the endleaf (in the consequence), but it needs to treat the leaves differently based on its context

data Polarity = Neg | Pos
    deriving (Eq, Show)

data Combination = And | Or
    deriving (Eq, Show)
type Combine_rule :: Combination -> Polarity -> Constraint



class Combine_rule a b where
    rAnd1_rule ::  String -> Context -> NodeId -> NodeId -> NodeId -> NodeId -> NodeId -> (Context, NodeId)
    rAnd1'_rule :: String -> Context -> NodeId -> NodeId -> NodeId -> NodeId -> NodeId -> (Context, NodeId)
    rOr1_rule ::   String -> Context -> NodeId -> NodeId -> (Context, NodeId)
    rOr1'_rule ::  String -> Context -> NodeId -> NodeId -> NodeId -> NodeId -> (Context, NodeId)

instance Combine_rule And Neg where
    rAnd1_rule = r1_rule @Neg1 True
    rAnd1'_rule = r1'_rule @Neg1 True
    rOr1_rule = r0_rule @Neg0 True
    rOr1'_rule = r0'_rule @Neg0 True

instance Combine_rule And Pos where
    rAnd1_rule = r1_rule @Pos1 True
    rAnd1'_rule = r1'_rule @Pos1 True
    rOr1_rule = r0_rule @Pos0 True
    rOr1'_rule = r0'_rule @Pos0 True

instance Combine_rule Or Neg where
    rAnd1_rule = r1_rule @Neg0 False
    rAnd1'_rule = r1'_rule @Neg0 False
    rOr1_rule = r0_rule @Neg1 False
    rOr1'_rule = r0'_rule @Neg1 False

instance Combine_rule Or Pos where
    rAnd1_rule = r1_rule @Pos0 False
    rAnd1'_rule = r1'_rule @Pos0 False
    rOr1_rule = r0_rule @Pos1 False
    rOr1'_rule = r0'_rule @Pos1 False



type DdF4 :: Inf -> Constraint
type Dd1 :: Inf -> Constraint

supply_dds :: DdManipulation -> Context -> NodeId -> NodeId -> (Context, NodeId)
supply_dds f c a b = f c a b (getDd c a) (getDd c b)

intersection :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
intersection c a b = intersection'  c a b
    -- `debug` ("intersection: \n" ++ show_dd settings c a ++ " \n; "  ++ show_dd settings c b)
intersection' :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
intersection' c a_id b_id a (Leaf False) = (c, b_id)
intersection' c a_id b_id (Leaf False) b = (c, a_id)
intersection' c a_id b_id a (Leaf True) = insert c a
intersection' c a_id b_id (Leaf True) b = insert c b
intersection' c a_id b_id a b = intersectionMain c a_id b_id
union :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
union c a b = union' c a b
    -- `debug` ("union: " ++ show c ++ " ; " ++ show_dd settings c a ++ " ; "  ++ show_dd settings c b)
union' :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
union' c a_id b_id a (Leaf True) = (c, b_id)
union' c a_id b_id (Leaf True) b = (c, a_id)
union' c a_id b_id a (Leaf False) = insert c a
union' c a_id b_id (Leaf False) b = insert c b
union' c a_id b_id a b = unionMain c a_id b_id

negation' :: (Context, NodeId) -> (Context, NodeId)
negation' (c, node_id) = negation'' c node_id (getDd c node_id)

negation_ :: Context -> NodeId -> (Context, NodeId)
negation_ c node_id = negation'' c node_id (getDd c node_id)

negation'' :: Context -> NodeId -> Dd -> (Context, NodeId)
negation'' c node_id dd  = let r = negation c node_id dd in r
    -- `debug` (colorize "green" "negation : \n" ++ "  ->   " ++ show_dd settings c node_id ++
    --         "\n  =>   " ++ show_dd settings (fst r) (snd r)  ++ "\n") -- "\n -> \n" )

negation :: Context -> NodeId -> Dd -> (Context, NodeId)
negation c node_id d@(Node position pos_child neg_child)  = withCache_ c node_id $ let
    (c', posR) = negation_ c pos_child  --`debug` ("negation pos child: " ++ show_dd settings c pos_child ++ " , " ++ " -> " ++ show (getDd c pos_child) )
    (c'', negR) = negation_ c' neg_child  --`debug` ("negation neg child: " ++ show_dd settings c neg_child ++ " , " ++ "-> " ++ show (getDd c' neg_child))
    in insert c'' $ Node position posR negR -- `debug` (" inserted: " ++ show (insert c'' $ Node position posR negR))
negation c node_id d@(InfNodes position dc n1 n0 p1 p0) = withCache_ c  node_id $ let
    (c', r_dc) = negation_ c dc
    (c'', r_n0) = negation_ c' n1
    (c''', r_n1) = negation_ c'' n0
    (c'''', r_p0) = negation_ c''' p1
    (c''''', r_p1) = negation_ c'''' p0
        in insert c''''' $ InfNodes position r_dc r_n1 r_n0 r_p1 r_p0
negation c node_id d@(EndInfNode a) = withCache_ c  node_id $ let
    (c', result) = negation'' c a (getDd c a) --`debug` ("negation endinf child: " ++ show_dd settings c a )
    in insert c' $ EndInfNode result
negation c _ (Leaf b) = (c, leaf $ not b) --`debug` ("returning : " ++ show (c, leaf $ not b))


applyElimRule_arg :: Context -> Inf -> Dd -> (Context, NodeId)
applyElimRule_arg c Dc d = applyElimRule @Dc c d
applyElimRule_arg c Neg1 d = applyElimRule @Neg1 c d
applyElimRule_arg c Neg0 d = applyElimRule @Neg0 c d
applyElimRule_arg c Pos1 d = applyElimRule @Pos1 c d
applyElimRule_arg c Pos0 d = applyElimRule @Pos0 c d

-- why am i doing this directly below?
-- because the union of a leaf has different outcomes depending on the context its in, which can be switched when exiting a infnodes domain
intersectionLocal_arg :: (Inf, FType) -> Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
intersectionLocal_arg (i,t) c (0,0) b_id a b
    | i `elem` [Dc,Neg1,Pos1] = (c,(0,0))
    | i `elem` [Neg0,Pos0] = (c, b_id)
intersectionLocal_arg (i,t) c (1,0) b_id a b
    | i `elem` [Dc,Neg1,Pos1] = (c, b_id)
    | i `elem` [Neg0,Pos0] = (c,(1,0))
intersectionLocal_arg (i,t) c a_id (0,0) a b
    | i `elem` [Dc,Neg1,Pos1] = (c,(0,0))
    | i `elem` [Neg0,Pos0] = (c, a_id)
intersectionLocal_arg (i,t) c a_id (1, 0) a b
    | i `elem` [Dc,Neg1,Pos1] = (c, a_id)
    | i `elem` [Neg0,Pos0] = (c,(1,0))
intersectionLocal_arg t c a b a_id b_id = case t of
    (Dc, Inter) -> intersectionLocal @Dc c a b a_id b_id
    (Neg1, Inter) -> intersectionLocal @Neg1 c a b a_id b_id
    (Neg0, Inter) -> intersectionLocal @Neg0 c a b a_id b_id
    (Pos1, Inter) -> intersectionLocal @Pos1 c a b a_id b_id
    (Pos0, Inter) -> intersectionLocal @Pos0 c a b a_id b_id
    _-> error "non inter"

unionLocal_arg :: (Inf, FType) -> Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
unionLocal_arg t c a b = unionLocal_arg' t c a b --`debug` ("unionLocal arg t = " ++ show t ++ ", \n \t a = " ++ show_dd settings c a ++ ", \n \t b = " ++ show_dd settings c b)
unionLocal_arg' :: (Inf, FType) -> Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
unionLocal_arg' (i,t) c a_id b_id a@(Leaf False) b
    | i `elem` [Dc,Neg1,Pos1] = (c, b_id)
    | i `elem` [Neg0,Pos0] = (c, (0,0))
unionLocal_arg' (i,t) c a_id b_id a@(Leaf True) b
    | i `elem` [Dc,Neg1,Pos1] = (c, (1,0))
    | i `elem` [Neg0,Pos0] = (c, b_id)
unionLocal_arg' (i,t) c a_id b_id a b@(Leaf False)
    | i `elem` [Dc,Neg1,Pos1] = (c, a_id)
    | i `elem` [Neg0,Pos0] = (c, (0,0))
unionLocal_arg' (i,t) c a_id b_id a b@(Leaf True)
    | i `elem` [Dc,Neg1,Pos1] = (c, (1,0))
    | i `elem` [Neg0,Pos0] = (c, a_id)
unionLocal_arg' t c a b a_id b_id = case t of
    (Dc, Union) -> unionLocal @Dc c a b a_id b_id
    (Neg1, Union) -> unionLocal @Neg1 c a b a_id b_id
    (Neg0, Union) -> unionLocal @Neg0 c a b a_id b_id
    (Pos1, Union) -> unionLocal @Pos1 c a b a_id b_id
    (Pos0, Union) -> unionLocal @Pos0 c a b a_id b_id
    _ -> error ""

continue_outer t c a_id b_id a b = continue_outer' t c a_id b_id a b --`debug` ("continue outer: \n a: " ++ show_dd settings c a_id ++ "\n b: " ++ show_dd settings c b_id)

continue_outer' :: (Inf, FType) -> Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
continue_outer' t c = case t of
    (Dc, Inter) -> intersectionLocal @Dc c
    (Neg1, Inter) -> intersectionLocal @Neg1 c
    (Neg0, Inter) -> intersectionLocal @Neg0 c
    (Pos1, Inter) -> intersectionLocal @Pos1 c
    (Pos0, Inter) -> intersectionLocal @Pos0 c

    (Dc, Union) -> unionLocal @Dc c
    (Neg1, Union) -> unionLocal @Neg1 c
    (Neg0, Union) -> unionLocal @Neg0 c
    (Pos1, Union) -> unionLocal @Pos1 c
    (Pos0, Union) -> unionLocal @Pos0 c

    (Dc, MixedIntersection) -> mixedIntersection @Dc c
    (Neg1, MixedIntersection) -> mixedIntersection @Neg1 c
    (Neg0, MixedIntersection) -> mixedIntersection @Neg0 c
    (Pos1, MixedIntersection) -> mixedIntersection @Pos1 c
    (Pos0, MixedIntersection) -> mixedIntersection @Pos0 c

    (Dc, MixedUnion) -> mixedUnion @Dc c
    (Neg1, MixedUnion) -> mixedUnion @Neg1 c
    (Neg0, MixedUnion) -> mixedUnion @Neg0 c
    (Pos1, MixedUnion) -> mixedUnion @Pos1 c
    (Pos0, MixedUnion) -> mixedUnion @Pos0 c

    (Dc, Absorb) -> absorb @Dc c
    (Neg1, Absorb) -> absorb @Neg1 c
    (Neg0, Absorb) -> absorb @Neg0 c
    (Pos1, Absorb) -> absorb @Pos1 c
    (Pos0, Absorb) -> absorb @Pos0 c

    (_, _) -> error (show t ++ ", " ++ show c ++ ", ")


t_and_r_arg :: (Inf, FType) -> Bool -> Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
t_and_r_arg t l c a_id b_id a b = case t of
    (Dc, Absorb) -> absorb @Dc c a_id b_id a b
    (Neg1, Absorb) -> absorb @Neg1 c a_id b_id a b
    (Neg0, Absorb) -> absorb @Neg0 c a_id b_id a b
    (Pos1, Absorb) -> absorb @Pos1 c a_id b_id a b
    (Pos0, Absorb) -> absorb @Pos0 c a_id b_id a b
    (Dc, T_and_r) -> traverse_and_return @Dc l c a_id b_id a b
    (Neg1, T_and_r) -> traverse_and_return @Neg1 l c a_id b_id a b
    (Neg0, T_and_r) -> traverse_and_return @Neg0 l c a_id b_id a b
    (Pos1, T_and_r) -> traverse_and_return @Pos1 l c a_id b_id a b
    (Pos0, T_and_r) -> traverse_and_return @Pos0 l c a_id b_id a b
    (Dc, Remove) -> remove_outercomplement_from @Dc c a_id b_id a b
    (Neg1, Remove) -> remove_outercomplement_from @Neg1 c a_id b_id a b
    (Neg0, Remove) -> remove_outercomplement_from @Neg0 c a_id b_id a b
    (Pos1, Remove) -> remove_outercomplement_from @Pos1 c a_id b_id a b
    (Pos0, Remove) -> remove_outercomplement_from @Pos0 c a_id b_id a b

    (_, _) -> error (show t ++ ", " ++ show c ++ ", \n   ->  " ++ show_dd settings c a_id ++ ", " ++ show_dd settings c b_id)

addInfNode :: Context -> Int -> Inf -> NodeId -> (Context, NodeId)
addInfNode c n inf conseq  =
        case inf of -- only for Dc we need to check the b, since after a hole we interpret the following sub domains in substance (1-set)
            Dc -> insert c' $ InfNodes n dd l0 l1 l0 l1
            Neg1 -> insert c' $ InfNodes n l0 dd l1 l0 l1
            Neg0 -> insert c' $ InfNodes n l1 l0 dd l0 l1
            Pos1 -> insert c' $ InfNodes n l0 l0 l1 dd l1
            Pos0 -> insert c' $ InfNodes n l1 l0 l1 l0 dd
        where
            (c', dd) = insert c $ EndInfNode conseq

intersectionInferA :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
intersectionInferA Context{func_stack = []} _ _ _ _ = error "empty context"
intersectionInferA  _ _ _ _ (Leaf _) = error "Leaf in A"
intersectionInferA  _ _ _ _ (EndInfNode _) = error "EndNode in A"
intersectionInferA  _ _ _ _ (Node _ _ _) = error "Node in A"

intersectionInferA c a_id b_id a b = debug_manipulation (intersectionInferA' c a_id b_id a b) "intersection" "intersectionInferA" c a_id b_id
intersectionInferA' :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
intersectionInferA' c'@Context{func_stack = ((inf, _) : _)} a_id' b_id a' b@(InfNodes positionB dcB n1B n0B p1B p0B) =
    case inf of
        Dc -> let -- replace all the A stuf with (dc: a, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
            (c1, !dcR ) = intersectionLocal @Dc c a_id dcB a dcB_dd
            dcR_dd = getDd c1 dcR

            (c2, !n1R ) = (if n0B == (1,0) then
                    absorb @Neg1 c21 absorb_a dcR (getDd c21 absorb_a) dcR_dd  else
                    remove_outercomplement_from @Neg1 c22 rmv_a n0B (getDd c22 rmv_a) n0B_dd)
                    -- todo applyInfElimRule @Neg1 c1 $  for mixed intersection below! probably!
            (c21, !absorb_a) = mixedIntersection @Neg1 c1 n1B a_id n1B_dd a
            (c22, !rmv_a) = absorb @Neg1 c21 absorb_a dcR (getDd c21 absorb_a) dcR_dd
            (c3, !n0R ) = absorb @Neg0 c31 absorb_a3 dcR (getDd c31 absorb_a3) dcR_dd --`debug` ( "inter: " ++ show (mixedIntersection @Neg0 c n0A dcR) ++ "\n n0A: " ++ show n0A  ++ "\n dcR" ++ show dcR)
            (c31, !absorb_a3) = mixedIntersection @Neg0 c2 n0B dcR n0B_dd dcR_dd

            (c4, !p1R ) = if p0B == (1,0) then
                absorb @Pos1 c41 lala dcR (getDd c41 lala) dcR_dd else
                remove_outercomplement_from @Pos1 c42 lolo p0B (getDd c42 lolo) p0B_dd
            (c41, !lala) = mixedIntersection @Pos1 c3 p1B a_id p1B_dd a
            (c42, !lolo) = absorb @Pos1 c41 lala dcR (getDd c41 lala) dcR_dd
            (c5, !p0R ) = absorb @Neg0 c51 hey dcR (getDd c51 hey) dcR_dd
            (c51, !hey) = mixedIntersection @Pos0 c4 p0B dcR p0B_dd dcR_dd

            in insert c5 $ InfNodes positionB dcR n1R n0R p1R p0R

        Neg1 -> let -- replace all the A stuf with (dc: 0, neg1: a, neg0: 1, pos1: 0, pos0: 1)
            (c1, !n1R ) = unionLocal @Neg1 c12 negcalc1 negcalc2 (getDd c12 negcalc1) (getDd c13 negcalc2)
            (c12, !negcalc1) = intersectionLocal @Neg1 c13 a_id n1B a n1B_dd
            (c13, !negcalc2) = (if n0B == (1,0) then (c2, n1R') else (c14, negcalc3))
            (c14, !negcalc3) = remove_outercomplement_from @Neg1 c2 n0B n1R' n0B_dd (getDd c n1R')
            (c2, !n1R')  = mixedIntersection @Neg1 c a_id dcB a dcB_dd
            in insert c1 $ InfNodes positionB (0,0) n1R (1,0) (0,0) (1,0)
        Neg0 -> let -- replace all the A stuf with (dc: 1, neg1: 0, neg0: a, pos1: 0, pos0: 1)
            (c1, !n0R')  = intersectionLocal @Neg0 c a_id n0B a n0B_dd
            (c2, !n0R ) = mixedIntersection @Neg0 c1 n0R' dcB (getDd c1 n0R') dcB_dd
            in insert c2 $ InfNodes positionB dcB (0,0) n0R (0,0) (1,0)
        Pos1 -> let -- replace all the A stuf with (dc: 0, neg1: 0, neg0: 1, pos1: a, pos0: 1)
            (c1, !p1R ) = unionLocal @Pos1 c12 poscalc1 poscalc2 (getDd c12 poscalc1) (getDd c13 poscalc2)
            (c12, !poscalc1) = intersectionLocal @Pos1 c13 a_id n1B a n1B_dd
            (c13, !poscalc2) = (if p0B == (1,0) then (c2, p1R') else (c14, poscalc3))
            (c14, !poscalc3) = remove_outercomplement_from @Pos1 c2 n0B p1R' n0B_dd (getDd c p1R')
            (c2, !p1R')  = mixedIntersection @Pos1 c a_id dcB a dcB_dd
            in insert c1 $ InfNodes positionB (0,0) (0,0) (1,0) p1R (1,0)
        Pos0 -> let -- replace all the A stuf with (dc: (1,0), neg1: (1,0), neg0: a, pos1: (1,0), pos0: (1,0))
            (c1, !p0R')  = intersectionLocal @Pos0 c a_id p0B a p0B_dd
            (c2, !p0R ) = mixedIntersection @Pos0 c1 p0R' dcB (getDd c1 p0R') dcB_dd
            in insert c2 $ InfNodes positionB dcB (0,0) (1,0) (0,0) p0R

        where
            (c, a_id) = insert c' $ EndInfNode a_id'
            a = getDd c a_id
            dcB_dd = getDd c dcB
            n1B_dd = getDd c n1B
            n0B_dd = getDd c n0B
            p1B_dd = getDd c p1B
            p0B_dd = getDd c p0B

intersectionInferA' _ _ _ _ _ = undefined

intersectionInferB :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
intersectionInferB Context{func_stack = []} _ _ _ _ = error "empty context"
intersectionInferB _ _ _ (Leaf _) _ = error "Leaf in A"
intersectionInferB _ _ _ (EndInfNode _) _ = error "EndNode in A"
intersectionInferB _ _ _ (Node _ _ _) _ = error "Node in A"

intersectionInferB c a_id b_id a b =  debug_manipulation (intersectionInferB' c a_id b_id a b) "intersection" "intersectionInferB" c a_id b_id
intersectionInferB' :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
intersectionInferB' c'@Context{func_stack = ((inf, _) : _)} a_id b_id' a@(InfNodes positionA dcA n1A n0A p1A p0A) b' =
    case inf of
        Dc -> let -- replace all the B stuf with (dc: b, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
            (c1, dcR ) = intersectionLocal @Dc c dcA b_id dcA_dd b --`debug` ("dcR: " ++ (show_dd settings c b_id))
            !dcR_dd = getDd c1 dcR

            (c2, n1R ) = (if n0A == (1,0) then
                    absorb @Neg1 c21 absorb_a dcR (getDd c21 absorb_a) dcR_dd  else
                    remove_outercomplement_from @Neg1 c22 rmv_a n0A (getDd c22 rmv_a) n0A_dd)
            (c21, absorb_a) = mixedIntersection @Neg1 c1 n1A b_id n1A_dd b --`debug` ("mix2 :: " ++ (show_dd settings c1 n1A) ++ (show_dd settings c1 b_id) ++ "= \n " ++ (show_dd settings (fst (mixedIntersection @Neg1 c1 n1A b_id n1A_dd b)) (snd (mixedIntersection @Neg1 c1 n1A b_id n1A_dd b))))
            (c22, rmv_a) = absorb @Neg1 c21 absorb_a dcR (getDd c21 absorb_a) dcR_dd -- `debug` "absorb"

            (c3, n0R ) = absorb @Neg0 c31 absorb_a3 dcR (getDd c31 absorb_a3) dcR_dd --`debug` ( "inter: " ++ show (mixedIntersection @Neg0 c n0A dcR) ++ "\n n0A: " ++ show n0A  ++ "\n dcR" ++ show dcR)
            (c31, absorb_a3) = mixedIntersection @Neg0 c2 n0A dcR n0A_dd dcR_dd

            (c4, p1R) = if p0A == (1,0) then
                absorb @Pos1 c41 lala dcR (getDd c41 lala) dcR_dd else
                remove_outercomplement_from @Pos1 c42 lolo p0A (getDd c42 lolo) p0A_dd
            (c41, lala) = mixedIntersection @Pos1 c3 p1A b_id p1A_dd b
            (c42, lolo) = absorb @Pos1 c43 lili dcR (getDd c43 lili) dcR_dd
            (c43, lili) = mixedIntersection @Pos1 c3 p1A b_id p1A_dd b

            (c5, p0R ) = absorb @Neg0 c51 hey dcR (getDd c51 hey) dcR_dd
            (c51, hey) = mixedIntersection @Pos0 c4 p0A dcR p0A_dd dcR_dd

            in insert c5 $ InfNodes positionA dcR n1R n0R p1R p0R --`debug` "inferintersectionB"

        Neg1 -> let -- replace all the A stuf with (dc: 0, neg1: a, neg0: 1, pos1: 0, pos0: 1)
            (c1, n1R ) = unionLocal @Neg1 c12 negcalc1 negcalc2 (getDd c12 negcalc1) (getDd c13 negcalc2)
            (c12, negcalc1) = intersectionLocal @Neg1 c n1A b_id n1A_dd b
            (c13, negcalc2) = (if n0A == (1,0) then (c2, n1R') else (c14, negcalc3))
            (c14, negcalc3) = remove_outercomplement_from @Neg1 c2 n0A n1R' n0A_dd (getDd c n1R')

            (c2, n1R')  = mixedIntersection @Neg1 c b_id dcA b dcA_dd

            in insert c1 $ InfNodes positionA (0,0) n1R (1,0) (0,0) (1,0)

        Neg0 -> let -- replace all the A stuf with (dc: 1, neg1: 0, neg0: a, pos1: 0, pos0: 1)
            (c1, n0R')  = intersectionLocal @Neg0 c2 n0A b_id n0A_dd b

            (c2, n0R ) = mixedIntersection @Neg0 c1 n0R' dcA (getDd c1 n0R') dcA_dd

            in insert c2 $ InfNodes positionA dcA (0,0) n0R (0,0) (1,0)

        Pos1 -> let -- replace all the A stuf with (dc: 0, neg1: 0, neg0: 1, pos1: a, pos0: 1)
            (c1, p1R ) = unionLocal @Pos1 c12 poscalc1 poscalc2 (getDd c12 poscalc1) (getDd c13 poscalc2)
            (c12, poscalc1) = intersectionLocal @Pos1 c13 n1A b_id n1A_dd b
            (c13, poscalc2) = (if p0A == (1,0) then (c2, p1R') else (c14, poscalc3))
            (c14, poscalc3) = remove_outercomplement_from @Pos1 c2 n0A p1R' n0A_dd (getDd c p1R')

            (c2, p1R')  = mixedIntersection @Pos1 c b_id dcA b dcA_dd

            in insert c1 $ InfNodes positionA (0,0) (0,0) (1,0) p1R (1,0)

        Pos0 -> let -- replace all the A stuf with (dc: (1,0), neg1: (1,0), neg0: a, pos1: (1,0), pos0: (1,0))
            (c1, p0R')  = intersectionLocal @Pos0 c p0A b_id p0A_dd b
            (c2, p0R ) = mixedIntersection @Pos0 c1 p0R' dcA (getDd c p0R') dcA_dd

            in insert c2 $ InfNodes positionA dcA (0,0) (1,0) (0,0) p0R

        where
            (c, b_id) = insert c' $ EndInfNode b_id'
            b = getDd c b_id
            dcA_dd = getDd c' dcA
            n1A_dd = getDd c' n1A
            n0A_dd = getDd c' n0A
            p1A_dd = getDd c' p1A
            p0A_dd = getDd c' p0A


intersectionInferB' _ _ _ _ _ = undefined


intersectionMain :: Context -> NodeId -> NodeId -> (Context, NodeId)
intersectionMain c a b = debug_manipulation (intersectionMain' c a b (getDd c a) (getDd c b))
    "intersection" "intersectionMain" c a b
intersectionMain' :: DdManipulation
intersectionMain'  c@Context{} !a_id !b_id a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B)
    | positionA == positionB =  let
        (c1, dcR) = intersectionLocal @Dc c dcA dcB (getDd c dcA)  (getDd c dcB) --`debug` ("intersection A ("++ show positionA ++ ")==B (" ++ show positionB )
            -- `debug` ("\nDcR dcA ^ dcB \t = " ++ show (intersectionLocal @Dc c dcA dcB (getDd c dcA) (getDd c dcB))
            -- ++ "\n\t dcA = " ++ show dcA
            -- ++ "\n\t dcB = " ++ show dcB
            -- ++ "\n")
        (c2, n1R') = rAnd1'_rule @And @Neg "" c1 n0R' n1A n1B dcA dcB
        (c3, n0R') = rOr1'_rule @And @Neg "" c2 n0A n0B dcA dcB -- holes get unioned, because i keep the consequence of holes "uncomplemented" we get local union then intersection.
        (c4, n1R) = rAnd1_rule @And @Neg "" c3 n0R' dcR n1R' n1A n1B
        (c5, n0R) = rOr1_rule @And @Neg "" c4 n0R' dcR -- keep the holes that fit inside dcR

        (c6, p1R') = rAnd1'_rule @And @Pos "" c5 p0R' p1A p1B dcA dcB
        (c7, p0R') = rOr1'_rule @And @Pos "" c6 p0A p0B dcA dcB -- holes get unioned, because i keep the consequence of holes "uncomplemented" we get local union then intersection.
        (c8, p1R) = rAnd1_rule @And @Pos "" c7 p0R' dcR p1R' p1A p1B
        (c9, p0R) = rOr1_rule @And @Pos "" c8 p0R' dcR
        -- -- if the local hole fits inside dcR but the consequence of p0R' does not fit inside the consequenc of dcR it should return n0R' -> Leaf false
        in insert c9 $ InfNodes positionA dcR n1R n0R p1R p0R
    | positionA > positionB = withCache c (a_id, b_id, "intersection") $ intersectionInferA c a_id b_id a b `debug` "interA"
    | positionA < positionB = withCache c (a_id, b_id, "intersection") $ intersectionInferB c a_id b_id a b `debug` "interB"-- replace all the A stuf with (dc: a, neg1: 0, neg0: (1,0), pos1: (1,0), pos0: (1,0))
intersectionMain' c a_id b_id a b = error (show_dd settings c a_id ++ ", " ++ show_dd settings c b_id ++ ", "++ show c)

unionInferA :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
unionInferA Context{func_stack = []} _ _ _ _ = error "empty context"
unionInferA  _ _ _ _ (Leaf _) = error "Leaf in A"
unionInferA  _ _ _ _ (EndInfNode _) = error "EndNode in A"
unionInferA  _ _ _ _ (Node _ _ _) = error "Node in A"

unionInferA c a_id b_id a b =  debug_manipulation (unionInferA' c a_id b_id a b) "union" "unionInferA" c a_id b_id   -- ++ " = " ++ show (unionInferA' c a_id b_id a b ))
unionInferA' :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
unionInferA' c'@Context{func_stack = ((inf, _) : _)} a_id' b_id a' b@(InfNodes positionB dcB n1B n0B p1B p0B) =
    case inf of
        Dc -> let -- replace all the A stuf with (dc: a, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
            (c1, dcR ) = unionLocal @Dc c a_id dcB a dcB_dd
            !dcR_dd = getDd c1 dcR

                        -- dcR = unionLocal @Dc c  a dcB --pass along the consequence of B for both dcA and not dcA
            (c2, n1R) = absorb @Neg1 c21 n1R2 dcR (getDd c21 n1R2) dcR_dd
            (c21, n1R2) = mixedUnion @Neg1 c1 n1B dcR n1B_dd dcR_dd

            (c3, n0R) = if n1B == (0,0)
                    then absorb @Neg0 c32 n0R' dcR (getDd c32 n0R') dcR_dd
                    else absorb @Neg0 c31 ja dcR (getDd c31 ja) dcR_dd --`debug` ("n0B != 0" ++ show_dd settings c31 ja)
            (c31, ja) = remove_outercomplement_from @Neg0 c32 n1B n0R' n1B_dd (getDd c32 n0R')
            (c32, n0R') = mixedUnion @Neg0 c2 n0B a_id n0B_dd a


            (c4, p1R) = absorb @Pos1 c41 p1R2 dcR (getDd c41 p1R2) dcR_dd
            (c41, p1R2) = mixedUnion @Pos1 c3 p1B dcR p1B_dd dcR_dd

            (c5, p0R) = if p1B == (0,0)
                    then absorb @Neg0 c52 p0R' dcR (getDd c52 p0R') dcR_dd
                    else absorb @Neg0 c51 ja2 dcR (getDd c51 ja2) dcR_dd
            (c51, ja2) = remove_outercomplement_from @Neg0 c52 p1B p0R' p1B_dd (getDd c52 p0R')
            (c52, p0R') = mixedUnion @Neg0 c4 p0B a_id p0B_dd a

            in insert c5 $ InfNodes positionB dcR n1R n0R p1R p0R

        Neg1 -> let -- replace all the A stuf with (dc: (1,0), neg1: a, neg0: (1,0), pos1: (1,0), pos0: (1,0))
            (c1, n1R')  = unionLocal @Neg1 c a_id n1B a n1B_dd --`debug` ("--------- " ++ show n1B)
            (c2, n1R ) = mixedUnion @Neg1 c1 n1R' dcB (getDd c' n1R') dcB_dd

            in insert c2 $ InfNodes positionB (0,0) n1R (1,0) (0,0) (1,0)

        Neg0 -> let -- replace all the A stuf with (dc: (1,0), neg1: (1,0), neg0: a, pos1: (1,0), pos0: (1,0))
            (c1, n0R ) = intersectionLocal @Neg0 c12 negcalc1 negcalc2 (getDd c12 negcalc1) (getDd c13 negcalc2)
            (c12, negcalc1) = unionLocal @Neg0 c a_id n1B a n1B_dd
            (c13, negcalc2) = (if n0B == (1,0) then (c2, n0R') else (c14, negcalc3))
            (c14, negcalc3) = remove_outercomplement_from @Neg0 c2 n1B n0R' n1B_dd (getDd c2 n0R')
            (c2, n0R')  = mixedIntersection @Neg0 c a_id dcB a dcB_dd
            in insert c1 $ InfNodes positionB dcB (0,0) n0R (0,0) (1,0)
        Pos1 -> let -- replace all the A stuf with (dc: (1,0), neg1: (1,0), neg0: (1,0), pos1: a, pos0: (1,0))
            (c1, p1R')  = unionLocal @Pos1 c a_id p1B a p1B_dd
            (c2, p1R ) = mixedUnion @Pos1 c1 p1R' dcB (getDd c' p1R') dcB_dd
            in insert c2 $ InfNodes positionB (0,0) (0,0) (1,0) p1R (1,0)
        Pos0 -> let -- replace all the A stuf with (dc: (1,0), neg1: (1,0), neg0: a, pos1: (1,0), pos0: (1,0))
            (c1, p0R ) = intersectionLocal @Pos0 c12 poscalc1 poscalc2 (getDd c12 poscalc1) (getDd c13 poscalc2)
            (c12, poscalc1) = unionLocal @Pos0 c a_id n1B a n1B_dd
            (c13, poscalc2) = (if p0B == (1,0) then (c2, p0R') else (c14, poscalc3))
            (c14, poscalc3) = remove_outercomplement_from @Pos0 c2 n1B p0R' n1B_dd (getDd c2 p0R')
            (c2, p0R')  = mixedIntersection @Pos0 c a_id dcB a dcB_dd
            in insert c1 $ InfNodes positionB dcB (0,0) (1,0) (0,0) p0R

        where
            (c, a_id) = insert c' $ EndInfNode a_id'
            a = getDd c a_id
            dcB_dd = getDd c dcB
            n1B_dd = getDd c n1B
            n0B_dd = getDd c n0B
            p1B_dd = getDd c p1B
            p0B_dd = getDd c p0B

unionInferA' _ _ _ _ _ = undefined


unionInferB :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
unionInferB Context{func_stack = []} _ _ _ _ = error "empty context"
unionInferB _ _ _ (Leaf _) _ = error "Leaf in A"
unionInferB _ _ _ (EndInfNode _) _ = error "EndNode in A"
unionInferB _ _ _ (Node _ _ _) _ = error "Node in A"

unionInferB c a_id b_id a b =  debug_manipulation (unionInferB' c a_id b_id a b) "union" "unionInferB" c a_id b_id
unionInferB' :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
unionInferB' c'@Context{func_stack = ((inf, _) : _)} a_id b_id' a@(InfNodes positionA dcA n1A n0A p1A p0A) b' =
    case inf of
        Dc -> let -- replace all the A stuf with (dc: a, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
            (c1, dcR ) = unionLocal @Dc c dcA b_id dcA_dd b
            !dcR_dd = getDd c1 dcR

                        -- dcR = unionLocal @Dc c  a dcA --pass along the consequence of B for both dcA and not dcA
            (c2, n1R) = absorb @Neg1 c21 n1R2 dcR (getDd c21 n1R2) dcR_dd
            (c21, n1R2) = mixedUnion @Neg1 c1 n1A dcR n1A_dd dcR_dd

            (c3, n0R) = if n1A == (0,0)
                    then absorb @Neg0 c32 n0R' dcR (getDd c32 n0R') dcR_dd -- `debug` ("n0R :: " ++ show_dd settings (fst $ absorb @Neg0 c32 n0R' dcR (getDd c32 n0R') dcR_dd) (snd $ absorb @Neg0 c32 n0R' dcR (getDd c32 n0R') dcR_dd))
                    else absorb @Neg0 c31 ja dcR (getDd c31 ja) dcR_dd -- `debug` ("n0R :: " ++ show_dd settings (fst $ absorb @Neg0 c31 dcR ja (getDd c31 ja) dcR_dd) (ja))
            (c31, ja) = remove_outercomplement_from @Neg0 c32 n1A n0R' n1A_dd (getDd c32 n0R')
            (c32, n0R') = mixedUnion @Neg0 c2 n0A b_id n0A_dd b --`debug` ("mixedunion:: " ++ show_dd settings (fst $ mixedUnion @Neg0 c2 n0A b_id n0A_dd b) (snd $ mixedUnion @Neg0 c2 n0A b_id n0A_dd b))


            (c4, p1R) = absorb @Pos1 c41 p1R2 dcR (getDd c41 p1R2) dcR_dd
            (c41, p1R2) = mixedUnion @Pos1 c3 p1A dcR p1A_dd dcR_dd

            (c5, p0R) = if p1A == (0,0)
                    then absorb @Pos0 c52 p0R' dcR (getDd c52 p0R') dcR_dd
                    else absorb @Pos0 c51 ja2 dcR (getDd c51 ja2) dcR_dd
            (c51, ja2) = remove_outercomplement_from @Pos0 c52 p1A p0R' p1A_dd (getDd c52 p0R')
            (c52, p0R') = mixedUnion @Pos0 c4 p0A b_id p0A_dd b

            in insert c5 $ InfNodes positionA dcR n1R n0R p1R p0R

        Neg1 -> let -- replace all the A stuf with (dc: (1,0), neg1: a, neg0: (1,0), pos1: (1,0), pos0: (1,0))
            (c1, n1R')  = unionLocal @Neg1 c n1A b_id n1A_dd b
            (c2, n1R ) = mixedUnion @Neg1 c' n1R' dcA (getDd c1 n1R') dcA_dd
            in insert c2 $ InfNodes positionA (0,0) n1R (1,0) (0,0) (1,0)
        Neg0 -> let -- replace all the A stuf with (dc: (1,0), neg1: (1,0), neg0: a, pos1: (1,0), pos0: (1,0))
            (c1, n0R ) = intersectionLocal @Neg0 c12 negcalc1 negcalc2 (getDd c12 negcalc1) (getDd c13 negcalc2)
            (c12, negcalc1) = unionLocal @Neg0 c n1A b_id n1A_dd b
            (c13, negcalc2) = (if n0A == (1,0) then (c2, n0R') else (c14, negcalc3))
            (c14, negcalc3) = remove_outercomplement_from @Neg0 c2 n1A n0R' n1A_dd (getDd c2 n0R')
            (c2, n0R')  = mixedIntersection @Neg0 c b_id dcA b dcA_dd
            in insert c1 $ InfNodes positionA dcA (0,0) n0R (0,0) (1,0)
        Pos1 -> let -- replace all the A stuf with (dc: (1,0), neg1: (1,0), neg0: (1,0), pos1: a, pos0: (1,0))
            (c1, p1R')  = unionLocal @Pos1 c p1A b_id p1A_dd b
            (c2, p1R ) = mixedUnion @Pos1 c1 p1R' dcA (getDd c' p1R') dcA_dd
            in insert c2 $ InfNodes positionA (0,0) (0,0) (1,0) p1R (1,0)
        Pos0 -> let -- replace all the A stuf with (dc: (1,0), neg1: (1,0), neg0: a, pos1: (1,0), pos0: (1,0))
            (c1, p0R ) = intersectionLocal @Pos0 c12 poscalc1 poscalc2 (getDd c12 poscalc1) (getDd c13 poscalc2)
            (c12, poscalc1) = unionLocal @Pos0 c n1A b_id n1A_dd b
            (c13, poscalc2) = (if p0A == (1,0) then (c2, p0R') else (c14, poscalc3))
            (c14, poscalc3) = remove_outercomplement_from @Pos0 c2 n1A p0R' n1A_dd (getDd c2 p0R')
            (c2, p0R')  = mixedIntersection @Pos0 c b_id dcA b dcA_dd
            in insert c1 $ InfNodes positionA dcA (0,0) (1,0) (0,0) p0R

        where
            (c, b_id) = insert c' $ EndInfNode b_id'
            b = getDd c b_id
            dcA_dd = getDd c dcA
            n1A_dd = getDd c n1A
            n0A_dd = getDd c n0A
            p1A_dd = getDd c p1A
            p0A_dd = getDd c p0A

unionInferB' _ _ _ _ _ = undefined

unionMain :: Context -> NodeId -> NodeId -> (Context, NodeId)
-- -- exclusive points (0's / holes) under union are filled unless they are present in both A and B (so only an intersection between them needs to be done)
-- -- inclusive point (1's ) under union are intersected with the opposite infinite subset (dc) before they are added together
unionMain c !a_id !b_id = debug_manipulation (unionMain' c a_id b_id (getDd c a_id) (getDd c b_id))
    "union" "unionMain" c a_id b_id
unionMain' :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
unionMain' c a_id b_id a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B)
    | positionA == positionB =  let
        (c1, dcR) = unionLocal @Dc c dcA dcB (getDd c dcA)  (getDd c dcB)
        (c2, n1R') = rOr1'_rule @Or @Neg "" c1 n1A n1B dcA dcB --`debug` ("n1R' \n" ++ show_dd settings c p1A)
        (c3, n0R') = rAnd1'_rule @Or @Neg "" c2 n1R' n0A n0B dcA dcB -- holes get unioned, because i keep the consequence of holes "uncomplemented" we get local union then intersection.
        (c4, n1R) = rOr1_rule @Or @Neg "" c3 n1R' dcR
        (c5, n0R) = rAnd1_rule @Or @Neg "" c4 n1R' dcR n0R' n0A n0B

        (c6, p1R') = rOr1'_rule @Or @Pos "" c5 p1A p1B dcA dcB --`debug` ("p1R' \n" ++ show_dd settings c p1A)
        (c7, p0R') = rAnd1'_rule @Or @Pos "" c6 p1R' p0A p0B dcA dcB --`debug` "p0R'"
        (c8, p1R) = rOr1_rule @Or @Pos "" c7 p1R' dcR --`debug` "p1R"
        (c9, p0R) = rAnd1_rule @Or @Pos "" c8 p1R' dcR p0R' p0A p0B --`debug` "p0R"
    in insert c9 $ InfNodes positionA dcR n1R n0R p1R p0R
    | positionA > positionB = withCache c (a_id, b_id, "union") $ unionInferA c a_id b_id a b --`debug` ("unionA: " ++ (show_dd settings c a_id) ++ "\n" ++ (show_dd settings c b_id))
    | positionA < positionB = withCache c (a_id, b_id, "union") $ unionInferB c a_id b_id a b -- replace all the A stuf with (dc: a, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
unionMain' c a_id b_id a b = error (show a ++ ", " ++ show_dd settings c b_id ++ ", "++ show c)


-- -- captures the general patterns for the functions
class Dd1 a where
    intersectionLocal' :: DdManipulation
    mixedIntersection' :: DdManipulation
    mixedUnion' :: DdManipulation
    unionLocal' :: DdManipulation
    remove_outercomplement_from' :: DdManipulation
    absorb' :: DdManipulation
    traverse_and_return' :: Bool -> Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
    r1_rule :: Bool -> String -> Context -> NodeId -> NodeId -> NodeId -> NodeId -> NodeId -> (Context, NodeId)
    r1'_rule :: Bool -> String -> Context -> NodeId -> NodeId -> NodeId -> NodeId -> NodeId -> (Context, NodeId)
    r0_rule :: Bool -> String -> Context -> NodeId -> NodeId -> (Context, NodeId)
    r0'_rule :: Bool -> String -> Context -> NodeId -> NodeId -> NodeId -> NodeId -> (Context, NodeId)
    apply :: FType -> Context -> NodeId -> NodeId -> String -> DdManipulation -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
    apply2 :: FType -> Context -> NodeId -> NodeId -> String -> DdManipulation -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)



instance (DdF4 a) => Dd1 a where
    r1_rule b s c _0R' dcR _1R' _1A _1B = case s of
        "" -> let
            (c2, _1R) = absorb @a c21 _1R1 dcR (getDd c21 _1R1) (getDd c dcR)
            (c21, _1R1) = (if b then unionLocal @a else intersectionLocal @a ) c22 _1R2 _1R3 (getDd c22 _1R2) (getDd c22 _1R3)
            (c22, _1R2) = (if b then intersectionLocal @a else unionLocal @a) c23 _1A _1B (getDd c _1A) (getDd c _1B) -- overlapping points are by definition not inside the others dc, thus have to be preserved
            (c23, _1R3) = if _0R' == if b then (1,0) else (0,0)
                    then (c, _1R')
                    else remove_outercomplement_from @a c _0R' _1R' (getDd c _0R') (getDd c _1R')  -- holes absorb points under intersection
            --     `debug` (("\n_1R \t ((_1A ^ _1B) v (_0R' / _1R')) @ dcR \t = " ++ show (absorb @a c a_id b_id (unionLocal @a c
            --         (intersectionLocal @a c _1A _1B)
            --         (if _0R' == (1,0) then _1R' else remove_outercomplement_from @a c _0R' _1R')) dcR)
            --     ++ "\n \t ((_1A ^ _1B) v (_0R' / _1R')) = " ++  show (unionLocal @a c
            --         (intersectionLocal @a c _1A _1B)
            --         (if _0R' == (1,0) then _1R' else remove_outercomplement_from @a c _0R' _1R')))
            --     ++ "\n\t (_1A ^ _1B) = " ++ show (intersectionLocal @a c _1A _1B)
            --     ++ "\n \t (_0R' / _1R') = " ++ show (if _0R' == (1,0) then _1R' else remove_outercomplement_from @a c _0R' _1R')
            --     ++ "\n \t _0R' = " ++ show _0R'
            --     ++ "\n\t _1R' = " ++ show _1R')
            in (c2, _1R) -- `debug` "r1"
        _ -> error "wrong string in rule"

    r1'_rule b s c n0R' _1A _1B dcA dcB = case s of
        "" -> let
            (c3, _1R') = (if b then unionLocal @a else intersectionLocal @a) c31 _1R'1 _1R'2 (getDd c31 _1R'1) (getDd c32 _1R'2)-- guaranteed that dcA and dcB do not overlap around the finite points, thus they do not get absorbed
            (c31, _1R'1) = (if b then mixedIntersection @a else mixedUnion @a) c32 _1A dcB (getDd c _1A) (getDd c dcB) -- keep the points that fit inside B
            (c32, _1R'2) = (if b then mixedIntersection @a else mixedUnion @a) c _1B dcA (getDd c _1B) (getDd c dcA) -- keep the points that fit inside A
                -- `debug` ("\n_1R' ((_1A ^ dcB) v (_1B ^ dcA)) \t = " ++ show (unionLocal @a c-- guaranteed that dcA and dcB do not overlap around the finite points, thus they do not get absorbed
                -- (mixedIntersection @a c _1A dcB) -- keep the points that fit inside B
                -- (mixedIntersection @a c _1B dcA)))
            in (c3, _1R') -- `debug` "r1'"
        _ -> error "wrong string in rule"


    r0_rule b s c _0R' dcR = case s of
        "" -> let
            (c4, _0R) = absorb @a c _0R' dcR (getDd c _0R') (getDd c dcR) in (c4, _0R)
                -- `debug` (col Vivid Green "\n_0R " ++ "\t (_0R' ^ dcR) @ dcR = " ++ show (absorb @a c41 _0R1 dcR (getDd c41 _0R1) (getDd c dcR)))
        _ -> error "wrong string in rule"

    -- we can add a speed up: in case of intersection and 1 context we can use dcR instead of 2 calls to dcA and dcB. Ofcourse the dual also works for union and 0
    -- todo add dcA dcB
    r0'_rule b s c _0A _0B dcA dcB = case s of
        "" -> let
            (c', r) = (if b then intersectionLocal @a else unionLocal @a) c51 _0A _0B (getDd c51 _0R'1)  (getDd c52 _0R'2)
            (c51, _0R'1) = (if b then mixedUnion @a else mixedIntersection @a) c52 _0A dcB (getDd c _0A) (getDd c dcB)
            (c52, _0R'2) = (if b then mixedUnion @a else mixedIntersection @a) c _0B dcA (getDd c _0B) (getDd c dcA)
            in (c', r)
        _ -> error "wrong string in rule"


    -- | take cache keys, manipulation function and its arguments, gives its result back with insertion in nodelookup map, func cache and elim rule
    apply operator c a_key b_key f_key f a_id b_id a b = let (c', r) = f c{func_stack = (to_constr @a, operator) : func_stack c} a_id b_id a b in withCache c' (a_key, b_key, f_key) $ applyInfElimRule @a c' $ getDd c' r --`debug` "apply" -- `debug` ("apply"  ++ (show_dd settings c a_id) ++ "\n" ++ (show_dd settings c b_id) ++ " ==> \n" ++ (show_dd settings c' r))
    apply2 operator c a_key b_key f_key f a_id b_id a b = let (c', r) = f c{func_stack = (to_constr @a, operator)  : func_stack c} a_id b_id a b in withCache c' (a_key, b_key, f_key) $ applyInfElimRule2 @a c' $ getDd c' r -- `debug` ("apply2222222222222222222222222222222222"  ++ (show_dd settings c a_id) ++ "\n" ++ (show_dd settings c b_id) ++ " ==> \n" ++ (show_dd settings c' r))
     -- reached leaf, so return a result here
    remove_outercomplement_from' c a_id b_id a@(Leaf _) b@(Leaf _)
        | a_id == false @a = (c, false @a)  --oposite, thus turn false and true around (becaus @a implies the type of b)
        | b_id == false @a = (c, false @a)
        | otherwise = (c, true @a)
    remove_outercomplement_from' c a_id b_id a@(Leaf _) b@(Node _ _ _)
        | a_id == false @a = (c, false @a)
        | a_id == true @a = (c, b_id) -- inferNodeA_opposite @a (remove_outercomplement_from @a) c a_id b_id a b
    remove_outercomplement_from' c a_id b_id a@(Node _ _ _) b@(Leaf _)
        | b_id == false @a = (c, false @a)
        | b_id == true @a = (c, a_id) -- inferNodeB @a (remove_outercomplement_from @a) c a_id b_id a b
    remove_outercomplement_from' c a_id b_id a@(Leaf _) b@(InfNodes {})
        | a_id == false @a = (c, false @a)
        | a_id == true @a = (c, b_id) `debug` ("remove from " ++ show (true @a) ++ " resulting in: " ++ show_dd settings c b_id)
    remove_outercomplement_from' c a_id b_id a@(InfNodes {}) b@(Leaf _)
        | b_id == false @a = (c, false @a)
        | b_id == true @a = (c, a_id) `debug` ("remove from " ++ show (true @a) ++ " resulting in: " ++ show a)
    remove_outercomplement_from' c a_id b_id a@(EndInfNode a') b@(Leaf _)
        | b_id == false @a = (c, false @a) -- bot
        | b_id == true @a = applyInfElimRule @a c (getDd c a')
    remove_outercomplement_from' c a_id b_id a@(Leaf _) b@(EndInfNode b')
        | a_id == false @a = (c, false @a) -- bot
        | a_id == true @a = applyInfElimRule @a c (getDd c b')
    remove_outercomplement_from' Context{func_stack=[]} _ _ a@(EndInfNode _) b@(Leaf _) = error "empty context"


    remove_outercomplement_from' c a_id b_id a@(Node positionA pos_childA neg_childA) b@(EndInfNode d) = inferNodeB @a (remove_outercomplement_from @a) c a_id b_id a b
    remove_outercomplement_from' c a_id b_id a@(EndInfNode d) b@(Node positionB pos_childB neg_childB) = inferNodeA_opposite @a (remove_outercomplement_from @a) c a_id b_id a b
--     -- removecomplements cannot be nested
    remove_outercomplement_from' c@(Context{func_stack = (f:fs)}) a_id b_id (EndInfNode a) (EndInfNode b) = let (c', r) = (negation c a (getDd c a)) in continue_outer f c'{func_stack = fs} r b (getDd c' r) (getDd c b)  -- todo negation a makes sense? or should i use maybe_negate on both to make sure we get the same polarity?
    remove_outercomplement_from' c@(Context{func_stack = []}) a_id b_id a@(EndInfNode childA)  b@(EndInfNode childB) = error "should not have empty context stack"

    -- No leafs involved
    remove_outercomplement_from' c a_id b_id a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)-- no mismatch, thus no inference is needed

        -- No mismatch, only the appropriate ZDD elim is applied
        | positionA == positionB =
            let (c', pos_result) = remove_outercomplement_from @a c pos_childA pos_childB (getDd c neg_childA) (getDd c neg_childB)
                (c'', neg_result) = remove_outercomplement_from @a c' neg_childA neg_childB (getDd c neg_childA) (getDd c neg_childB)
            in withCache c (a_id, b_id, "remove_outercomplement") $ applyElimRule @a c'' (Node positionA pos_result neg_result)

        -- mismatch with no Bot involved, thus with ZDD types inference we return bot
        | positionA < positionB = remove_outercomplement_from @a c neg_childA b_id (getDd c neg_childA) b
        | positionA > positionB =
            withCache c (a_id, b_id, "remove_outercomplement") $ let (c', r) = (remove_outercomplement_from @a c a_id neg_childB a (getDd c neg_childB)) in insert c' $ Node positionB pos_childB r


    remove_outercomplement_from' c a_id b_id a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) -- check define inner recursion for lobsided intersectio/union: (-. a .^. b)?
        | positionA > positionB = case to_constr @a of
            Dc -> error "remove outer complement from with a dc should not be possible"
            Neg1 -> f True
            Neg0 -> f False
            Pos1 -> f True
            Pos0 -> f False
        | positionA < positionB =  withCache c (a_id, b_id, "remove_outercomplement") $ remove_outercomplement_from @a c neg_childA b_id (getDd c neg_childA) b
        | positionA == positionB =  undefined
        where
            f b' = apply @a Remove c a_id b_id "remove_outercomplement" (t_and_rInferA_ @a b') a_id b_id a b

    remove_outercomplement_from' c a_id b_id a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB)
        | positionA > positionB =  withCache c (a_id, b_id, "remove_outercomplement") $ remove_outercomplement_from @a c a_id neg_childB a (getDd c neg_childB)
        | positionA < positionB =   case to_constr @a of
            Dc -> error "remove outer complement from with a dc should not be possible"
            Neg1 -> f False
            Neg0 -> f True
            Pos1 -> f False
            Pos0 -> f True
        | positionA == positionB =  undefined
        where
            f b' = apply @a Remove c a_id b_id "remove_outercomplement" (t_and_rInferB_ @a b') a_id b_id a b


    remove_outercomplement_from' c a_id b_id a@(InfNodes{}) b@(EndInfNode d) =
        case to_constr @a of
            Dc -> error "remove outer complement from with a dc should not be possible"
            Neg1 -> f False
            Neg0 -> f True
            Pos1 -> f False
            Pos0 -> f True
        where
            f b' = apply @a Remove c a_id b_id "remove_outercomplement" (t_and_rInferB_ @a b') a_id b_id a b

    remove_outercomplement_from' c a_id b_id a@(EndInfNode d) b@(InfNodes{}) =
        case to_constr @a of
            Dc -> error "remove outer complement from with a dc should not be possible"
            Neg1 -> f False
            Neg0 -> f True
            Pos1 -> f False
            Pos0 -> f True
        where
            f b' = apply @a Remove c a_id b_id "remove_outercomplement" (t_and_rInferA_ @a b') a_id b_id a b


    remove_outercomplement_from' c a_id b_id a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B)
        | positionA == positionB = case to_constr @a of
            Dc -> error "absorb with a dc as first argument should not be possible"
            Neg1 -> fm False
            Neg0 -> fm True
            Pos1 -> fm False
            Pos0 -> fm True
        | positionA < positionB = case to_constr @a of
            Dc -> error "remove outer complement from with a dc should not be possible"
            Neg1 -> fb False
            Neg0 -> fb True
            Pos1 -> fb False
            Pos0 -> fb True
        | positionA > positionB = case to_constr @a of
            Dc -> error "remove outer complement from with a dc should not be possible"
            Neg1 -> fa False
            Neg0 -> fa True
            Pos1 -> fa False
            Pos0 -> fa True
        where
            fm b' = apply @a Remove c a_id b_id "remove_outercomplement" (t_and_rMain b') a_id b_id a b
            fb b' = apply @a Remove c a_id b_id "remove_outercomplement" (t_and_rInferB_ @a b') a_id b_id a b
            fa b' = apply @a Remove c a_id b_id "remove_outercomplement" (t_and_rInferA_ @a b') a_id b_id a b

    remove_outercomplement_from' c a_id b_id a b = undefined `debug4` (show a ++ "  :  " ++ show_dd settings c b_id)

    intersectionLocal' c a_id b_id a@(Leaf True) b@InfNodes{} = insert c $ EndInfNode b_id
    intersectionLocal' c a_id b_id a@(Leaf True) (EndInfNode (0,0)) = (c, (0,0))
    intersectionLocal' c a_id b_id a@(Leaf True) (EndInfNode (1,0)) = (c, (1,0))
    intersectionLocal' c a_id b_id a@(Leaf True) b = (c, b_id) --`debug` ("returning" ++ show_dd settings c b_id_id)
    intersectionLocal' c@(Context{func_stack = (f:fs)}) a_id b_id a@(Leaf False) b@(EndInfNode childB ) = withCache c (a_id, b_id, "remove_outercomplement") $ intersectionLocal_arg f c{func_stack = fs} a_id childB a (getDd c childB)

    intersectionLocal' c a_id b_id a@(Leaf False) (EndInfNode (0,0)) = (c, (0,0))  --`debug` ("returning" ++ show a_id)-- dc case for leafs
    intersectionLocal' c a_id b_id a@(Leaf False) (EndInfNode (1,0)) = (c, (0,0))  --`debug` ("returning" ++ show a_id)-- dc case for leafs
    intersectionLocal' c a_id b_id a@(Leaf False) b@(Leaf _) = (c, (0,0))  --`debug` ("returning" ++ show a_id)-- dc case for leafs

    intersectionLocal' c a_id b_id a@(Leaf False) b@(InfNodes {}) =  apply @a Inter c a_id b_id "remove_outercomplement" (intersectionInferA_ @a) a_id b_id a b -- leaf with node or end infnode
    intersectionLocal' c a_id b_id a@(Leaf False) b = inferNodeA @a (intersectionLocal @a) c  a_id b_id a b -- leaf with node or end infnode

    intersectionLocal' c a_id b_id a@InfNodes{} b@(Leaf True) = insert c $ EndInfNode a_id
    intersectionLocal' c a_id b_id (EndInfNode (0,0)) b@(Leaf True) = (,) c (0,0)
    intersectionLocal' c a_id b_id (EndInfNode (1,0)) b@(Leaf True) = (,) c (1,0)
    intersectionLocal' c a_id b_id a b@(Leaf True) = (,) c a_id
    intersectionLocal' c@(Context{func_stack = (f:fs)}) a_id b_id a@(EndInfNode childA ) b@(Leaf False) = apply @a Inter c{func_stack = fs} a_id b_id "remove_outercomplement" (intersectionLocal_arg f) childA b_id (getDd c childA) b

    intersectionLocal' c a_id b_id a@(InfNodes {}) b@(Leaf False) = apply @a Inter c a_id b_id "remove_outercomplement" (intersectionInferB_ @a) a_id b_id a b -- leaf with node or end infnode
    intersectionLocal' c a_id b_id a b@(Leaf False) = inferNodeB @a (intersectionLocal @a) c a_id b_id a b -- leaf with node or end infnode

    -- infer node at DdF4, and here the shared abstrations
    intersectionLocal' c a_id b_id a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
        -- Match
        | positionA == positionB =
            let (c', pos_result) = supply_dds (intersectionLocal @a) c pos_childA pos_childB
                (c'', neg_result) = supply_dds (intersectionLocal @a) c' neg_childA neg_childB
            in  withCache c (a_id, b_id, "intersection") $ applyElimRule @a c'' (Node positionA pos_result neg_result)
        -- Mismatch, but with a inference we ontinue recursion with the earliest (thus lowest valued) node.
        | positionA < positionB = inferNodeB @a (intersectionLocal @a) c a_id b_id a b
        | positionA > positionB = inferNodeA @a (intersectionLocal @a) c a_id b_id a b

    -- go one recursive layer deeper !
    intersectionLocal' c a_id b_id a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB =  inferNodeA @a (intersectionLocal @a) c  a_id b_id a b -- infer node A
        | positionA < positionB = apply @a Inter c a_id b_id "intersection" (intersectionInferB_ @a) a_id b_id a b -- infer infnode B and start intersection inside it
    intersectionLocal' c a_id b_id a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB _ _ _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB =  apply @a Inter c a_id b_id "intersection" (intersectionInferA_ @a) a_id b_id a b
        | positionA < positionB =  inferNodeB @a (intersectionLocal @a) c  a_id b_id a b
    intersectionLocal'  c a_id b_id a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _)
        | positionA == positionB =  apply @a Inter c a_id b_id "intersection" (intersection) a_id b_id a b --`debug5` ("infinf: " ++ show a ++ show b ++ "\n"++ show_dd settings c a_id ++ show_dd settings c b_id) -- start intersection and push local-intersection to the context
        | positionA < positionB =  apply @a Inter c a_id b_id "intersection" (intersectionInferB_ @a) a_id b_id a b -- infer infnode B
        | positionA > positionB =  apply @a Inter c a_id b_id "intersection" (intersectionInferA_ @a) a_id b_id a b -- infer infnode A
    intersectionLocal' c a_id b_id a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) =  apply @a Inter c a_id b_id "intersection" (intersectionInferB_ @a) a_id b_id a b
    intersectionLocal' c a_id b_id a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) =  apply @a Inter c a_id b_id "intersection" (intersectionInferA_ @a) a_id b_id a b

    -- continue local traversal
    intersectionLocal' c a_id b_id a@(Node positionA pos_childA neg_childA) b@(EndInfNode childB) = inferNodeB @a (intersectionLocal @a) c a_id b_id a b
    intersectionLocal' c a_id b_id a@(EndInfNode childA) b@(Node positionB pos_childB neg_childB) = inferNodeA @a (intersectionLocal @a) c a_id b_id a b
    -- continue previous super domain traversal
    intersectionLocal' c@(Context{func_stack = (f:fs)}) a_id b_id a@(EndInfNode childA)  b@(EndInfNode childB) = withCache c (a_id, b_id, "intersection") $ (continue_outer f c{func_stack = fs} childA childB (getDd c childA) (getDd c childB)) --`debug` ("endinfendinf interLocqal : " ++ "show (continue_outer f c{func_stack=fs} childA childB)" ++ " \n : " ++ show childA ++ " , " ++ show childB)
    intersectionLocal' c@(Context{func_stack = []}) a_id b_id a@(EndInfNode childA)  b@(EndInfNode childB) = error "should not have empty context stack"-- applyInfElimRule @a c $ intersection  Context{func_stack = []} childA childB


    intersectionLocal' c a_id b_id a b = error ("how did we get here? " ++  show c ++ show a ++ "  -  " ++ show_dd settings c b_id)

    unionLocal' c a_id b_id a@(Leaf False) b@(InfNodes {}) = insert c $ EndInfNode b_id --`debug` "insert in leaf false kk"
    unionLocal' c a_id b_id a@(Leaf False) (EndInfNode (0,0)) = (,) c (0,0)
    unionLocal' c a_id b_id a@(Leaf False) (EndInfNode (1,0)) = (,) c (1,0)
    unionLocal' c a_id b_id a@(Leaf False) b = (,) c b_id  --findme --  fix below - add endinfnode?
    unionLocal' c@(Context{func_stack = (f:fs)}) a_id b_id a@(Leaf True) b@(EndInfNode childB ) = withCache c (a_id, b_id, "union") $ unionLocal_arg f c{func_stack = fs} a_id childB a (getDd c childB) --`debug` ("endif a = true, f_stack = " ++ show f ++ "," ++ show fs ++ " a: " ++ show a ++ " b: " ++ show childB)
    unionLocal' c a_id b_id a@(Leaf True) (EndInfNode (0,0)) = (,) c (1,0)
    unionLocal' c a_id b_id a@(Leaf True) (EndInfNode (1,0)) = (,) c (1,0)
    unionLocal' c a_id b_id a@(Leaf True) b@(Leaf _) = (,) c (1,0)
    unionLocal' c a_id b_id a@(Leaf True) b@(InfNodes {}) =  apply @a Union c a_id b_id "union" (unionInferA_ @a) a_id b_id a b
    unionLocal' c a_id b_id a@(Leaf True) b = inferNodeA @a (unionLocal @a) c a_id b_id a b -- leaf with node or end infnode

    unionLocal' c a_id b_id a@(InfNodes {}) b@(Leaf False) = insert c $ EndInfNode a_id --`debug` ("insert in leaf false kk" ++ show_dd settings c a_id ++ "\n" ++ show a)
    unionLocal' c a_id b_id (EndInfNode (0,0)) b@(Leaf False) = (,) c (0,0)
    unionLocal' c a_id b_id (EndInfNode (1,0)) b@(Leaf False) = (,) c (1,0)
    unionLocal' c a_id b_id a b@(Leaf False) = (,) c a_id
    unionLocal' c@(Context{func_stack = (f:fs)}) a_id b_id a@(EndInfNode childA ) b@(Leaf True) = withCache c (a_id, b_id, "union") $ unionLocal_arg f c{func_stack = fs} childA b_id (getDd c childA) b --`debug` ("endif b = true, f_stakc = " ++ show f ++ "," ++ show fs ++ " a: " ++ show childA ++ " b: "  ++ show_dd settings c b_id)

    unionLocal' c a_id b_id a@(InfNodes {}) b@(Leaf True) = apply @a Union c a_id b_id "union" (unionInferB_ @a) a_id b_id a b
    unionLocal' c a_id b_id a b@(Leaf True) = inferNodeB @a (unionLocal @a) c a_id b_id a b -- leaf with node or end infnode


    unionLocal' c a_id b_id a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
        -- no mismatch, only the appropriate elim rule is applied
        | positionA == positionB =
            let (c', pos_result) = supply_dds (unionLocal @a) c pos_childA pos_childB
                (c'', neg_result) = supply_dds (unionLocal @a) c' neg_childA neg_childB
            in withCache c (a_id, b_id, "union") $ applyElimRule @a c'' (Node positionA pos_result neg_result)
        | positionA < positionB = inferNodeB @a (unionLocal @a) c a_id b_id a b
        | positionA > positionB = inferNodeA @a (unionLocal @a) c a_id b_id a b

    unionLocal' c a_id b_id a@(InfNodes positionA _ _ _ _ _)  b@(Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB = inferNodeA @a (unionLocal @a) c a_id b_id a b
        | positionA < positionB = apply @a Union c a_id b_id "union" (unionInferB_ @a) a_id b_id a b -- infer infnode for A

    unionLocal' c a_id b_id a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes" -- a possible option: (InfNodes (dcA .*. pos_childB) (n1A .*. pos_childB) (n0A .*. pos_childB) (p1A .*. pos_childB) (p0A .*. pos_childB))
        | positionA < positionB =  inferNodeB @a (unionLocal @a) c a_id b_id a b
        | positionA > positionB =  apply @a Union c a_id b_id "union" (unionInferA_ @a) a_id b_id a b -- infer infnode for B

    unionLocal' c a_id b_id a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _)
        | positionA == positionB = apply @a Union c{func_stack = (to_constr @a, Union) : func_stack c} a_id b_id "union" union a_id b_id a b
        | positionA < positionB =  apply @a Union c a_id b_id "union" (unionInferB_ @a) a_id b_id a b -- infer infnode A
        | positionA > positionB =  apply @a Union c a_id b_id "union" (unionInferA_ @a) a_id b_id a b -- infer infnode B

    unionLocal' c a_id b_id a@(InfNodes {}) b@(EndInfNode _) =  apply @a Union c a_id b_id "union" (unionInferB_ @a) a_id b_id a b
    unionLocal' c a_id b_id a@(EndInfNode _) b@(InfNodes {}) =  apply @a Union c a_id b_id "union" (unionInferA_ @a) a_id b_id a b

    -- continue local traversal
    unionLocal' c a_id b_id a@(Node positionA pos_childA neg_childA) b@(EndInfNode childB) = inferNodeB @a (unionLocal @a) c a_id b_id a b
    unionLocal' c a_id b_id a@(EndInfNode childA) b@(Node positionB pos_childB neg_childB) = inferNodeA @a (unionLocal @a) c a_id b_id a b

--     -- continue previous super domain traversal
    unionLocal' c@(Context{func_stack = (f:fs)}) a_id b_id a@(EndInfNode childA)  b@(EndInfNode childB) = withCache c (a_id, b_id, "union") $ continue_outer f c{func_stack = fs} childA childB (getDd c childA) (getDd c childB)  --`debug` ("endinf endinf union local, childA = " ++ show childA  ++ " \n \t childB = " ++ show childB )
    unionLocal' c@(Context{func_stack = []}) a_id b_id a@(EndInfNode childA)  b@(EndInfNode childB) = error "should not have empty context stack"  -- applyInfElimRule @a c $ union  Context{func_stack = []} childA childB
    unionLocal' c a_id b_id a b = error (show c ++ show a ++ show_dd settings c b_id)

    -- todo add endinf (0,0) / (1,0) case?
    mixedIntersection' c a_id b_id (Leaf _) (Leaf _) = if a_id == false @a then (c, false @a) else (c, (0,0))-- if n then 1 if n' then 0
    -- exception cases where zdd and its polar are not false @a, and dc is not a leaf.

    mixedIntersection' c a_id b_id (Leaf False) b = (c, (0,0))
    mixedIntersection' c a_id b_id (Leaf True) (EndInfNode (0,0)) = if a_id == false @a then (c, false @a) else (c, (0,0))
    mixedIntersection' c a_id b_id (Leaf True) (EndInfNode (1,0)) = if a_id == false @a then (c, false @a) else (c, (1,0))
    mixedIntersection' c a_id b_id (Leaf True) b = if a_id == false @a then (c, false @a) else (c, b_id)
    -- exception where the zdd is not a leaf and dc is
    mixedIntersection' c a_id b_id a (Leaf False) = (c, (0,0))
    -- note that the a cannot be larger than 1 thus, the positive polarity of the zdd cannot not be one in this case (since it will always be largerthan dcR under intersection)
    mixedIntersection' c a_id b_id (EndInfNode (0,0)) (Leaf True) = (c, (0,0))
    mixedIntersection' c a_id b_id (EndInfNode (1,0)) (Leaf True) = (c, (1,0))
    mixedIntersection' c a_id b_id a (Leaf True) = (c, a_id)

    -- No leafs involved
    mixedIntersection' c a_id b_id a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

        -- No mismatch
        | positionA == positionB =
            let (c', pos_result) = mixedIntersection @a c pos_childA pos_childB (getDd c pos_childA) (getDd c pos_childB)
                (c'', neg_result) = mixedIntersection @a c' neg_childA neg_childB (getDd c neg_childA) (getDd c neg_childB)
            in withCache c'' (a_id, b_id, "intersection") $ applyElimRule @a c'' (Node positionA pos_result neg_result)

--         -- Mismatch
        | positionA > positionB = inferNodeA @a (mixedIntersection @a) c a_id b_id a b
        | positionA < positionB =
            let (c', pos_result) = mixedIntersection @a c pos_childA b_id (getDd c pos_childA) b
                (c'', neg_result) = mixedIntersection @a c' neg_childA b_id (getDd c neg_childA) b
            in withCache c'' (a_id, b_id, "intersection") $ applyElimRule @a c'' (Node positionA pos_result neg_result)

    -- Single InfNode has been reached, similar to single Leaf node cases.
    mixedIntersection' c a_id b_id a@(Node positionA pos_childA neg_childA)  b@(EndInfNode _) =
                let (c', pos_result) = mixedIntersection @a c pos_childA b_id (getDd c pos_childA) b
                    (c'', neg_result) = mixedIntersection @a c' neg_childA b_id (getDd c neg_childA) b
                in withCache c (a_id, b_id, "intersection") $ applyElimRule @a c'' (Node positionA pos_result neg_result)

    mixedIntersection' c a_id b_id a@(EndInfNode _) b@(Node positionB pos_childB neg_childB) =
        inferNodeA @a (mixedIntersection @a) c a_id b_id a b

    mixedIntersection' c a_id b_id a@(InfNodes positionA dcA n1A n0A p1A p0A) b@(InfNodes positionB dcB n1B n0B p1B p0B)
        | positionA == positionB = apply @a MixedIntersection c a_id b_id "intersection" (intersection) a_id b_id a b
        | positionA > positionB = apply @a MixedIntersection c a_id b_id "intersection" (intersectionInferA_ @a) a_id b_id a b
        | positionB > positionA = apply @a MixedIntersection c a_id b_id "intersection" (intersectionInferB_ @a) a_id b_id a b

    mixedIntersection' c a_id b_id a@(InfNodes positionA dcA n1A n0A p1A p0A) b@(Node positionB pos_childB neg_childB)
        | positionA == positionB = error "not yet implemented for zdd types, bdd is impossible"
        | positionA > positionB = inferNodeA @a (mixedIntersection @a) c a_id b_id a b
        | positionB > positionA = apply @a MixedIntersection c a_id b_id "intersection" (intersectionInferB_ @a) a_id b_id a b
    mixedIntersection' c a_id b_id a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB dcB n1B n0B p1B p0B)
        | positionA == positionB = error "not yet implemented for zdd types, bdd is impossible"
        | positionA > positionB = apply @a MixedIntersection c a_id b_id "intersection" (intersectionInferA_ @a) a_id b_id a b
        | positionB > positionA =
                let (c', pos_result) = mixedIntersection @a c pos_childA b_id (getDd c pos_childA) b
                    (c'', neg_result) = mixedIntersection @a c' neg_childA b_id (getDd c neg_childA) b
                in withCache c (a_id, b_id, "intersection") $ applyElimRule @a c'' (Node positionA pos_result neg_result)
    -- Both InfNodes have been reached - run the usual intersection.
    mixedIntersection' c@(Context{func_stack = (f:fs)}) a_id b_id (EndInfNode a)  (EndInfNode b) = withCache c (a_id, b_id, "intersection") $ continue_outer f c{func_stack = fs} a b (getDd c a) (getDd c b)
    mixedIntersection' c@(Context{func_stack = []}) a_id b_id (EndInfNode a)  (EndInfNode b) = error "should not have an empty context, check if top layer has DC context given along" -- apply @a c a_id b_id (intersection  Context{func_stack = []} a (negate_maybe @a b)
    mixedIntersection' c a_id b_id a b = error ("mixedinter - " ++ show c ++ " ; "++ show a ++ "  ;  " ++ show_dd settings c b_id)

    mixedUnion' c a_id b_id (Leaf _) (Leaf _) = if a_id == false @a then (c, false @a) else (c, (1,0))-- if n then 1 if n' then 0
    -- exception cases where zdd and its polar are not false @a, and dc is not a leaf.
    mixedUnion' c a_id b_id (Leaf True) (EndInfNode (1,0)) = (c, (1,0))
    mixedUnion' c a_id b_id (Leaf True) (EndInfNode (0,0)) = (c, (1,0))
    mixedUnion' c a_id b_id (Leaf True) b = (c, (1,0))
    mixedUnion' c a_id b_id (Leaf False) b = if a_id == false @a then (c, false @a) else (c,b_id)
    -- exception where the zdd is not a leaf and dc is
    mixedUnion' c a_id b_id (EndInfNode (1,0)) (Leaf True) = (c, (1,0))
    mixedUnion' c a_id b_id (EndInfNode (0,0)) (Leaf True) = (c, (1,0))
    mixedUnion' c a_id b_id a (Leaf True) = (c, (1,0))
    -- note that the a cannot be smaller than 0 thus, the negative polarity of the zdd cannot not be one in this case (since it will always be smaller than dcR under intersection)
    mixedUnion' c a_id b_id a (Leaf False) = (c, a_id)

    -- No leafs involved
    mixedUnion' c a_id b_id a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
        -- No mismatch
        | positionA == positionB =
            let (c', pos_result) = mixedUnion @a c pos_childA pos_childB (getDd c pos_childA) (getDd c pos_childB)
                (c'', neg_result) = mixedUnion @a c' neg_childA neg_childB (getDd c neg_childA) (getDd c neg_childB)
            in withCache c (a_id, b_id, "union") $ applyElimRule @a c'' (Node positionA pos_result neg_result)
        -- Mismatch
        | positionA > positionB = inferNodeA @a (mixedUnion @a) c a_id b_id a b
        | positionA < positionB =
            let (c', pos_result) = mixedUnion @a c pos_childA b_id (getDd c pos_childA) b
                (c'', neg_result) = mixedUnion @a c' neg_childA b_id (getDd c neg_childA) b
            in withCache c (a_id, b_id, "union") $ applyElimRule @a c'' (Node positionA pos_result neg_result)

    -- Single InfNode has been reached, similar to single Leaf node cases.
    mixedUnion' c a_id b_id a@(Node positionA pos_childA neg_childA)  b@(EndInfNode _) =
                let (c', pos_result) = mixedUnion @a c pos_childA b_id (getDd c pos_childA) b
                    (c'', neg_result) = mixedUnion @a c' neg_childA b_id (getDd c neg_childA) b
                in withCache c (a_id, b_id, "union") $ applyElimRule @a c'' (Node positionA pos_result neg_result)

    mixedUnion' c a_id b_id a@(EndInfNode _) b@(Node positionB pos_childB neg_childB) =
        inferNodeA @a (mixedUnion @a) c a_id b_id a b

    mixedUnion' c a_id b_id a@(InfNodes positionA dcA n1A n0A p1A p0A) b@(InfNodes positionB dcB n1B n0B p1B p0B)
        | positionA == positionB = apply @a Union c a_id b_id "union" (union) a_id b_id a b
        | positionA > positionB = apply @a Union c a_id b_id "union" (unionInferA_ @a) a_id b_id a b
        | positionB > positionA = apply @a Union c a_id b_id "union" (unionInferB_ @a) a_id b_id a b
    mixedUnion' c a_id b_id a@(InfNodes positionA dcA n1A n0A p1A p0A) b@(Node positionB pos_childB neg_childB)
        | positionA == positionB = error "not yet implemented for zdd types, bdd is impossible"
        | positionA > positionB = inferNodeA @a (mixedUnion @a) c a_id b_id a b
        | positionB > positionA = apply @a Union c a_id b_id "union" (unionInferB_ @a) a_id b_id a b
    mixedUnion' c a_id b_id a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB dcB n1B n0B p1B p0B)
        | positionA == positionB = undefined
        | positionA > positionB = apply @a Union c a_id b_id "union" (unionInferA_ @a) a_id b_id a b
        | positionB > positionA =
            let (c', pos_result) = mixedUnion @a c pos_childA b_id (getDd c pos_childA) b
                (c'', neg_result) = mixedUnion @a c' neg_childA b_id (getDd c neg_childA) b
            in withCache c (a_id, b_id, "union") $ applyElimRule @a c'' (Node positionA pos_result neg_result)
    -- Both InfNodes have been reached - run the usual union.
    mixedUnion' c@(Context{func_stack = (f:fs)}) a_id b_id (EndInfNode a)  (EndInfNode b) =  unionLocal_arg f c{func_stack = fs} a b (getDd c a) (getDd c b)
    mixedUnion' c@(Context{func_stack = []}) a_id b_id (EndInfNode a)  (EndInfNode b) = error "should not have an empty context, check if top layer has DC context given along" -- apply @a c a_id b_id (intersection  Context{func_stack = []} a (negate_maybe @a b)
    mixedUnion' c a_id b_id a b = error ("mixedunion - " ++ show c ++ " ; "++ show_dd settings c a_id ++ "  ;  " ++ show_dd settings c b_id)

    --todo add endinfnode (0,0) /(1,0) removal on leaf cases
    absorb' c a_id b_id a@(Leaf _) dc = if a == dc then (c, false @a) else (c, a_id)
    -- absorb' c a_id b_id a@(EndInfNode _) dc@(Node positionD pos_childD neg_childD)  = inferNodeA @a (absorb @a) c a_id b_id a dc
    absorb' c a_id b_id a@(EndInfNode a_child) dc@(Leaf _)  = if (getDd c a_child) == dc then (c, false @a) else (c, a_id)
    absorb' c a_id b_id a@(InfNodes {}) dc@(Leaf _)  = (c, a_id)
    absorb' c a_id b_id a@(Node positionA pos_childA neg_childA) dc@(EndInfNode _)  = --infere Dc node
        let (c', pos_result) = absorb @a c pos_childA b_id (getDd c pos_childA) dc
            (c'', neg_result) = absorb @a c' neg_childA b_id (getDd c neg_childA) dc
        in withCache c (a_id, b_id, "absorb") $ applyElimRule @a c'' (Node positionA pos_result neg_result)
    absorb' c a_id b_id a@(EndInfNode a') dc@(EndInfNode dc') = if a' == dc' then (c, false @a) else (c, a_id)
    absorb' c a_id b_id a@(Node positionA pos_childA neg_childA) dc@(Leaf _) =
        let (c', pos_result) = absorb @a c pos_childA b_id (getDd c pos_childA) dc
            (c'', neg_result) = absorb @a c' neg_childA b_id (getDd c neg_childA) dc
        in withCache c (a_id, b_id, "absorb") $ applyElimRule @a c'' (Node positionA pos_result neg_result)

    absorb' c a_id b_id a@(Node positionA pos_childA neg_childA)  dc@(Node positionD pos_childD neg_childD)
        -- No mismatch
        | positionA == positionD =
            let (c', pos_result) = absorb @a c pos_childA pos_childD (getDd c pos_childA) (getDd c pos_childD)
                (c'', neg_result) = absorb @a c' neg_childA neg_childD (getDd c neg_childA) (getDd c neg_childD)
            in withCache c (a_id, b_id, "absorb") $ applyElimRule @a c'' (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionD = inferNodeA @a (absorb @a) c a_id b_id a dc
        | positionA < positionD =
            let (c', pos_result) = absorb @a c pos_childA b_id (getDd c pos_childA) dc
                (c'', neg_result) = absorb @a c' neg_childA b_id (getDd c neg_childA) dc
            in withCache c (a_id, b_id, "absorb") $ applyElimRule @a c'' (Node positionA pos_result neg_result)

    absorb' c a_id b_id a@(InfNodes {}) b@(InfNodes {}) = case to_constr @a of
        Dc -> error "absorb with a dc as first argument should not be possible"
        Neg1 -> f True
        Neg0 -> f False
        Pos1 -> f True
        Pos0 -> f False
        where
            f b' = apply @a Absorb c a_id b_id "absorb" (t_and_rMain b') a_id b_id a b

    absorb' c a_id b_id a@(InfNodes positionA dcA n1A n0A p1A p0A) dc@(Node positionD pos_childD neg_childD)
        | positionA > positionD = inferNodeA @a (absorb @a) c a_id b_id a dc
        | positionA < positionD = case to_constr @a of
            Dc -> error "absorb with a dc as first argument should not be possible"
            Neg1 -> f True
            Neg0 -> f False
            Pos1 -> f True
            Pos0 -> f False
        | otherwise = undefined
            where
                f b' = apply @Dc Absorb c a_id b_id "absorb" (t_and_rInferB b') a_id b_id a dc
    -- add posB == posA, then we consider node to be AllNegs -> [1]
    absorb' c a_id b_id a@(Node positionA pos_childA neg_childA) dc@(InfNodes positionD dcA n1A n0A p1A p0A)
        | positionA > positionD =  case to_constr @a of
                Dc -> error "absorb with a dc as first argument should not be possible"
                Neg1 -> f True
                Neg0 -> f False
                Pos1 -> f True
                Pos0 -> f False
        | positionA < positionD =
            let (c', pos_result) = absorb @a c pos_childA b_id (getDd c pos_childA) dc
                (c'', neg_result) = absorb @a c' pos_childA b_id (getDd c neg_childA) dc
            in withCache c (a_id, b_id, "absorb") $ applyElimRule @a c'' (Node positionD pos_result neg_result)
        | otherwise = undefined
            where
                f b' = apply @a Absorb c a_id b_id "absorb" (t_and_rInferA b') a_id b_id a dc

    absorb' c a_id b_id a@(InfNodes{}) b@(EndInfNode _) = let
        l = not $ (to_constr @a) `elem` [Neg0, Pos0]
        in apply @Dc Absorb c a_id b_id "absorb" (t_and_rInferB_ @Dc l) a_id b_id a b -- intersectionInferB c{func_stack = ((to_constr @a, Absorb): func_stack c)} a_id b_id a b
    absorb' c a_id b_id a@(EndInfNode _) b@(InfNodes{}) = let
        l = not $ (to_constr @a) `elem` [Neg0, Pos0]
        in apply @a Absorb c a_id b_id "absorb" (t_and_rInferA_ @a l) a_id b_id a b -- intersectionInferB c{func_stack = ((to_constr @a, Absorb): func_stack c)} a_id b_id a b

    absorb' c a_id b_id a b = error $ "absorb , " ++ "a = " ++ show a ++ "b = " ++ show_dd settings c b_id


    -- use inferA because maybe we need to pop back to top level where absorb or remove_complement is being applied

    traverse_and_return' l c a_id b_id a'@(Leaf a) b'@(Leaf b)
        | absorb_or_remove c = if a == b && b == l then (c, leaf $ not l) else (c, b_id)
        | (a /= b) && b == l = (c, leaf $ not l)
        | otherwise = (c, b_id)
    traverse_and_return' l c a_id b_id a@(Leaf _) b@(InfNodes {})
        | absorb_or_remove c = if a == b && b == Leaf l then (c, leaf $ not l) else apply @a T_and_r c a_id b_id "traverse_and_return" (t_and_rInferA_ @a l) a_id b_id a b
        | (a /= b) && b == Leaf l = (c, leaf $ not l)
        | otherwise = apply @a T_and_r c a_id b_id "traverse_and_return" (t_and_rInferA_ @a l) a_id b_id a b
    traverse_and_return' l c a_id b_id a@(InfNodes {}) b@(Leaf _)
        | absorb_or_remove c = if a == b && b == Leaf l then (c, leaf $ not l) else apply @a T_and_r c a_id b_id "traverse_and_return" (t_and_rInferA_ @a l) a_id b_id a b
        | (a /= b) && b == Leaf l = (c, leaf $ not l)
        | otherwise = apply @a T_and_r c a_id b_id "traverse_and_return" (t_and_rInferA_ @a l) a_id b_id a b
    -- for when no Leaf is changed we return a, thus a should be of the right type
    -- test carefully
    -- first check whether the flip needs to happen before applying infelimrule
    traverse_and_return' l c@(Context{func_stack = (f:fs)}) a_id b_id a@(Leaf _) (EndInfNode b')  = if a == getDd c b' && a == Leaf l then (c, a_id) else apply @a T_and_r c a_id b_id "traverse_and_return" (t_and_r_arg f l) a_id b' a (getDd c b') -- what if EndInfNode EndInfnode (a == b); should not be possible since we require all DD's to be Endinfnode reduced.
    traverse_and_return' l c@(Context{func_stack = (f:fs)}) a_id b_id (EndInfNode a') b@(Leaf _)  = if getDd c a' == b && b == Leaf l then (c, b_id) else apply @a T_and_r c a_id b_id "traverse_and_return" (t_and_r_arg f l) a' b_id (getDd c a') b
    -- -- go back one recursively if on the context there is a t_and_r or absorb call
    traverse_and_return' l c@(Context{func_stack = (f:fs)}) a_id b_id a@(EndInfNode a') b@(EndInfNode b') = if a' == b' && b == Leaf l then (c, a_id) else apply @a T_and_r c a_id b_id "traverse_and_return" (t_and_r_arg f l) a' b' (getDd c a') (getDd c b')
    traverse_and_return' l Context{func_stack = []} _ _ _ _ = error "should not have an empty context, check if top layer has DC context given along"

    traverse_and_return' l c a_id b_id a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
        -- No mismatch
        | positionA == positionB =
            let (c', pos_result) = traverse_and_return @a l c pos_childA pos_childB (getDd c pos_childA) (getDd c pos_childB)
                (c'', neg_result) = traverse_and_return @a l c' neg_childA neg_childB (getDd c neg_childA) (getDd c neg_childB)
            in withCache c (a_id, b_id, "traverse_and_return") $ applyElimRule @a c'' (Node positionA pos_result neg_result)
        -- Mismatch
        | positionA > positionB = inferNodeA @a (traverse_and_return @a l) c a_id b_id a b
        | positionA < positionB = inferNodeB @a (traverse_and_return @a l) c a_id b_id a b
        -- fix : endinfnode
    traverse_and_return' l c a_id b_id a@(EndInfNode _) b@(Node positionD pos_childD neg_childD)  =  inferNodeA @a (traverse_and_return @a l) c a_id b_id a b `debug` "hello debugger"
    traverse_and_return' l c a_id b_id a@(Node positionD pos_childD neg_childD) b@(EndInfNode _)  =  inferNodeB @a (traverse_and_return @a l) c a_id b_id a b

    traverse_and_return' l c a_id b_id a@(Node positionA pos_childA neg_childA) b@(Leaf _) = inferNodeB @a (traverse_and_return @a l) c a_id b_id a b
    traverse_and_return' l c a_id b_id a@(Leaf _) b@(Node positionB pos_childB neg_childB) = inferNodeA @a (traverse_and_return @a l) c a_id b_id a b

    traverse_and_return' l c a_id b_id a@(InfNodes positionA dcA n1A n0A p1A p0A) b@(InfNodes positionB dcB n1B n0B p1B p0B)
        -- test t_and_rMain here (look what a clean union call does different from unionMain)
        | positionA == positionB = apply @a T_and_r c a_id b_id "traverse_and_return" (t_and_rMain l) a_id b_id a b
        | positionA > positionB = apply @a T_and_r c a_id b_id "traverse_and_return" (t_and_rInferA_ @a l) a_id b_id a b
        | positionB > positionA = apply @a T_and_r c a_id b_id "traverse_and_return" (t_and_rInferB_ @a l) a_id b_id a b
    traverse_and_return' l c a_id b_id a@(InfNodes positionA dcA n1A n0A p1A p0A) b@(Node positionB pos_childB neg_childB)
        | positionA < positionB = inferNodeB @a (traverse_and_return @a l) c a_id b_id a b
        | positionA > positionB = apply @a T_and_r c a_id b_id "traverse_and_return" (t_and_rInferA_ @a l) a_id b_id a b
        | positionA == positionB = undefined
    -- for posB == posA; then we consider node to be AllNegs -> [1]
    traverse_and_return' l c a_id b_id a@(Node positionA pos_childD neg_childD) b@(InfNodes positionB dcB n1B n0B p1B p0B)
        | positionA > positionB = inferNodeA @a (traverse_and_return @a l) c a_id b_id a b
        | positionA < positionB = apply @a T_and_r c a_id b_id "traverse_and_return" (t_and_rInferB_ @a l) a_id b_id a b
        | positionA == positionB = undefined

    -- add infnode to b and perform traverse and return. No need to flip the result, that gets done/determined at the leaf level
    -- we have to take along the leaf we are checking with, thus if we are in finite land; we only have to check for the finite other types where we can expect to see the leaf we are checking weith
    traverse_and_return' l c a_id b_id a@(InfNodes{}) b@(EndInfNode _) = apply @a T_and_r c a_id b_id "traverse_and_return" (t_and_rInferB_ @a l) a_id b_id a b
    traverse_and_return' l c a_id b_id a@(EndInfNode _) b@(InfNodes{}) = apply @a T_and_r c a_id b_id "traverse_and_return" (t_and_rInferA_ @a l) a_id b_id a b
    traverse_and_return' l c a_id b_id a b = error $ "traverse_and_return , " ++ "a = " ++ show a ++ "b = " ++ show_dd settings c b_id

absorb_or_remove :: Context -> Bool
absorb_or_remove c@(Context {func_stack = ((_, f) : cs)})
  | f == Absorb = True
  | f == Remove = False
  | otherwise = absorb_or_remove c{func_stack = cs}
absorb_or_remove c@(Context{func_stack = []}) = error "no absorb or remove in current stack"
-- holds the debug and class specific functions
class DdF4 a where
    to_constr :: Inf
    applyElimRule :: Context -> Dd -> (Context, NodeId)
    intersectionLocal :: DdManipulation
    unionLocal :: DdManipulation
    mixedIntersection :: DdManipulation
    mixedUnion :: DdManipulation
    absorb :: DdManipulation
    traverse_and_return :: Bool -> Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
    remove_outercomplement_from :: DdManipulation

    false :: NodeId
    true :: NodeId
    negate_maybe :: Context -> NodeId -> Dd -> (Context, NodeId)
    applyInfElimRule :: Context -> Dd -> (Context, NodeId)
    applyInfElimRule2 :: Context -> Dd -> (Context, NodeId)
    intersectionInferA_ :: DdManipulation
    intersectionInferB_ :: DdManipulation
    unionInferA_ :: DdManipulation
    unionInferB_ :: DdManipulation
    t_and_rInferA_ :: Bool -> Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
    t_and_rInferB_ :: Bool -> Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
    inferNodeA :: DdManipulation -> Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
    inferNodeA_opposite :: DdManipulation -> Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
    inferNodeB :: DdManipulation -> Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)

type DdManipulation = Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)

instance DdF4 Dc where
    to_constr = Dc
    applyInfElimRule c (Leaf b) = (c, leaf b)
    applyInfElimRule c d = let (c', r) = applyElimRule @Dc c d in case getDd c' r of

        x@(InfNodes {}) -> insert c' $ EndInfNode r
        x -> (c', r)
    applyInfElimRule2 c (Leaf b) = (c, leaf b)
    applyInfElimRule2 c (EndInfNode (0,0)) = (c, (0,0))
    applyInfElimRule2 c (EndInfNode (1,0)) = (c, (1,0))
    applyInfElimRule2 c (EndInfNode child) = (c, child)
    applyInfElimRule2 c d = applyElimRule @Dc c d
    applyElimRule c d@(Node _ posC negC) = if posC == negC then (c, posC) else insert c d
    applyElimRule c d@(InfNodes pos dcR n1R n0R p1R p0R) =
        if (n1R, n0R, p1R, p0R) == ((0,0), (1,0), (0,0), (1,0)) then
                        (case getDd c dcR of
                            (EndInfNode x) -> (c, x)
                            (Leaf False) -> (c, (0,0))
                            (Leaf True) -> (c, (1,0))
                            _ -> insert c $ InfNodes pos dcR n1R n0R p1R p0R)
                        else insert c $ InfNodes pos dcR n1R n0R p1R p0R
    applyElimRule c d = insert c d-- (EndInfNode _) = error "cannot end on end infnodlet c = lastN' (len positionA) c ine"
    false = (-1,-1) --hack to not be equal to any leaf
    true = (-1,-1)
    negate_maybe c d_id _ = (c, d_id)
    intersectionInferB_ c a_id b_id a@(InfNodes positionA _ _ _ _ _) b = let (c', r) = intersectionInferB c{func_stack = ((Dc, Inter): func_stack c)} a_id b_id a b in ( c', r) --`debug` "adding"
    intersectionInferB_ _ _ _ _ _ = undefined
    intersectionInferA_ c a_id b_id a b@(InfNodes positionB _ _ _ _ _) = let (c', r) = intersectionInferA c{func_stack = ((Dc, Inter): func_stack c)} a_id b_id a b in ( c', r) --`debug` "adding"
    intersectionInferA_ _ _ _ _ _ = undefined
    unionInferB_ c a_id b_id a@(InfNodes positionA _ _ _ _ _) b = let (c', r) = unionInferB c{func_stack=((Dc, Union): func_stack c)} a_id b_id a b in ( c', r) --`debug` "adding"
    unionInferB_ _ _ _ _ _ = undefined
    unionInferA_ c a_id b_id a b@(InfNodes positionB _ _ _ _ _) = let (c', r) = unionInferA c{func_stack=((Dc, Union): func_stack c)} a_id b_id a b in ( c', r) --`debug` "adding"
    unionInferA_ c a_id b_id _ _ = error $ "-------------" ++ show_dd settings c a_id ++ "\n ==" ++ show_dd settings c b_id ++ ""
--     t_and_rInferA_ l c a_id b_id a b@(InfNodes positionB _ _ _ _ _) = t_and_rInferA l ((Dc, T_and_r): func_stack c)} a_id b_id a b
    t_and_rInferA_ l _ _ _ _ _ = undefined
--     t_and_rInferB_ l c a_id b_id a b@(InfNodes positionA _ _ _ _ _) = t_and_rInferB l ((Dc, T_and_r): func_stack c)} a_id b_id a b
    t_and_rInferB_ l _ _ _ _ _ = undefined
    intersectionLocal c a_id b_id a b = if (getDd c a_id == a) && (getDd c b_id == b)
        then  debug_manipulation (intersectionLocal' @Dc c a_id b_id a b)
            "intersection" "intersectionLocal Dc" c a_id b_id --"\n result: \n" ++ showTree c' (getDd c' r))
        else error "a and b are not equal"
    -- comparing nodes, allowed mis-matches based on each inference rule
    unionLocal c a_id b_id a b = if (getDd c a_id == a) && (getDd c b_id == b)
        then debug_manipulation (unionLocal' @Dc c a_id b_id a b)
            "union" "unionLocal Dc" c a_id b_id --"\n result: \n" ++ showTree c' (getDd c' r))
        else error "a and b are not equal"


    traverse_and_return l c a_id b_id a b = debug_manipulation (traverse_and_return' @Dc l c a_id b_id a b)
        "traverse_and_return" "traverse_and_return dc" c a_id b_id


    mixedIntersection c a_id b_id a b = error "mixedintersection only with finite kinds"
    mixedUnion c a_id b_id a b = error "mixedintersection only with finite kinds"
    absorb = error "mixedintersection only with finite kinds"
    remove_outercomplement_from = error ""

    inferNodeA f c a_id b_id a b@(Node positionB pos_childB neg_childB) =
        let (c', pos_result) = supply_dds f c a_id pos_childB
            (c'', neg_result) = supply_dds f c' a_id neg_childB
        in applyElimRule @Dc c'' (Node positionB pos_result neg_result)
    inferNodeA _ c a_id b_id a b = error ("inferNode : " ++ show c ++ ", " ++ show a ++ ", " ++ show_dd settings c b_id)

    inferNodeA_opposite = inferNodeA @Dc

    inferNodeB f c a_id b_id a@(Node positionA pos_childA neg_childA) b =
        let (c', pos_result) = supply_dds f c pos_childA b_id
            (c'', neg_result) = supply_dds f c' neg_childA b_id
        in applyElimRule @Dc c'' (Node positionA pos_result neg_result)
    inferNodeB f c a_id b_id a b = undefined `debug` ("infernodeB dc ; " ++ show c ++ "\n \t a: " ++ show a ++ " \n \t b: " ++ show_dd settings c b_id)


instance DdF4 Neg1 where
    to_constr = Neg1
    applyInfElimRule c (Leaf b) = (c, leaf b)
    applyInfElimRule c d = let (c', r) = applyElimRule @Neg1 c d in insert c' $ EndInfNode r

    applyElimRule c d@(Node _ posC negC) = if posC == (0,0) then (c, negC) else insert c d
    applyElimRule c d@(InfNodes pos dcR n1R n0R p1R p0R) =
        if (dcR, n0R, p1R, p0R) == ((0,0), (1,0), (0,0), (1,0)) then
                        (case getDd c n1R of
                            (EndInfNode x) -> (c, x)
                            (Leaf False) -> (c, (0,0))
                            (Leaf True) -> (c, (1,0))
                            _ -> insert c $ InfNodes pos dcR n1R n0R p1R p0R)
                        else insert c $ InfNodes pos dcR n1R n0R p1R p0R
    applyElimRule c d = insert c d

    false = (0,0)
    true = (1,0)
    negate_maybe c d_id _ = (c, d_id)

    intersectionInferB_ c a_id b_id a@(InfNodes positionA _ _ _ _ _) b = let (c', r) = intersectionInferB c{func_stack=((Neg1, Inter): func_stack c)} a_id b_id a b in ( c', r)
    intersectionInferB_ _ _ _ _ _ = undefined
    intersectionInferA_ c a_id b_id a b@(InfNodes positionB _ _ _ _ _) = let (c', r) = intersectionInferA c{func_stack=((Neg1, Inter): func_stack c)} a_id b_id a b in ( c', r)
    intersectionInferA_ _ _ _ _ _ = undefined
    unionInferB_ c a_id b_id a@(InfNodes positionA _ _ _ _ _) b = let (c', r) = unionInferB c{func_stack=((Neg1, Union): func_stack c)} a_id b_id a b in ( c', r)
    unionInferB_ _ _ _ _ _ = undefined
    unionInferA_ c a_id b_id a b@(InfNodes positionB _ _ _ _ _) = let (c', r) = unionInferA c{func_stack=((Neg1, Union): func_stack c)} a_id b_id a b in ( c', r)
    unionInferA_ _ _ _ _ _ = undefined
--     t_and_rInferA_ l c a_id b_id a b@(InfNodes positionB _ _ _ _ _) = t_and_rInferA l ((Neg1, T_and_r): func_stack c)} a_id b_id a b
    t_and_rInferA_ l _ _ _ = undefined
--     t_and_rInferB_ l c a_id b_id a b@(InfNodes positionA _ _ _ _ _) = t_and_rInferB l ((Neg1, T_and_r): func_stack c)} a_id b_id a b
    t_and_rInferB_ l _ _ _ = undefined

    intersectionLocal c a_id b_id a b = debug_manipulation (intersectionLocal' @Neg1 c a_id b_id a b)
        "intersection" "intersectionLocal neg1" c a_id b_id

    unionLocal c a_id b_id a b = debug_manipulation (unionLocal' @Neg1 c a_id b_id a b)
        "union" "unionLocal neg1" c a_id b_id
    traverse_and_return l c a_id b_id a b = debug_manipulation (traverse_and_return' @Neg1 l c a_id b_id a b)
        "traverse_and_return" "traverse_and_return neg1" c a_id b_id

    absorb c a_id b_id a b = debug_manipulation (absorb' @Neg1 c a_id b_id a b)
        "absorb" "absorb neg1" c a_id b_id

    inferNodeA f c a_id b_id a  b@(Node positionB pos_childB neg_childB) =
        let (c', r) = f c a_id b_id (Node positionB (0,0) a_id) b in applyElimRule @Neg1 c' (getDd c' r)
    inferNodeA f c a_id b_id  a b = undefined `debug` ("inferNodeA ; c= " ++ (show c) ++ " a= " ++ (show a) ++ " b= " ++ (show_dd settings c b_id))

    inferNodeA_opposite = inferNodeA @Neg0

    inferNodeB f c a_id b_id a@(Node positionA pos_childA neg_childA) b =
        let (c', r) = f c a_id b_id a (Node positionA (0,0) b_id) in applyElimRule @Neg1 c' $ getDd c' r
    inferNodeB _ _ a_id b_id  _ _ = undefined

    mixedIntersection c a_id b_id a b = debug_manipulation (mixedIntersection' @Neg1 c a_id b_id a b)
        "intersection" "mixedIntersection neg1" c a_id b_id

    mixedUnion c a_id b_id a b = debug_manipulation (mixedUnion' @Neg1 c a_id b_id a b)
        "union" "mixedUnion neg1" c a_id b_id

    remove_outercomplement_from c a_id b_id a b = debug_manipulation ( remove_outercomplement_from' @Neg1 c a_id b_id a b)
        "remove_outercomplement" "remove_f0s1_from_f1s1" c a_id b_id


instance DdF4 Neg0 where
    to_constr = Neg0
    applyInfElimRule c (Leaf b) = (c, leaf b)
    applyInfElimRule c d = let (c', r) = applyElimRule @Neg0 c d in insert c' $ EndInfNode r


    applyElimRule :: Context -> Dd -> (Context, NodeId)
    applyElimRule c d@(Node _ posC negC) = if posC == (1,0) then (c, negC) else insert c d
    applyElimRule c d@(InfNodes pos dcR n1R n0R p1R p0R) =
        if (n1R, dcR, p1R, p0R) == ((0,0), (1,0), (0,0), (1,0)) then
            (case getDd c n0R of
                (EndInfNode x) -> (c, x)
                (Leaf False) -> (c, (0,0))
                (Leaf True) -> (c, (1,0))
                _ -> insert c $ InfNodes pos dcR n1R n0R p1R p0R)
        else insert c $ InfNodes pos dcR n1R n0R p1R p0R
    applyElimRule c d = insert c d

    false = (1,0)
    true = (0,0)
    negate_maybe c d_id d = negation c d_id d

    intersectionInferB_ c a_id b_id a@(InfNodes positionA _ _ _ _ _) b = let (c', r) = intersectionInferB c{func_stack=((Neg0, Inter): func_stack c)} a_id b_id a b in ( c', r)
    intersectionInferB_ _ _ _ _ _ = undefined
    intersectionInferA_ c a_id b_id a b@(InfNodes positionB _ _ _ _ _) = let (c', r) = intersectionInferA c{func_stack=((Neg0, Inter): func_stack c)} a_id b_id a b in ( c', r)
    intersectionInferA_ _ _ _ _ _  = undefined
    unionInferB_ c a_id b_id a@(InfNodes positionA _ _ _ _ _) b = let (c', r) = unionInferB c{func_stack=((Neg0, Union): func_stack c)} a_id b_id a b in ( c', r)
    unionInferB_ _ _ _ _ _ = undefined
    unionInferA_ c a_id b_id a b@(InfNodes positionB _ _ _ _ _) = let (c', r) = unionInferA c{func_stack=((Neg0, Union): func_stack c)} a_id b_id a b in ( c', r)
    unionInferA_ _ _ _ _ _ = undefined
--     t_and_rInferA_ l c a_id b_id a b@(InfNodes positionB _ _ _ _ _) = t_and_rInferA l ((Neg0, T_and_r): func_stack c)} a_id b_id a b
    t_and_rInferA_ l _ _ _ = undefined
--     t_and_rInferB_ l c a_id b_id a b@(InfNodes positionA _ _ _ _ _) = t_and_rInferB l ((Neg0, T_and_r): func_stack c)} a_id b_id a b
    t_and_rInferB_ l _ _ _ = undefined

--         -- Leaf and node
    unionLocal c a_id b_id a b = debug_manipulation (unionLocal' @Neg0 c a_id b_id a b)
        "union" "unionLocal neg0: " c a_id b_id

    intersectionLocal c a_id b_id a b = debug_manipulation (intersectionLocal' @Neg0 c a_id b_id a b)
        "intersection" "intersectionLocal neg0: " c a_id b_id

    traverse_and_return l c a_id b_id a b =  debug_manipulation (traverse_and_return' @Neg0 l c a_id b_id a b)
        "traverse_and_return" "traverse_and_return neg0" c a_id b_id
    absorb c a_id b_id a b =  debug_manipulation (absorb' @Neg0 c a_id b_id a b)
        "absorb" "absorb neg0" c a_id b_id

    inferNodeA f c a_id b_id a b@(Node positionB pos_childB neg_childB) =
        let (c', r) = f c a_id b_id (Node positionB (1, 0) a_id) b in applyElimRule @Neg0 c' (getDd c' r)
    inferNodeA _ _ a_id b_id _ _ = undefined
    inferNodeA_opposite = inferNodeA @Neg1
    inferNodeB f c a_id b_id a@(Node positionA pos_childA neg_childA) b =
        let (c', r) = f c a_id b_id a (Node positionA (1, 0) b_id) in applyElimRule @Neg0 c' (getDd c' r)
    inferNodeB _ _ a_id b_id _ _ = undefined


    mixedIntersection c a_id b_id a b = debug_manipulation (mixedIntersection' @Neg0 c a_id b_id a b)
        "intersection" "mixedIntersection neg0" c a_id b_id

    mixedUnion c a_id b_id a b = debug_manipulation (mixedUnion' @Neg0 c a_id b_id a b)
        "union" "mixedUnion neg0" c a_id b_id


    remove_outercomplement_from c a_id b_id a b =  debug_manipulation (remove_outercomplement_from' @Neg0 c a_id b_id a b)
        "remove_outercomplement" "remove_f0s1_from_f1s1" c a_id b_id


instance DdF4 Pos1 where
    to_constr = Pos1
    applyInfElimRule c (Leaf b) = (c, leaf b)
    applyInfElimRule c d = let (c', r) = applyElimRule @Pos1 c d in insert c' $ EndInfNode r

    applyElimRule c d@(Node _ posC negC) = if negC == (0,0) then (c, posC) else insert c d
    applyElimRule c d@(InfNodes pos dcR n1R n0R p1R p0R) =
        if (n1R, n0R, dcR, p0R) == ((0,0), (1,0), (0,0), (1,0)) then
            (case getDd c p1R of
                (EndInfNode x) -> (c, x)
                (Leaf False) -> (c, (0,0))
                (Leaf True) -> (c, (1,0))
                _ -> insert c $ InfNodes pos dcR n1R n0R p1R p0R)
        else insert c $ InfNodes pos dcR n1R n0R p1R p0R
    applyElimRule c d = insert c d

    false = (0,0)
    true = (1,0)
    negate_maybe c d_id _ = (c, d_id)


    intersectionInferB_ c a_id b_id a@(InfNodes positionA _ _ _ _ _) b = let (c', r) = intersectionInferB c{func_stack=((Pos1, Inter): func_stack c)} a_id b_id a b in ( c', r)
    intersectionInferB_ _ _ _ _ _ = undefined
    intersectionInferA_ c a_id b_id a b@(InfNodes positionB _ _ _ _ _) = let (c', r) = intersectionInferA c{func_stack=((Pos1, Inter): func_stack c)} a_id b_id a b in ( c', r)
    intersectionInferA_ _ _ _ _ _ = undefined
    unionInferB_ c a_id b_id a@(InfNodes positionA _ _ _ _ _) b = let (c', r) = unionInferB c{func_stack=(Pos1, Union): func_stack c} a_id b_id a b in ( c', r)
    unionInferB_ _ _ _ _ _ = undefined
    unionInferA_ c a_id b_id a b@(InfNodes positionB _ _ _ _ _) = let (c', r) = unionInferA c{func_stack=(Pos1, Union): func_stack c} a_id b_id a b in ( c', r)
    unionInferA_ _ _ _ _ _ = undefined
--     t_and_rInferA_ l c a_id b_id a b@(InfNodes positionB _ _ _ _ _) = t_and_rInferA l c{func_stack=(Pos1, T_and_r): func_stack c} a b
    t_and_rInferA_ l _ _ _ = undefined
--     t_and_rInferB_ l c a_id b_id a b@(InfNodes positionA _ _ _ _ _) = t_and_rInferB l c{func_stack=(Pos1, T_and_r): func_stack c} a b
    t_and_rInferB_ l _ _ _ = undefined

    intersectionLocal c a_id b_id a b = debug_manipulation (intersectionLocal' @Pos1 c a_id b_id a b)
        "intersection" "intersectionLocal pos1: " c a_id b_id

    unionLocal c a_id b_id a b = debug_manipulation (unionLocal' @Pos1 c a_id b_id a b)
        "union" "unionLocal pos1" c a_id b_id

    traverse_and_return l c a_id b_id a b = debug_manipulation (traverse_and_return' @Pos1 l c a_id b_id a b)
        "traverse_and_return" "traverse_and_return pos1" c a_id b_id

    absorb c a_id b_id a b = debug_manipulation (absorb' @Pos1 c a_id b_id a b)
        "absorb" "absorb pos1" c a_id b_id

    inferNodeA f c a_id b_id a b@(Node positionB pos_childB neg_childB) =
        let (c', r) = f c a_id b_id (Node positionB a_id (0,0)) b in applyElimRule @Pos1 c' $ getDd c' r
    inferNodeA _ c a_id b_id a b = error ("pos1" ++ show c ++ show a ++ show_dd settings c b_id )
    inferNodeA_opposite = inferNodeA @Pos0
    inferNodeB f c a_id b_id a@(Node positionA pos_childA neg_childA) b =
        let (c', r) = f c a_id b_id a (Node positionA b_id (0,0)) in applyElimRule @Pos1 c' $ getDd c' r
    inferNodeB _ c a_id b_id a b = error "infernodeB" -- c a_id b_id

    mixedIntersection c a_id b_id a b = debug_manipulation (mixedIntersection' @Pos1 c a_id b_id a b)
        "intersection" "mixedIntersection pos1" c a_id b_id

    mixedUnion c a_id b_id a b = debug_manipulation (mixedUnion' @Pos1 c a_id b_id a b)
        "union" "mixedUnion pos1" c a_id b_id

    remove_outercomplement_from c a_id b_id a b =  debug_manipulation (remove_outercomplement_from' @Pos1 c a_id b_id a b)
        "remove_outercomplement" "remove_f0s1_from_f1s1Z" c a_id b_id



instance DdF4 Pos0 where
    to_constr = Pos0
    applyInfElimRule c (Leaf b) = (c, leaf b)
    applyInfElimRule c d = let (c', r) = applyElimRule @Pos0 c d in insert c' $ EndInfNode r

    applyElimRule c d@(Node _ posC negC) = if negC == (1,0) then (c, posC) else insert c d
    applyElimRule c d@(InfNodes pos dcR n1R n0R p1R p0R) =
        if (n1R, n0R, p1R, dcR) == ((0,0), (1,0), (0,0), (1,0)) then
            (case getDd c p0R of
                (EndInfNode x) -> (c, x)
                (Leaf False) -> (c, (0,0))
                (Leaf True) -> (c, (1,0))
                _ -> insert c $ InfNodes pos dcR n1R n0R p1R p0R)
        else insert c $ InfNodes pos dcR n1R n0R p1R p0R
    applyElimRule c d = insert c d

    false = (1,0)
    true = (0,0)
    negate_maybe = negation

    intersectionInferB_ c a_id b_id a@(InfNodes positionA _ _ _ _ _) b = let (c', r) = intersectionInferB c{func_stack=((Pos0, Inter): func_stack c)} a_id b_id a b in ( c', r)
    intersectionInferB_ _ _ _ _ _ = undefined
    intersectionInferA_ c a_id b_id a b@(InfNodes positionB _ _ _ _ _) = let (c', r) = intersectionInferA c{func_stack=((Pos0, Inter): func_stack c)} a_id b_id a b in ( c', r)
    intersectionInferA_ _ _ _ _ _= undefined
    unionInferB_ c a_id b_id a@(InfNodes positionA _ _ _ _ _) b = let (c', r) = unionInferB c{func_stack=((Pos0, Union): func_stack c)} a_id b_id a b in ( c', r)
    unionInferB_ _ _ _ _ _ = undefined
    unionInferA_ c a_id b_id a b@(InfNodes positionB _ _ _ _ _) = let (c', r) = unionInferA c{func_stack=((Pos0, Union): func_stack c)} a_id b_id a b in ( c', r)
    unionInferA_ _ _ _ _ _= undefined
--     t_and_rInferA_ l c a_id b_id a b@(InfNodes positionB _ _ _ _ _) = t_and_rInferA l c{func_stack=((Pos0, T_and_r): func_stack c)) a b
    t_and_rInferA_ l _ _ _ = undefined
--     t_and_rInferB_ l c a_id b_id a b@(InfNodes positionA _ _ _ _ _) = t_and_rInferB l c{func_stack=((Pos0, T_and_r): func_stack c)) a b
    t_and_rInferB_ l _ _ _ = undefined

--     -- Leaf and node
    unionLocal c a_id b_id a b = debug_manipulation (unionLocal' @Pos0 c a_id b_id a b  )
        "union" "unionLocal pos0" c a_id b_id
    intersectionLocal c a_id b_id a b = debug_manipulation (intersectionLocal' @Pos0 c a_id b_id a b)
        "intersection" "intersectionLocal pos0" c a_id b_id

    absorb c a_id b_id a b = debug_manipulation (absorb' @Pos0 c a_id b_id a b)
        "absorb" "absorb pos0" c a_id b_id

    inferNodeA f c a_id b_id a  b@(Node positionB pos_childB neg_childB) =
        let (c', r) = f c a_id b_id (Node positionB a_id (1,0)) b in applyElimRule @Pos0 c' $ getDd c' r
    inferNodeA _ c a_id b_id a b = error (show c ++ " , a = " ++ show a ++ " , b = " ++ show_dd settings c b_id)
    inferNodeA_opposite = inferNodeA @Pos1
    inferNodeB f c a_id b_id a@(Node positionA pos_childA neg_childA)  b =
        let (c', r) = f c a_id b_id a (Node positionA b_id (1,0)) in applyElimRule @Pos0 c' $ getDd c' r
    inferNodeB _ c a_id b_id a b= error (show c ++ " , a = " ++ show a ++ " , b = " ++ show_dd settings c b_id)

    mixedIntersection c a_id b_id a b = debug_manipulation (mixedIntersection' @Pos0 c a_id b_id a b)
        "intersection" "mixedIntersection pos0" c a_id b_id

    mixedUnion c a_id b_id a b = debug_manipulation (mixedUnion' @Pos0 c a_id b_id a b)
        "union" "mixedUnion pos0" c a_id b_id

    traverse_and_return l c a_id b_id a b = debug_manipulation ( traverse_and_return' @Pos0 l c a_id b_id a b)
        "traverse_and_return" "traverse_and_return pos0" c a_id b_id

    remove_outercomplement_from c a_id b_id a b = debug_manipulation ( remove_outercomplement_from' @Pos0 c a_id b_id a b)
        "remove_outercomplement" "remove_f0s1_from_f1s1" c a_id b_id



-- -- tandr simple functions
t_and_rInferA :: Bool -> Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
t_and_rInferA _ Context{func_stack = []} _ _ _ _ = error "empty context"
t_and_rInferA _  _ _ _ _ (Leaf _) = error "Leaf in A"
t_and_rInferA _  _ _ _ _ (EndInfNode _) = error "EndNode in A"
t_and_rInferA _  _ _ _ _ (Node _ _ _) = error "Node in A"
t_and_rInferA l c a_id b_id a b =  t_and_rInferA' l c a_id b_id a b --`debug5` ("t_and_rInferA" ++ show l ++ ": " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show_dd settings c b_id) -- ++ " = " ++ show (t_and_rInferA' l c a_id b_id a b ))


t_and_rInferA' :: Bool -> Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
t_and_rInferA' l c@Context{func_stack = ((inf, _) : _)} a_id b_id a' b@(InfNodes positionB dcB n1B n0B p1B p0B) =
    let (c', a) = insert c (EndInfNode a_id) in
        let
        (c'', dcR) = traverse_and_return @Dc l c' a dcB (getDd c a) (getDd c dcB)
        (c''', n1R) = traverse_and_return @Neg1 l c'' a n1B (getDd c a) (getDd c n1B)
        (c'''', n0R) = traverse_and_return @Neg0 l c''' a n0B (getDd c a) (getDd c n0B)
        (c''''', p1R) = traverse_and_return @Pos1 l c'''' a p1B (getDd c a) (getDd c p1B)
        (c'''''', p0R) = traverse_and_return @Pos0 l c''''' a p0B (getDd c a) (getDd c p0B)
        in insert c'''''' $ InfNodes positionB dcR n1R n0R p1R p0R
t_and_rInferA' _ _ _ _ _ _ = undefined

t_and_rInferB :: Bool -> Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
t_and_rInferB _ Context{func_stack = []} _ _ _ _ = error "empty context"
t_and_rInferB _  _ _ _ _ (Leaf _) = error "Leaf in A"
t_and_rInferB _  _ _ _ _ (EndInfNode _) = error "EndNode in A"
t_and_rInferB _  _ _ _ _ (Node _ _ _) = error "Node in A"
t_and_rInferB l c a_id b_id a b =  t_and_rInferB' l c a_id b_id a b `debug4` ("t_and_rInferB" ++ show l ++ ": " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show_dd settings c b_id)
t_and_rInferB' :: Bool -> Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
t_and_rInferB' l c@Context{func_stack = ((inf, _) : _)} a_id b_id a@(InfNodes positionA dcA n1A n0A p1A p0A) b' = let (c', b) = insert c (EndInfNode b_id) in
    (if l then
        (case inf of
                Dc -> error "inferring an infnode for a Dc context should not happen.. i think"
                    -- (c', dcR) = traverse_and_return @Dc l c dcA b (getDd c ) (getDd c b) --inter
                    -- (c', n1R) = traverse_and_return @Neg1 l c n1A b (getDd c ) (getDd c b) -- union
                    -- (c', n0R) = traverse_and_return @Neg0 l c n0A b (getDd c ) (getDd c b)
                    -- (c', p1R) = traverse_and_return @Pos1 l c p1A b (getDd c ) (getDd c b)
                    -- (c', p0R) = traverse_and_return @Pos0 l c p0A b (getDd c ) (getDd c b)
                    -- in applyElimRule @Dc (InfNodes positionA dcR n1R n0R p1R p0R)
                Neg1 -> let -- replace all the B stuf with (dc: 0, neg1: b, neg0: 1, pos1: 0, pos0: 1)
                    (c'', n1R) = traverse_and_return @Neg1 l c' n1A b (getDd c' n1A) (getDd c' b) --inter dcA
                    in insert c'' $ InfNodes positionA dcA n1R n0A p1A p0A
                Neg0 -> let -- replace all the B stuf with (dc: 1, neg1: 0, neg0: b, pos1: 0, pos0: 1)
                    (c'', n0R) = traverse_and_return @Neg0 l c' n0A b (getDd c' n0A) (getDd c' b)
                    in insert c'' $ InfNodes positionA dcA n1A n0R p1A p0A
                Pos1 -> let -- replace all the B stuf with (dc: 0, neg1: 0, neg0: 1, pos1: b, pos0: 1)
                    -- for absorb dcA has to be checked with leaf false
                    -- there is something and it can only get less inb the finite types
                    -- so only local 1 ands 0s get pruned and nothing else changes
                    -- thus intersection/union/remove_compl and absorb do not have to be performed on the finite types if they are changed
                    (c'', p1R) = traverse_and_return @Pos1 l c' p1A b (getDd c' p1A) (getDd c' b)
                    in applyElimRule @Pos1 c'' (InfNodes positionA dcA n1A n0A p1R p0A)
                Pos0 -> let -- replace all the B stuf with (dc: 0, neg1: 0, neg0: 1, pos1: 0, pos0: b)
                    (c'', p0R) = traverse_and_return @Pos0 l c' p0A b (getDd c' p0A) (getDd c' b)
                    in applyElimRule @Pos0 c'' (InfNodes positionA dcA n1A n0A p1A p0R)
        ) else (case inf of
            -- todo how does l change the function?
                Dc -> error "inferring an infnode for a Dc context should not happen.. i think"
                    -- (c'', dcR) = traverse_and_return @Dc l c' dcA b (getDd c' b) (getDd c' b) --inter
                    -- (c'', n1R) = traverse_and_return @Neg1 l c' n1A b (getDd c' b) (getDd c' b) -- union
                    -- (c'', n0R) = traverse_and_return @Neg0 l c' n0A b (getDd c' b) (getDd c' b)
                    -- (c'', p1R) = traverse_and_return @Pos1 l c' p1A b (getDd c' b) (getDd c' b)
                    -- (c'', p0R) = traverse_and_return @Pos0 l c' p0A b (getDd c' b) (getDd c' b)
                    -- in applyElimRule @Dc (InfNodes positionA dcR n1R n0R p1R p0R)
                Neg1 -> let -- replace all the B stuf with (dc: 0, neg1: b, neg0: 1, pos1: 0, pos0: 1)
                    (c'', n1R) = traverse_and_return @Neg1 l c' n1A b (getDd c' b) (getDd c' b) --inter dcA
                    in insert c'' $ InfNodes positionA dcA n1R n0A p1A p0A
                Neg0 -> let -- replace all the B stuf with (dc: 1, neg1: 0, neg0: b, pos1: 0, pos0: 1)
                    (c'', n0R) = traverse_and_return @Neg0 l c' n0A b (getDd c' b) (getDd c' b)
                    in insert c'' $ InfNodes positionA dcA n1A n0R p1A p0A
                Pos1 -> let -- replace all the B stuf with (dc: 0, neg1: 0, neg0: 1, pos1: b, pos0: 1)
                    -- for absorb dcA has to be checked with leaf false
                    -- there is something and it can only get less inb the finite types
                    -- so only local 1 ands 0s get pruned and nothing else changes
                    -- thus intersection/union/remove_compl and absorb do not have to be performed on the finite types if they are changed
                    (c'', p1R) = traverse_and_return @Pos1 l c' p1A b (getDd c' b) (getDd c' b)
                    in insert c'' $ InfNodes positionA dcA n1A n0A p1R p0A
                Pos0 -> let -- replace all the B stuf with (dc: 0, neg1: 0, neg0: 1, pos1: 0, pos0: b)
                    (c'', p0R) = traverse_and_return @Pos0 l c' p0A b (getDd c' b) (getDd c' b)
                    in insert c'' $ InfNodes positionA dcA n1A n0A p1A p0R))
t_and_rInferB' l c a_id b_id a b = error (" : " ++ show a ++ show_dd settings c b_id ++ show c ++ show l)


t_and_rMain :: Bool -> Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
t_and_rMain _ Context{func_stack = []} a_id b_id _ _ = error "empty context"
t_and_rMain _ _ a_id b_id _ (Leaf _) = error "Leaf in A"
t_and_rMain _ _ a_id b_id _ (EndInfNode _) = error "EndNode in A"
t_and_rMain _ _ a_id b_id _ (Node _ _ _) = error "Node in A"
t_and_rMain l c a_id b_id a b = debug_manipulation (t_and_rMain' l c a_id b_id a b)
   "traverse_and_return" ("t_and_rMain" ++ show l) c a_id b_id-- ++ " = " ++ show (t_and_rMain' l c a b ))
t_and_rMain' :: Bool -> Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
t_and_rMain' l c@Context{func_stack = ((inf, _) : _)} a_id b_id a@(InfNodes positionA dcA n1A n0A p1A p0A) b@(InfNodes positionB dcB n1B n0B p1B p0B) = let
            (c', dcR) = traverse_and_return @Dc l c dcA dcB (getDd c dcA) (getDd c dcB)
            (c'', n1R) = traverse_and_return @Neg1 l c' n1A n1B (getDd c n1A) (getDd c n1B)
            (c''', n0R) = traverse_and_return @Neg0 l c'' n0A n0B (getDd c n0A) (getDd c n0B)
            (c'''', p1R) = traverse_and_return @Pos1 l c''' p1A p1B (getDd c p1A) (getDd c p1B)
            (c''''', p0R) = traverse_and_return @Pos0 l c'''' p0A p0B (getDd c p0A) (getDd c p0B)
            in insert c''''' $ InfNodes positionB dcR n1R n0R p1R p0R
t_and_rMain' _ _ _ _ _ _ = undefined



debugFlag = True
debugFlag2 = True

force_eval_debug :: c -> String -> c
force_eval_debug f s = unsafePerformIO $ do
    !x <- return f
    print s
    return x

debug :: c -> String -> c
debug f s = if debugFlag then trace s f else f

debug3 :: c -> [String] -> c
debug3 f s = trace (format' s) f

debug2 :: a -> String -> a
debug2 f s = if debugFlag2 then trace (colorize "red" s) f else f

debug4 :: a -> String -> a
debug4 f s = if True then trace (colorize "green" s) f else f

-- debug5 :: a -> String -> a
-- debug5 f s = if True then trace (colorize "red" s) f else f
