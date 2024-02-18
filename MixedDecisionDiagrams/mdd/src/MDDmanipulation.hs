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

module MDDmanipulation where

import MDD
import Debug.Trace (trace)
import Data.Kind
import System.Console.ANSI
    ( setSGRCode,
      Color(Blue, Red, Green),
      ColorIntensity(Vivid),
      ConsoleLayer(Foreground),
      SGR(Reset, SetColor) )
import Data.Map (Map)
import qualified Data.Map as Map
import Data.GraphViz.Attributes.Colors.X11 (x11Colour)
import System.Console.ANSI.Codes (csi)
import Data.Hashable



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



type DdF4 :: Inf -> Constraint
type Dd1 :: Inf -> Constraint



intersection :: Context -> Dd -> Dd -> Dd
intersection c a b = intersection'  c a b
    `debug` ("intersection: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)
intersection' :: Context -> Dd -> Dd -> Dd
intersection' c a (Leaf False) = Leaf False
intersection' c (Leaf False) b = Leaf False
intersection' c a (Leaf True) = a
intersection' c (Leaf True) b = b
intersection' c a b = intersectionMain c a b
-- union :: Context -> Dd -> Dd -> Dd
-- union c a b = union'  c a b
--     `debug` ("union: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)
-- union' :: Context -> Dd -> Dd -> Dd
-- union' c a (Leaf True) = Leaf True
-- union' c (Leaf True) b = Leaf True
-- union' c a (Leaf False) = a
-- union' c (Leaf False) b = b
-- union' c a b = unionMain c a b

negation :: Context -> Dd -> (Context, Dd)
negation c d@(Node position pos_child neg_child) = withCache_ c (hash d) $ let
    (c', posR) = merge_rule_ negation c (getDd c pos_child)
    (c'', negR) = merge_rule_ negation c' (getDd c' pos_child)
    in (c'', Node position posR negR)
negation c d@(InfNodes position dc_n n1_n n0_n p1_n p0_n) = withCache_ c (hash d) $ let
    (c', r_dc) = merge_rule_ negation c $ getDd c dc_n
    (c'', r_n0) = merge_rule_ negation c $ getDd c' n0_n
    (c''', r_n1) = merge_rule_ negation c $ getDd c'' n1_n
    (c'''', r_p0) = merge_rule_ negation c $ getDd c''' p0_n
    (c''''', r_p1) = merge_rule_ negation c $ getDd c'''' p1_n
        in (c''''', InfNodes position r_dc r_n1 r_n0 r_p1 r_p0)
negation c d@(EndInfNode a) = withCache_ c (hash d) $ let
    (c', result) = merge_rule_ negation c (getDd c a)
    in (c', EndInfNode result)
negation c (Leaf b) = (c, Leaf $ not b)



-- applyElimRule_arg :: Inf -> Dd -> Dd
-- applyElimRule_arg Dc d = applyElimRule @Dc d
-- applyElimRule_arg Neg1 d = applyElimRule @Neg1 d
-- applyElimRule_arg Neg0 d = applyElimRule @Neg0 d
-- applyElimRule_arg Pos1 d = applyElimRule @Pos1 d
-- applyElimRule_arg Pos0 d = applyElimRule @Pos0 d

-- --todo why am i doing this directly below?
intersectionLocal_arg :: (Inf, FType) -> Context -> Dd -> Dd -> Dd
intersectionLocal_arg (i,t) Context{func_context= []} 0 b
    | i `elem` [Dc,Neg1,Pos1] = if debugFlag then Leaf False `debug5` (show i ++ "Leaf False") else Leaf False
    | i `elem` [Neg0,Pos0] = if debugFlag then b `debug5` (show i ++ "b") else b
intersectionLocal_arg (i,t) [] 1 b
    | i `elem` [Dc,Neg1,Pos1] = if debugFlag then b `debug5` (show i ++ "b") else b
    | i `elem` [Neg0,Pos0] = if debugFlag then Leaf True `debug5` (show i ++ "Leaf True") else Leaf True
intersectionLocal_arg (i,t) [] a 0
    | i `elem` [Dc,Neg1,Pos1] = if debugFlag then Leaf False `debug5` (show i ++ "Leaf False") else Leaf False
    | i `elem` [Neg0,Pos0] = if debugFlag then a `debug5` (show i ++ "a") else a
intersectionLocal_arg (i,t) [] a 1
    | i `elem` [Dc,Neg1,Pos1] = if debugFlag then a `debug5` (show i ++ "a") else a
    | i `elem` [Neg0,Pos0] = if debugFlag then Leaf True `debug5` (show i ++ "Leaf True") else Leaf True
intersectionLocal_arg a b c d = continue_outer a b c d
-- unionLocal_arg :: (Inf, FType) -> Context -> Dd -> Dd -> Dd
-- unionLocal_arg t c a b = unionLocal_arg' t c a b `debug2` ("unionLocal arg t = " ++ show t ++ ", c = " ++ show c ++ ", \n \t a = " ++ show a ++ ", \n \t b = " ++ show b)
-- unionLocal_arg' :: (Inf, FType) -> Context -> Dd -> Dd -> Dd
-- unionLocal_arg' (i,t) [] a@(Leaf False) b
--     | i `elem` [Dc,Neg1,Pos1] = b `debug2` (show i ++ "b")
--     | i `elem` [Neg0,Pos0] = Leaf False `debug2` (show i ++ "Leaf False")
-- unionLocal_arg' (i,t) [] a@(Leaf True) b
--     | i `elem` [Dc,Neg1,Pos1] = Leaf True `debug2` (show i ++ "Leaf True")
--     | i `elem` [Neg0,Pos0] = b `debug2` (show i ++ "b")
-- unionLocal_arg' (i,t) [] a b@(Leaf False)
--     | i `elem` [Dc,Neg1,Pos1] = a `debug2` (show i ++ "a")
--     | i `elem` [Neg0,Pos0] = Leaf False `debug2` (show i ++ "Leaf False")
-- unionLocal_arg' (i,t) [] a b@(Leaf True)
--     | i `elem` [Dc,Neg1,Pos1] = Leaf True `debug2` (show i ++ "Leaf True")
--     | i `elem` [Neg0,Pos0] = a `debug2` (show i ++ "a")
-- unionLocal_arg' t c a b = continue_outer t c a b


-- continue_outer :: (Inf, FType) -> Context -> Dd -> Dd -> Dd
-- continue_outer t c a b = case t of
--     (Dc, Inter) -> (intersectionLocal @Dc c a b) `debug5` "inter"
--     (Neg1, Inter) -> intersectionLocal @Neg1 c a b
--     (Neg0, Inter) -> intersectionLocal @Neg0 c a b
--     (Pos1, Inter) -> intersectionLocal @Pos1 c a b
--     (Pos0, Inter) -> intersectionLocal @Pos0 c a b

--     (Dc, Union) -> unionLocal @Dc c a b
--     (Neg1, Union) -> unionLocal @Neg1 c a b
--     (Neg0, Union) -> unionLocal @Neg0 c a b
--     (Pos1, Union) -> unionLocal @Pos1 c a b
--     (Pos0, Union) -> unionLocal @Pos0 c a b

--     (Dc, MixedIntersection) -> mixedIntersection @Dc c a b
--     (Neg1, MixedIntersection) -> mixedIntersection @Neg1 c a b
--     (Neg0, MixedIntersection) -> mixedIntersection @Neg0 c a b
--     (Pos1, MixedIntersection) -> mixedIntersection @Pos1 c a b
--     (Pos0, MixedIntersection) -> mixedIntersection @Pos0 c a b

--     (Dc, MixedUnion) -> mixedUnion @Dc c a b
--     (Neg1, MixedUnion) -> mixedUnion @Neg1 c a b
--     (Neg0, MixedUnion) -> mixedUnion @Neg0 c a b
--     (Pos1, MixedUnion) -> mixedUnion @Pos1 c a b
--     (Pos0, MixedUnion) -> mixedUnion @Pos0 c a b

--     (Dc, Absorb) -> absorb @Dc c a b
--     (Neg1, Absorb) -> absorb @Neg1 c a b
--     (Neg0, Absorb) -> absorb @Neg0 c a b
--     (Pos1, Absorb) -> absorb @Pos1 c a b
--     (Pos0, Absorb) -> absorb @Pos0 c a b

--     (_, _) -> error (show t ++ ", " ++ show c ++ ", " ++ show a ++ ", " ++ show b)


-- t_and_r_arg :: (Inf, FType) -> Bool -> Context -> Dd -> Dd -> Dd
-- t_and_r_arg t l c a b = case t of
--     (Dc, Absorb) -> absorb @Dc c a b
--     (Neg1, Absorb) -> absorb @Neg1 c a b
--     (Neg0, Absorb) -> absorb @Neg0 c a b
--     (Pos1, Absorb) -> absorb @Pos1 c a b
--     (Pos0, Absorb) -> absorb @Pos0 c a b
--     (Dc, T_and_r) -> traverse_and_return @Dc l c a b
--     (Neg1, T_and_r) -> traverse_and_return @Neg1 l c a b
--     (Neg0, T_and_r) -> traverse_and_return @Neg0 l c a b
--     (Pos1, T_and_r) -> traverse_and_return @Pos1 l c a b
--     (Pos0, T_and_r) -> traverse_and_return @Pos0 l c a b
--     (Dc, Remove) -> remove_outercomplement_from @Dc c a b
--     (Neg1, Remove) -> remove_outercomplement_from @Neg1 c a b
--     (Neg0, Remove) -> remove_outercomplement_from @Neg0 c a b
--     (Pos1, Remove) -> remove_outercomplement_from @Pos1 c a b
--     (Pos0, Remove) -> remove_outercomplement_from @Pos0 c a b

--     (_, _) -> error (show t ++ ", " ++ show c ++ ", " ++ show a ++ ", " ++ show b)


addInfNode :: Context -> Int -> Inf -> Dd -> Dd
addInfNode c n inf conseq  =
        case inf of -- only for Dc we need to check the b, since after a hole we interpret the following sub domains in substance (1-set)
            Dc -> auto_insert c $ InfNodes n (EndInfNode conseq) 0 1 0 1
            Neg1 -> auto_insert c $ InfNodes n 0 (EndInfNode conseq) 1 0 1
            Neg0 -> auto_insert c $ InfNodes n 1 0 (EndInfNode conseq) 0 1
            Pos1 -> auto_insert c $ InfNodes n 0 0 1 (EndInfNode conseq) 1
            Pos0 -> auto_insert c $ InfNodes n 1 0 1 0 (EndInfNode conseq)

intersectionInferA :: Context -> Dd -> Dd -> Dd
intersectionInferA [] _ _ = error "empty context"
intersectionInferA _ _ (Leaf _) = error "Leaf in A"
intersectionInferA _ _ (EndInfNode _) = error "EndNode in A"
intersectionInferA _ _ (Node _ _ _) = error "Node in A"

-- intersectionInferA c a b = intersectionInferA' c a b  `debug3` ["intersectionInferA: " ++ show c ++ " ; ", show a ++ " ; " , show b ++ " = \n " , show ( intersectionInferA' c a b) ++ "\n"]
-- intersectionInferA' :: [(Inf, FType)] -> Dd -> Dd -> Dd
-- intersectionInferA' c@((inf, _) : _) a' b@(InfNodes positionB dcB n1B n0B p1B p0B) = let a = EndInfNode a' in
--     case inf of
--         Dc -> let -- replace all the A stuf with (dc: a, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
--             dcR = intersectionLocal @Dc c a dcB
--             n1R = (if n0B == 1 then
--                     absorb @Neg1 c (mixedIntersection @Neg1 c n1B a) dcR  else
--                     remove_outercomplement_from @Neg1 c n0B (absorb @Neg1 c (mixedIntersection @Neg1 c n1B a) dcR))
--             n0R = absorb @Neg0 c (mixedIntersection @Neg0 c n0B dcR) dcR --`debug` ( "inter: " ++ show (mixedIntersection @Neg0 c n0A dcR) ++ "\n n0A: " ++ show n0A  ++ "\n dcR" ++ show dcR)
--             p1R = if p0B == 1 then
--                 absorb @Pos1 c (mixedIntersection @Pos1 c p1B a) dcR else
--                 remove_outercomplement_from @Pos1 c p0B (absorb @Pos1 c (mixedIntersection @Pos1 c p1B a) dcR)
--             p0R = absorb @Neg0 c (mixedIntersection @Pos0 c p0B dcR) dcR
--             in InfNodes positionB dcR n1R n0R p1R p0R

--         Neg1 -> let -- replace all the A stuf with (dc: 0, neg1: a, neg0: 1, pos1: 0, pos0: 1)
--             n1R = unionLocal @Neg1 c
--                 (intersectionLocal @Neg1 c a n1B)
--                 (if n0B == 1 then n1R' else remove_outercomplement_from @Neg1 c n0B n1R')
--             n1R' = mixedIntersection @Neg1 c a dcB
--             in InfNodes positionB 0 n1R 1 0 1
--         Neg0 -> let -- replace all the A stuf with (dc: 1, neg1: 0, neg0: a, pos1: 0, pos0: 1)
--             n0R' = intersectionLocal @Neg0 c a n0B
--             n0R = mixedIntersection @Neg0 c n0R' dcB
--             in InfNodes positionB dcB 0 n0R 0 1
--         Pos1 -> let -- replace all the A stuf with (dc: 0, neg1: 0, neg0: 1, pos1: a, pos0: 1)
--             p1R = unionLocal @Pos1 c
--                 (intersectionLocal @Pos1 c a n1B)
--                 (if n0B == 1 then p1R' else remove_outercomplement_from @Pos1 c n0B p1R')
--             p1R' = mixedIntersection @Pos1 c a dcB
--             in InfNodes positionB 0 0 1 p1R 1
--         Pos0 -> let -- replace all the A stuf with (dc: 1, neg1: 0, neg0: a, pos1: 0, pos0: 1)
--             p0R' = intersectionLocal @Pos0 c a p0B
--             p0R = mixedIntersection @Pos0 c p0R' dcB
--             in InfNodes positionB dcB 0 1 0 p0R
-- intersectionInferA' _ _ _ = undefined

-- intersectionInferB :: Context -> Dd -> Dd -> Dd
-- intersectionInferB [] _ _ = error "empty context"
-- intersectionInferB _ (Leaf _) _ = error "Leaf in A"
-- intersectionInferB _ (EndInfNode _) _ = error "EndNode in A"
-- intersectionInferB _ (Node _ _ _) _ = error "Node in A"

-- intersectionInferB c a b =  intersectionInferB' c a b `debug4` ("intersectionInferB: " ++ show c ++ " ; " ++ show a ++ " ; " ++ show b ++ " = \n " ++ show (intersectionInferB' c a b) ++ "\n")
-- intersectionInferB' :: [(Inf, FType)] -> Dd -> Dd -> Dd
-- intersectionInferB' c@((inf, _) : _) a@(InfNodes positionA dcA n1A n0A p1A p0A)  b' = let b = EndInfNode b' in
--     case inf of
--         Dc -> let
--             dcR = intersectionLocal @Dc c dcA b
--             n1R = (if n0A == 1 then
--                 absorb @Neg1 c (mixedIntersection @Neg1 c n1A b) dcR  else
--                 remove_outercomplement_from @Neg1 c n0A (absorb @Neg1 c (mixedIntersection @Neg1 c n1A b) dcR))
--             n0R = absorb @Neg0 c (mixedIntersection @Neg0 c n0A dcR) dcR
--             p1R = if p0A == 1 then
--                 absorb @Pos1 c (mixedIntersection @Pos1 c p1A b) dcR else
--                 remove_outercomplement_from @Pos1 c p0A (absorb @Pos1 c (mixedIntersection @Pos1 c p1A b) dcR)
--             p0R = absorb @Pos0 c (mixedIntersection @Pos0 c p0A dcR) dcR `debug` ("\n"++ show (absorb @Pos0 c (mixedIntersection @Pos0 c p0A dcR) dcR) ++ "\n" ++ show (mixedIntersection @Pos0 c p0A dcR)++"\n")
--             in (InfNodes positionA dcR n1R n0R p1R p0R) `debug` ("\n\n ------ " ++ show ( InfNodes positionA dcR n1R n0R p1R p0R))

--         Neg1 -> let -- replace all the B stuf with (dc: 0, neg1: b, neg0: 1, pos1: 0, pos0: 1)
--             n1R = unionLocal @Neg1 c
--                 (intersectionLocal @Neg1 c n1A b)
--                 (if n0A == 1 then n1R' else remove_outercomplement_from @Neg1 c n0A n1R')
--             n1R' = mixedIntersection @Neg1 c b dcA
--             in InfNodes positionA 0 n1R 1 0 1
--         Neg0 -> let -- replace all the B stuf with (dc: 1, neg1: 0, neg0: b, pos1: 0, pos0: 1)
--             n0R' = intersectionLocal @Neg0 c n0A b
--             n0R = mixedIntersection @Neg0 c n0R' dcA
--             in InfNodes positionA dcA 0 n0R 0 1
--         Pos1 -> let -- replace all the B stuf with (dc: 0, neg1: 0, neg0: 1, pos1: b, pos0: 1)
--             p1R = unionLocal @Pos1 c
--                 (intersectionLocal @Pos1 c n1A b )
--                 (if p0A == 1 then p1R' else remove_outercomplement_from @Pos1 c p0A p1R')
--             p1R' = mixedIntersection @Pos1 c dcA b
--             in InfNodes positionA 0 0 1 p1R 1
--         Pos0 -> let -- replace all the B stuf with (dc: 1, neg1: 0, neg0: b, pos1: 0, pos0: 1)
--             p0R' = intersectionLocal @Pos0 c p0A b
--             p0R = mixedIntersection @Pos0 c p0R' dcA
--             in InfNodes positionA dcA 0 1 0 p0R


-- intersectionInferB' _ _ _ = undefined


intersectionMain :: Context -> Dd -> Dd -> Dd
intersectionMain (c : cs) a b = intersectionMain' (c : cs) a b  `debug4` ("intersectionMain, from " ++ show c ++ "; " ++ show a ++ " ; "  ++ show b ++ "= \n " ++ show (intersectionMain' (c : cs) a b))
intersectionMain [] _ _ = error "empty list not possible"
intersectionMain' :: Context -> Dd -> Dd -> Dd
intersectionMain'  c@((inf, _) : _) a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B)
    | positionA == positionB =  let
        dcR = intersectionLocal @Dc c dcA dcB --`debug` ("intersection A ("++ show positionA ++ ")==B (" ++ show positionB ++ "), with c = " ++ show c)
            `debug` ("\nDcR dcA ^ dcB \t = " ++ show (intersectionLocal @Dc c dcA dcB)
            ++ "\n\t dcA = " ++ show dcA
            ++ "\n\t dcB = " ++ show dcB
            ++ "\n")

        n1R = absorb @Neg1 c (unionLocal @Neg1 c
            (intersectionLocal @Neg1 c n1A n1B) -- overlapping points are by definition not inside the others dc, thus have to be preserved
            (if n0R' == 1 then n1R' else remove_outercomplement_from @Neg1 c n0R' n1R')) dcR -- holes absorb points under intersection
            `debug` (("\nn1R \t ((n1A ^ n1B) v (n0R' / n1R')) @ dcR \t = " ++ show (absorb @Neg1 c (unionLocal @Neg1 c
                (intersectionLocal @Neg1 c n1A n1B)
                (if n0R' == 1 then n1R' else remove_outercomplement_from @Neg1 c n0R' n1R')) dcR)
            ++ "\n \t ((n1A ^ n1B) v (n0R' / n1R')) = " ++  show (unionLocal @Neg1 c
                (intersectionLocal @Neg1 c n1A n1B)
                (if n0R' == 1 then n1R' else remove_outercomplement_from @Neg1 c n0R' n1R')))
            ++ "\n\t (n1A ^ n1B) = " ++ show (intersectionLocal @Neg1 c n1A n1B)
            ++ "\n \t (n0R' / n1R') = " ++ show (if n0R' == 1 then n1R' else remove_outercomplement_from @Neg1 c n0R' n1R')
            ++ "\n \t n0R' = " ++ show n0R'
            ++ "\n\t n1R' = " ++ show n1R')
        n1R' = unionLocal @Neg1 c -- guaranteed that dcA and dcB do not overlap around the finite points, thus they do not get absorbed
            (mixedIntersection @Neg1 c n1A dcB) -- keep the points that fit inside B
            (mixedIntersection @Neg1 c n1B dcA) -- keep the points that fit inside A
            `debug` ("\nn1R' ((n1A ^ dcB) v (n1B ^ dcA)) \t = " ++ show (unionLocal @Neg1 c-- guaranteed that dcA and dcB do not overlap around the finite points, thus they do not get absorbed
            (mixedIntersection @Neg1 c n1A dcB) -- keep the points that fit inside B
            (mixedIntersection @Neg1 c n1B dcA)))

        n0R' = intersectionLocal @Neg0 c n0A n0B -- holes get unioned, because i keep the consequence of holes "uncomplemented" we get local union then intersection.
            `debug` ("\nn0R' \t n0A ^ n0B = " ++ show (intersectionLocal @Neg0 c n0A n0B)
            ++ "\n\t n0A = " ++ show (n0A)
            ++ "\n\t n0B = " ++ show (n0B)
            ++ "\n")
        n0R = absorb @Neg0 c (mixedIntersection @Neg0 c n0R' dcR) dcR-- keep the holes that fit inside dcR
            `debug` ("\nn0R \t (n0R' ^ dcR) @ dcR = " ++ show (absorb @Neg0 c (mixedIntersection @Neg0 c n0R' dcR) dcR)
            ++ "\n\t (n0R' ^ dcR) = " ++ show (mixedIntersection @Neg0 c n0R' dcR)
            ++ "\n\t dcR = " ++ show dcR
            ++ "\n")

        -- if the local hole fits inside dcR but the consequence of n0R' does not fit inside the consequenc of dcR it should return n0R' -> Leaf false
        ------------------------------------
        p1R = absorb @Pos1 c (unionLocal @Pos1 c
            (intersectionLocal @Pos1 c p1A p1B)
            (if p0R' == 1 then p1R' else remove_outercomplement_from @Pos1 c p0R' p1R')) dcR
            `debug` ("\np1R \t (p1A ^ p1B) v (p1R' / p0R') \t = " ++ show (unionLocal @Pos1 c
                (intersectionLocal @Pos1 c p1A p1B)
                (if p0R' == 1 then p1R' else remove_outercomplement_from @Pos1 c p0R' p1R'))
            ++ "\n \t (p1A ^ p1B) = " ++ show (intersectionLocal @Pos1 c p1A p1B)
            ++ "\n \t (p1R' / p0R') = " ++ show (if p0R' == 1 then p1R' else remove_outercomplement_from @Pos1 c p0R' p1R')
            ++ "\n\t p0R' = " ++ show p0R'
            ++ "\n\t p1R' = " ++ show p1R'
            ++ "\n")
        p1R' = unionLocal @Pos1 c
            (mixedIntersection @Pos1 c p1A dcB)
            (mixedIntersection @Pos1 c p1B dcA)
            `debug` ("\np1R' \t (p1A ^ dcB) v (p1B ^ dcA) \t = " ++ show (unionLocal @Pos1 c
                (mixedIntersection @Pos1 c p1A dcB)
                (mixedIntersection @Pos1 c p1B dcA))
            ++ "\n\t (p1A ^ dcB) = " ++ show (mixedIntersection @Pos1 c p1A dcB)
            ++ "\n\t (p1B ^ dcA) = " ++ show (mixedIntersection @Pos1 c p1B dcA)
            -- ++ "\n\t (rm p1R p0R')" ++ show (if p1R' == 0 then p0R' else remove_f1s0_from_f0s0 c p1R' p0R')
            ++ "\n\t p1A = " ++ show p1A
            ++ "\n\t p1B = " ++ show p1B
            ++ "\n\t dcA = " ++ show dcA
            ++ "\n\t dcB = " ++ show dcB
            ++ "\n")
        p0R' = intersectionLocal @Pos0 c p0A p0B -- local union then intersection
            `debug` ("\np0R' \t p0A ^ p0B = " ++ show (intersectionLocal @Pos0 c p0A p0B)
            ++ "\n\t p0A = " ++ show p0A
            ++ "\n\t p0B = " ++ show p0B
            ++ "\n")
        p0R = absorb @Pos0 c (mixedIntersection @Pos0 c p0R' dcR) dcR
            `debug` ("\np0R \t (p0R' ^ dcR) @ dcR = " ++ show (absorb @Pos0 c (mixedIntersection @Pos0 c p0R' dcR) dcR)
            ++ "\n\t (p0R' ^ dcR) = " ++ show (mixedIntersection @Pos0 c p0R' dcR)
            ++ "\n\t dcR = " ++ show dcR
            ++ "\n")
        in InfNodes positionA dcR n1R n0R p1R p0R
    | positionA > positionB = intersectionInferA c a b
    | positionA < positionB = intersectionInferB c a b-- replace all the A stuf with (dc: a, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
intersectionMain' c a b = error (show a ++ ", " ++ show b ++ ", "++ show c)

-- unionInferA :: Context -> Dd -> Dd -> Dd
-- unionInferA [] _ _ = error "empty context"
-- unionInferA _ _ (Leaf _) = error "Leaf in A"
-- unionInferA _ _ (EndInfNode _) = error "EndNode in A"
-- unionInferA _ _ (Node _ _ _) = error "Node in A"

-- unionInferA c a b =  unionInferA' c a b `debug4` ("unionInferA: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b ++ " = " ++ show (unionInferA' c a b ))
-- unionInferA' :: [(Inf, FType)] -> Dd -> Dd -> Dd
-- unionInferA' c@((inf, _) : _) a' b@(InfNodes positionB dcB n1B n0B p1B p0B) = let a = EndInfNode a' in
--     case inf of
--         Dc -> let
--             dcR = unionLocal @Dc c  a dcB --pass along the consequence of B for both dcA and not dcA
--             n1R = absorb @Neg1 c (mixedUnion @Neg1 c n1B dcR) dcR

--             n0R = let n0R' = mixedUnion @Neg0 c n0B a in
--                 if n1B == 0 then absorb @Neg0 c n0R' dcR else absorb @Neg0 c (remove_outercomplement_from @Neg0 c n1B n0R') dcR

--             p1R = absorb @Pos1 c (mixedUnion @Pos1 c p1B dcR) dcR
--             p0R = let p0R' = mixedUnion @Pos0 c p0B a in
--                 if p1B == 0 then absorb @Pos0 c p0R' dcR else absorb @Pos0 c (remove_outercomplement_from @Pos0 c p1B p0R') dcR

--             in InfNodes positionB dcR n1R n0R p1R p0R

--         Neg1 -> let -- replace all the A stuf with (dc: 0, neg1: a, neg0: 1, pos1: 0, pos0: 1)
--             n1R' = unionLocal @Neg1 c a n1B `debug` ("--------- " ++ show n1B)
--             n1R = mixedUnion @Neg1 c n1R' dcB
--             in InfNodes positionB 0 n1R 1 0 1
--         Neg0 -> let -- replace all the A stuf with (dc: 1, neg1: 0, neg0: a, pos1: 0, pos0: 1)
--             n0R = intersectionLocal @Neg0 c
--                 (unionLocal @Neg0 c a n0B)
--                 (if n1B == 1 then n0R' else remove_outercomplement_from @Neg0 c n1B n0R')
--             n0R' = mixedUnion @Neg0 c a dcB
--             in InfNodes positionB dcB 0 n0R 0 1
--         Pos1 -> let -- replace all the A stuf with (dc: 0, neg1: 0, neg0: 1, pos1: a, pos0: 1)
--             p1R' = unionLocal @Pos1 c a p1B
--             p1R = mixedUnion @Pos1 c p1R' dcB
--             in InfNodes positionB 0 0 1 p1R 1
--         Pos0 -> let -- replace all the A stuf with (dc: 1, neg1: 0, neg0: a, pos1: 0, pos0: 1)
--             p0R = intersectionLocal @Pos0 c
--                 (unionLocal @Pos0 c a n0B)
--                 (if p1B == 1 then p0R' else remove_outercomplement_from @Pos0 c p1B p0R')
--             p0R' = mixedUnion @Pos0 c a dcB
--             in InfNodes positionB dcB 0 1 0 p0R
-- unionInferA' _ _ _ = undefined


-- unionInferB :: Context -> Dd -> Dd -> Dd
-- unionInferB [] _ _ = error "empty context"
-- unionInferB _ (Leaf _) _ = error "Leaf in A"
-- unionInferB _ (EndInfNode _) _ = error "EndNode in A"
-- unionInferB _ (Node _ _ _) _ = error "Node in A"

-- unionInferB c a b =  unionInferB' c a b  `debug4` ("unionInferB: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b ++ " = " ++ show (unionInferB' c a b ))
-- unionInferB' :: [(Inf, FType)] -> Dd -> Dd -> Dd
-- unionInferB' c@((inf, _) : _) a@(InfNodes positionA dcA n1A n0A p1A p0A) b' = let b = EndInfNode b' in
--     case inf of
--         Dc -> let
--             dcR = unionLocal @Dc c b dcA
--                 `debug` ("\ndcR \t = " ++ show (unionLocal @Dc c b dcA))
--             n1R = absorb @Neg1 c (mixedUnion @Neg1 c n1A dcR) dcR
--                 `debug` ("\nn1R (n1A ^ dcR) @ dcR \t = " ++ show (absorb @Neg1 c (mixedUnion @Neg1 c n1A dcR) dcR))

--             n0R = (let n0R' = mixedUnion @Neg0 c n0A b in
--                 if n1A == 0 then absorb @Neg0 c  n0R' dcR else  absorb @Neg0 c (remove_outercomplement_from @Neg0 c n1A n0R') dcR)
--                 `debug` ("**n0R' = n0A v b = " ++ show (mixedUnion @Neg0 c n0A b) ++ "\n" ++
--                 "**n0R' @ dcR = " ++ show (absorb @Neg0 c  (mixedUnion @Neg0 c n0A b) dcR) ++ "\n" ++
--                 "**n0A = " ++ show n0A ++ "\n" ++
--                 "**b = " ++ show b ++ "\n")

--             p1R = absorb @Pos1 c (mixedUnion @Pos1 c p1A dcR) dcR
--                 `debug` ("\np1R (p1A ^ dcR) @ dcR \t = " ++ show (absorb @Pos1 c (mixedUnion @Pos1 c p1A dcR) dcR))
--             p0R = (let p0R' =  mixedUnion @Pos0 c p0A b in
--                 if p1A == 0 then absorb @Pos0 c p0R' dcR else absorb @Pos0 c (remove_outercomplement_from @Pos0 c p1A p0R') dcR)
--                 `debug` ("p0R' = " ++ show (mixedUnion @Pos0 c p0A b) ++ "\n")
--                 `debug` ("p0R' @ dcR = " ++ show (absorb @Pos0 c (mixedUnion @Pos0 c p0A b) dcR) ++ "\n")
--                 `debug` ("p0A = " ++ show p0A)
--             in InfNodes positionA dcR n1R n0R p1R p0R
--         Neg1 -> let -- replace all the B stuf with (dc: 0, neg1: b, neg0: 1, pos1: 0, pos0: 1)
--             n1R' = unionLocal @Neg1 c n1A b
--             n1R = mixedUnion @Neg1 c n1R' dcA
--             in InfNodes positionA 0 n1R 1 0 1
--         Neg0 -> let -- replace all the B stuf with (dc: 1, neg1: 0, neg0: b, pos1: 0, pos0: 1)
--             n0R = intersectionLocal @Neg0 c
--                 (unionLocal @Neg0 c n0A b)
--                 (if n1A == 1 then n0R' else remove_outercomplement_from @Neg0 c n1A n0R')
--                 `debug` ("n0R = (n0A U b) ^ (n1A / n0R') = \n " ++ show n0R)
--             n0R' = mixedUnion @Neg0 c b dcA
--                 `debug` ("n0R' = (b ^ dcA) = \n " ++ show n0R')
--             in InfNodes positionA dcA 0 n0R 0 1
--         Pos1 -> let -- replace all the B stuf with (dc: 0, neg1: 0, neg0: 1, pos1: b, pos0: 1)
--             p1R' = unionLocal @Pos1 c p1A b
--             p1R = mixedUnion @Pos1 c p1R' dcA
--             in InfNodes positionA 0 0 1 p1R 1
--         Pos0 -> let -- replace all the B stuf with (dc: 1, neg1: 0, neg0: b, pos1: 0, pos0: 1)
--             p0R = intersectionLocal @Pos0 c
--                 (unionLocal @Pos0 c n0A b )
--                 (if p1A == 1 then p0R' else remove_outercomplement_from @Pos0 c p1A p0R')
--                 `debug` ("p0R = (p0A U b) ^ (p1A / p0R') = \n " ++ show p0R)
--             p0R' = mixedUnion @Pos0 c b dcA
--                 `debug` ("p0R' = (b ^ dcA) = \n " ++ show p0R')
--             in InfNodes positionA dcA 0 1 0 p0R
-- unionInferB' _ _ _ = undefined

-- unionMain :: Context -> Dd -> Dd -> Dd
-- -- exclusive points (0's / holes) under union are filled unless they are present in both A and B (so only an intersection between them needs to be done)
-- -- inclusive point (1's ) under union are intersected with the opposite infinite subset (dc) before they are added together
-- unionMain c a b = unionMain' c a b  `debug4` ("unionMain: " ++ show c ++ " ; " ++ show a ++ " ; " ++ show b ++ " = " ++ show (unionMain' c a b))
-- unionMain' :: Context -> Dd -> Dd -> Dd
-- unionMain'  c a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B)
--     | positionA == positionB =  let

--         dcR = unionLocal @Dc c  dcA dcB
--             `debug` ("\nDcR \t dcA v dcB = " ++ show (unionLocal @Dc c dcA dcB)
--             ++ "\n\t dcA = " ++ show dcA
--             ++ "\n\t dcB = " ++ show dcB
--             ++ "\n")

--         n1R = absorb @Neg1 c (mixedUnion @Neg1 c n1R' dcR) dcR
--             `debug` ("\nn1R \t (n1R' v  dcR) @ dcR = " ++ show (absorb @Neg1 c (mixedUnion @Neg1 c n1R' dcR) dcR)
--             ++ "\n\t (n1R' ^ dcR) = " ++ show (mixedUnion @Neg1 c n1R' dcR)
--             ++ "\n\t n1R' = " ++ show n1R'
--             ++ "\n\t dcR = " ++ show dcR
--             ++ "\n")
--         n1R' = unionLocal @Neg1 c n1A n1B
--             `debug2` ("\nn1R' \t n1A v n1B \b = " ++ show (unionLocal @Neg1 c n1A n1B)
--             ++ "\n\t n1A = " ++ show n1A
--             ++ "\n\t n1B = " ++ show n1B
--             ++ "\n")

--         n0R = absorb @Neg0 c (intersectionLocal @Neg0 c
--             (unionLocal @Neg0 c n0A n0B)
--             (if n1R' == 0 then n0R' else remove_outercomplement_from @Neg0 c n1R' n0R')) dcR
--             `debug2` ("\nn0R \t ((n0A v n0B) ^ (n0R' / n1R')) @ dcR = " ++ show ( absorb @Neg0 c (intersectionLocal @Neg0 c
--                     (unionLocal @Neg0 c n0A n0B)
--                     (if n1R' == 0 then n0R' else remove_outercomplement_from @Neg0 c n1R' n0R')) dcR)
--                 ++ "\n\t (n0A v n0B) = " ++ show (unionLocal @Neg0 c n0A n0B)
--                 ++ "\n\t (n0R' / n1R') = " ++ show (if n1R' == 0 then n0R' else remove_outercomplement_from @Pos0 c n1R' n0R')
--                 ++ "\n\t n0A = " ++ show n0A
--                 ++ "\n\t n0B = " ++ show n0B
--                 ++ "\n\t n1R' = " ++ show n1R'
--                 ++ "\n\t n0R' = " ++ show n0R'
--                 ++ "\n")
--         n0R' = intersectionLocal @Neg0 c
--             (mixedUnion @Neg0 c n0A dcB) -- remove the holes that do fit in B (unioned away) // note that in consequence this reverts back to to union and is absorbed if consequence of n0A == dcR
--             (mixedUnion @Neg0 c n0B dcA) -- remove the holes that do fit in A (unioned away)
--             `debug2` ("\nn0R' \t (n0A ^ dcB) ^ (n0B ^ dcA) = " ++ show (intersectionLocal @Neg0 c
--                 (mixedUnion @Neg0 c n0A dcB)
--                 (mixedUnion @Neg0 c n0B dcA))
--                 ++ "\n\t (n0A ^ dcB) ^ (n0B ^ dcA) = " ++ show (intersectionLocal @Neg0 c
--                                                 (mixedUnion @Neg0 c n0A dcB)
--                                                 (mixedUnion @Neg0 c n0B dcA))
--                 ++ "\n\t (n0A ^ dcB) = " ++ show (mixedUnion @Neg0 c n0A dcB)
--                 ++ "\n\t (n0B ^ dcA) = " ++ show (mixedUnion @Neg0 c n0B dcA)
--                 ++ "\n\t dcR = " ++ show dcR
--                 ++ "\n\t n0A = " ++ show n0A
--                 ++ "\n\t n0B = " ++ show n0B
--                 ++ "\n\t dcB = " ++ show dcB
--                 ++ "\n\t dcA = " ++ show dcA
--                 ++ "\n")

--         ------------------------------------
--         -- n0R = (n0A cap n0B) cup ((n0A cap neg dcB) cap n1B) cup ((n0B cap neg dcA) cap n1A) <-> (n0A cup n0B) cap n1R* cap neg dcR
--         p1R = absorb @Pos1 c (mixedUnion @Pos1 c p1R' dcR) dcR
--             `debug` ("\np1R \t (p1R' ^ dcR) @ dcR = " ++ show (absorb @Pos1 c (mixedUnion @Pos1 c p1R' dcR) dcR)
--             ++ "\n\t p1R' = " ++ show p1R'
--             ++ "\n\t dcR = " ++ show dcR
--             ++ "\n")
--         p1R' = unionLocal @Pos1 c p1A p1B
--             `debug` ("\np1R \t p1A v p1B"
--             ++ "\n\t p1A = " ++ show p1A
--             ++ "\n\t p1B = " ++ show p1B
--             ++ "\n")

--         p0R = absorb @Pos0 c (intersectionLocal @Pos0 c
--             (unionLocal @Pos0 c p0A p0B)
--             (if p1R' == 0 then p0R' else remove_outercomplement_from @Pos0 c p1R' p0R')) dcR
--             `debug` ("\np0R = ((p0A v p0B) ^ (p0R' / p1R')) @dcR \t = " ++ show (absorb @Pos0 c (intersectionLocal @Pos0 c
--                 (unionLocal @Pos0 c p0A p0B)
--                 (if p1R' == 0 then p0R' else remove_outercomplement_from @Pos0 c p1R' p0R')) dcR)
--             ++ "\n\t (p0A v p0B) = " ++ show (unionLocal @Pos0 c p0A p0B)
--             ++ "\n\t (p0R' / p1R') = " ++ show (if p1R' == 0 then p0R' else remove_outercomplement_from @Pos0 c p1R' p0R')
--             ++ "\n\t p0A = " ++ show p0A
--             ++ "\n\t p0B = " ++ show p0B
--             ++ "\n\t p1R' = " ++ show p1R'
--             ++ "\n\t p0R' = " ++ show p0R'
--             ++ "\n")
--         p0R' = intersectionLocal @Pos0 c
--             (mixedUnion @Pos0 c p0A dcB) -- remove the holes that do fit in B: if the consequence of p0A after union is the same as the consequence of dcB, then it is also removed. If the consequence is smaller it is kept.
--             (mixedUnion @Pos0 c p0B dcA)
--             `debug` ("\np0R' \t  ((p0A ^ dcB) ^ (p0B ^ dcA)) \t = " ++ show (intersectionLocal @Pos0 c
--                                                 (mixedUnion @Pos0 c p0A dcB)
--                                                 (mixedUnion @Pos0 c p0B dcA))
--                 ++ "\n\t (p0A ^ dcB) ^ (p0B ^ dcA) = " ++ show (intersectionLocal @Pos0 c
--                                                 (mixedUnion @Pos0 c p0A dcB)
--                                                 (mixedUnion @Pos0 c p0B dcA))
--                 ++ "\n\t (p0A ^ dcB) = " ++ show (mixedUnion @Pos0 c p0A dcB)
--                 ++ "\n\t (p0B ^ dcA) = " ++ show (mixedUnion @Pos0 c p0B dcA)
--                 ++ "\n\t dcR = " ++ show dcR
--                 ++ "\n\t p0A = " ++ show p0A
--                 ++ "\n\t p0B = " ++ show p0B
--                 ++ "\n\t dcB = " ++ show dcB
--                 ++ "\n\t dcA = " ++ show dcA
--                 ++ "\n")

--         in InfNodes positionA dcR n1R n0R p1R p0R `debug2` ("unionMain = " ++ show (InfNodes positionA dcR n1R n0R p1R p0R))

--     | positionA > positionB = unionInferA c a b-- replace all the A stuf with (dc: a, neg1: 0, neg0: 1, pos1: 0, pos0: 1)

--     -- c cannot be empty..
--     | positionA < positionB = unionInferB c a b-- replace all the A stuf with (dc: a, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
-- unionMain' c a b = error "no 2 StartInfNode's in union main"


-- -- captures the general patterns for the functions
class Dd1 a where
    intersectionLocal' :: Context -> Dd -> Dd -> Dd
--     mixedIntersection' :: Context -> Dd -> Dd -> Dd
--     mixedUnion' :: Context -> Dd -> Dd -> Dd
--     unionLocal' :: Context -> Dd -> Dd -> Dd
--     remove_outercomplement_from' :: Context -> Dd -> Dd -> Dd
--     absorb' :: Context -> Dd -> Dd -> Dd
--     traverse_and_return' :: Bool -> Context -> Dd -> Dd -> Dd



instance (DdF4 a) => Dd1 a where
    -- reached leaf, so return a result here
--     remove_outercomplement_from' c a@(Leaf _) b@(Leaf _)
--         | a == false @a = false @a  --oposite, thus turn false and true around (becaus @a implies the type of b)
--         | b == false @a = false @a
--         | otherwise = true @a
--     remove_outercomplement_from' c a@(Leaf _) b@(Node _ _ _)
--         | a == false @a = false @a
--         | a == true @a = b -- inferNodeA_opposite @a (remove_outercomplement_from @a) c a b
--     remove_outercomplement_from' c a@(Node _ _ _) b@(Leaf _)
--         | b == false @a = false @a
--         | b == true @a = a -- inferNodeB @a (remove_outercomplement_from @a) c a b
--     remove_outercomplement_from' c a@(Leaf _) b@(InfNodes {})
--         | a == false @a = false @a
--         | a == true @a = b `debug2` ("remove from " ++ show (true @a) ++ " resulting in: " ++ show b)
--     remove_outercomplement_from' c a@(InfNodes {}) b@(Leaf _)
--         | b == false @a = false @a
--         | b == true @a = a `debug2` ("remove from " ++ show (true @a) ++ " resulting in: " ++ show a)
--     remove_outercomplement_from' c a@(EndInfNode a') b@(Leaf _)
--         | b == false @a = false @a -- bot
--         | b == true @a = applyInfElimRule @a a'
--     remove_outercomplement_from' c a@(Leaf _) b@(EndInfNode b')
--         | a == false @a = false @a -- bot
--         | a == true @a = applyInfElimRule @a b'
--     remove_outercomplement_from' [] a@(EndInfNode _) b@(Leaf _) = error "empty context"


--     remove_outercomplement_from' c a@(Node positionA pos_childA neg_childA) b@(EndInfNode d) = inferNodeB @a (remove_outercomplement_from @a) c a b
--     remove_outercomplement_from' c a@(EndInfNode d) b@(Node positionB pos_childB neg_childB) = inferNodeA_opposite @a (remove_outercomplement_from @a) c a b
--     -- removecomplements cannot be nested
--     remove_outercomplement_from' c@(Context{func_context = (f:fs)}) (EndInfNode a) (EndInfNode b) = continue_outer f c{func_context = fs} (negation a) b -- todo negation a makes sense? or should i use maybe_negate on both to make sure we get the same polarity?
--     remove_outercomplement_from' [] a@(EndInfNode childA)  b@(EndInfNode childB) = error "should not have empty context stack"

--     -- No leafs involved
--     remove_outercomplement_from' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)-- no mismatch, thus no inference is needed

--         -- No mismatch, only the appropriate ZDD elim is applied
--         | positionA == positionB =
--             let pos_result = remove_outercomplement_from @a c pos_childA pos_childB
--                 neg_result = remove_outercomplement_from @a c neg_childA neg_childB
--             in applyElimRule @a (Node positionA pos_result neg_result)

--         -- mismatch with no Bot involved, thus with ZDD types inference we return bot
--         | positionA < positionB =
--             remove_outercomplement_from @a c neg_childA b
--         | positionA > positionB =
--             Node positionB pos_childB (remove_outercomplement_from @a c a neg_childB)


--     remove_outercomplement_from' c a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) -- check define inner recursion for lobsided intersectio/union: (-. a .^. b)?
--         | positionA > positionB = case to_constr @a of
--             Dc -> error "remove outer complement from with a dc should not be possible"
--             Neg1 -> applyInfElimRule @a $ t_and_rInferA_ @a False ((to_constr @a, Absorb) : c) a b
--             Neg0 -> applyInfElimRule @a $ t_and_rInferA_ @a True ((to_constr @a, Absorb) : c) a b
--             Pos1 -> applyInfElimRule @a $ t_and_rInferA_ @a False ((to_constr @a, Absorb) : c) a b
--             Pos0 -> applyInfElimRule @a $ t_and_rInferA_ @a True ((to_constr @a, Absorb) : c) a b
--         | positionA < positionB =  remove_outercomplement_from @a c neg_childA b
--         | positionA == positionB =  undefined
--     remove_outercomplement_from' c a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB)
--         | positionA > positionB =  remove_outercomplement_from @a c a neg_childB
--         | positionA < positionB =   case to_constr @a of
--             Dc -> error "remove outer complement from with a dc should not be possible"
--             Neg1 -> applyInfElimRule @a $ t_and_rInferB_ @a False ((to_constr @a, Absorb) : c) a b
--             Neg0 -> applyInfElimRule @a $ t_and_rInferB_ @a True ((to_constr @a, Absorb) : c) a b
--             Pos1 -> applyInfElimRule @a $ t_and_rInferB_ @a False ((to_constr @a, Absorb) : c) a b
--             Pos0 -> applyInfElimRule @a $ t_and_rInferB_ @a True ((to_constr @a, Absorb) : c) a b
--         | positionA == positionB =  undefined

--     remove_outercomplement_from' c a@(InfNodes{}) b@(EndInfNode d) =
--         case to_constr @a of
--             Dc -> error "remove outer complement from with a dc should not be possible"
--             Neg1 -> applyInfElimRule @a $ t_and_rInferB_ @a False ((to_constr @a, Absorb) : c) a b
--             Neg0 -> applyInfElimRule @a $ t_and_rInferB_ @a True ((to_constr @a, Absorb) : c) a b
--             Pos1 -> applyInfElimRule @a $ t_and_rInferB_ @a False ((to_constr @a, Absorb) : c) a b
--             Pos0 -> applyInfElimRule @a $ t_and_rInferB_ @a True ((to_constr @a, Absorb) : c) a b
--     remove_outercomplement_from' c a@(EndInfNode d) b@(InfNodes{}) =
--         case to_constr @a of
--             Dc -> error "remove outer complement from with a dc should not be possible"
--             Neg1 -> applyInfElimRule @a $ t_and_rInferA_ @a False ((to_constr @a, Absorb) : c) a b
--             Neg0 -> applyInfElimRule @a $ t_and_rInferA_ @a True ((to_constr @a, Absorb) : c) a b
--             Pos1 -> applyInfElimRule @a $ t_and_rInferA_ @a False ((to_constr @a, Absorb) : c) a b
--             Pos0 -> applyInfElimRule @a $ t_and_rInferA_ @a True ((to_constr @a, Absorb) : c) a b


--     remove_outercomplement_from' c a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B)
--         | positionA == positionB = case to_constr @a of
--             Dc -> error "absorb with a dc as first argument should not be possible"
--             Neg1 -> applyInfElimRule @a $ t_and_rMain False ((to_constr @a, Remove):c) a b
--             Neg0 -> applyInfElimRule @a $ t_and_rMain True ((to_constr @a, Remove):c) a b
--             Pos1 -> applyInfElimRule @a $ t_and_rMain False ((to_constr @a, Remove):c) a b
--             Pos0 -> applyInfElimRule @a $ t_and_rMain True ((to_constr @a, Remove):c) a b
--         | positionA < positionB = case to_constr @a of
--             Dc -> error "remove outer complement from with a dc should not be possible"
--             Neg1 -> applyInfElimRule @a $ t_and_rInferB_ @a False ((to_constr @a, Remove):c) a b
--             Neg0 -> applyInfElimRule @a $ t_and_rInferB_ @a True ((to_constr @a, Remove):c) a b
--             Pos1 -> applyInfElimRule @a $ t_and_rInferB_ @a False ((to_constr @a, Remove):c) a b
--             Pos0 -> applyInfElimRule @a $ t_and_rInferB_ @a True ((to_constr @a, Remove):c) a b
--         | positionA > positionB = case to_constr @a of
--             Dc -> error "remove outer complement from with a dc should not be possible"
--             Neg1 -> applyInfElimRule @a $ t_and_rInferA_ @a False ((to_constr @a, Remove):c) a b
--             Neg0 -> applyInfElimRule @a $ t_and_rInferA_ @a True ((to_constr @a, Remove):c) a b
--             Pos1 -> applyInfElimRule @a $ t_and_rInferA_ @a False ((to_constr @a, Remove):c) a b
--             Pos0 -> applyInfElimRule @a $ t_and_rInferA_ @a True ((to_constr @a, Remove):c) a b
--     remove_outercomplement_from' c a b = undefined `debug4` (show a ++ "  :  " ++ show b)

    intersectionLocal' c a@1 b = b
    intersectionLocal' c@(Context{func_context = (f:fs)}) a@0 b@(EndInfNode childB ) = intersectionLocal_arg f c{func_context = fs} a childB
    intersectionLocal' c a@0 b@(Leaf _) = Leaf False -- dc case for leafs

    intersectionLocal' c a@0 b@(InfNodes {}) = applyInfElimRule @a $ intersectionInferA_ @a c a b -- leaf with node or end infnode
    intersectionLocal' c a@0 b = inferNodeA @a (intersectionLocal @a) c a b -- leaf with node or end infnode

    intersectionLocal' c a b@1 = a
    intersectionLocal' c@(Context{func_context = (f:fs)}) a@(EndInfNode childA ) b@0 = intersectionLocal_arg f c{func_context = fs} childA b

    intersectionLocal' c a@(Leaf _) b@0 = Leaf False -- dc case for leafs
    intersectionLocal' c a@(InfNodes {}) b@0 = applyInfElimRule @a $ intersectionInferB_ @a c a b -- leaf with node or end infnode
    intersectionLocal' c a b@0 = inferNodeB @a (intersectionLocal @a) c a b -- leaf with node or end infnode

    -- infer node at DdF4, and here the shared abstrations
    intersectionLocal' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
        -- Match
        | positionA == positionB =
            let pos_result = intersectionLocal @a c pos_childA pos_childB
                neg_result = intersectionLocal @a c neg_childA neg_childB
            in applyElimRule @a (Node positionA pos_result neg_result)
        -- Mismatch, but with a inference we ontinue recursion with the earliest (thus lowest valued) node.
        | positionA < positionB = inferNodeB @a (intersectionLocal @a) c a b
        | positionA > positionB = inferNodeA @a (intersectionLocal @a) c a b

    -- go one recursive layer deeper !
    intersectionLocal' c a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB = inferNodeA @a (intersectionLocal @a) c a b -- infer node A
        | positionA < positionB = applyInfElimRule @a $ intersectionInferB_ @a c a b -- infer infnode B and start intersection inside it
    intersectionLocal' c a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB _ _ _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB = applyInfElimRule @a $ intersectionInferA_ @a c a b
        | positionA < positionB = inferNodeB @a (intersectionLocal @a) c a b
    intersectionLocal'  c a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _)
        | positionA == positionB = applyInfElimRule @a $ intersection  ((to_constr @a, Inter):c) a b `debug5` ("infinf: " ++ show a ++ show b) -- start intersection and push local-intersection to the context
        | positionA < positionB = applyInfElimRule @a $ intersectionInferB_ @a c a b -- infer infnode B
        | positionA > positionB = applyInfElimRule @a $ intersectionInferA_ @a c a b -- infer infnode A
    intersectionLocal' c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = applyInfElimRule @a $ intersectionInferB_ @a c a b
    intersectionLocal' c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = applyInfElimRule @a $ intersectionInferA_ @a c a b

    -- continue local traversal
    intersectionLocal' c a@(Node positionA pos_childA neg_childA) b@(EndInfNode childB) = inferNodeB @a (intersectionLocal @a) c a b
    intersectionLocal' c a@(EndInfNode childA) b@(Node positionB pos_childB neg_childB) = inferNodeA @a (intersectionLocal @a) c a b
    -- continue previous super domain traversal
    intersectionLocal' c@(Context{func_context = (f:fs)}) a@(EndInfNode childA)  b@(EndInfNode childB) = (continue_outer f c{func_context = fs} childA childB) `debug2` ("endinfendinf interLocqal : " ++ show (continue_outer c cs childA childB) ++ " \n : " ++ show childA ++ " , " ++ show childB)
    intersectionLocal' [] a@(EndInfNode childA)  b@(EndInfNode childB) = error "should not have empty context stack"-- applyInfElimRule @a $ intersection  [] childA childB


    intersectionLocal' c a b = error ("how did we get here? " ++  show c ++ show a ++ "  -  " ++ show b)

--     unionLocal' c a@0 b = b
--     unionLocal' c@(Context{func_context = (f:fs)}) a@1 b@(EndInfNode childB ) = unionLocal_arg f c{func_context = fs} a childB `debug2` ("endif a = true, c = " ++ show c ++ "," ++ show cs ++ " a: " ++ show a ++ " b: " ++ show childB)
--     unionLocal' c a@1 b@(Leaf _) = Leaf True
--     unionLocal' c a@1 b@(InfNodes {}) = applyInfElimRule @a $ unionInferA_ @a c a b
--     unionLocal' c a@1 b = inferNodeA @a (unionLocal @a) c a b -- leaf with node or end infnode

--     unionLocal' c a b@0 = a
--     unionLocal' c@(Context{func_context = (f:fs)}) a@(EndInfNode childA ) b@1 = unionLocal_arg f c{func_context = fs} childA b `debug2` ("endif b = true, c = " ++ show c ++ "," ++ show cs ++ " a: " ++ show childA ++ " b: "  ++ show b)
--     unionLocal' c a@(Leaf _) b@1 = Leaf True
--     unionLocal' c a@(InfNodes {}) b@1 = applyInfElimRule @a $ unionInferB_ @a c a b
--     unionLocal' c a b@1 = inferNodeB @a (unionLocal @a) c a b -- leaf with node or end infnode


--     unionLocal' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
--         -- no mismatch, only the appropriate elim rule is applied
--         | positionA == positionB =
--             let pos_result = unionLocal @a c pos_childA pos_childB
--                 neg_result = unionLocal @a c neg_childA neg_childB
--             in applyElimRule @a (Node positionA pos_result neg_result)
--         | positionA < positionB = inferNodeB @a (unionLocal @a) c a b
--         | positionA > positionB = inferNodeA @a (unionLocal @a) c a b

--     unionLocal' c a@(InfNodes positionA _ _ _ _ _)  b@(Node positionB pos_childB neg_childB)
--         | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
--         | positionA > positionB = inferNodeA @a (unionLocal @a) c a b
--         | positionA < positionB = applyInfElimRule @a $ unionInferA_ @a c a b -- infer infnode for A

--     unionLocal' c a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _)
--         | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes" -- a possible option: (InfNodes (dcA .*. pos_childB) (n1A .*. pos_childB) (n0A .*. pos_childB) (p1A .*. pos_childB) (p0A .*. pos_childB))
--         | positionA < positionB = inferNodeB @a (unionLocal @a) c a b
--         | positionA > positionB = applyInfElimRule @a $ unionInferB_ @a c a b -- infer infnode for B

--     unionLocal' c a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _)
--         | positionA == positionB = applyInfElimRule @a $ union  ((to_constr @a, Union):c) a b
--         | positionA < positionB = applyInfElimRule @a $ unionInferB_ @a c a b -- infer infnode A
--         | positionA > positionB = applyInfElimRule @a $ unionInferA_ @a c a b -- infer infnode B

--     unionLocal' c a@(InfNodes {}) b@(EndInfNode _) = applyInfElimRule @a $ unionInferB_ @a c a b
--     unionLocal' c a@(EndInfNode _) b@(InfNodes {}) = applyInfElimRule @a $ unionInferA_ @a c a b

--     -- continue local traversal
--     unionLocal' c a@(Node positionA pos_childA neg_childA) b@(EndInfNode childB) = inferNodeB @a (unionLocal @a) c a b
--     unionLocal' c a@(EndInfNode childA) b@(Node positionB pos_childB neg_childB) = inferNodeA @a (unionLocal @a) c a b

--     -- continue previous super domain traversal
--     unionLocal' c@(Context{func_context = (f:fs)}) a@(EndInfNode childA)  b@(EndInfNode childB) = continue_outer f c{func_context = fs} childA childB `debug2` ("endinf endinf union local, childA = " ++ show childA  ++ " \n \t childB = " ++ show childB )
--     unionLocal' [] a@(EndInfNode childA)  b@(EndInfNode childB) = error "should not have empty context stack"  -- applyInfElimRule @a $ union  [] childA childB
--     unionLocal' c a b = error (show c ++ show a ++ show b)

--     mixedIntersection' c l@(Leaf _) (Leaf _) = if l == false @a then false @a else Leaf False-- if n then 1 if n' then 0
--     -- exception cases where zdd and its polar are not false @a, and dc is not a leaf.
--     mixedIntersection' c l@0 b = Leaf False
--     mixedIntersection' c l@1 b = if l == false @a then false @a else b
--     -- exception where the zdd is not a leaf and dc is
--     mixedIntersection' c a l@0 = Leaf False
--     -- note that the a cannot be larger than 1 thus, the positive polarity of the zdd cannot not be one in this case (since it will always be largerthan dcR under intersection)
--     mixedIntersection' c a l@1 = a

--     -- No leafs involved
--     mixedIntersection' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

--         -- No mismatch
--         | positionA == positionB =
--             let pos_result = mixedIntersection @a c pos_childA pos_childB
--                 neg_result = mixedIntersection @a c neg_childA neg_childB
--             in applyElimRule @a (Node positionA pos_result neg_result)

--         -- Mismatch
--         | positionA > positionB = inferNodeA @a (mixedIntersection @a) c a b
--         | positionA < positionB =
--             let pos_result = mixedIntersection @a c pos_childA b
--                 neg_result = mixedIntersection @a c neg_childA b
--             in applyElimRule @a (Node positionA pos_result neg_result)

--     -- Single InfNode has been reached, similar to single Leaf node cases.
--     mixedIntersection' c a@(Node positionA pos_childA neg_childA)  b@(EndInfNode _) =
--                 let pos_result = mixedIntersection @a c pos_childA b
--                     neg_result = mixedIntersection @a c neg_childA b
--                 in applyElimRule @a (Node positionA pos_result neg_result)

--     mixedIntersection' c a@(EndInfNode _) b@(Node positionB pos_childB neg_childB) =
--         inferNodeA @a (mixedIntersection @a) c a b

--     mixedIntersection' c a@(InfNodes positionA dcA n1A n0A p1A p0A) b@(InfNodes positionB dcB n1B n0B p1B p0B)
--         | positionA == positionB = applyInfElimRule @a $ intersection  ((to_constr @a, MixedIntersection):c) a b
--         | positionA > positionB = applyInfElimRule @a $ intersectionInferA_ @a c a b
--         | positionB > positionA = applyInfElimRule @a $ intersectionInferB_ @a c a b

--     mixedIntersection' c a@(InfNodes positionA dcA n1A n0A p1A p0A) b@(Node positionB pos_childB neg_childB)
--         | positionA == positionB = error "not yet implemented for zdd types, bdd is impossible"
--         | positionA > positionB = inferNodeA @a (mixedIntersection @a) c a b
--         | positionB > positionA = applyInfElimRule @a $ intersectionInferB_ @a c a b
--     mixedIntersection' c a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB dcB n1B n0B p1B p0B)
--         | positionA == positionB = error "not yet implemented for zdd types, bdd is impossible"
--         | positionA > positionB = applyInfElimRule @a $ intersectionInferA_ @a c a b
--         | positionB > positionA =
--                 let pos_result = mixedIntersection @a c pos_childA b
--                     neg_result = mixedIntersection @a c neg_childA b
--                 in applyElimRule @a (Node positionA pos_result neg_result)
--     -- Both InfNodes have been reached - run the usual intersection.
--     mixedIntersection' c@(Context{func_context = (f:fs)}) (EndInfNode a)  (EndInfNode b) = continue_outer f c{func_context = fs} a b
--     mixedIntersection' [] (EndInfNode a)  (EndInfNode b) = error "should not have an empty context, check if top layer has DC context given along" -- applyInfElimRule @a $ intersection  [] a (negate_maybe @a b)
--     mixedIntersection' c a b = error ("mixedinter - " ++ show c ++ " ; "++ show a ++ "  ;  " ++ show b)

--     mixedUnion' c l@(Leaf _) (Leaf _) = if l == false @a then false @a else Leaf True-- if n then 1 if n' then 0
--     -- exception cases where zdd and its polar are not false @a, and dc is not a leaf.
--     mixedUnion' c l@1 b = Leaf True
--     mixedUnion' c l@0 b = if l == false @a then false @a else  b
--     -- exception where the zdd is not a leaf and dc is
--     mixedUnion' c a l@1 = Leaf True
--     -- note that the a cannot be smaller than 0 thus, the negative polarity of the zdd cannot not be one in this case (since it will always be smaller than dcR under intersection)
--     mixedUnion' c a l@0 = a

--     -- No leafs involved
--     mixedUnion' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
--         -- No mismatch
--         | positionA == positionB =
--             let pos_result = mixedUnion @a c pos_childA pos_childB
--                 neg_result = mixedUnion @a c neg_childA neg_childB
--             in applyElimRule @a (Node positionA pos_result neg_result)
--         -- Mismatch
--         | positionA > positionB = inferNodeA @a (mixedUnion @a) c a b
--         | positionA < positionB =
--             let pos_result = mixedUnion @a c pos_childA b
--                 neg_result = mixedUnion @a c neg_childA b
--             in applyElimRule @a (Node positionA pos_result neg_result)

--     -- Single InfNode has been reached, similar to single Leaf node cases.
--     mixedUnion' c a@(Node positionA pos_childA neg_childA)  b@(EndInfNode _) =
--                 let pos_result = mixedUnion @a c pos_childA b
--                     neg_result = mixedUnion @a c neg_childA b
--                 in applyElimRule @a (Node positionA pos_result neg_result)

--     mixedUnion' c a@(EndInfNode _) b@(Node positionB pos_childB neg_childB) =
--         inferNodeA @a (mixedUnion @a) c a b

--     mixedUnion' c a@(InfNodes positionA dcA n1A n0A p1A p0A) b@(InfNodes positionB dcB n1B n0B p1B p0B)
--         | positionA == positionB = applyInfElimRule @a $ union  ((to_constr @a, MixedUnion):c) a b
--         | positionA > positionB = applyInfElimRule @a $ unionInferA_ @a c a b
--         | positionB > positionA = applyInfElimRule @a $ unionInferB_ @a c a b
--     mixedUnion' c a@(InfNodes positionA dcA n1A n0A p1A p0A) b@(Node positionB pos_childB neg_childB)
--         | positionA == positionB = error "not yet implemented for zdd types, bdd is impossible"
--         | positionA > positionB = inferNodeA @a (mixedUnion @a) c a b
--         | positionB > positionA = applyInfElimRule @a $ unionInferB_ @a c a b
--     mixedUnion' c a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB dcB n1B n0B p1B p0B)
--         | positionA == positionB = undefined
--         | positionA > positionB = applyInfElimRule @a $ unionInferA_ @a c a b
--         | positionB > positionA =
--             let pos_result = mixedUnion @a c pos_childA b
--                 neg_result = mixedUnion @a c neg_childA b
--             in applyElimRule @a (Node positionA pos_result neg_result)
--     -- Both InfNodes have been reached - run the usual union.
--     mixedUnion' c@(Context{func_context = (f:fs)}) (EndInfNode a)  (EndInfNode b) =  unionLocal_arg f c{func_context = fs} a b
--     mixedUnion' [] (EndInfNode a)  (EndInfNode b) = error "should not have an empty context, check if top layer has DC context given along" -- applyInfElimRule @a $ intersection  [] a (negate_maybe @a b)
--     mixedUnion' c a b = error ("mixedunion - " ++ show c ++ " ; "++ show a ++ "  ;  " ++ show b)

--     absorb' c a@(Leaf _) dc = if a == dc then false @a else a
--     absorb' c a@(EndInfNode _) dc@(Node positionD pos_childD neg_childD)  =  inferNodeA @a (absorb @a) c a dc
--     absorb' c (EndInfNode a) dc@(Leaf _)  = if a == dc then false @a else EndInfNode a
--     absorb' c a@(InfNodes {}) dc@(Leaf _)  = a
--     absorb' c a@(Node positionA pos_childA neg_childA) dc@(EndInfNode _)  = --infere Dc node
--         let pos_result = absorb @a c pos_childA dc
--             neg_result = absorb @a c neg_childA dc
--         in applyElimRule @a (Node positionA pos_result neg_result)
--     absorb' c a@(EndInfNode a') dc@(EndInfNode dc') = if a' == dc' then false @a else a
--     absorb' c a@(Node positionA pos_childA neg_childA) dc@(Leaf _) =
--         let pos_result = absorb @a c pos_childA dc
--             neg_result = absorb @a c neg_childA dc
--         in applyElimRule @a (Node positionA pos_result neg_result)

--     absorb' c a@(Node positionA pos_childA neg_childA)  dc@(Node positionD pos_childD neg_childD)
--         -- No mismatch
--         | positionA == positionD =
--             let pos_result = absorb @a c pos_childA pos_childD
--                 neg_result = absorb @a c neg_childA neg_childD
--             in applyElimRule @a (Node positionA pos_result neg_result)

--         -- Mismatch
--         | positionA > positionD = inferNodeA @a (absorb @a) c a dc
--         | positionA < positionD =
--             let pos_result = absorb @a c pos_childA dc
--                 neg_result = absorb @a c neg_childA dc
--             in applyElimRule @a (Node positionA pos_result neg_result)

--     absorb' c a@(InfNodes {}) b@(InfNodes {}) = case to_constr @a of
--         Dc -> error "absorb with a dc as first argument should not be possible"
--         Neg1 -> f True ((to_constr @a, Absorb) : c)
--         Neg0 -> f False ((to_constr @a, Absorb) : c)
--         Pos1 -> f True ((to_constr @a, Absorb) : c)
--         Pos0 -> f False ((to_constr @a, Absorb) : c)
--         where
--                 f = \x y -> applyInfElimRule @a $ t_and_rMain x y a b

--     absorb' c a@(InfNodes positionA dcA n1A n0A p1A p0A) dc@(Node positionD pos_childD neg_childD)
--         | positionA > positionD = inferNodeA @a (absorb @a) c a dc
--         | positionA < positionD = case to_constr @a of
--             Dc -> error "absorb with a dc as first argument should not be possible"
--             Neg1 -> f True ((Dc, Absorb) : c)
--             Neg0 -> f False ((Dc, Absorb) : c)
--             Pos1 -> f True ((Dc, Absorb) : c)
--             Pos0 -> f False ((Dc, Absorb) : c)
--         | otherwise = undefined
--             where
--                 f = \x y -> applyInfElimRule @Dc $ t_and_rInferB_ @Dc x y  a dc
--     -- add posB == posA, then we consider node to be AllNegs -> [1]
--     absorb' c a@(Node positionA pos_childA neg_childA) dc@(InfNodes positionD dcA n1A n0A p1A p0A)
--         | positionA > positionD =
--             let f = \x y -> applyInfElimRule @a $ t_and_rInferA_ @a x y a dc
--             in case to_constr @a of
--                 Dc -> error "absorb with a dc as first argument should not be possible"
--                 Neg1 -> f True ((to_constr @a, Absorb) : c)
--                 Neg0 -> f False ((to_constr @a, Absorb) : c)
--                 Pos1 -> f True ((to_constr @a, Absorb) : c)
--                 Pos0 -> f False ((to_constr @a, Absorb) : c)
--         | positionA < positionD =
--             let pos_result = absorb @a c a pos_childA
--                 neg_result = absorb @a c a neg_childA
--             in applyElimRule @a (Node positionD pos_result neg_result)
--         | otherwise = undefined
--     absorb' c a@(InfNodes{}) b@(EndInfNode _) = let
--         l = not $ (to_constr @a) `elem` [Neg0, Pos0]
--         in applyInfElimRule @Dc $ t_and_rInferB_ @Dc l ((Dc, Absorb) : c) a b -- intersectionInferB ((to_constr @a, Absorb):c) a b
--     absorb' c a@(EndInfNode _) b@(InfNodes{}) = let
--         l = not $ (to_constr @a) `elem` [Neg0, Pos0]
--         in applyInfElimRule @a $ t_and_rInferA_ @a l ((to_constr @a, Absorb) : c) a b -- intersectionInferB ((to_constr @a, Absorb):c) a b
--     absorb' c a b = error $ "absorb , " ++ "a = " ++ show a ++ "b = " ++ show b


--     -- use inferA because maybe we need to pop back to top level where absorb or remove_complement is being applied

--     traverse_and_return' l c a'@(Leaf a) b'@(Leaf b)
--         | absorb_or_remove c = if a == b && b == l then Leaf $ not l else b'
--         | (a /= b) && b == l = Leaf $ not l
--         | otherwise = b'
--     traverse_and_return' l c a@(Leaf _) b@(InfNodes {})
--         | absorb_or_remove c = if a == b && b == Leaf l then Leaf $ not l else applyInfElimRule @a $ t_and_rInferA_ @a l c a b
--         | (a /= b) && b == Leaf l = Leaf $ not l
--         | otherwise = applyInfElimRule @a $ t_and_rInferA_ @a l c a b
--     traverse_and_return' l c a@(InfNodes {}) b@(Leaf _)
--         | absorb_or_remove c = if a == b && b == Leaf l then Leaf $ not l else applyInfElimRule @a $ t_and_rInferA_ @a l c a b
--         | (a /= b) && b == Leaf l = Leaf $ not l
--         | otherwise = applyInfElimRule @a $ t_and_rInferA_ @a l c a b
--     -- for when no Leaf is changed we return a, thus a should be of the right type
--     -- test carefully
--     -- first check whether the flip needs to happen before applying infelimrule
--     traverse_and_return' l c@(Context{func_context = (f:fs)}) a@(Leaf _) (EndInfNode b')  = if a == b' && b' == Leaf l then Leaf $ not l else applyInfElimRule @a $ t_and_r_arg f l c{func_context = fs} a b' -- what if EndInfNode EndInfnode (a == b); should not be possible since we require all DD's to be Endinfnode reduced.
--     traverse_and_return' l c@(Context{func_context = (f:fs)}) (EndInfNode a') b@(Leaf _)  = if a' == b && b == Leaf l then Leaf $ not l else applyInfElimRule @a $ t_and_r_arg f l c{func_context = fs} a' b
--     -- go back one recursively if on the context there is a t_and_r or absorb call
--     traverse_and_return' l c@(Context{func_context = (f:fs)}) a@(EndInfNode a') b@(EndInfNode b') = if a' == b' && b' == Leaf l then Leaf $ not l else applyInfElimRule @a $ t_and_r_arg f l c{func_context = fs} a' b'
--     traverse_and_return' l [] _ _ = error "should not have an empty context, check if top layer has DC context given along"

--     traverse_and_return' l c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
--         -- No mismatch
--         | positionA == positionB =
--             let pos_result = traverse_and_return @a l c pos_childA pos_childB
--                 neg_result = traverse_and_return @a l c neg_childA neg_childB
--             in applyElimRule @a (Node positionA pos_result neg_result)
--         -- Mismatch
--         | positionA > positionB = inferNodeA @a (traverse_and_return @a l) c a b
--         | positionA < positionB = inferNodeB @a (traverse_and_return @a l) c a b
--     traverse_and_return' l c a@(EndInfNode _) b@(Node positionD pos_childD neg_childD)  =  inferNodeA @a (traverse_and_return @a l) c a b
--     traverse_and_return' l c a@(Node positionD pos_childD neg_childD) b@(EndInfNode _)  =  inferNodeB @a (traverse_and_return @a l) c a b

--     traverse_and_return' l c a@(Node positionA pos_childA neg_childA) b@(Leaf _) = inferNodeB @a (traverse_and_return @a l) c a b
--     traverse_and_return' l c a@(Leaf _) b@(Node positionB pos_childB neg_childB) = inferNodeA @a (traverse_and_return @a l) c a b

--     traverse_and_return' l c a@(InfNodes positionA dcA n1A n0A p1A p0A) b@(InfNodes positionB dcB n1B n0B p1B p0B)
--         -- test t_and_rMain here (look what a clean union call does different from unionMain)
--         | positionA == positionB = applyInfElimRule @a $ t_and_rMain l ((to_constr @a, T_and_r):c) a b
--         | positionA > positionB = applyInfElimRule @a $ t_and_rInferA_ @a l c a b
--         | positionB > positionA = applyInfElimRule @a $ t_and_rInferB_ @a l c a b
--     traverse_and_return' l c a@(InfNodes positionA dcA n1A n0A p1A p0A) b@(Node positionB pos_childB neg_childB)
--         | positionA < positionB = inferNodeB @a (traverse_and_return @a l) c a b
--         | positionA > positionB = applyInfElimRule @a $ t_and_rInferA_ @a l c a b
--         | positionA == positionB = undefined
--     -- for posB == posA; then we consider node to be AllNegs -> [1]
--     traverse_and_return' l c a@(Node positionA pos_childD neg_childD) b@(InfNodes positionB dcB n1B n0B p1B p0B)
--         | positionA > positionB = inferNodeA @a (traverse_and_return @a l) c a b
--         | positionA < positionB = applyInfElimRule @a $ t_and_rInferB_ @a l c a b
--         | positionA == positionB = undefined

--     -- add infnode to b and perform traverse and return. No need to flip the result, that gets done/determined at the leaf level
--     -- we have to take along the leaf we are checking with, thus if we are in finite land; we only have to check for the finite other types where we can expect to see the leaf we are checking weith
--     traverse_and_return' l c a@(InfNodes{}) b@(EndInfNode _) = applyInfElimRule @a $ t_and_rInferB_ @a l c a b
--     traverse_and_return' l c a@(EndInfNode _) b@(InfNodes{}) = applyInfElimRule @a $ t_and_rInferA_ @a l c a b
--     traverse_and_return' l c a b = error $ "traverse_and_return , " ++ "a = " ++ show a ++ "b = " ++ show b

absorb_or_remove :: Context -> Bool
absorb_or_remove c@(Context{func_context = ((_, f) : cs)}) = if f == Absorb then True else if f == Remove then False else absorb_or_remove c{func_context = cs}
absorb_or_remove c@(Context{func_context = []}) = error "no absorb or remove in current stack"
-- -- holds the debug and class specific functions
class DdF4 a where
--     to_constr :: Inf
    applyElimRule :: Dd -> Dd
    intersectionLocal :: Context -> Dd -> Dd -> Dd
--     unionLocal :: Context -> Dd -> Dd -> Dd
--     mixedIntersection :: Context -> Dd -> Dd -> Dd
--     mixedUnion :: Context -> Dd -> Dd -> Dd
--     absorb :: Context -> Dd -> Dd -> Dd
--     traverse_and_return :: Bool -> Context -> Dd -> Dd -> Dd
--     remove_outercomplement_from :: Context -> Dd -> Dd -> Dd

    false :: Dd
    true :: Dd
--     negate_maybe :: Dd -> Dd
--     applyInfElimRule :: Dd -> Dd
--     intersectionInferA_ :: Context -> Dd -> Dd -> Dd
--     intersectionInferB_ :: Context -> Dd -> Dd -> Dd
--     unionInferA_ :: Context -> Dd -> Dd -> Dd
--     unionInferB_ :: Context -> Dd -> Dd -> Dd
--     t_and_rInferA_ :: Bool -> Context -> Dd -> Dd -> Dd
--     t_and_rInferB_ :: Bool -> Context -> Dd -> Dd -> Dd
--     inferNodeA :: (Context -> Dd -> Dd -> Dd) -> Context -> Dd -> Dd -> Dd
--     inferNodeA_opposite :: (Context -> Dd -> Dd -> Dd) -> Context -> Dd -> Dd -> Dd
--     inferNodeB :: (Context -> Dd -> Dd -> Dd) -> Context -> Dd -> Dd -> Dd


instance DdF4 Dc where
--     to_constr = Dc
--     applyInfElimRule (Leaf b) = Leaf b
--     applyInfElimRule d = case applyElimRule @Dc d of
--         x@(InfNodes {}) -> EndInfNode x
--         x -> x
--     applyElimRule d@(Node _ posC negC) = if posC == negC then posC else d
--     applyElimRule d@(InfNodes pos dcR n1R n0R p1R p0R) =
--         if (n1R, n0R, p1R, p0R) == (Leaf False, Leaf True, Leaf False, Leaf True) then
--                         (case dcR of
--                             (EndInfNode x) -> x
--                             0 -> Leaf False
--                             1 -> Leaf True
--                             _ -> InfNodes pos dcR n1R n0R p1R p0R)
--                         else InfNodes pos dcR n1R n0R p1R p0R
--     applyElimRule (Leaf b) = Leaf b
--     applyElimRule d = d-- (EndInfNode _) = error "cannot end on end infnodlet c = lastN' (len positionA) c ine"
    false = EndInfNode $ EndInfNode $ Leaf False
    true = EndInfNode $ auto_insert c ( hash $ EndInfNode $ Leaf True)
--     negate_maybe d = d
--     intersectionInferB_ c a@(InfNodes positionA _ _ _ _ _) b = intersectionInferB ((Dc, Inter):c) a b
--     intersectionInferB_ _ _ _ = undefined
--     intersectionInferA_ c a b@(InfNodes positionB _ _ _ _ _) = intersectionInferA ((Dc, Inter):c) a b
--     intersectionInferA_ _ _ _ = undefined
--     unionInferB_ c a@(InfNodes positionA _ _ _ _ _) b = unionInferB ((Dc, Union):c) a b
--     unionInferB_ _ _ _ = undefined
--     unionInferA_ c a b@(InfNodes positionB _ _ _ _ _) = unionInferA ((Dc, Union):c) a b
--     unionInferA_ _ _ _ = undefined
--     t_and_rInferA_ l c a b@(InfNodes positionB _ _ _ _ _) = t_and_rInferA l ((Dc, T_and_r):c) a b
--     t_and_rInferA_ l _ _ _ = undefined
--     t_and_rInferB_ l c a b@(InfNodes positionA _ _ _ _ _) = t_and_rInferB l ((Dc, T_and_r):c) a b
--     t_and_rInferB_ l _ _ _ = undefined
--     intersectionLocal c a b = intersectionLocal' @Dc c a b
--         `debug2` ("intersectionLocal Dc: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b ++ " = \n " ++ show (intersectionLocal' @Dc c a b))
--     -- comparing nodes, allowed mis-matches based on each inference rule
--     unionLocal c a b =  unionLocal' @Dc c a b
--         `debug2` ("unionLocal Dc: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

--     traverse_and_return c a b =  traverse_and_return' @Dc c a b
--         `debug2` ("traverse_and_return dc: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)


--     mixedIntersection c a b = error "mixedintersection only with finite kinds"
--     mixedUnion c a b = error "mixedintersection only with finite kinds"
--     absorb = error "mixedintersection only with finite kinds"
--     remove_outercomplement_from = error ""

--     inferNodeA f c a b@(Node positionB pos_childB neg_childB) =
--         let pos_result = f c a pos_childB
--             neg_result = f c a neg_childB
--         in applyElimRule @Dc (Node positionB pos_result neg_result)
--         `debug2` ("infernodeA dc ; " ++ (show $ applyElimRule @Dc (Node positionB pos_result neg_result)))
--     inferNodeA _ c a b = error ("inferNode : " ++ show c ++ ", " ++ show a ++ ", " ++ show b)

--     inferNodeA_opposite = inferNodeA @Dc

--     inferNodeB f c a@(Node positionA pos_childA neg_childA) b =
--         let pos_result = f c pos_childA b
--             neg_result = f c neg_childA b
--         in applyElimRule @Dc (Node positionA pos_result neg_result)
--         `debug2` ("infernodeB dc ; " ++ (show $ applyElimRule @Dc (Node positionA pos_result neg_result)))
--     inferNodeB f c a b = undefined `debug2` ("infernodeB dc ; " ++ show c ++ "\n \t a: " ++ show a ++ " \n \t b: " ++ show b)


instance DdF4 Neg1 where
--     to_constr = Neg1
--     applyInfElimRule (Leaf b) = Leaf b
--     applyInfElimRule d = EndInfNode $ applyElimRule @Neg1 d

--     applyElimRule d@(Node _ posC negC) = ( if posC == 0 then negC else d )
--     applyElimRule d@(InfNodes pos dcR n1R n0R p1R p0R) =
--         if (dcR, n0R, p1R, p0R) == (Leaf False, Leaf True, Leaf False, Leaf True) then
--                         (case n1R of
--                             (EndInfNode x) -> x
--                             0 -> Leaf False
--                             1 -> Leaf True
--                             _ -> InfNodes pos dcR n1R n0R p1R p0R)
--                         else InfNodes pos dcR n1R n0R p1R p0R
--     applyElimRule d = d

    false = Leaf False
    true = Leaf True
--     negate_maybe d = d

--     intersectionInferB_ c a@(InfNodes positionA _ _ _ _ _) b = intersectionInferB ((Neg1, Inter):c) a b
--     intersectionInferB_ _ _ _ = undefined
--     intersectionInferA_ c a b@(InfNodes positionB _ _ _ _ _) = intersectionInferA ((Neg1, Inter):c) a b
--     intersectionInferA_ _ _ _ = undefined
--     unionInferB_ c a@(InfNodes positionA _ _ _ _ _) b = unionInferB ((Neg1, Union):c) a b
--     unionInferB_ _ _ _ = undefined
--     unionInferA_ c a b@(InfNodes positionB _ _ _ _ _) = unionInferA ((Neg1, Union):c) a b
--     unionInferA_ _ _ _ = undefined
--     t_and_rInferA_ l c a b@(InfNodes positionB _ _ _ _ _) = t_and_rInferA l ((Neg1, T_and_r):c) a b
--     t_and_rInferA_ l _ _ _ = undefined
--     t_and_rInferB_ l c a b@(InfNodes positionA _ _ _ _ _) = t_and_rInferB l ((Neg1, T_and_r):c) a b
--     t_and_rInferB_ l _ _ _ = undefined

--     intersectionLocal c a b = intersectionLocal' @Neg1 c a b
--         `debug` ("intersectionLocal neg1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

--     unionLocal c a b = unionLocal' @Neg1 c a b
--         `debug` ("unionLocal neg1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b ++ " = " ++ (show $ unionLocal' @Neg1 c a b))

--     traverse_and_return c a b =  traverse_and_return' @Neg1 c a b
--         `debug` ("traverse_and_return neg1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

--     absorb c a b = absorb' @Neg1 c a b  `debug2` ("absorb neg1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

--     inferNodeA f c a  b@(Node positionB pos_childB neg_childB) =
--         applyElimRule @Neg1 $ f c (Node positionB 0 a) b
--     inferNodeA f c a b = undefined `debug` ("inferNodeA ; c= " ++ (show c) ++ " a= " ++ (show a) ++ " b= " ++ (show b))

--     inferNodeA_opposite = inferNodeA @Neg0

--     inferNodeB f c a@(Node positionA pos_childA neg_childA) b =
--         applyElimRule @Neg1 $ f c a (Node positionA 0 b)
--     inferNodeB _ _ _ _ = undefined

--     mixedIntersection c a b = mixedIntersection' @Neg1 c a b
--         `debug2` ("mixedIntersection neg1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

--     mixedUnion c a b = mixedUnion' @Neg1 c a b
--         `debug2` ("mixedUnion neg1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

--     remove_outercomplement_from c a b =  remove_outercomplement_from' @Neg1 c a b
--         `debug2` ("remove_f0s1_from_f1s1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)


instance DdF4 Neg0 where
--     to_constr = Neg0
--     applyInfElimRule (Leaf b) = Leaf b
--     applyInfElimRule d = EndInfNode $ applyElimRule @Neg0 d


--     applyElimRule d@(Node _ posC negC) = if posC == 1 then negC else d
--     applyElimRule d@(InfNodes pos dcR n1R n0R p1R p0R) =
--         if (n1R, dcR, p1R, p0R) == (Leaf False, Leaf True, Leaf False, Leaf True) then
--             (case n0R of
--                 (EndInfNode x) -> x
--                 0 -> Leaf False
--                 1 -> Leaf True
--                 _ -> InfNodes pos dcR n1R n0R p1R p0R)
--             else InfNodes pos dcR n1R n0R p1R p0R
--     applyElimRule d = d

    false = Leaf True
    true = Leaf False
--     negate_maybe d = negation d

--     intersectionInferB_ c a@(InfNodes positionA _ _ _ _ _) b = intersectionInferB ((Neg0, Inter):c) a b
--     intersectionInferB_ _ _ _ = undefined
--     intersectionInferA_ c a b@(InfNodes positionB _ _ _ _ _) = intersectionInferA ((Neg0, Inter):c) a b
--     intersectionInferA_ _ _ _ = undefined
--     unionInferB_ c a@(InfNodes positionA _ _ _ _ _) b = unionInferB ((Neg0, Union):c) a b
--     unionInferB_ _ _ _ = undefined
--     unionInferA_ c a b@(InfNodes positionB _ _ _ _ _) = unionInferA ((Neg0, Union):c) a b
--     unionInferA_ _ _ _ = undefined
--     t_and_rInferA_ l c a b@(InfNodes positionB _ _ _ _ _) = t_and_rInferA l ((Neg0, T_and_r):c) a b
--     t_and_rInferA_ l _ _ _ = undefined
--     t_and_rInferB_ l c a b@(InfNodes positionA _ _ _ _ _) = t_and_rInferB l ((Neg0, T_and_r):c) a b
--     t_and_rInferB_ l _ _ _ = undefined

--         -- Leaf and node
--     unionLocal c a b = unionLocal' @Neg0 c a b
--         `debug2` ("unionLocal neg0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b ++ " = " ++ show (unionLocal' @Neg0 c a b))


--     intersectionLocal c a b = intersectionLocal' @Neg0 c a b
--         `debug2` ("intersectionLocal neg0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b ++ " = " ++ show (intersectionLocal' @Neg0 c a b))

--     traverse_and_return c a b =  traverse_and_return' @Neg0 c a b
--         `debug` ("traverse_and_return neg0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)
--     absorb c a b =  absorb' @Neg0 c a b
--         `debug` ("absorb neg0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

--     inferNodeA f c a  b@(Node positionB pos_childB neg_childB) =
--         applyElimRule @Neg0 $ f c (Node positionB 1 a) b
--     inferNodeA _ _ _ _ = undefined
--     inferNodeA_opposite = inferNodeA @Neg1
--     inferNodeB f c a@(Node positionA pos_childA neg_childA) b =
--         applyElimRule @Neg0 $ f c a (Node positionA 1 b)
--     inferNodeB _ _ _ _ = undefined


--     mixedIntersection c a b = mixedIntersection' @Neg0 c a b
--         `debug2` ("mixedIntersection neg0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

--     mixedUnion c a b = mixedUnion' @Neg0 c a b
--         `debug2` ("mixedUnion neg0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b ++ " = " ++ show (mixedUnion' @Neg0 c a b))


--     remove_outercomplement_from c a b =  remove_outercomplement_from' @Neg0 c a b
--         `debug2` ("remove_f0s1_from_f1s1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)


instance DdF4 Pos1 where
--     to_constr = Pos1
--     applyInfElimRule (Leaf b) = Leaf b
--     applyInfElimRule d = EndInfNode $ applyElimRule @Pos1 d

--     applyElimRule d@(Node _ posC negC) = if negC == 0 then posC else d
--     applyElimRule d@(InfNodes pos dcR n1R n0R p1R p0R) =
--         if (n1R, n0R, dcR, p0R) == (Leaf False, Leaf True, Leaf False, Leaf True) then
--             (case p1R of
--                 (EndInfNode x) -> x
--                 0 -> Leaf False
--                 1 -> Leaf True
--                 _ -> InfNodes pos dcR n1R n0R p1R p0R)
--             else InfNodes pos dcR n1R n0R p1R p0R
--     applyElimRule d = d

    false = Leaf False
    true = Leaf True
--     negate_maybe d = d


--     intersectionInferB_ c a@(InfNodes positionA _ _ _ _ _) b = intersectionInferB ((Pos1, Inter):c) a b
--     intersectionInferB_ _ _ _ = undefined
--     intersectionInferA_ c a b@(InfNodes positionB _ _ _ _ _) = intersectionInferA ((Pos1, Inter):c) a b
--     intersectionInferA_ _ _ _ = undefined
--     unionInferB_ c a@(InfNodes positionA _ _ _ _ _) b = unionInferB ((Pos1, Union):c) a b
--     unionInferB_ _ _ _ = undefined
--     unionInferA_ c a b@(InfNodes positionB _ _ _ _ _) = unionInferA ((Pos1, Union):c) a b
--     unionInferA_ _ _ _ = undefined
--     t_and_rInferA_ l c a b@(InfNodes positionB _ _ _ _ _) = t_and_rInferA l ((Pos1, T_and_r):c) a b
--     t_and_rInferA_ l _ _ _ = undefined
--     t_and_rInferB_ l c a b@(InfNodes positionA _ _ _ _ _) = t_and_rInferB l ((Pos1, T_and_r):c) a b
--     t_and_rInferB_ l _ _ _ = undefined

--     intersectionLocal c a b = intersectionLocal' @Pos1 c a b
--         `debug` ("intersectionLocal pos1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

--     unionLocal c a b = unionLocal' @Pos1 c a b
--         `debug2` ("unionLocal pos1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

--     traverse_and_return c a b =  traverse_and_return' @Pos1 c a b
--         `debug` ("traverse_and_return pos1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

--     absorb c a b = absorb' @Pos1 c a b
--         `debug2` ("absorb pos1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

--     inferNodeA f c a b@(Node positionB pos_childB neg_childB) =
--         applyElimRule @Pos1 $ f c (Node positionB a 0) b
--     inferNodeA _ c a b = error ("pos1" ++ show c ++ show a ++ show b )
--     inferNodeA_opposite = inferNodeA @Pos0
--     inferNodeB f c a@(Node positionA pos_childA neg_childA) b =
--         applyElimRule @Pos1 $ f c a (Node positionA b 0)
--     inferNodeB _ c a b = error ("infernodeB: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

--     mixedIntersection c a b = mixedIntersection' @Pos1 c a b
--         `debug2` ("mixedIntersection pos1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

--     mixedUnion c a b = mixedUnion' @Pos1 c a b
--         `debug2` ("mixedUnion pos1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

--     remove_outercomplement_from c a b =  remove_outercomplement_from' @Pos1 c a b
--         `debug2` ("remove_f0s1_from_f1s1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)



instance DdF4 Pos0 where
--     to_constr = Pos0
--     applyInfElimRule (Leaf b) = Leaf b
--     applyInfElimRule d = EndInfNode $ applyElimRule @Pos0 d

--     applyElimRule d@(Node _ posC negC) = if negC == 1 then posC else d
--     applyElimRule d@(InfNodes pos dcR n1R n0R p1R p0R) =
--         if (n1R, n0R, p1R, dcR) == (Leaf False, Leaf True, Leaf False, Leaf True) then
--             (case p0R of
--                 (EndInfNode x) -> x
--                 0 -> Leaf False
--                 1 -> Leaf True
--                 _ -> InfNodes pos dcR n1R n0R p1R p0R)
--             else InfNodes pos dcR n1R n0R p1R p0R
--     applyElimRule d = d

    false = Leaf True
    true = Leaf False
--     negate_maybe d = negation d

--     intersectionInferB_ c a@(InfNodes positionA _ _ _ _ _) b = intersectionInferB ((Pos0, Inter):c) a b
--     intersectionInferB_ _ _ _ = undefined
--     intersectionInferA_ c a b@(InfNodes positionB _ _ _ _ _) = intersectionInferA ((Pos0, Inter):c) a b
--     intersectionInferA_ _ _ _ = undefined
--     unionInferB_ c a@(InfNodes positionA _ _ _ _ _) b = unionInferB ((Pos0, Union):c) a b
--     unionInferB_ _ _ _ = undefined
--     unionInferA_ c a b@(InfNodes positionB _ _ _ _ _) = unionInferA ((Pos0, Union):c) a b
--     unionInferA_ _ _ _ = undefined
--     t_and_rInferA_ l c a b@(InfNodes positionB _ _ _ _ _) = t_and_rInferA l ((Pos0, T_and_r):c) a b
--     t_and_rInferA_ l _ _ _ = undefined
--     t_and_rInferB_ l c a b@(InfNodes positionA _ _ _ _ _) = t_and_rInferB l ((Pos0, T_and_r):c) a b
--     t_and_rInferB_ l _ _ _ = undefined

--     -- Leaf and node
--     unionLocal c a b = unionLocal' @Pos0 c a b  `debug2` ("unionLocal pos0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

--     --unionLocal c a@(InfNodes positionA dcA n1A n0A p1A p0A) 1 = union @False c a (inferInfNode c True a)
--     --unionLocal c 1 b@(InfNodes positionB dcB n1B n0B p1B p0B) = union @False c (inferInfNode c True b) b
--     intersectionLocal c a b = intersectionLocal' @Pos0 c a b
--         `debug2` ("intersectionLocal pos0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

--     absorb c a b = absorb' @Pos0 c a b  `debug2` ("absorb pos0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

--     inferNodeA f c a  b@(Node positionB pos_childB neg_childB) =
--         applyElimRule @Pos0 $ f c (Node positionB a 1) b
--     inferNodeA _ c a b = error (show c ++ " , a = " ++ show a ++ " , b = " ++ show b)
--     inferNodeA_opposite = inferNodeA @Pos1
--     inferNodeB f c a@(Node positionA pos_childA neg_childA)  b =
--         applyElimRule @Pos0 $ f c a (Node positionA b 1)
--     inferNodeB _ c a b= error (show c ++ " , a = " ++ show a ++ " , b = " ++ show b)

--     mixedIntersection c a b = mixedIntersection' @Pos0 c a b
--         `debug2` ("mixedIntersection pos0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

--     mixedUnion c a b = mixedUnion' @Pos0 c a b
--         `debug2` ("mixedUnion pos0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

--     traverse_and_return c a b =  traverse_and_return' @Pos0 c a b
--         `debug` ("traverse_and_return pos0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

--     remove_outercomplement_from c a b =  remove_outercomplement_from' @Pos0 c a b
--         `debug2` ("remove_f0s1_from_f1s1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)



-- -- tandr simple functions
-- t_and_rInferA :: Bool -> [(Inf, FType)] -> Dd -> Dd -> Dd
-- t_and_rInferA _ [] _ _ = error "empty context"
-- t_and_rInferA _ _ _ (Leaf _) = error "Leaf in A"
-- t_and_rInferA _ _ _ (EndInfNode _) = error "EndNode in A"
-- t_and_rInferA _ _ _ (Node _ _ _) = error "Node in A"
-- t_and_rInferA l c a b =  t_and_rInferA' l c a b `debug5` ("t_and_rInferA" ++ show l ++ ": " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b ++ " = " ++ show (t_and_rInferA' l c a b ))
-- t_and_rInferB' :: Bool -> [(Inf, FType)] -> Dd -> Dd -> Dd
-- t_and_rInferB' l c@((inf, _) : _) a@(InfNodes positionA dcA n1A n0A p1A p0A) b' = let b = EndInfNode b' in
--     (if l then
--         (case inf of
--                 Dc -> error "inferring an infnode for a Dc context should not happen.. i think"
--                     -- dcR = traverse_and_return @Dc l c dcA b --inter
--                     -- n1R = traverse_and_return @Neg1 l c n1A b -- union
--                     -- n0R = traverse_and_return @Neg0 l c n0A b
--                     -- p1R = traverse_and_return @Pos1 l c p1A b
--                     -- p0R = traverse_and_return @Pos0 l c p0A b
--                     -- in applyElimRule @Dc (InfNodes positionA dcR n1R n0R p1R p0R)
--                 Neg1 -> let -- replace all the B stuf with (dc: 0, neg1: b, neg0: 1, pos1: 0, pos0: 1)
--                     n1R = traverse_and_return @Neg1 l c n1A b --inter dcA
--                     in InfNodes positionA dcA n1R n0A p1A p0A
--                 Neg0 -> let -- replace all the B stuf with (dc: 1, neg1: 0, neg0: b, pos1: 0, pos0: 1)
--                     n0R = traverse_and_return @Neg0 l c n0A b
--                     in InfNodes positionA dcA n1A n0R p1A p0A
--                 Pos1 -> let -- replace all the B stuf with (dc: 0, neg1: 0, neg0: 1, pos1: b, pos0: 1)
--                     -- for absorb dcA has to be checked with leaf false
--                     -- there is something and it can only get less inb the finite types
--                     -- so only local 1 ands 0s get pruned and nothing else changes
--                     -- thus intersection/union/remove_compl and absorb do not have to be performed on the finite types if they are changed
--                     p1R = traverse_and_return @Pos1 l c p1A b
--                     in applyElimRule @Pos1 (InfNodes positionA dcA n1A n0A p1R p0A)
--                 Pos0 -> let -- replace all the B stuf with (dc: 0, neg1: 0, neg0: 1, pos1: 0, pos0: b)
--                     p0R = traverse_and_return @Pos0 l c p0A b
--                     in applyElimRule @Pos0 (InfNodes positionA dcA n1A n0A p1A p0R)
--         ) else (case inf of
--             -- todo how does l change the function?
--                 Dc -> error "inferring an infnode for a Dc context should not happen.. i think"
--                     -- dcR = traverse_and_return @Dc l c dcA b --inter
--                     -- n1R = traverse_and_return @Neg1 l c n1A b -- union
--                     -- n0R = traverse_and_return @Neg0 l c n0A b
--                     -- p1R = traverse_and_return @Pos1 l c p1A b
--                     -- p0R = traverse_and_return @Pos0 l c p0A b
--                     -- in applyElimRule @Dc (InfNodes positionA dcR n1R n0R p1R p0R)
--                 Neg1 -> let -- replace all the B stuf with (dc: 0, neg1: b, neg0: 1, pos1: 0, pos0: 1)
--                     n1R = traverse_and_return @Neg1 l c n1A b --inter dcA
--                     in InfNodes positionA dcA n1R n0A p1A p0A
--                 Neg0 -> let -- replace all the B stuf with (dc: 1, neg1: 0, neg0: b, pos1: 0, pos0: 1)
--                     n0R = traverse_and_return @Neg0 l c n0A b
--                     in InfNodes positionA dcA n1A n0R p1A p0A
--                 Pos1 -> let -- replace all the B stuf with (dc: 0, neg1: 0, neg0: 1, pos1: b, pos0: 1)
--                     -- for absorb dcA has to be checked with leaf false
--                     -- there is something and it can only get less inb the finite types
--                     -- so only local 1 ands 0s get pruned and nothing else changes
--                     -- thus intersection/union/remove_compl and absorb do not have to be performed on the finite types if they are changed
--                     p1R = traverse_and_return @Pos1 l c p1A b
--                     in InfNodes positionA dcA n1A n0A p1R p0A
--                 Pos0 -> let -- replace all the B stuf with (dc: 0, neg1: 0, neg0: 1, pos1: 0, pos0: b)
--                     p0R = traverse_and_return @Pos0 l c p0A b
--                     in InfNodes positionA dcA n1A n0A p1A p0R))

-- t_and_rInferB' l c a b = error (" : " ++ show a ++ show b ++ show c ++ show l)

-- t_and_rInferB :: Bool -> [(Inf, FType)] -> Dd -> Dd -> Dd
-- t_and_rInferB _ [] _ _ = error "empty context"
-- t_and_rInferB _ _ _ (Leaf _) = error "Leaf in A"
-- t_and_rInferB _ _ _ (EndInfNode _) = error "EndNode in A"
-- t_and_rInferB _ _ _ (Node _ _ _) = error "Node in A"
-- t_and_rInferB l c a b =  t_and_rInferB' l c a b `debug4` ("t_and_rInferB" ++ show l ++ ": " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b ++ " = " ++ show (t_and_rInferB' l c a b ))
-- t_and_rInferA' :: Bool -> [(Inf, FType)] -> Dd -> Dd -> Dd
-- t_and_rInferA' l c@((inf, _) : _) a' b@(InfNodes positionB dcB n1B n0B p1B p0B) = let a = EndInfNode a' in let
--             dcR = traverse_and_return @Dc l c dcB a
--             n1R = traverse_and_return @Neg1 l c n1B a
--             n0R = traverse_and_return @Neg0 l c n0B a
--             p1R = traverse_and_return @Pos1 l c p1B a
--             p0R = traverse_and_return @Pos0 l c p0B a
--             in InfNodes positionB dcR n1R n0R p1R p0R
-- t_and_rInferA' _ _ _ _ = undefined

-- t_and_rMain :: Bool -> Context -> Dd -> Dd -> Dd
-- t_and_rMain _ [] _ _ = error "empty context"
-- t_and_rMain _ _ _ (Leaf _) = error "Leaf in A"
-- t_and_rMain _ _ _ (EndInfNode _) = error "EndNode in A"
-- t_and_rMain _ _ _ (Node _ _ _) = error "Node in A"
-- t_and_rMain l c a b =  t_and_rMain' l c a b `debug4` ("t_and_rMain" ++ show l ++ ": " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b ++ " = " ++ show (t_and_rMain' l c a b ))
-- t_and_rMain' :: Bool -> [(Inf, FType)] -> Dd -> Dd -> Dd
-- t_and_rMain' l c@((inf, _) : _) a@(InfNodes positionA dcA n1A n0A p1A p0A) b@(InfNodes positionB dcB n1B n0B p1B p0B) = let
--             dcR = traverse_and_return @Dc l c dcA dcB
--             n1R = traverse_and_return @Neg1 l c n1A n1B
--             n0R = traverse_and_return @Neg0 l c n0A n0B
--             p1R = traverse_and_return @Pos1 l c p1A p1B
--             p0R = traverse_and_return @Pos0 l c p0A p0B
--             in InfNodes positionB dcR n1R n0R p1R p0R
-- t_and_rMain' _ _ _ _ = undefined





debug :: c -> String -> c
debug f s = if debugFlag then trace s f else f

debug3 :: c -> [String] -> c
debug3 f s = trace (format' s) f

debug2 :: a -> String -> a
debug2 f s = if debugFlag2 then trace (colorize "red" s) f else f

debug4 :: a -> String -> a
debug4 f s = if False then trace (colorize "green" s) f else f

debug5 :: a -> String -> a
debug5 f s = if True then trace (colorize "red" s) f else f

format :: String -> String
format s = format' $ words s

format' :: [String] -> String
format' [] = "" -- Base case: return an empty string for an empty list
format' (n : n2 : n3 : ns) =
    colorize "red" n ++ colorize "green" n2 ++ colorize "" n3 ++ format' ns
format' (n : n2 : ns) =
    colorize "red" n ++ colorize "green" n2 ++ format' ns
format' (n : ns) =
    n ++ format' ns


colorize :: String -> String -> String
colorize c s
    | c == "red" = setSGRCode [SetColor Foreground Vivid Red] ++ s ++ setSGRCode [Reset]
    | c == "green" = setSGRCode [SetColor Foreground Vivid Green] ++ s ++ setSGRCode [Reset]
    | otherwise = setSGRCode [SetColor Foreground Vivid Blue] ++ s ++ setSGRCode [Reset]




-- memoize :: (Context -> Dd -> Dd -> Dd) -> Context -> Dd -> Dd -> String -> Int -> Dd
-- memoize