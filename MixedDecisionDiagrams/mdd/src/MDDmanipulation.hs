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

module MDDmanipulation where

import MDD
import Debug.Trace (trace)
import Data.Kind
import System.Console.ANSI
import Data.Data (ConIndex, Constr)

-- todo continue local traversal with children and popped ontext when EndIfnode with EndIfnode is encountered

-- todo finish with Neg0, Pos variants and BDD
-- todo do also the other functions
-- todo shift the contexts: stack current only when diving deeper, not when starting.


-- | !! 2 design decisions, either the finite typ[e recopy the infinite types consequences (which means we need to constantly check for absorbs after each change) or the finite types have the add on


-- create stack also for function calls: only mixed and absorb can be added
-- add additional context types: mixed and absorb

-- | This module describes functions that manipulate MDDs.

-- For the usual Binary Decision Diagrams there are 4 patterns (3 combinations) to account for:
-- Leaf | Leaf
-- Node | Leaf
-- Node | Node

-- For MDDs (with four types of nodes) there are additional patterns (10 combinations total):

-- InfS | InfS
-- InfS | InfE
-- InfE | InfE

-- Leaf | InfS
-- infer Top for InfS
-- Leaf | InfE
-- pop local context,
-- there should be a infEnd for every InfStart thus we loose Leaf inference:

-- Node | InfS
-- Node | InfE
-- continue local node recursion until InfE or InfS is reached

-- Since the structures are fundamental in nature there are many symmetrical functions,
-- and the Infnodes introduce them as a local context during DD manipulation,
-- for which we have defined 2 function classes.
-- one for which Inference rule is used,
-- and a second one for whether output negation should be applied on the result before returning. -- todo This will be removed??
-- It effectively reads all Leaf True as Leaf False and vice versa.
-- It "remebers" whether a call to the function is made from a local F0 context.
-- I chose to let the variant depent on types instead of arguments or tags to reduce memory usage and its reading.
-- letting the compiler figure out which low-level functions should be stringed together *should* be faster than deciding this during run time. (not tested yet)



-- if one of the two zdd paths, to be unioned, does not exist durring recursion with mixedunion, then union the consequences with the missing zdd's bdd counterpart

-- absorb decing choice: make 2, union and intersection, if the 0 and 1 zdds are never constructed to be smalleer and larger (respectively) then we could have only 1 absorb. evenmore so we could combine the absorb with the mixed intersection / mixed union, which is probably best for perfornace
-- the aborb needs not perform an intersection or union after the endleaf (in the consequence), but it needs to treat the leaves differently based on its context

type FuncCtx = [(Inf, FType)]

debugFlag :: Bool
debugFlag = True
debugFlag2 :: Bool
debugFlag2 = False

data FType = Union | Inter | Mixed | Absorb | Remove
    deriving (Eq, Show)


type DdF4 :: Inf -> Constraint
type DdF2 :: Bool -> Constraint
type Dd1 :: Inf -> Constraint


class DdF2 a where
    intersection :: FuncCtx -> Dd -> Dd  -> Dd
    intersection' :: FuncCtx -> Dd -> Dd  -> Dd
    union :: FuncCtx -> Dd -> Dd  -> Dd
    union' :: FuncCtx -> Dd -> Dd  -> Dd



instance DdF2 True where
    intersection c a b = intersection' @True c a b
        `debug` ("intersection: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)
    intersection' c a (Leaf False) = Leaf False
    intersection' c (Leaf False) b = Leaf False
    intersection' c a (Leaf True) = a
    intersection' c (Leaf True) b = b
    intersection' c a b = intersectionMain c a b
    union c a b = union' @True c a b
        `debug` ("union: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)
    union' c a (Leaf True) = Leaf True
    union' c (Leaf True) b = Leaf True
    union' c a (Leaf False) = a
    union' c (Leaf False) b = b
    union' c a b = unionMain c a b




negation :: Dd -> Dd
negation (Node position pos_child neg_child) = Node position (negation pos_child) (negation neg_child)
negation (InfNodes position dc_n n1_n n0_n p1_n p0_n) = InfNodes position (negation dc_n) (negation n0_n) (negation n1_n) (negation p0_n) (negation p1_n)
negation (EndInfNode a) = EndInfNode (negation a)
negation (Leaf b) = Leaf $ not b

isEndInfNode :: Dd -> Bool
isEndInfNode(EndInfNode _) = True
isEndInfNode _ = False

applyElimRule_arg :: Inf -> Dd -> Dd
applyElimRule_arg Dc d = applyElimRule @Dc d
applyElimRule_arg Neg1 d = applyElimRule @Neg1 d
applyElimRule_arg Neg0 d = applyElimRule @Neg0 d
applyElimRule_arg Pos1 d = applyElimRule @Pos1 d
applyElimRule_arg Pos0 d = applyElimRule @Pos0 d


intersectionLocal_arg :: (Inf, FType) -> FuncCtx -> Dd -> Dd -> Dd
intersectionLocal_arg (i,t) [] (Leaf False) b
    | i `elem` [Dc,Neg1,Pos1] = if debugFlag then Leaf False `debug2` (show i ++ "Leaf False") else Leaf False
    | i `elem` [Neg0,Pos0] = if debugFlag then b `debug2` (show i ++ "b") else b
intersectionLocal_arg (i,t) [] (Leaf True) b
    | i `elem` [Dc,Neg1,Pos1] = if debugFlag then b `debug2` (show i ++ "b") else b
    | i `elem` [Neg0,Pos0] = if debugFlag then Leaf True `debug2` (show i ++ "Leaf True") else Leaf True
intersectionLocal_arg (i,t) [] a (Leaf False)
    | i `elem` [Dc,Neg1,Pos1] = if debugFlag then Leaf False `debug2` (show i ++ "Leaf False") else Leaf False
    | i `elem` [Neg0,Pos0] = if debugFlag then a `debug2` (show i ++ "a") else a
intersectionLocal_arg (i,t) [] a (Leaf True)
    | i `elem` [Dc,Neg1,Pos1] = if debugFlag then a `debug2` (show i ++ "a") else a
    | i `elem` [Neg0,Pos0] = if debugFlag then Leaf True `debug2` (show i ++ "Leaf True") else Leaf True

intersectionLocal_arg t c a b = case t of
    (Dc, Inter) -> intersectionLocal @Dc c a b
    (Neg1, Inter) -> intersectionLocal @Neg1 c a b
    (Neg0, Inter) -> intersectionLocal @Neg0 c a b
    (Pos1, Inter) -> intersectionLocal @Pos1 c a b
    (Pos0, Inter) -> intersectionLocal @Pos0 c a b

    (Dc, Union) -> unionLocal @Dc c a b
    (Neg1, Union) -> unionLocal @Neg1 c a b
    (Neg0, Union) -> unionLocal @Neg0 c a b
    (Pos1, Union) -> unionLocal @Pos1 c a b
    (Pos0, Union) -> unionLocal @Pos0 c a b

    (Dc, Mixed) -> mixedIntersection @Dc c a b
    (Neg1, Mixed) -> mixedIntersection @Neg1 c a b
    (Neg0, Mixed) -> mixedIntersection @Neg0 c a b
    (Pos1, Mixed) -> mixedIntersection @Pos1 c a b
    (Pos0, Mixed) -> mixedIntersection @Pos0 c a b

    (Dc, Absorb) -> absorb @Dc c a b
    (Neg1, Absorb) -> absorb @Neg1 c a b
    (Neg0, Absorb) -> absorb @Neg0 c a b
    (Pos1, Absorb) -> absorb @Pos1 c a b
    (Pos0, Absorb) -> absorb @Pos0 c a b

    (_, _) -> error (show t ++ ", " ++ show c ++ ", " ++ show a ++ ", " ++ show b)

unionLocal_arg :: (Inf, FType) -> FuncCtx -> Dd -> Dd -> Dd
unionLocal_arg (i,t) [] (Leaf False) b
    | i `elem` [Dc,Neg1,Pos1] = if debugFlag then b `debug2` (show i ++ "b") else b
    | i `elem` [Neg0,Pos0] = if debugFlag then Leaf False `debug2` (show i ++ "Leaf False") else Leaf False
unionLocal_arg (i,t) [] (Leaf True) b
    | i `elem` [Dc,Neg1,Pos1] = if debugFlag then Leaf True `debug2` (show i ++ "Leaf True") else Leaf True
    | i `elem` [Neg0,Pos0] = if debugFlag then b `debug2` (show i ++ "b") else b
unionLocal_arg (i,t) [] a (Leaf False)
    | i `elem` [Dc,Neg1,Pos1] = if debugFlag then a `debug2` (show i ++ "a") else a
    | i `elem` [Neg0,Pos0] = if debugFlag then Leaf False `debug2` (show i ++ "Leaf False") else Leaf False
unionLocal_arg (i,t) [] a (Leaf True)
    | i `elem` [Dc,Neg1,Pos1] = if debugFlag then Leaf True `debug2` (show i ++ "Leaf True") else Leaf True
    | i `elem` [Neg0,Pos0] = if debugFlag then a `debug2` (show i ++ "a") else a

unionLocal_arg t c a b = case t of
    (Dc, Inter) -> intersectionLocal @Dc c a b
    (Neg1, Inter) -> intersectionLocal @Neg1 c a b
    (Neg0, Inter) -> intersectionLocal @Neg0 c a b
    (Pos1, Inter) -> intersectionLocal @Pos1 c a b
    (Pos0, Inter) -> intersectionLocal @Pos0 c a b

    (Dc, Union) -> unionLocal @Dc c a b
    (Neg1, Union) -> unionLocal @Neg1 c a b
    (Neg0, Union) -> unionLocal @Neg0 c a b
    (Pos1, Union) -> unionLocal @Pos1 c a b
    (Pos0, Union) -> unionLocal @Pos0 c a b

    (Dc, Mixed) -> mixedIntersection @Dc c a b
    (Neg1, Mixed) -> mixedIntersection @Neg1 c a b
    (Neg0, Mixed) -> mixedIntersection @Neg0 c a b
    (Pos1, Mixed) -> mixedIntersection @Pos1 c a b
    (Pos0, Mixed) -> mixedIntersection @Pos0 c a b

    (Dc, Absorb) -> absorb @Dc c a b
    (Neg1, Absorb) -> absorb @Neg1 c a b
    (Neg0, Absorb) -> absorb @Neg0 c a b
    (Pos1, Absorb) -> absorb @Pos1 c a b
    (Pos0, Absorb) -> absorb @Pos0 c a b

    (_, _) -> error (show t ++ ", " ++ show c ++ ", " ++ show a ++ ", " ++ show b)

addInfNode :: Int -> Inf -> Dd -> Dd
addInfNode n inf conseq  =
        case inf of -- only for Dc we need to check the b, since after a hole we interpret the following sub domains in substance (1-set)
            Dc -> InfNodes n (EndInfNode conseq) (Leaf False) (Leaf True) (Leaf False) (Leaf True)
            Neg1 -> InfNodes n (Leaf False) (EndInfNode conseq) (Leaf True) (Leaf False) (Leaf True)
            Neg0 -> InfNodes n (Leaf True) (Leaf False) (EndInfNode conseq) (Leaf False) (Leaf True)
            Pos1 -> InfNodes n (Leaf False) (Leaf False) (Leaf True) (EndInfNode conseq) (Leaf True)
            Pos0 -> InfNodes n (Leaf True) (Leaf False) (Leaf True) (Leaf False) (EndInfNode conseq)

intersectionInferA :: FuncCtx -> Dd -> Dd -> Dd
intersectionInferA [] _ _ = error "empty context"
intersectionInferA _ _ (Leaf _) = error "Leaf in A"
intersectionInferA _ _ (EndInfNode _) = error "EndNode in A"
intersectionInferA _ _ (Node _ _ _) = error "Node in A"

intersectionInferA c a b = intersectionInferA' c a b  `debug` ("intersectionInferA: " ++ show c ++ " ; " ++ show a ++ " ; " ++ show b)
intersectionInferA' :: [(Inf, FType)] -> Dd -> Dd -> Dd
intersectionInferA' c@((inf, _) : _) a' b@(InfNodes positionB dcB n1B n0B p1B p0B) = let a = EndInfNode a' in
    case inf of
        Dc -> let -- replace all the A stuf with (dc: a, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
            dcR = intersectionLocal @Dc c a dcB
            n1R = (if n0B == Leaf True then
                    absorb @Neg1 c (mixedIntersection @Neg1 c n1B a) dcR  else
                    remove_outercomplement_from @Neg1 c n0B (absorb @Neg1 c (mixedIntersection @Neg1 c n1B a) dcR))
            n0R = absorb @Neg0 c (mixedIntersection @Neg0 c n0B dcR) dcR --`debug` ( "inter: " ++ show (mixedIntersection @Neg0 c n0A dcR) ++ "\n n0A: " ++ show n0A  ++ "\n dcR" ++ show dcR)
            p1R = if p0B == Leaf True then
                absorb @Pos1 c (mixedIntersection @Pos1 c p1B a) dcR else
                remove_outercomplement_from @Pos1 c p0B (absorb @Pos1 c (mixedIntersection @Pos1 c p1B a) dcR)
            p0R = absorb @Neg0 c (mixedIntersection @Pos0 c p0B dcR) dcR
            in applyElimRule @Dc $ InfNodes positionB dcR n1R n0R p1R p0R

        Neg1 -> let -- replace all the A stuf with (dc: 0, neg1: a, neg0: 1, pos1: 0, pos0: 1)
            n1R = unionLocal @Neg1 c
                (intersectionLocal @Neg1 c a n1B)
                (if n0B == Leaf True then n1R' else remove_outercomplement_from @Neg1 c n0B n1R')
            n1R' = mixedIntersection @Neg1 c a dcB
            in applyElimRule @Neg1 $ InfNodes positionB (Leaf False) n1R (Leaf True) (Leaf False) (Leaf True)
        Neg0 -> let -- replace all the A stuf with (dc: 1, neg1: 0, neg0: a, pos1: 0, pos0: 1)
            n0R' = intersectionLocal @Neg0 c a n0B
            n0R = mixedIntersection @Neg0 c n0R' dcB
            in applyElimRule @Neg0 $ InfNodes positionB dcB (Leaf False) n0R (Leaf False) (Leaf True)
        Pos1 -> let -- replace all the A stuf with (dc: 0, neg1: 0, neg0: 1, pos1: a, pos0: 1)
            p1R = unionLocal @Pos1 c
                (intersectionLocal @Pos1 c a n1B)
                (if n0B == Leaf True then p1R' else remove_outercomplement_from @Pos1 c n0B p1R')
            p1R' = mixedIntersection @Pos1 c a dcB
            in applyElimRule @Pos1 $ InfNodes positionB (Leaf False) (Leaf False) (Leaf True) p1R (Leaf True)
        Pos0 -> let -- replace all the A stuf with (dc: 1, neg1: 0, neg0: a, pos1: 0, pos0: 1)
            p0R' = intersectionLocal @Pos0 c a p0B
            p0R = mixedIntersection @Pos0 c p0R' dcB
            in applyElimRule @Pos0 $ InfNodes positionB dcB (Leaf False) (Leaf True) (Leaf False) p0R
intersectionInferA' _ _ _ = undefined

intersectionInferB :: FuncCtx -> Dd -> Dd -> Dd
intersectionInferB [] _ _ = error "empty context"
intersectionInferB _ (Leaf _) _ = error "Leaf in A"
intersectionInferB _ (EndInfNode _) _ = error "EndNode in A"
intersectionInferB _ (Node _ _ _) _ = error "Node in A"

intersectionInferB c a b =  intersectionInferB' c a b `debug` ("intersectionInferB: " ++ show c ++ " ; " ++ show a ++ " ; " ++ show b)
intersectionInferB' :: [(Inf, FType)] -> Dd -> Dd -> Dd
intersectionInferB' c@((inf, _) : _) a@(InfNodes positionA dcA n1A n0A p1A p0A)  b' = let b = EndInfNode b' in
    case inf of
        Dc -> let
            dcR = intersectionLocal @Dc c dcA b
            n1R = (if n0A == Leaf True then
                absorb @Neg1 c (mixedIntersection @Neg1 c n1A b) dcR  else
                remove_outercomplement_from @Neg1 c n0A (absorb @Neg1 c (mixedIntersection @Neg1 c n1A b) dcR))
            n0R = absorb @Neg0 c (mixedIntersection @Neg0 c n0A dcR) dcR
            p1R = if p0A == Leaf True then
                absorb @Pos1 c (mixedIntersection @Pos1 c p1A b) dcR else
                remove_outercomplement_from @Pos1 c p0A (absorb @Pos1 c (mixedIntersection @Pos1 c p1A b) dcR)
            p0R = absorb @Pos0 c (mixedIntersection @Pos0 c p0A dcR) dcR `debug` ("\n"++ show (absorb @Pos0 c (mixedIntersection @Pos0 c p0A dcR) dcR) ++ "\n" ++ show (mixedIntersection @Pos0 c p0A dcR)++"\n")
            in (applyElimRule @Dc $ InfNodes positionA dcR n1R n0R p1R p0R) `debug` ("\n\n ------ " ++ show ( InfNodes positionA dcR n1R n0R p1R p0R))

        Neg1 -> let -- replace all the B stuf with (dc: 0, neg1: b, neg0: 1, pos1: 0, pos0: 1)
            n1R = unionLocal @Neg1 c
                (intersectionLocal @Neg1 c n1A b)
                (if n0A == Leaf True then n1R' else remove_outercomplement_from @Neg1 c n0A n1R')
            n1R' = mixedIntersection @Neg1 c b dcA
            in applyElimRule @Neg1 $ InfNodes positionA (Leaf False) n1R (Leaf True) (Leaf False) (Leaf True)
        Neg0 -> let -- replace all the B stuf with (dc: 1, neg1: 0, neg0: b, pos1: 0, pos0: 1)
            n0R' = intersectionLocal @Neg0 c n0A b
            n0R = mixedIntersection @Neg0 c n0R' dcA
            in applyElimRule @Neg0 $ InfNodes positionA dcA (Leaf False) n0R (Leaf False) (Leaf True)
        Pos1 -> let -- replace all the B stuf with (dc: 0, neg1: 0, neg0: 1, pos1: b, pos0: 1)
            p1R = unionLocal @Pos1 c
                (intersectionLocal @Pos1 c n1A b )
                (if p0A == Leaf True then p1R' else remove_outercomplement_from @Pos1 c p0A p1R')
            p1R' = mixedIntersection @Pos1 c dcA b
            in applyElimRule @Pos1 $ InfNodes positionA (Leaf False) (Leaf False) (Leaf True) p1R (Leaf True)
        Pos0 -> let -- replace all the B stuf with (dc: 1, neg1: 0, neg0: b, pos1: 0, pos0: 1)
            p0R' = intersectionLocal @Pos0 c p0A b
            p0R = mixedIntersection @Pos0 c p0R' dcA
            in applyElimRule @Pos0 $ InfNodes positionA dcA (Leaf False) (Leaf True) (Leaf False) p0R


intersectionInferB' _ _ _ = undefined


-- main idea is that

intersectionMain :: FuncCtx -> Dd -> Dd -> Dd
intersectionMain c a b = intersectionMain' c a b  `debug` ("intersectionMain: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)
intersectionMain' :: FuncCtx -> Dd -> Dd -> Dd
intersectionMain'  c a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B)
    | positionA == positionB =  let
        dcR = intersectionLocal @Dc c dcA dcB --`debug` ("intersection A ("++ show positionA ++ ")==B (" ++ show positionB ++ "), with c = " ++ show c)
            `debug` ("\nDcR dcA ^ dcB \t = " ++ show (intersectionLocal @Dc c dcA dcB)
            ++ "\n\t dcA = " ++ show dcA
            ++ "\n\t dcB = " ++ show dcB
            ++ "\n")

        n1R = absorb @Neg1 c (unionLocal @Neg1 c
            (intersectionLocal @Neg1 c n1A n1B) -- overlapping points are by definition not inside the others dc, thus have to be preserved
            (if n0R' == Leaf True then n1R' else remove_outercomplement_from @Neg1 c n0R' n1R')) dcR -- holes absorb points under intersection
            `debug` (("\nn1R \t ((n1A ^ n1B) v (n0R' / n1R')) @ dcR \t = " ++ show (absorb @Neg1 c (unionLocal @Neg1 c
                (intersectionLocal @Neg1 c n1A n1B)
                (if n0R' == Leaf True then n1R' else remove_outercomplement_from @Neg1 c n0R' n1R')) dcR)
            ++ "\n \t ((n1A ^ n1B) v (n0R' / n1R')) = " ++  show (unionLocal @Neg1 c
                (intersectionLocal @Neg1 c n1A n1B)
                (if n0R' == Leaf True then n1R' else remove_outercomplement_from @Neg1 c n0R' n1R')))
            ++ "\n\t (n1A ^ n1B) = " ++ show (intersectionLocal @Neg1 c n1A n1B)
            ++ "\n \t (n0R' / n1R') = " ++ show (if n0R' == Leaf True then n1R' else remove_outercomplement_from @Neg1 c n0R' n1R')
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
            ++ "\n\t n0A = " ++ show(n0A)
            ++ "\n\t n0B = " ++ show(n0B)
            ++ "\n")
        n0R = absorb @Neg0 c (mixedIntersection @Neg0 c n0R' dcR) dcR-- keep the holes that fit inside dcR
            `debug` ("\nn0R \t (n0R' ^ dcR) @ dcR = " ++ show (absorb @Neg0 c (mixedIntersection @Neg0 c n0R' dcR) dcR)
            ++ "\n\t (n0R' ^ dcR) = " ++ show(mixedIntersection @Neg0 c n0R' dcR)
            ++ "\n\t dcR = " ++ show dcR
            ++ "\n")
        -- if the local hole fits inside dcR but the consequence of n0R' does not fit inside the consequenc of dcR it should return n0R' -> Leaf false
        ------------------------------------
        p1R = absorb @Pos1 c (unionLocal @Pos1 c
            (intersectionLocal @Pos1 c p1A p1B)
            (if p0R' == Leaf True then p1R' else remove_outercomplement_from @Pos1 c p0R' p1R')) dcR
            `debug` ("\np1R \t (p1A ^ p1B) v (p1R' / p0R') \t = " ++ show (unionLocal @Pos1 c
                (intersectionLocal @Pos1 c p1A p1B)
                (if p0R' == Leaf True then p1R' else remove_outercomplement_from @Pos1 c p0R' p1R'))
            ++ "\n \t (p1A ^ p1B) = " ++ show (intersectionLocal @Pos1 c p1A p1B)
            ++ "\n \t (p1R' / p0R') = " ++ show (if p0R' == Leaf True then p1R' else remove_outercomplement_from @Pos1 c p0R' p1R')
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
            -- ++ "\n\t (rm p1R p0R')" ++ show (if p1R' == Leaf False then p0R' else remove_f1s0_from_f0s0 c p1R' p0R')
            ++ "\n\t p1A = " ++ show p1A
            ++ "\n\t p1B = " ++ show p1B
            ++ "\n\t dcA = " ++ show dcA
            ++ "\n\t dcB = " ++ show dcB
            ++ "\n")
        p0R' = intersectionLocal @Pos0 c p0A p0B -- local union then intersection
            `debug` ("\np0R' \t p0A ^ p0B = " ++ show (intersectionLocal @Pos0 c p0A p0B)
            ++ "\n\t p0A = " ++ show(p0A)
            ++ "\n\t p0B = " ++ show(p0B)
            ++ "\n")
        p0R = absorb @Pos0 c (mixedIntersection @Pos0 c p0R' dcR) dcR
            `debug` ("\np0R \t (p0R' ^ dcR) @ dcR = " ++ show (absorb @Pos0 c (mixedIntersection @Pos0 c p0R' dcR) dcR)
            ++ "\n\t (p0R' ^ dcR) = " ++ show(mixedIntersection @Pos0 c p0R' dcR)
            ++ "\n\t dcR = " ++ show dcR
            ++ "\n")
        in applyElimRule @Dc $ InfNodes positionA dcR n1R n0R p1R p0R -- todo applyElimRule @a?
    | positionA > positionB = intersectionInferA c a b
    | positionA < positionB = intersectionInferB c a b-- replace all the A stuf with (dc: a, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
intersectionMain' c a b = error (show a ++ ", " ++ show b ++ ", "++ show c)

unionInferA :: FuncCtx -> Dd -> Dd -> Dd
unionInferA [] _ _ = error "empty context"
unionInferA _ _ (Leaf _) = error "Leaf in A"
unionInferA _ _ (EndInfNode _) = error "EndNode in A"
unionInferA _ _ (Node _ _ _) = error "Node in A"

unionInferA c a b =  unionInferA' c a b `debug` ("unionInferA: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)
unionInferA' :: [(Inf, FType)] -> Dd -> Dd -> Dd
unionInferA' c@((inf, _) : _) a' b@(InfNodes positionB dcB n1B n0B p1B p0B) = let a = EndInfNode a' in
    case inf of
        Dc -> let
            dcR = unionLocal @Dc c  a dcB --pass along the consequence of B for both dcA and not dcA
            n1R = absorb @Neg1 c (mixedIntersection @Neg1 c n1B (negation dcR)) dcR -- todo MixedIntersection!

            n0R = let n0R' = mixedIntersection @Neg0 c n0B a in
                if n1B == Leaf False then absorb @Neg0 c n0R' dcR else absorb @Neg0 c (remove_outercomplement_from @Neg0 c n1B n0R') dcR

            p1R = absorb @Pos1 c (mixedIntersection @Pos1 c p1B (negation dcR)) dcR
            p0R = let p0R' = mixedIntersection @Pos0 c p0B a in
                if p1B == Leaf False then absorb @Pos0 c p0R' dcR else absorb @Pos0 c (remove_outercomplement_from @Pos0 c p1B p0R') dcR

            in applyElimRule @Dc (InfNodes positionB dcR n1R n0R p1R p0R)

        Neg1 -> let -- replace all the A stuf with (dc: 0, neg1: a, neg0: 1, pos1: 0, pos0: 1)
            n1R' = unionLocal @Neg1 c a n1B `debug` ("--------- " ++ show n1B)
            n1R = mixedIntersection @Neg1 c n1R' dcB
            in applyElimRule @Neg1 $ InfNodes positionB (Leaf False) n1R (Leaf True) (Leaf False) (Leaf True)
        Neg0 -> let -- replace all the A stuf with (dc: 1, neg1: 0, neg0: a, pos1: 0, pos0: 1)
            n0R = intersectionLocal @Neg0 c
                (unionLocal @Neg0 c a n0B)
                (if n1B == Leaf True then n0R' else remove_outercomplement_from @Neg0 c n1B n0R')
            n0R' = mixedIntersection @Neg0 c a dcB
            in applyElimRule @Neg0 $ InfNodes positionB dcB (Leaf False) n0R (Leaf False) (Leaf True)
        Pos1 -> let -- replace all the A stuf with (dc: 0, neg1: 0, neg0: 1, pos1: a, pos0: 1)
            p1R' = unionLocal @Pos1 c a p1B
            p1R = mixedIntersection @Pos1 c p1R' dcB
            in applyElimRule @Pos1 $ InfNodes positionB (Leaf False) (Leaf False) (Leaf True) p1R (Leaf True)
        Pos0 -> let -- replace all the A stuf with (dc: 1, neg1: 0, neg0: a, pos1: 0, pos0: 1)
            p0R = intersectionLocal @Pos0 c
                (unionLocal @Pos0 c a n0B)
                (if p1B == Leaf True then p0R' else remove_outercomplement_from @Pos0 c p1B p0R')
            p0R' = mixedIntersection @Pos0 c a dcB
            in applyElimRule @Pos0 $ InfNodes positionB dcB (Leaf False) (Leaf True) (Leaf False) p0R
unionInferA' _ _ _ = undefined


unionInferB :: FuncCtx -> Dd -> Dd -> Dd
unionInferB [] _ _ = error "empty context"
unionInferB _ (Leaf _) _ = error "Leaf in A"
unionInferB _ (EndInfNode _) _ = error "EndNode in A"
unionInferB _ (Node _ _ _) _ = error "Node in A"

unionInferB c a b =  unionInferB' c a b  `debug` ("unionInferB: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)
unionInferB' :: [(Inf, FType)] -> Dd -> Dd -> Dd
unionInferB' c@((inf, _) : _) a@(InfNodes positionA dcA n1A n0A p1A p0A) b' = let b = EndInfNode b' in
    case inf of
        Dc -> let
            dcR = unionLocal @Dc c b dcA
                `debug` ("\ndcR \t = " ++ show (unionLocal @Dc c b dcA))
            n1R = absorb @Neg1 c (mixedUnion @Neg1 c n1A dcR) dcR
                `debug` ("\nn1R (n1A ^ dcR) @ dcR \t = " ++ show (absorb @Neg1 c (mixedUnion @Neg1 c n1A dcR) dcR))

            n0R = (let n0R' = mixedIntersection @Neg0 c n0A b in
                if n1A == Leaf False then absorb @Neg0 c  n0R' dcR else  absorb @Neg0 c (remove_outercomplement_from @Neg0 c n1A n0R') dcR)
                `debug` ("n0R' = " ++ show (mixedIntersection @Neg0 c n0A b) ++ "\n")
                `debug` ("n0R' @ dcR = " ++ show (absorb @Neg0 c  (mixedIntersection @Neg0 c n0A b) dcR))

            p1R = absorb @Pos1 c (mixedUnion @Pos1 c p1A dcR) dcR
                `debug` ("\np1R (p1A ^ dcR) @ dcR \t = " ++ show (absorb @Pos1 c (mixedUnion @Pos1 c p1A dcR) dcR))
            p0R = (let p0R' =  mixedIntersection @Pos0 c p0A b in
                if p1A == Leaf False then absorb @Pos0 c p0R' dcR else absorb @Pos0 c (remove_outercomplement_from @Pos0 c p1A p0R') dcR)
                `debug` ("p0R' = " ++ show (mixedIntersection @Pos0 c p0A b) ++ "\n")
                `debug` ("p0R' @ dcR = " ++ show (absorb @Pos0 c (mixedIntersection @Pos0 c p0A b) dcR) ++ "\n")
            in applyElimRule @Dc (InfNodes positionA dcR n1R n0R p1R p0R) `debug` ("result unionInferB" ++ show (InfNodes positionA dcR n1R n0R p1R p0R))
        Neg1 -> let -- replace all the B stuf with (dc: 0, neg1: b, neg0: 1, pos1: 0, pos0: 1)
            n1R' = unionLocal @Neg1 c n1A b
            n1R = mixedIntersection @Neg1 c n1R' dcA
            in applyElimRule @Neg1 $ InfNodes positionA (Leaf False) n1R (Leaf True) (Leaf False) (Leaf True)
        Neg0 -> let -- replace all the B stuf with (dc: 1, neg1: 0, neg0: b, pos1: 0, pos0: 1)
            n0R = intersectionLocal @Neg0 c
                (unionLocal @Neg0 c n0A b)
                (if n1A == Leaf True then n0R' else remove_outercomplement_from @Neg0 c n1A n0R')
                `debug` ("n0R = (n0A U b) ^ (n1A / n0R') = \n " ++ show n0R)
            n0R' = mixedIntersection @Neg0 c b dcA
                `debug` ("n0R' = (b ^ dcA) = \n " ++ show n0R')
            in applyElimRule @Neg0 $ InfNodes positionA dcA (Leaf False) n0R (Leaf False) (Leaf True)
        Pos1 -> let -- replace all the B stuf with (dc: 0, neg1: 0, neg0: 1, pos1: b, pos0: 1)
            p1R' = unionLocal @Pos1 c p1A b
            p1R = mixedIntersection @Pos1 c p1R' dcA
            in applyElimRule @Pos1 $ InfNodes positionA (Leaf False) (Leaf False) (Leaf True) p1R (Leaf True)
        Pos0 -> let -- replace all the B stuf with (dc: 1, neg1: 0, neg0: b, pos1: 0, pos0: 1)
            p0R = intersectionLocal @Pos0 c
                (unionLocal @Pos0 c n0A b )
                (if p1A == Leaf True then p0R' else remove_outercomplement_from @Pos0 c p1A p0R')
                `debug` ("p0R = (p0A U b) ^ (p1A / p0R') = \n " ++ show p0R)
            p0R' = mixedIntersection @Pos0 c b dcA
                `debug` ("p0R' = (b ^ dcA) = \n " ++ show p0R')
            in applyElimRule @Pos0 $ InfNodes positionA dcA (Leaf False) (Leaf True) (Leaf False) p0R
unionInferB' _ _ _ = undefined


unionMain :: FuncCtx -> Dd -> Dd -> Dd
-- exclusive points (0's / holes) under union are filled unless they are present in both A and B (so only an intersection between them needs to be done)
-- inclusive point (1's ) under union are intersected with the opposite infinite subset (dc) before they are added together
unionMain c a b = unionMain' c a b  `debug` ("unionMain: " ++ show c ++ " ; " ++ show a ++ " ; " ++ show b)
unionMain' :: FuncCtx -> Dd -> Dd -> Dd
unionMain'  c a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B)
    | positionA == positionB =  let

        dcR = unionLocal @Dc c  dcA dcB
            `debug` ("\nDcR \t dcA v dcB = " ++ show (unionLocal @Dc c dcA dcB)
            ++ "\n\t dcA = " ++ show dcA
            ++ "\n\t dcB = " ++ show dcB
            ++ "\n")

        n1R = absorb @Neg1 c (mixedUnion @Neg1 c n1R' dcR) dcR
            `debug` ("\nn1R \t (n1R' ^  -. dcR) @ dcR = " ++ show (absorb @Neg1 c (mixedUnion @Neg1 c n1R' dcR) dcR)
            ++ "\n\t (n1R' ^ dcR) = " ++ show (mixedUnion @Neg1 c n1R' dcR)
            ++ "\n\t n1R' = " ++ show n1R'
            ++ "\n\t dcR = " ++ show dcR
            ++ "\n")
        n1R' = unionLocal @Neg1 c n1A n1B
            `debug` ("\nn1R' \t n1A v n1B \b = " ++ show (unionLocal @Neg1 c n1A n1B)
            ++ "\n\t n1A = " ++ show n1A
            ++ "\n\t n1B = " ++ show n1B
            ++ "\n")

        n0R = absorb @Neg0 c (intersectionLocal @Neg0 c
            (unionLocal @Neg0 c n0A n0B)
            (if n1R' == Leaf False then n0R' else remove_outercomplement_from @Neg0 c n1R' n0R')) dcR
            `debug` ("\nn0R \t ((n0A v n0B) ^ (n0R' / n1R')) @ dcR = " ++ show ( absorb @Neg0 c (intersectionLocal @Neg0 c
                    (unionLocal @Neg0 c n0A n0B)
                    (if n1R' == Leaf False then n0R' else remove_outercomplement_from @Neg0 c n1R' n0R')) dcR)
                ++ "\n\t (n0A v n0B) = " ++ show (unionLocal @Neg0 c n0A n0B)
                ++ "\n\t (n0R' / n1R') = " ++ show (if n1R' == Leaf False then n0R' else remove_outercomplement_from @Pos0 c n1R' n0R')
                ++ "\n\t n0A = " ++ show n0A
                ++ "\n\t n0B = " ++ show n0B
                ++ "\n\t n1R' = " ++ show n1R'
                ++ "\n\t n0R' = " ++ show n0R'
                ++ "\n")
        n0R' = intersectionLocal @Neg0 c
            (mixedUnion @Neg0 c n0A dcB) -- remove the holes that do fit in B (unioned away) // note that in consequence this reverts back to to union and is absorbed if consequence of n0A == dcR
            (mixedUnion @Neg0 c n0B dcA) -- remove the holes that do fit in A (unioned away)
            `debug` ("\nn0R' \t (n0A ^ dcB) ^ (n0B ^ dcA) = " ++ show (intersectionLocal @Neg0 c
                (mixedUnion @Neg0 c n0A dcB)
                (mixedUnion @Neg0 c n0B dcA))
                ++ "\n\t (n0A ^ dcB) ^ (n0B ^ dcA) = " ++ show (intersectionLocal @Neg0 c
                                                (mixedUnion @Neg0 c n0A dcB)
                                                (mixedUnion @Neg0 c n0B dcA))
                ++ "\n\t (n0A ^ dcB) = " ++ show (mixedUnion @Neg0 c n0A dcB)
                ++ "\n\t (n0B ^ dcA) = " ++ show (mixedUnion @Neg0 c n0B dcA)
                ++ "\n\t dcR = " ++ show dcR
                ++ "\n\t n0A = " ++ show n0A
                ++ "\n\t n0B = " ++ show n0B
                ++ "\n\t dcB = " ++ show dcB
                ++ "\n\t dcA = " ++ show dcA
                ++ "\n")

        ------------------------------------
        -- n0R = (n0A cap n0B) cup ((n0A cap neg dcB) cap n1B) cup ((n0B cap neg dcA) cap n1A) <-> (n0A cup n0B) cap n1R* cap neg dcR
        p1R = absorb @Pos1 c (mixedUnion @Pos1 c p1R' dcR) dcR
            `debug` ("\np1R \t (p1R' ^ dcR) @ dcR = " ++ show (absorb @Pos1 c (mixedUnion @Pos1 c p1R' dcR) dcR)
            ++ "\n\t p1R' = " ++ show p1R'
            ++ "\n\t dcR = " ++ show dcR
            ++ "\n")
        p1R' = unionLocal @Pos1 c p1A p1B
            `debug` ("\np1R \t p1A v p1B"
            ++ "\n\t p1A = " ++ show p1A
            ++ "\n\t p1B = " ++ show p1B
            ++ "\n")

        p0R = absorb @Pos0 c (intersectionLocal @Pos0 c
            (unionLocal @Pos0 c p0A p0B)
            (if p1R' == Leaf False then p0R' else remove_outercomplement_from @Pos0 c p1R' p0R')) dcR
            `debug` ("\np0R = ((p0A v p0B) ^ (p0R' / p1R')) @dcR \t = " ++ show (absorb @Pos0 c (intersectionLocal @Pos0 c
                (unionLocal @Pos0 c p0A p0B)
                (if p1R' == Leaf False then p0R' else remove_outercomplement_from @Pos0 c p1R' p0R')) dcR)
            ++ "\n\t (p0A v p0B) = " ++ show (unionLocal @Pos0 c p0A p0B)
            ++ "\n\t (p0R' / p1R') = " ++ show (if p1R' == Leaf False then p0R' else remove_outercomplement_from @Pos0 c p1R' p0R')
            ++ "\n\t p0A = " ++ show p0A
            ++ "\n\t p0B = " ++ show p0B
            ++ "\n\t p1R' = " ++ show p1R'
            ++ "\n\t p0R' = " ++ show p0R'
            ++ "\n")
        p0R' = intersectionLocal @Pos0 c
            (mixedUnion @Pos0 c p0A dcB) -- remove the holes that do fit in B: if the consequence of p0A after union is the same as the consequence of dcB, then it is also removed. If the consequence is smaller it is kept.
            (mixedUnion @Pos0 c p0B dcA)
            `debug` ("\np0R' \t  ((p0A ^ dcB) ^ (p0B ^ dcA)) \t = " ++ show (intersectionLocal @Pos0 c
                                                (mixedUnion @Pos0 c p0A dcB)
                                                (mixedUnion @Pos0 c p0B dcA))
                ++ "\n\t (p0A ^ dcB) ^ (p0B ^ dcA) = " ++ show (intersectionLocal @Pos0 c
                                                (mixedUnion @Pos0 c p0A dcB)
                                                (mixedUnion @Pos0 c p0B dcA))
                ++ "\n\t (p0A ^ dcB) = " ++ show (mixedUnion @Pos0 c p0A dcB)
                ++ "\n\t (p0B ^ dcA) = " ++ show (mixedUnion @Pos0 c p0B dcA)
                ++ "\n\t dcR = " ++ show dcR
                ++ "\n\t p0A = " ++ show p0A
                ++ "\n\t p0B = " ++ show p0B
                ++ "\n\t dcB = " ++ show dcB
                ++ "\n\t dcA = " ++ show dcA
                ++ "\n")

        in applyElimRule @Dc (InfNodes positionA dcR n1R n0R p1R p0R)

    | positionA > positionB = unionInferA c a b-- replace all the A stuf with (dc: a, neg1: 0, neg0: 1, pos1: 0, pos0: 1)

    -- c cannot be empty..
    | positionA < positionB = unionInferB c a b-- replace all the A stuf with (dc: a, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
unionMain' c a b = error "no 2 StartInfNode's in intersection main"


-- captures the general patterns for the functions
class Dd1 a where
    intersectionLocal' :: FuncCtx -> Dd -> Dd -> Dd
    mixedIntersection' :: FuncCtx -> Dd -> Dd -> Dd
    mixedUnion' :: FuncCtx -> Dd -> Dd -> Dd
    unionLocal' :: FuncCtx -> Dd -> Dd -> Dd
    remove_outercomplement_from' :: FuncCtx -> Dd -> Dd -> Dd
    absorb' :: FuncCtx -> Dd -> Dd -> Dd

--1:: 1 - 1 = 1
--1:: 1 - 0 = 0
--1:: 0 - 1 = 0
--1:: 0 - 0 = 0

--0:: 1 - 1 = 1
--0:: 1 - 0 = 1
--0:: 0 - 1 = 1
--0:: 0 - 0 = 0

instance (DdF4 a) => Dd1 a where
    remove_outercomplement_from' c a@(Leaf _) b@(Leaf _)
        | a == false @a = false @a  --oposite, thus turn false and true around (becaus @a implies the type of b)
        | b == false @a = false @a
        | otherwise = true @a
    remove_outercomplement_from' c a@(Leaf _) b@(Node _ _ _)
        | a == false @a = false @a
        | a == true @a = inferNodeA_opposite @a (remove_outercomplement_from @a) c a b
    remove_outercomplement_from' c a@(Node _ _ _) b@(Leaf _)
        | b == false @a = false @a
        | b == true @a = inferNodeB @a (remove_outercomplement_from @a) c a b
    remove_outercomplement_from' (c:cs) a@(EndInfNode a') b@(Leaf _) -- todo when zooming in we might need inferInfNodeB c cs a b, as long as we only can ascend from here
        | b == false @a = false @a -- bot
        | b == true @a = applyInfElimRule @a a' `debug2` ("++++++++++ " ++ show(applyInfElimRule @a $ negation a')) -- subtract a from top
    remove_outercomplement_from' (c:cs) a@(Leaf _) b@(EndInfNode b') -- todo when zooming in we might need inferInfNodeB c cs a b, as long as we only can ascend from here
        | a == false @a = false @a -- bot
        | a == true @a = applyInfElimRule @a b' `debug2` ("++++++++++ " ++ show(applyInfElimRule @a $ negation b')) -- subtract a from top
    remove_outercomplement_from' [] a@(EndInfNode _) b@(Leaf _) = error "empty context"

    remove_outercomplement_from' c a@(Node positionA pos_childA neg_childA) b@(EndInfNode d) = inferNodeB @a (remove_outercomplement_from @a) c a b
    remove_outercomplement_from' c a@(EndInfNode d) b@(Node positionB pos_childB neg_childB) = inferNodeA_opposite @a (remove_outercomplement_from @a) c a b
    remove_outercomplement_from' (c:cs) (EndInfNode a) (EndInfNode b) = applyInfElimRule @a $ intersectionLocal_arg c cs (negation a) b -- todo negation a makes sense? or should i use maybe_negate on both to make sure we get the same polarity?
    remove_outercomplement_from' [] a@(EndInfNode childA)  b@(EndInfNode childB) = error "should not have empty context stack"

    -- No leafs involved
    remove_outercomplement_from' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)-- no mismatch, thus no inference is needed

        -- No mismatch, only the appropriate ZDD elim is applied
        | positionA == positionB =
            let pos_result = remove_outercomplement_from @a c pos_childA pos_childB
                neg_result = remove_outercomplement_from @a c neg_childA neg_childB
            in applyElimRule @a (Node positionA pos_result neg_result)

        -- mismatch with no Bot involved, thus with ZDD types inference we return bot
        | positionA < positionB =
            remove_outercomplement_from @a c neg_childA b
        | positionA > positionB =
            Node positionB pos_childB (remove_outercomplement_from @a c a neg_childB) --todo


    remove_outercomplement_from' c a@(Node positionA pos_childA neg_childA)  b@(InfNodes{}) = undefined -- todo define inner recursion for lobsided intersectio/union: (-. a .^. b)?
    remove_outercomplement_from' c a@(InfNodes{}) b@(Node positionB pos_childB neg_childB) = undefined
    remove_outercomplement_from' c a@(InfNodes{}) b@(EndInfNode d) = undefined
    remove_outercomplement_from' c a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B) = undefined
    remove_outercomplement_from' c a b = undefined `debug` (show a ++ "  :  " ++ show b)

    -- Leafs INTERSECTION LOCAL WORKS AS UNION FOR F0 TYPES?!
    intersectionLocal' c a@(Leaf False) _ = Leaf False `debug` "return leaf false"
    intersectionLocal' c a@(Leaf True) b = b `debug` "return leaf b"
    intersectionLocal' c _ b@(Leaf False) = Leaf False `debug` "return leaf false"
    intersectionLocal' c a b@(Leaf True) = a `debug` "return leaf a"

    -- infer node at DdF4, and here the shared abstrations
    intersectionLocal' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
        -- Match
        | positionA == positionB =
            let pos_result = intersectionLocal @a c pos_childA pos_childB
                neg_result = intersectionLocal @a c neg_childA neg_childB
            in applyElimRule @a (Node positionA pos_result neg_result) `debug` ("okee " ++ show pos_result ++ " , " ++ show neg_result ++ " , " ++ show ( (Node positionA pos_result neg_result)))
        -- Mismatch, but with a inference we ontinue recursion with the earliest (thus lowest valued) node.
        | positionA < positionB = inferNodeB @a (intersectionLocal @a) c a b `debug` ("return* " ++ show ( inferNodeB @a (intersectionLocal @a) c a b ))
        | positionA > positionB = inferNodeA @a (intersectionLocal @a) c a b `debug` ("return* " ++ show ( inferNodeA @a (intersectionLocal @a) c a b ))
    intersectionLocal' c a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) = applyElimRule @a $ inferNodeA @a (intersectionLocal @a) c a b
        --if positionA == positionB
        --    then
        --        error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        --        -- depends on how you want to model: if property green is true, and you zoom in on that property
        --        -- (i.e. property of being green exists out of a bunch of subproperties) do you then get that those multiple properties have to be true together before you have green?
        --        -- Or does just 1 have to be true? (e.i. either all have to be true or none have to be true before Propertie is true)
        --    else
        --        undefined
        --        -- inferNodeA @a c a b (intersectionLocal @a)
        --        -- Node positionB (Leaf False) (intersectionLocal @Neg1 c a neg_childB)
        --        -- Node positionB (Leaf True) (intersectionLocal @Neg0 c a neg_childB)
    intersectionLocal' c a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB _ _ _ _ _) =
        if positionA == positionB then error "undefined, multiple options possible for interpreting node in a context to sub nodes" else
            inferNodeB @a (intersectionLocal @a) c a b
    intersectionLocal'  c a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = intersection @True ((to_constr @a, Inter):c) a b

    -- continue local traversal
    intersectionLocal' c a@(Node positionA pos_childA neg_childA) b@(EndInfNode childB) = applyElimRule @a $ inferNodeB @a (intersectionLocal @a) c a b
    intersectionLocal' c a@(EndInfNode childA) b@(Node positionB pos_childB neg_childB) = applyElimRule @a $ inferNodeA @a (intersectionLocal @a) c a b
    -- continue previous super domain traversal
    intersectionLocal' (c:cs) a@(EndInfNode childA)  b@(EndInfNode childB) = applyInfElimRule @a $ intersectionLocal_arg c cs childA childB
    intersectionLocal' [] a@(EndInfNode childA)  b@(EndInfNode childB) = error "should not have empty context stack"-- applyInfElimRule @a $ intersection @True [] childA childB
    intersectionLocal' c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = intersectionInferB_ @a c a b
    intersectionLocal' c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = intersectionInferA_ @a c a b

    intersectionLocal' c a b = error ("how did we get here? " ++  show c ++ show a ++ "  -  " ++ show b)

    -- Leafs UNION LOCAL WORKS AS INTERSECTION FOR F0 TYPES?!
    unionLocal' c a@(Leaf True) _ = Leaf True
    unionLocal' c a@(Leaf False) b = b
    unionLocal' c _ b@(Leaf True) = Leaf True
    unionLocal' c a b@(Leaf False) = a

    unionLocal' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

        -- no mismatch, only the appropriate ZDD elim is applied
        | positionA == positionB =
            let pos_result = unionLocal @a c pos_childA pos_childB
                neg_result = unionLocal @a c neg_childA neg_childB
            in applyElimRule @a (Node positionA pos_result neg_result)

        -- mismatch, but with dc inference we continue recursion with the highest (thus lowest valued) node
        -- refactor into two functions? one for mixed inference rules, one for single
        | positionA < positionB = inferNodeB @a (unionLocal @a) c a b
        | positionA > positionB = inferNodeA @a (unionLocal @a) c a b

    unionLocal' c a@(InfNodes positionA _ _ _ _ _)  b@(Node positionB pos_childB neg_childB) = applyElimRule @a $ Node positionB (unionLocal @a c a pos_childB) (unionLocal @a c a neg_childB)
        --if positionA == positionB then error "undefined, multiple options possible for interpreting node in a context to sub nodes" else
            -- undefined
            --let pos_result = unionLocal @a c a pos_childB
            --    neg_result = unionLocal @a c a neg_childB
            --in applyElimRule @a (Node positionB pos_result neg_result)

    unionLocal' c a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) =
        if positionA == positionB then error "undefined, multiple options possible for interpreting node in a context to sub nodes" -- a possible option: (InfNodes (dcA .*. pos_childB) (n1A .*. pos_childB) (n0A .*. pos_childB) (p1A .*. pos_childB) (p0A .*. pos_childB))
        else undefined

    unionLocal' c a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) =  intersection @True ((to_constr @a, Union):c) a b

    -- continue local traversal
    unionLocal' c a@(Node positionA pos_childA neg_childA) b@(EndInfNode childB) = applyElimRule @a $ Node positionA (unionLocal @a c pos_childA b) (unionLocal @a c neg_childA b)
    unionLocal' c a@(EndInfNode childA) b@(Node positionB pos_childB neg_childB) = applyElimRule @a $ Node positionB (unionLocal @a c a pos_childB) (unionLocal @a c a neg_childB)
    -- continue previous super domain traversal
    unionLocal' (c:cs) a@(EndInfNode childA)  b@(EndInfNode childB) = applyInfElimRule @a $ unionLocal_arg c cs childA childB
    unionLocal' [] a@(EndInfNode childA)  b@(EndInfNode childB) = error "should not have empty context stack"  -- applyInfElimRule @a $ union @True [] childA childB
    unionLocal' c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = unionInferB_ @a c a b
    unionLocal' c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = unionInferA_ @a c a b
    unionLocal' c a b = error (show c ++ show a ++ show b)

    mixedIntersection' c l@(Leaf _) (Leaf _) = if l == false @a then false @a else Leaf False-- if n then 1 if n' then 0
    -- exception cases where zdd and its polar are not false @a, and dc is not a leaf.
    mixedIntersection' c l@(Leaf False) b = Leaf False
    mixedIntersection' c l@(Leaf True) b = b
    -- exception where the zdd is not a leaf and dc is
    mixedIntersection' c a l@(Leaf False) = Leaf False
    -- note that the a cannot be larger than 1 thus, the positive polarity of the zdd cannot not be one in this case (since it will always be largerthan dcR under intersection)
    mixedIntersection' c a l@(Leaf True) = a

    -- No leafs involved
    mixedIntersection' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

        -- No mismatch
        | positionA == positionB =
            let pos_result = mixedIntersection @a c pos_childA pos_childB
                neg_result = mixedIntersection @a c neg_childA neg_childB
            in applyElimRule @a (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionB = inferNodeA @a (mixedIntersection @a) c a b
        | positionA < positionB =
            let pos_result = mixedIntersection @a c pos_childA b
                neg_result = mixedIntersection @a c neg_childA b
            in applyElimRule @a (Node positionA pos_result neg_result)

    -- Single InfNode has been reached, similar to single Leaf node cases.
    mixedIntersection' c a@(Node positionA pos_childA neg_childA)  b@(EndInfNode _) =
                let pos_result = mixedIntersection @a c pos_childA b
                    neg_result = mixedIntersection @a c neg_childA b
                in applyElimRule @a (Node positionA pos_result neg_result)

    mixedIntersection' c a@(EndInfNode _) b@(Node positionB pos_childB neg_childB) =
        inferNodeA @a (mixedIntersection @a) c a b

    mixedIntersection' c a@(InfNodes positionA dcA n1A n0A p1A p0A) b@(Node positionB pos_childB neg_childB) =
        undefined
    mixedIntersection' c a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB dcB n1B n0B p1B p0B) =
        undefined
    -- Both InfNodes have been reached - run the usual intersection.
    mixedIntersection' c (EndInfNode a)  (EndInfNode b) = if (intersection @True c a b) == b then false @a else (intersection @True c a b) `debug3` ("mixedinter endinf - " ++ show c ++ " ; "++ show a ++ "  ;  " ++ show b)
    --mixedIntersection' [] (EndInfNode a)  (EndInfNode b) = error "should not have an empty context, check if top layer has DC context given along" -- applyInfElimRule @a $ intersection @True [] a (negate_maybe @a b)
    mixedIntersection' c a b = undefined `debug2` ("mixedinter - " ++ show c ++ " ; "++ show a ++ "  ;  " ++ show b)



    mixedUnion' c l@(Leaf _) (Leaf _) = if l == false @a then false @a else Leaf True-- if n then 1 if n' then 0
    -- exception cases where zdd and its polar are not false @a, and dc is not a leaf.
    mixedUnion' c l@(Leaf True) b = Leaf True
    mixedUnion' c l@(Leaf False) b = b
    -- exception where the zdd is not a leaf and dc is
    mixedUnion' c a l@(Leaf True) = Leaf True
    -- note that the a cannot be smaller than 0 thus, the negative polarity of the zdd cannot not be one in this case (since it will always be smaller than dcR under intersection)
    mixedUnion' c a l@(Leaf False) = a

    -- No leafs involved
    mixedUnion' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

        -- No mismatch
        | positionA == positionB =
            let pos_result = mixedUnion @a c pos_childA pos_childB
                neg_result = mixedUnion @a c neg_childA neg_childB
            in applyElimRule @a (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionB = inferNodeA @a (mixedUnion @a) c a b
        | positionA < positionB =
            let pos_result = mixedUnion @a c pos_childA b
                neg_result = mixedUnion @a c neg_childA b
            in applyElimRule @a (Node positionA pos_result neg_result)

    -- Single InfNode has been reached, similar to single Leaf node cases.
    mixedUnion' c a@(Node positionA pos_childA neg_childA)  b@(EndInfNode _) =
                let pos_result = mixedUnion @a c pos_childA b
                    neg_result = mixedUnion @a c neg_childA b
                in applyElimRule @a (Node positionA pos_result neg_result)

    mixedUnion' c a@(EndInfNode _) b@(Node positionB pos_childB neg_childB) =
        inferNodeA @a (mixedUnion @a) c a b

    mixedUnion' c a@(InfNodes positionA dcA n1A n0A p1A p0A) b@(Node positionB pos_childB neg_childB) =
        undefined
    mixedUnion' c a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB dcB n1B n0B p1B p0B) =
        undefined
    -- Both InfNodes have been reached - run the usual union.
    mixedUnion' c (EndInfNode a)  (EndInfNode b) = if (union @True c a b) == b then false @a else (union @True c a b) `debug3` ("mixedunion endinf - " ++ show c ++ " ; "++ show a ++ "  ;  " ++ show b)
    -- mixedUnion' [] (EndInfNode a)  (EndInfNode b) = error "should not have an empty context, check if top layer has DC context given along" -- applyInfElimRule @a $ intersection @True [] a (negate_maybe @a b)
    mixedUnion' c a b = undefined `debug2` ("mixedunion - " ++ show c ++ " ; "++ show a ++ "  ;  " ++ show b)


    absorb' c a@(Leaf _) dc = if a == dc then false @a else a

    -- absorb c (Leaf True) dc@(Node positionD pos_childD neg_childD)  = absorb @Neg1 c (Leaf True) neg_childD
    absorb' c a@(EndInfNode _) dc@(Node positionD pos_childD neg_childD)  =  inferNodeA @a (absorb @a) c a dc
    absorb' c (EndInfNode a) dc@(Leaf _)  = if a == dc then false @a else EndInfNode a -- todo what if EndInfNode EndInfnode (a == dc)
    absorb' c a@(Node positionA pos_childA neg_childA) dc@(EndInfNode _)  = --infere Dc node
        let pos_result = absorb @a c pos_childA dc
            neg_result = absorb @a c neg_childA dc
        in applyElimRule @a (Node positionA pos_result neg_result)
    absorb' c a@(EndInfNode a') dc@(EndInfNode dc') = if a' == dc' then false @a else a
    absorb' c a@(Node positionA pos_childA neg_childA) dc@(Leaf _) =
        let pos_result = absorb @a c pos_childA dc
            neg_result = absorb @a c neg_childA dc
        in applyElimRule @a (Node positionA pos_result neg_result)

    absorb' c a@(Node positionA pos_childA neg_childA)  dc@(Node positionD pos_childD neg_childD)
        -- No mismatch
        | positionA == positionD =
            let pos_result = absorb @a c pos_childA pos_childD
                neg_result = absorb @a c neg_childA neg_childD
            in applyElimRule @a (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionD = inferNodeA @a (absorb @a) c a dc
        | positionA < positionD =
            let pos_result = absorb @a c pos_childA dc
                neg_result = absorb @a c neg_childA dc
            in applyElimRule @a (Node positionA pos_result neg_result)

    absorb' c a@(InfNodes positionA dcA n1A n0A p1A p0A) dc@(Node positionD pos_childD neg_childD) = undefined -- todo add posB == posA, then we consider node to be AllNegs -> [1]
    absorb' c a@(Node positionA pos_childD neg_childD) dc@(InfNodes positionD dcA n1A n0A p1A p0A) = undefined

    absorb' c a@(InfNodes{}) b@(EndInfNode _) = intersectionInferB ((to_constr @a, Absorb):c) a b
    absorb' c a@(EndInfNode _) b@(InfNodes{}) = intersectionInferB ((to_constr @a, Absorb):c) a b
    absorb' c a b = error ""

-- holds the debug and class specific functions
class DdF4 a where
    to_constr :: Inf
    applyElimRule :: Dd -> Dd
    intersectionLocal :: FuncCtx -> Dd -> Dd -> Dd
    unionLocal :: FuncCtx -> Dd -> Dd -> Dd
    mixedIntersection :: FuncCtx -> Dd -> Dd -> Dd
    mixedUnion :: FuncCtx -> Dd -> Dd -> Dd
    absorb :: FuncCtx -> Dd -> Dd -> Dd
    remove_outercomplement_from :: FuncCtx -> Dd -> Dd -> Dd

    false :: Dd
    true :: Dd
    negate_maybe :: Dd -> Dd
    applyInfElimRule :: Dd -> Dd
    intersectionInferA_ :: FuncCtx -> Dd -> Dd -> Dd
    intersectionInferB_ :: FuncCtx -> Dd -> Dd -> Dd
    unionInferA_ :: FuncCtx -> Dd -> Dd -> Dd
    unionInferB_ :: FuncCtx -> Dd -> Dd -> Dd
    inferNodeA :: (FuncCtx -> Dd -> Dd -> Dd) -> FuncCtx -> Dd -> Dd -> Dd
    inferNodeA_opposite :: (FuncCtx -> Dd -> Dd -> Dd) -> FuncCtx -> Dd -> Dd -> Dd
    inferNodeB :: (FuncCtx -> Dd -> Dd -> Dd) -> FuncCtx -> Dd -> Dd -> Dd


instance DdF4 Dc where
    to_constr = Dc
    applyInfElimRule (Leaf b) = Leaf b
    applyInfElimRule d = EndInfNode d

    applyElimRule d@(Node _ posC negC) = if posC == negC then posC else d
    applyElimRule d@(InfNodes pos dcR n1R n0R p1R p0R) =
        if (n1R, n0R, p1R, p0R) == (Leaf False, Leaf True, Leaf False, Leaf True) then
                        (case dcR of
                            (EndInfNode x) -> x
                            (Leaf False) -> Leaf False
                            (Leaf True) -> Leaf True
                            _ -> InfNodes pos dcR n1R n0R p1R p0R)
                        else InfNodes pos dcR n1R n0R p1R p0R
    applyElimRule (Leaf b) = Leaf b
    applyElimRule d = d-- (EndInfNode _) = error "cannot end on end infnodlet c = lastN' (len positionA) c ine"

    -- Leaf and node
    -- intersectionLocal c a (Leaf False) = Leaf False
    -- intersectionLocal c (Leaf False) b = Leaf False
    -- intersectionLocal c a (Leaf True) = a
    -- intersectionLocal c (Leaf True) b = b
    -- todo add a "look forwards? to eable above quick checks?", after all the surrouding stack should be the same up to this point.. idk

    false = Leaf False
    true = Leaf True
    negate_maybe d = d



    intersectionInferB_ c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = intersectionInferB ((Dc, Inter):c) a b
    intersectionInferB_ _ _ _ = undefined
    intersectionInferA_ c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = intersectionInferA ((Dc, Inter):c) a b
    intersectionInferA_ _ _ _ = undefined
    unionInferB_ c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = unionInferB ((Dc, Union):c) a b
    unionInferB_ _ _ _ = undefined
    unionInferA_ c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = unionInferA ((Dc, Union):c) a b
    unionInferA_ _ _ _ = undefined

    intersectionLocal c a b = intersectionLocal' @Dc c a b
        `debug2` ("intersectionLocal Dc: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)


    -- comparing nodes, allowed mis-matches based on each inference rule
    unionLocal c a b =  unionLocal' @Dc c a b
        `debug2` ("unionLocal neg1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)


    mixedIntersection c a b = error "mixedintersection only with finite kinds"
    mixedUnion c a b = error "mixedintersection only with finite kinds"
    absorb = error "mixedintersection only with finite kinds"
    remove_outercomplement_from = error ""

    inferNodeA f c a b@(Node positionB pos_childB neg_childB) =
        let pos_result = f c a pos_childB
            neg_result = f c a neg_childB
        in applyElimRule @Dc (Node positionB pos_result neg_result)
    inferNodeA _ c a b = error ("inferNode : " ++ show c ++ ", " ++ show a ++ ", " ++ show b)

    inferNodeA_opposite = inferNodeA @Dc

    inferNodeB f c a@(Node positionA pos_childA neg_childA) b =
        let pos_result = f c pos_childA b
            neg_result = f c neg_childA b
        in applyElimRule @Dc (Node positionA pos_result neg_result)
    inferNodeB _ _ _ _ = undefined


instance DdF4 Neg1 where
    to_constr = Neg1
    applyInfElimRule (Leaf b) = Leaf b
    applyInfElimRule d = EndInfNode d

    applyElimRule d@(Node _ posC negC) = ( if posC == Leaf False then negC else d )
    applyElimRule d@(InfNodes pos dcR n1R n0R p1R p0R) =
        if (dcR, n0R, p1R, p0R) == (Leaf False, Leaf True, Leaf False, Leaf True) then
                        (case n1R of
                            (EndInfNode x) -> x
                            (Leaf False) -> Leaf False
                            (Leaf True) -> Leaf True
                            _ -> InfNodes pos dcR n1R n0R p1R p0R)
                        else InfNodes pos dcR n1R n0R p1R p0R
    applyElimRule d = d

    false = Leaf False
    true = Leaf True
    negate_maybe d = d

    intersectionInferB_ c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = intersectionInferB ((Neg1, Inter):c) a b
    intersectionInferB_ _ _ _ = undefined
    intersectionInferA_ c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = intersectionInferA ((Neg1, Inter):c) a b
    intersectionInferA_ _ _ _ = undefined

    intersectionLocal c a b = intersectionLocal' @Neg1 c a b
        `debug2` ("intersectionLocal neg1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)


    unionLocal c a b = unionLocal' @Neg1 c a b
        `debug2` ("unionLocal neg1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

-- ======================= Mixed Intersections =================================================================

    absorb c a b = absorb' @Neg1 c a b  `debug2` ("absorb neg1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

    inferNodeA f c a  b@(Node positionB pos_childB neg_childB) =
        applyElimRule @Neg1 $ f c (Node positionB (Leaf False) a) b
    inferNodeA _ _ _ _ = undefined

    inferNodeA_opposite = inferNodeA @Neg0

    inferNodeB f c a@(Node positionA pos_childA neg_childA) b =
        applyElimRule @Neg1 $ f c a (Node positionA (Leaf False) b)
    inferNodeB _ _ _ _ = undefined

    mixedIntersection c a b = mixedIntersection' @Neg1 c a b
        `debug2` ("mixedIntersection neg1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

    mixedUnion c a b = mixedUnion' @Neg1 c a b
        `debug2` ("mixedUnion neg1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

    remove_outercomplement_from c a b =  remove_outercomplement_from' @Neg1 c a b
        `debug2` ("remove_f0s1_from_f1s1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)


instance DdF4 Neg0 where
    to_constr = Neg0
    applyInfElimRule (Leaf b) = Leaf $ not b
    applyInfElimRule d = EndInfNode d


    applyElimRule d@(Node _ posC negC) = if posC == Leaf True then negC else d
    applyElimRule d@(InfNodes pos dcR n1R n0R p1R p0R) =
        if (n1R, dcR, p1R, p0R) == (Leaf False, Leaf True, Leaf False, Leaf True) then
            (case n0R of
                (EndInfNode x) -> x
                (Leaf False) -> Leaf False
                (Leaf True) -> Leaf True
                _ -> InfNodes pos dcR n1R n0R p1R p0R)
            else InfNodes pos dcR n1R n0R p1R p0R
    applyElimRule d = d

    false = Leaf True
    true = Leaf False
    negate_maybe d = negation d

    intersectionInferB_ c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = intersectionInferB ((Neg0, Inter):c) a b
    intersectionInferB_ _ _ _ = undefined
    intersectionInferA_ c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = intersectionInferA ((Neg0, Inter):c) a b
    intersectionInferA_ _ _ _ = undefined

        -- Leaf and node
    unionLocal c a b = unionLocal' @Neg0 c a b
        `debug2` ("unionLocal neg0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)


    intersectionLocal c a b = intersectionLocal' @Neg0 c a b
        `debug2` ("intersectionLocal neg0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)


    absorb c a b =  absorb' @Neg0 c a b
        `debug2` ("absorb neg0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

    inferNodeA f c a  b@(Node positionB pos_childB neg_childB) =
        applyElimRule @Neg0 $ f c (Node positionB (Leaf True) a) b
    inferNodeA _ _ _ _ = undefined
    inferNodeA_opposite = inferNodeA @Neg1
    inferNodeB f c a@(Node positionA pos_childA neg_childA) b =
        applyElimRule @Neg0 $ f c a (Node positionA (Leaf True) b)
    inferNodeB _ _ _ _ = undefined


    mixedIntersection c a b = mixedIntersection' @Neg0 c a b  `debug2` ("mixedIntersection neg0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

    mixedUnion c a b = mixedUnion' @Neg0 c a b
        `debug2` ("mixedUnion neg0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)


    remove_outercomplement_from c a b =  remove_outercomplement_from' @Neg0 c a b
        `debug2` ("remove_f0s1_from_f1s1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)


instance DdF4 Pos1 where
    to_constr = Pos1
    applyInfElimRule (Leaf b) = Leaf b
    applyInfElimRule d = EndInfNode d

    applyElimRule d@(Node _ posC negC) = if negC == Leaf False then posC else d
    applyElimRule d@(InfNodes pos dcR n1R n0R p1R p0R) =
        if (n1R, n0R, dcR, p0R) == (Leaf False, Leaf True, Leaf False, Leaf True) then
            (case p1R of
                (EndInfNode x) -> x
                (Leaf False) -> Leaf False
                (Leaf True) -> Leaf True
                _ -> InfNodes pos dcR n1R n0R p1R p0R)
            else InfNodes pos dcR n1R n0R p1R p0R
    applyElimRule d = d

    false = Leaf False
    true = Leaf True
    negate_maybe d = d


    intersectionInferB_ c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = intersectionInferB ((Pos1, Inter):c) a b
    intersectionInferB_ _ _ _ = undefined
    intersectionInferA_ c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = intersectionInferA ((Pos1, Inter):c) a b
    intersectionInferA_ _ _ _ = undefined

    intersectionLocal c a b = intersectionLocal' @Pos1 c a b
        `debug2` ("intersectionLocal pos1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

    unionLocal c a b = unionLocal' @Pos1 c a b
        `debug2` ("unionLocal pos1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

    absorb c a b = absorb' @Pos1 c a b
        `debug2` ("absorb pos1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

    inferNodeA f c a b@(Node positionB pos_childB neg_childB) =
        applyElimRule @Pos1 $ f c (Node positionB a (Leaf False)) b
    inferNodeA _ c a b = error ("pos1" ++ show c ++ show a ++ show b )
    inferNodeA_opposite = inferNodeA @Pos0
    inferNodeB f c a@(Node positionA pos_childA neg_childA) b =
        applyElimRule @Pos1 $ f c a (Node positionA b (Leaf False))
    inferNodeB _ c a b = error ("infernodeB: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

    mixedIntersection c a b = mixedIntersection' @Pos1 c a b  `debug2` ("mixedIntersection pos1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

    mixedUnion c a b = mixedUnion' @Pos1 c a b
        `debug2` ("mixedUnion pos1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

    remove_outercomplement_from c a b =  remove_outercomplement_from' @Pos1 c a b
        `debug2` ("remove_f0s1_from_f1s1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)



instance DdF4 Pos0 where
    to_constr = Pos0
    applyInfElimRule (Leaf b) = Leaf b
    applyInfElimRule d = EndInfNode d

    applyElimRule d@(Node _ posC negC) = if negC == Leaf True then posC else d
    applyElimRule d@(InfNodes pos dcR n1R n0R p1R p0R) =
        if (n1R, n0R, p1R, dcR) == (Leaf False, Leaf True, Leaf False, Leaf True) then
            (case p0R of
                (EndInfNode x) -> x
                (Leaf False) -> Leaf False
                (Leaf True) -> Leaf True
                _ -> InfNodes pos dcR n1R n0R p1R p0R)
            else InfNodes pos dcR n1R n0R p1R p0R
    applyElimRule d = d

    false = Leaf True
    true = Leaf False
    negate_maybe d = negation d

    intersectionInferB_ c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = intersectionInferB ((Pos0, Inter):c) a b
    intersectionInferB_ _ _ _ = undefined
    intersectionInferA_ c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = intersectionInferA ((Pos0, Inter):c) a b
    intersectionInferA_ _ _ _ = undefined
    unionInferB_ c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = unionInferB ((Pos0, Union):c) a b
    unionInferB_ _ _ _ = undefined
    unionInferA_ c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = unionInferA ((Pos0, Union):c) a b
    unionInferA_ _ _ _ = undefined

    -- Leaf and node
    unionLocal c a b = unionLocal' @Pos0 c a b  `debug2` ("unionLocal pos0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

    --unionLocal c a@(InfNodes positionA dcA n1A n0A p1A p0A) (Leaf True) = union @False c a (inferInfNode c True a)
    --unionLocal c (Leaf True) b@(InfNodes positionB dcB n1B n0B p1B p0B) = union @False c (inferInfNode c True b) b
    intersectionLocal c a b = intersectionLocal' @Pos0 c a b
        `debug2` ("intersectionLocal pos0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

    absorb c a b = absorb' @Pos0 c a b  `debug2` ("absorb pos0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

    inferNodeA f c a  b@(Node positionB pos_childB neg_childB) =
        applyElimRule @Pos0 $ f c (Node positionB a (Leaf True)) b
    inferNodeA _ c a b = error (show c ++ " , a = " ++ show a ++ " , b = " ++ show b)
    inferNodeA_opposite = inferNodeA @Pos1
    inferNodeB f c a@(Node positionA pos_childA neg_childA)  b =
        applyElimRule @Pos0 $ f c a (Node positionA b (Leaf True))
    inferNodeB _ _ _ _ = undefined

    mixedIntersection c a b = mixedIntersection' @Pos0 c a b
        `debug2` ("mixedIntersection: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

    mixedUnion c a b = mixedUnion' @Pos0 c a b
        `debug2` ("mixedUnion pos0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)

    remove_outercomplement_from c a b =  remove_outercomplement_from' @Pos0 c a b
        `debug2` ("remove_f0s1_from_f1s1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)







debug :: c -> String -> c
debug f s = if debugFlag then trace s f else f

debug3 :: c -> String -> c
debug3 = flip trace

debug2 :: a -> String -> a
debug2 f s = if debugFlag2 then trace (colorize s) f else f

colorize :: [Char] -> [Char]
colorize s = setSGRCode [SetColor Foreground Vivid Red] ++ s ++ setSGRCode [Reset]

