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

module MDDmanipulation where

import MDD
import Debug.Trace (trace)
import Data.Kind
import System.Console.ANSI

-- todo continue local traversal with children and popped ontext when EndIfnode with EndIfnode is encountered

-- todo finish with Neg0, Pos variants and BDD
-- todo do also the other functions
-- todo shift the contexts: stack current only when diving deeper, not when starting.


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

type FuncCtx = [(Inf, FType)]

debugFlag :: Bool
debugFlag = True

data FType = Norm | Mixed | Absorb
    deriving (Eq, Show)

type DdF4 :: Inf -> Constraint
type DdF2 :: Bool -> Constraint
type Dd1 :: Inf -> Constraint

class DdF2 a where
    intersection :: FuncCtx -> Dd -> Dd  -> Dd
    intersection' :: FuncCtx -> Dd -> Dd  -> Dd
    union :: FuncCtx -> Dd -> Dd  -> Dd
    union' :: FuncCtx -> Dd -> Dd  -> Dd
    applyInfElimRule :: Dd -> Dd

y23 = foo @Dc 2


instance DdF2 True where
    intersection c a b = intersection' @True c a b
        `debug2` ("intersection: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)
    intersection' c a (Leaf False) = Leaf False
    intersection' c (Leaf False) b = Leaf False
    intersection' c a (Leaf True) = a
    intersection' c (Leaf True) b = b
    intersection' c a b = intersectionMain c a b
    union c a b = union' @True c a b
        `debug2` ("union: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)
    union' c a (Leaf True) = Leaf True
    union' c (Leaf True) b = Leaf True
    union' c a (Leaf False) = a
    union' c (Leaf False) b = b
    union' c a b = unionMain c a b
    applyInfElimRule f = if f == Leaf False then Leaf False else EndInfNode f


instance DdF2 False where
    intersection c a b = intersection' @False c a b
        `debug2` ("intersection: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)
    intersection' c a (Leaf True) = Leaf True
    intersection' c (Leaf True) b = Leaf True
    intersection' c a (Leaf False) = a
    intersection' c (Leaf False) b = b
    intersection' c a b = intersectionMain c a b
    union c a b = union' @False c a b
        `debug2` ("intersection: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)
    union' c a (Leaf False) = Leaf False
    union' c (Leaf False) b = Leaf False
    union' c a (Leaf True) = a
    union' c (Leaf True) b = b
    union' c a b = unionMain c a b
    applyInfElimRule f = if f == Leaf False then Leaf True else EndInfNode f


negation :: Dd -> Dd
negation (Node position pos_child neg_child) = Node position (negation pos_child) (negation neg_child)
negation (InfNodes position dc_n n1_n n0_n p1_n p0_n) = InfNodes position (negation dc_n) (negation n0_n) (negation n1_n) (negation p0_n) (negation p1_n)
negation (EndInfNode a) = EndInfNode (negation a)
negation (Leaf b) = Leaf $ not b

isInfNode :: Dd -> Bool
isInfNode(InfNodes _ _ _ _ _ _) = True
isInfNode _ = False

applyElimRule_arg :: Inf -> Dd -> Dd
applyElimRule_arg Dc d = applyElimRule @Dc d
applyElimRule_arg Neg1 d = applyElimRule @Neg1 d
applyElimRule_arg Neg0 d = applyElimRule @Neg0 d
applyElimRule_arg Pos1 d = applyElimRule @Pos1 d
applyElimRule_arg Pos0 d = applyElimRule @Pos0 d


intersectionLocal_arg :: (Inf, FType) -> FuncCtx -> Dd -> Dd -> Dd
intersectionLocal_arg (i,t) [] (Leaf False) b
    | i `elem` [Dc,Neg1,Pos1] = if debugFlag then Leaf False `debug` (show i ++ "Leaf False") else Leaf False
    | i `elem` [Neg0,Pos0] = if debugFlag then b `debug` (show i ++ "b") else b
intersectionLocal_arg (i,t) [] (Leaf True) b
    | i `elem` [Dc,Neg1,Pos1] = if debugFlag then b `debug` (show i ++ "b") else b
    | i `elem` [Neg0,Pos0] = if debugFlag then Leaf True `debug` (show i ++ "Leaf True") else Leaf True
intersectionLocal_arg (i,t) [] a (Leaf False)
    | i `elem` [Dc,Neg1,Pos1] = if debugFlag then Leaf False `debug` (show i ++ "Leaf False") else Leaf False
    | i `elem` [Neg0,Pos0] = if debugFlag then a `debug` (show i ++ "a") else a
intersectionLocal_arg (i,t) [] a (Leaf True)
    | i `elem` [Dc,Neg1,Pos1] = if debugFlag then a `debug` (show i ++ "a") else a
    | i `elem` [Neg0,Pos0] = if debugFlag then Leaf True `debug` (show i ++ "Leaf True") else Leaf True

intersectionLocal_arg t c a b = case t of
    (Dc, Norm) -> intersectionLocal @Dc c a b
    (Neg1, Norm) -> intersectionLocal @Neg1 c a b
    (Neg0, Norm) -> intersectionLocal @Neg0 c a b
    (Pos1, Norm) -> intersectionLocal @Pos1 c a b
    (Pos0, Norm) -> intersectionLocal @Pos0 c a b

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

unionLocal_arg :: (Inf, FType) -> FuncCtx -> Dd -> Dd -> Dd
unionLocal_arg (i,t) [] (Leaf False) b
    | i `elem` [Dc,Neg1,Pos1] = if debugFlag then b `debug` (show i ++ "b") else b
    | i `elem` [Neg0,Pos0] = if debugFlag then Leaf False `debug` (show i ++ "Leaf False") else Leaf False
unionLocal_arg (i,t) [] (Leaf True) b
    | i `elem` [Dc,Neg1,Pos1] = if debugFlag then Leaf True `debug` (show i ++ "Leaf True") else Leaf True
    | i `elem` [Neg0,Pos0] = if debugFlag then b `debug` (show i ++ "b") else b
unionLocal_arg (i,t) [] a (Leaf False)
    | i `elem` [Dc,Neg1,Pos1] = if debugFlag then a `debug` (show i ++ "a") else a
    | i `elem` [Neg0,Pos0] = if debugFlag then Leaf False `debug` (show i ++ "Leaf False") else Leaf False
unionLocal_arg (i,t) [] a (Leaf True)
    | i `elem` [Dc,Neg1,Pos1] = if debugFlag then Leaf True `debug` (show i ++ "Leaf True") else Leaf True
    | i `elem` [Neg0,Pos0] = if debugFlag then a `debug` (show i ++ "a") else a

unionLocal_arg t c a b = case t of
    (Dc, Norm) -> intersectionLocal @Dc c a b
    (Neg1, Norm) -> intersectionLocal @Neg1 c a b
    (Neg0, Norm) -> intersectionLocal @Neg0 c a b
    (Pos1, Norm) -> intersectionLocal @Pos1 c a b
    (Pos0, Norm) -> intersectionLocal @Pos0 c a b

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

intersectionInferA c a b = if debugFlag then trace ("intersectionInferA: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) $ intersectionInferA' c a b else intersectionInferA' c a b
intersectionInferA' c@((inf, _) : _) a b@(InfNodes positionB dcB n1B n0B p1B p0B) =
    case inf of
        Dc -> let -- replace all the A stuf with (dc: a, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
            dcR = intersectionLocal @Dc c a dcB
            n1R = (if n0B == Leaf True then
                    absorb @Neg1 c (mixedIntersection @Neg1 c n1B a) dcR  else
                    remove_f0s1_from_f1s1 c n0B (absorb @Neg1 c (mixedIntersection @Neg1 c n1B a) dcR))
            n0R = mixedIntersection @Neg0 c n0B dcR --`debug` ( "inter: " ++ show (mixedIntersection @Neg0 c n0A dcR) ++ "\n n0A: " ++ show n0A  ++ "\n dcR" ++ show dcR)
            p1R = if p0B == Leaf True then
                absorb @Pos1 c (mixedIntersection @Pos1 c p1B a) dcR else
                remove_f0s0_from_f1s0 c p0B (absorb @Pos1 c (mixedIntersection @Pos1 c p1B a) dcR)
            p0R = mixedIntersection @Pos0 c p0B dcR
            in applyElimRule @Dc $ InfNodes positionB dcR n1R n0R p1R p0R

        Neg1 -> let -- replace all the A stuf with (dc: 0, neg1: a, neg0: 1, pos1: 0, pos0: 1)
            n1R = unionLocal @Neg1 c
                (intersectionLocal @Neg1 c a n1B)
                (if n0B == Leaf True then n1R' else remove_f0s1_from_f1s1 c n0B n1R')
            n1R' = mixedIntersection @Neg1 c a dcB
            in applyElimRule @Neg1 $ InfNodes positionB (Leaf False) n1R (Leaf True) (Leaf False) (Leaf True)
        Neg0 -> let -- replace all the A stuf with (dc: 1, neg1: 0, neg0: a, pos1: 0, pos0: 1)
            n0R' = intersectionLocal @Neg0 c a n0B
            n0R = mixedIntersection @Neg0 c n0R' dcB
            in applyElimRule @Neg0 $ InfNodes positionB dcB (Leaf False) n0R (Leaf False) (Leaf True)
        Pos1 -> let -- replace all the A stuf with (dc: 0, neg1: 0, neg0: 1, pos1: a, pos0: 1)
            p1R = unionLocal @Pos1 c
                (intersectionLocal @Pos1 c a n1B)
                (if n0B == Leaf True then p1R' else remove_f0s1_from_f1s1 c n0B p1R')
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

intersectionInferB c a b = if debugFlag then trace ("intersectionInferB: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) $ intersectionInferB' c a b else intersectionInferB' c a b
intersectionInferB' c@((inf, _) : _) a@(InfNodes positionA dcA n1A n0A p1A p0A)  b =
    case inf of
        Dc -> let
            dcR = intersectionLocal @Dc c dcA b
            n1R = (if n0A == Leaf True then
                absorb @Neg1 c (mixedIntersection @Neg1 c n1A b) dcR  else
                remove_f0s1_from_f1s1 c n0A (absorb @Neg1 c (mixedIntersection @Neg1 c n1A b) dcR))
            n0R = mixedIntersection @Neg0 c n0A dcR
            p1R = if p0A == Leaf True then
                absorb @Pos1 c (mixedIntersection @Pos1 c p1A b) dcR else
                remove_f0s0_from_f1s0 c p0A (absorb @Pos1 c (mixedIntersection @Pos1 c p1A b) dcR)
            p0R = mixedIntersection @Pos0 c p0A dcR
            in applyElimRule @Dc $ InfNodes positionA dcR n1R n0R p1R p0R

        Neg1 -> let -- replace all the B stuf with (dc: 0, neg1: b, neg0: 1, pos1: 0, pos0: 1)
            n1R = unionLocal @Neg1 c
                (intersectionLocal @Neg1 c n1A b)
                (if n0A == Leaf True then n1R' else remove_f0s1_from_f1s1 c n0A n1R')
            n1R' = mixedIntersection @Neg1 c b dcA
            in applyElimRule @Neg1 $ InfNodes positionA (Leaf False) n1R (Leaf True) (Leaf False) (Leaf True)
        Neg0 -> let -- replace all the B stuf with (dc: 1, neg1: 0, neg0: b, pos1: 0, pos0: 1)
            n0R' = intersectionLocal @Neg0 c n0A b
            n0R = mixedIntersection @Neg0 c n0R' dcA
            in applyElimRule @Neg0 $ InfNodes positionA dcA (Leaf False) n0R (Leaf False) (Leaf True)
        Pos1 -> let -- replace all the B stuf with (dc: 0, neg1: 0, neg0: 1, pos1: b, pos0: 1)
            p1R = unionLocal @Pos1 c
                (intersectionLocal @Pos1 c n1A b )
                (if p0A == Leaf True then p1R' else remove_f0s1_from_f1s1 c p0A p1R')
            p1R' = mixedIntersection @Pos1 c dcA b
            in applyElimRule @Pos1 $ InfNodes positionA (Leaf False) (Leaf False) (Leaf True) p1R (Leaf True)
        Pos0 -> let -- replace all the B stuf with (dc: 1, neg1: 0, neg0: b, pos1: 0, pos0: 1)
            p0R' = intersectionLocal @Pos0 c p0A b
            p0R = mixedIntersection @Pos0 c p0R' dcA
            in applyElimRule @Pos0 $ InfNodes positionA dcA (Leaf False) (Leaf True) (Leaf False) p0R
intersectionInferB' _ _ _ = undefined


-- main idea is that

intersectionMain :: FuncCtx -> Dd -> Dd -> Dd
intersectionMain c a b = if debugFlag then trace ("intersectionMain: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) $ intersectionMain' c a b else intersectionMain' c a b
intersectionMain'  c a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B)
    | positionA == positionB =  let
        dcR = intersectionLocal @Dc c dcA dcB --`debug` ("intersection A ("++ show positionA ++ ")==B (" ++ show positionB ++ "), with c = " ++ show c)
            `debug` "dcR"

        n1R = unionLocal @Neg1 c
            (intersectionLocal @Neg1 c n1A n1B) -- overlapping points are by definition not inside the others dc, thus have to be preserved
            (if n0R' == Leaf True then n1R' else remove_f0s1_from_f1s1 c n0R' n1R') -- holes absorb points under intersection
            `debug` "n1R"
        n1R' = unionLocal @Neg1 c -- guaranteed that dcA and dcB do not overlap around the finite points, thus they do not get absorbed
            (absorb @Neg1 c (mixedIntersection @Neg1 c n1A dcB) dcR) -- keep the points that fit inside B
            (absorb @Neg1 c (mixedIntersection @Neg1 c n1B dcA) dcR) -- keep the points that fit inside A
            `debug` "n1R'"

        n0R' = intersectionLocal @Neg0 c n0A n0B -- holes get unioned, because i keep the consequence of holes "uncomplemented" we get local union then intersection.
            `debug` "n0R'"
        n0R = absorb @Neg0 c (mixedIntersection @Neg0 c n0R' dcR) dcR-- keep the holes that fit inside dcR
            `debug` "n0R"
        -- if the local hole fits inside dcR but the consequence of n0R' does not fit inside the consequenc of dcR it should return n0R' -> Leaf false
        ------------------------------------
        p1R = unionLocal @Pos1 c
            (intersectionLocal @Pos1 c p1A p1B)
            (if p0R' == Leaf True then p1R' else remove_f0s0_from_f1s0 c p0R' p1R')
            `debug` "p1R"
        p1R' = unionLocal @Pos1 c
            (absorb @Pos1 c (mixedIntersection @Pos1 c p1A dcB) dcR)
            (absorb @Pos1 c (mixedIntersection @Pos1 c p1B dcA) dcR)
            `debug` "p1R'"
        p0R' = intersectionLocal @Pos0 c p0A p0B -- local union then intersection
            `debug` "p0R'"
        p0R = absorb @Pos0 c (mixedIntersection @Pos0 c p0R' dcR) dcR
            `debug` "p0R"
        in applyElimRule @Dc $ InfNodes positionA dcR n1R n0R p1R p0R
    | positionA > positionB = intersectionInferA c a b
    | positionA < positionB = intersectionInferB c a b-- replace all the A stuf with (dc: a, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
intersectionMain' c a b = error (show a ++ ", " ++ show b ++ ", "++ show c)

unionInferA :: FuncCtx -> Dd -> Dd -> Dd
unionInferA [] _ _ = error "empty context"
unionInferA _ _ (Leaf _) = error "Leaf in A"
unionInferA _ _ (EndInfNode _) = error "EndNode in A"
unionInferA _ _ (Node _ _ _) = error "Node in A"

unionInferA c a b = if debugFlag then trace ("unionInferA: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) $ unionInferA' c a b else unionInferA' c a b
unionInferA' c@((inf, _) : _) a b@(InfNodes positionB dcB n1B n0B p1B p0B) =
    case inf of
        Dc -> let
            dcR = unionLocal @Dc c  a dcB --pass along the consequence of B for both dcA and not dcA
            n1R = mixedIntersection @Neg1 c n1B dcR

            n0R = let n0R' = absorb @Neg0 c (mixedIntersection @Neg0 c n0B a) dcR in
                if n1B == Leaf False then n0R' else remove_f1s1_from_f0s1 c n1B n0R'

            p1R = mixedIntersection @Pos1 c p1B dcR
            p0R = let p0R' = absorb @Pos0 c (mixedIntersection @Pos0 c p0B a) dcR in
                if p1B == Leaf False then p0R' else remove_f1s0_from_f0s0 c p1B p0R'

            in applyElimRule @Dc (InfNodes positionB dcR n1R n0R p1R p0R)

        Neg1 -> let -- replace all the A stuf with (dc: 0, neg1: a, neg0: 1, pos1: 0, pos0: 1)
            n1R' = unionLocal @Neg1 c a n1B
            n1R = mixedIntersection @Neg1 c n1R' dcB
            in applyElimRule @Neg1 $ InfNodes positionB (Leaf False) n1R (Leaf True) (Leaf False) (Leaf True)
        Neg0 -> let -- replace all the A stuf with (dc: 1, neg1: 0, neg0: a, pos1: 0, pos0: 1)
            n0R = intersectionLocal @Neg0 c
                (unionLocal @Neg0 c a n0B)
                (if n1B == Leaf True then n0R' else remove_f1s1_from_f0s1 c n1B n0R')
            n0R' = mixedIntersection @Neg0 c a dcB
            in applyElimRule @Neg0 $ InfNodes positionB dcB (Leaf False) n0R (Leaf False) (Leaf True)
        Pos1 -> let -- replace all the A stuf with (dc: 0, neg1: 0, neg0: 1, pos1: a, pos0: 1)
            p1R' = unionLocal @Pos1 c a p1B
            p1R = mixedIntersection @Pos1 c p1R' dcB
            in applyElimRule @Pos1 $ InfNodes positionB (Leaf False) (Leaf False) (Leaf True) p1R (Leaf True)
        Pos0 -> let -- replace all the A stuf with (dc: 1, neg1: 0, neg0: a, pos1: 0, pos0: 1)
            p0R = intersectionLocal @Pos0 c
                (unionLocal @Pos0 c a n0B)
                (if p1B == Leaf True then p0R' else remove_f0s1_from_f1s1 c p1B p0R')
            p0R' = mixedIntersection @Pos0 c a dcB
            in applyElimRule @Pos0 $ InfNodes positionB dcB (Leaf False) (Leaf True) (Leaf False) p0R
unionInferA' _ _ _ = undefined


unionInferB :: FuncCtx -> Dd -> Dd -> Dd
unionInferB [] _ _ = error "empty context"
unionInferB _ (Leaf _) _ = error "Leaf in A"
unionInferB _ (EndInfNode _) _ = error "EndNode in A"
unionInferB _ (Node _ _ _) _ = error "Node in A"

unionInferB c a b = if debugFlag then trace ("unionInferB: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) $ unionInferB' c a b else unionInferB' c a b
unionInferB' c@((inf, _) : _) a@(InfNodes positionA dcA n1A n0A p1A p0A)  b =
    case inf of
        Dc -> let
            dcR = unionLocal @Dc c b dcA
                `debug` "dcR"
            n1R = mixedIntersection @Neg1 c n1A dcR
                `debug` "n1R"

            n0R = let n0R' = absorb @Neg0 c (mixedIntersection @Neg0 c n0A b) dcR in
                if n1A == Leaf False then n0R' else remove_f1s1_from_f0s1 c n1A n0R'
                `debug` "n0R"

            p1R = mixedIntersection @Pos1 c p1A dcR
                `debug` "p1R"
            p0R = let p0R' = absorb @Pos0 c (mixedIntersection @Pos0 c p0A b) dcR in
                if p1A == Leaf False then p0R' else remove_f1s0_from_f0s0 c p1A p0R'
                `debug` "p0R"
            in applyElimRule @Dc (InfNodes positionA dcR n1R n0R p1R p0R)
        Neg1 -> let -- replace all the B stuf with (dc: 0, neg1: b, neg0: 1, pos1: 0, pos0: 1)
            n1R' = unionLocal @Neg1 c n1A b
            n1R = mixedIntersection @Neg1 c n1R' dcA
            in applyElimRule @Neg1 $ InfNodes positionA (Leaf False) n1R (Leaf True) (Leaf False) (Leaf True)
        Neg0 -> let -- replace all the B stuf with (dc: 1, neg1: 0, neg0: b, pos1: 0, pos0: 1)
            n0R = intersectionLocal @Neg0 c
                (unionLocal @Neg0 c n0A b)
                (if n1A == Leaf True then n0R' else remove_f1s1_from_f0s1 c n1A n0R')
            n0R' = mixedIntersection @Neg0 c b dcA
            in applyElimRule @Neg0 $ InfNodes positionA dcA (Leaf False) n0R (Leaf False) (Leaf True)
        Pos1 -> let -- replace all the B stuf with (dc: 0, neg1: 0, neg0: 1, pos1: b, pos0: 1)
            p1R' = unionLocal @Pos1 c p1A b
            p1R = mixedIntersection @Pos1 c p1R' dcA
            in applyElimRule @Pos1 $ InfNodes positionA (Leaf False) (Leaf False) (Leaf True) p1R (Leaf True)
        Pos0 -> let -- replace all the B stuf with (dc: 1, neg1: 0, neg0: b, pos1: 0, pos0: 1)
            p0R = intersectionLocal @Pos0 c
                (unionLocal @Pos0 c n0A b )
                (if p1A == Leaf True then p0R' else remove_f1s1_from_f0s1 c p1A p0R')
            p0R' = mixedIntersection @Pos0 c b dcA
            in applyElimRule @Pos0 $ InfNodes positionA dcA (Leaf False) (Leaf True) (Leaf False) p0R
unionInferB' _ _ _ = undefined


unionMain :: FuncCtx -> Dd -> Dd -> Dd
-- exclusive points (0's / holes) under union are filled unless they are present in both A and B (so only an intersection between them needs to be done)
-- inclusive point (1's ) under union are intersected with the opposite infinite subset (dc) before they are added together
unionMain c a b = if debugFlag then trace ("unionMain: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) $ unionMain' c a b else unionMain' c a b
unionMain'  c a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B)
    | positionA == positionB =  let

        dcR = unionLocal @Dc c  dcA dcB
            `debug2` ("\nDcR dcA v dcB"
            ++ "\n\t dcA = " ++ show dcA
            ++ "\n\t dcB = " ++ show dcB
            ++ "\n")

        n1R = absorb @Neg1 c (mixedIntersection @Neg1 c n1R' dcR) dcR
            `debug2` ("\nn1R = n1R' ^ dcR"
            ++ "\n\t n1R' = " ++ show n1R'
            ++ "\n\t dcR = " ++ show dcR
            ++ "\n") -- todo union the consequences of n1R with dcR, then if they are the same absorb them
        n1R' = unionLocal @Neg1 c n1A n1B
            `debug2` ("\nn1R = n1A ^ n1B"
            ++ "\n\t n1A = " ++ show n1A
            ++ "\n\t n1B = " ++ show n1B
            ++ "\n")

        n0R = intersectionLocal @Neg0 c -- union then intersection
            (unionLocal @Neg0 c n0A n0B) -- intersection then union
            (if n1R' == Leaf False then n0R' else remove_f1s1_from_f0s1 c n1R' n0R')
            `debug` ("\nn0R (v) ^ (rm)")
        n0R' = intersectionLocal @Neg0 c
            (absorb @Neg0 c (mixedIntersection @Neg0 c n0A dcB) dcR) -- remove the holes that do fit in B (unioned away) // note that in consequence this reverts back to to union and is absorbed if consequence of n0A == dcR
            (absorb @Neg0 c (mixedIntersection @Neg0 c n0B dcA) dcR) -- remove the holes that do fit in A (unioned away)
            `debug` ("\nn0R' (@^) ^ (@^)")

        ------------------------------------
        -- n0R = (n0A cap n0B) cup ((n0A cap neg dcB) cap n1B) cup ((n0B cap neg dcA) cap n1A) <-> (n0A cup n0B) cap n1R* cap neg dcR
        p1R = absorb @Pos1 c (mixedIntersection @Pos1 c p1R' dcR) dcR
            `debug2` ("\np1R = p1R' ^ dcR"
            ++ "\n\t p1R' = " ++ show p1R'
            ++ "\n\t dcR = " ++ show dcR
            ++ "\n")
        p1R' = unionLocal @Pos1 c p1A p1B
            `debug2` ("\np1R = p1A ^ p1B"
            ++ "\n\t p1A = " ++ show p1A
            ++ "\n\t p1B = " ++ show p1B
            ++ "\n")

        p0R = intersectionLocal @Pos0 c
            (unionLocal @Pos0 c p0A p0B)
            (if p1R' == Leaf False then p0R' else remove_f1s0_from_f0s0 c p1R' p0R')
            `debug` ("\np0R = (p0A v p0B) ^ (rm p1R' p0R')"
            ++ "\n\t (p0A v p0B) = " ++ show (unionLocal @Pos0 c p0A p0B)
            -- ++ "\n\t (rm p1R p0R')" ++ show (if p1R' == Leaf False then p0R' else remove_f1s0_from_f0s0 c p1R' p0R')
            ++ "\n\t p0A = " ++ show p0A
            ++ "\n\t p0B = " ++ show p0B
            ++ "\n\t p1R' = " ++ show p1R'
            ++ "\n\t p0R' = " ++ show p0R'
            ++ "\n")
        p0R' = intersectionLocal @Pos0 c
            (absorb @Pos0 c (mixedIntersection @Pos0 c p0A dcB) dcR) -- remove the holes that do fit in B: if the consequence of p0A after union is the same as the consequence of dcB, then it is also removed. If the consequence is smaller it is kept.
            (absorb @Pos0 c (mixedIntersection @Pos0 c p0B dcA) dcR)
            `debug` ("\n\tp0R' =  ((p0A ^ dcB) @ dcR) ^ ((p0B ^ dcA) @ dcR)"
                ++ "\n\t dcR = " ++ show dcR
                ++ "\n\t p0A = " ++ show p0A
                ++ "\n\t p0B = " ++ show p0B
                ++ "\n\t dcA = " ++ show dcB
                ++ "\n\t dcB = " ++ show dcA
                ++ "\n\t (p0A ^ dcB) @ dcR) = " ++ show (absorb @Pos0 c (mixedIntersection @Pos0 c p0A dcB) dcR)
                ++ "\n\t (p0B ^ dcA) @ dcR) = " ++ show (absorb @Pos0 c (mixedIntersection @Pos0 c p0B dcA) dcR)
                ++ "\n\t (p0B ^ dcA) = " ++ show (mixedIntersection @Pos0 c p0B dcA)
                ++ "\n")

        in applyElimRule @Dc (InfNodes positionA dcR n1R n0R p1R p0R)

    | positionA > positionB = unionInferA c a b-- replace all the A stuf with (dc: a, neg1: 0, neg0: 1, pos1: 0, pos0: 1)

    -- c cannot be empty..
    | positionA < positionB = unionInferB c a b-- replace all the A stuf with (dc: a, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
unionMain' c a b = error "no 2 StartInfNode's in intersection main"





class DdF4 a where
    applyElimRule :: Dd -> Dd
    intersectionLocal :: FuncCtx -> Dd -> Dd -> Dd
    intersectionLocal' :: FuncCtx -> Dd -> Dd -> Dd
    unionLocal :: FuncCtx -> Dd -> Dd -> Dd
    unionLocal' :: FuncCtx -> Dd -> Dd -> Dd
    mixedIntersection :: FuncCtx -> Dd -> Dd -> Dd
    mixedIntersection' :: FuncCtx -> Dd -> Dd -> Dd
    absorb :: FuncCtx -> Dd -> Dd -> Dd
    absorb' :: FuncCtx -> Dd -> Dd -> Dd
    remove_outer_complement_from :: FuncCtx -> Dd -> Dd -> Dd
    bar :: Int -> Int
    false :: Dd
    true :: Dd
    inferNodeA_intersection :: FuncCtx -> Dd -> Dd -> Dd
    inferNodeB_intersection :: FuncCtx -> Dd -> Dd -> Dd
    nextInfDomain :: FuncCtx -> Dd -> Dd -> (FuncCtx -> Dd -> Dd -> Dd) -> Dd
    intersectionInferB_ :: FuncCtx -> Dd -> Dd -> Dd
    intersectionInferA_ :: FuncCtx -> Dd -> Dd -> Dd
    unionInferB_ :: FuncCtx -> Dd -> Dd -> Dd
    unionInferA_ :: FuncCtx -> Dd -> Dd -> Dd



class Dd1 a where
    foo :: Int -> Int
    intersectionLocal2' :: FuncCtx -> Dd -> Dd -> Dd
instance DdF4 a => Dd1 a where
    foo = bar @a
    -- infer node at DdF4, and here the shared abstrations
    intersectionLocal2' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
        -- Match
        | positionA == positionB =
            let pos_result = intersectionLocal @a c pos_childA pos_childB
                neg_result = intersectionLocal @a c neg_childA neg_childB
            in applyElimRule @a (Node positionA pos_result neg_result)
        -- Mismatch, but with a inference we ontinue recursion with the earliest (thus lowest valued) node.
        | positionA < positionB = inferNodeB_intersection @a c a b
        | positionA > positionB = inferNodeA_intersection @a c a b
    intersectionLocal2' c a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
        if positionA == positionB
            then
                error "undefined, multiple options possible for interpreting node in a context to sub nodes"
                -- depends on how you want to model: if property green is true, and you zoom in on that property
                -- (i.e. property of being green exists out of a bunch of subproperties) do you then get that those multiple properties have to be true together before you have green?
                -- Or does just 1 have to be true? (e.i. either all have to be true or none have to be true before Propertie is true)
            else
                undefined
                -- inferNodeA_intersection @a c a b
    intersectionLocal2' c a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB _ _ _ _ _) =
        if positionA == positionB then error "undefined, multiple options possible for interpreting node in a context to sub nodes" else
            inferNodeB_intersection @a c a b
    intersectionLocal2'  c a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = nextInfDomain @a c a b (intersection @True)

    -- continue local traversal
    intersectionLocal2' c a@(Node positionA pos_childA neg_childA) b@(EndInfNode childB) = applyElimRule @a $ inferNodeB_intersection @a c a b
    intersectionLocal2' c a@(EndInfNode childA) b@(Node positionB pos_childB neg_childB) = applyElimRule @a $ inferNodeA_intersection @a c a b
    -- continue previous super domain traversal
    intersectionLocal2' (c:cs) a@(EndInfNode childA)  b@(EndInfNode childB) = EndInfNode $ intersectionLocal_arg c cs childA childB
    intersectionLocal2' [] a@(EndInfNode childA)  b@(EndInfNode childB) = EndInfNode $ intersection @True [] childA childB
    intersectionLocal2' c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = intersectionInferB_ @a c a b
    intersectionLocal2' c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = intersectionInferA_ @a c a b

    intersectionLocal2' c a b = error ("how did we get here? " ++  show c ++ show a ++ "  -  " ++ show b)


instance DdF4 Dc where
    bar = (+1)
    applyElimRule d@(Node _ posC negC) = if posC == negC then posC else d
    applyElimRule d@(InfNodes pos dcR n1R n0R p1R p0R) =
        if (n1R, n0R, p1R, p0R) == (Leaf False, Leaf True, Leaf False, Leaf True) then
                        (if isInfNode dcR then dcR else
                            if dcR == Leaf False then Leaf False else
                                if dcR == Leaf True then Leaf True else
                                    InfNodes pos dcR n1R n0R p1R p0R)
                        else InfNodes pos dcR n1R n0R p1R p0R
    applyElimRule (Leaf b) = Leaf b
    applyElimRule (EndInfNode _) = error "cannot end on end infnodlet c = lastN' (len positionA) c ine"

    -- Leaf and node
    -- intersectionLocal c a (Leaf False) = Leaf False
    -- intersectionLocal c (Leaf False) b = Leaf False
    -- intersectionLocal c a (Leaf True) = a
    -- intersectionLocal c (Leaf True) b = b
    -- todo add a "look forwards? to eable above quick checks?", after all the surrouding stack should be the same up to this point.. idk

    false = Leaf False
    true = Leaf True
    inferNodeA_intersection c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) =
        let pos_result = intersectionLocal' @Dc c a pos_childB
            neg_result = intersectionLocal' @Dc c a neg_childB
        in applyElimRule @Dc (Node positionB pos_result neg_result)
    inferNodeA_intersection _ _ _ = undefined
    inferNodeB_intersection c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) =
        let pos_result = intersectionLocal' @Dc c pos_childA b
            neg_result = intersectionLocal' @Dc c neg_childA b
        in applyElimRule @Dc (Node positionA pos_result neg_result)
    inferNodeB_intersection _ _ _ = undefined

    nextInfDomain c a b f = f ((Dc, Norm):c) a b
    intersectionInferB_ c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = intersectionInferB ((Dc, Norm):c) a b
    intersectionInferB_ _ _ _ = undefined
    intersectionInferA_ c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = intersectionInferA ((Dc, Norm):c) a b
    intersectionInferA_ _ _ _ = undefined

    intersectionLocal c a b = intersectionLocal2' @Dc c a b
        `debug2` ("intersectionLocal neg1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)


    -- comparing nodes, allowed mis-matches based on each inference rule
    unionLocal c a b = if debugFlag then trace ("unionLocal neg1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) $ unionLocal' @Dc c a b else unionLocal' @Dc c a b
    unionLocal' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

        -- no mismatch, only the appropriate ZDD elim is applied
        | positionA == positionB =
            let pos_result = unionLocal @Dc c pos_childA pos_childB
                neg_result = unionLocal @Dc c neg_childA neg_childB
            in applyElimRule @Dc (Node positionA pos_result neg_result)

        -- mismatch, but with dc inference we continue recursion with the highest (thus lowest valued) node
        -- refactor into two functions? one for mixed inference rules, one for single
        | positionA < positionB =
            let pos_result = unionLocal @Dc c pos_childA b
                neg_result = unionLocal @Dc c neg_childA b
            in applyElimRule @Dc (Node positionA pos_result neg_result)

        | positionA > positionB =
            let pos_result = unionLocal @Dc c a pos_childB
                neg_result = unionLocal @Dc c a neg_childB
            in applyElimRule @Dc (Node positionB pos_result neg_result)

    unionLocal' c a@(InfNodes positionA _ _ _ _ _)  b@(Node positionB pos_childB neg_childB) =
        if positionA == positionB then error "undefined, multiple options possible for interpreting node in Dc context to sub nodes" else
            let pos_result = unionLocal @Dc c a pos_childB
                neg_result = unionLocal @Dc c a neg_childB
            in applyElimRule @Dc (Node positionB pos_result neg_result)

    unionLocal' c a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) =
        if positionA == positionB then error "undefined, multiple options possible for interpreting node in Dc context to sub nodes" -- a possible option: (InfNodes (dcA .*. pos_childB) (n1A .*. pos_childB) (n0A .*. pos_childB) (p1A .*. pos_childB) (p0A .*. pos_childB))
        else let pos_result = unionLocal @Dc c pos_childA b
                 neg_result = unionLocal @Dc c neg_childA b
             in applyElimRule @Dc (Node positionA pos_result neg_result)

    unionLocal' c a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = unionMain ((Dc,Norm):c) a b

    -- continue local traversal
    unionLocal' c a@(Node positionA pos_childA neg_childA) b@(EndInfNode childB) = applyElimRule @Dc $ Node positionA (unionLocal @Dc c pos_childA b) (unionLocal @Dc c neg_childA b)
    unionLocal' c a@(EndInfNode childA) b@(Node positionB pos_childB neg_childB) = applyElimRule @Dc $ Node positionB (unionLocal @Dc c a pos_childB) (unionLocal @Dc c a neg_childB)
    -- continue previous super domain traversal
    unionLocal' (c:cs) a@(EndInfNode childA)  b@(EndInfNode childB) = EndInfNode $ unionLocal_arg c cs childA childB
    unionLocal' [] a@(EndInfNode childA)  b@(EndInfNode childB) = EndInfNode $ union @True [] childA childB
    unionLocal' c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = unionInferB ((Dc,Norm):c) a b
    unionLocal' c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = unionInferA ((Dc,Norm):c) a b
    unionLocal' c a b = error (show c ++ show a ++ show b)

    mixedIntersection = error "mixedintersection only with finite kinds"
    absorb = error "mixedintersection only with finite kinds"



instance DdF4 Neg1 where
    applyElimRule d@(Node _ posC negC) = if posC == Leaf False then posC else d
    applyElimRule d@(InfNodes pos dcR n1R n0R p1R p0R) =
        if (dcR, n0R, p1R, p0R) == (Leaf False, Leaf True, Leaf False, Leaf True) then
                        (if isInfNode n1R then n1R else
                            if n1R == Leaf False then Leaf False else
                                if n1R == Leaf True then Leaf True else
                                    InfNodes pos dcR n1R n0R p1R p0R)
                        else InfNodes pos dcR n1R n0R p1R p0R
    applyElimRule d = d

    false = Leaf False
    true = Leaf True
    inferNodeA_intersection c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) =
        intersectionLocal' @Neg1 c neg_childA b
    inferNodeA_intersection _ _ _ = undefined
    inferNodeB_intersection c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) =
        intersectionLocal' @Neg1 c a neg_childB
    inferNodeB_intersection _ _ _ = undefined
    nextInfDomain c a b f = f ((Neg1, Norm):c) a b
    intersectionInferB_ c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = intersectionInferB ((Neg1, Norm):c) a b
    intersectionInferB_ _ _ _ = undefined
    intersectionInferA_ c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = intersectionInferA ((Neg1, Norm):c) a b
    intersectionInferA_ _ _ _ = undefined

    intersectionLocal c a b = if debugFlag then trace ("intersectionLocal neg1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) $ intersectionLocal' @Neg1 c a b else intersectionLocal' @Neg1 c a b
    intersectionLocal' c a (Leaf False) = false @Neg1
    intersectionLocal' c (Leaf False) b = Leaf False

   -- comparing nodes, allowed mis-matches based on each inference rule
    intersectionLocal' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
        -- match
        | positionA == positionB =
            let pos_result = intersectionLocal @Neg1 c pos_childA pos_childB
                neg_result = intersectionLocal @Neg1 c neg_childA neg_childB
            in applyElimRule @Neg1 (Node positionA pos_result neg_result)

        | positionA < positionB =
            intersectionLocal @Neg1 c neg_childA b
        | positionA > positionB =
            intersectionLocal @Neg1 c a neg_childB

    intersectionLocal' c a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
        -- todo add posB == posA, then we consider node to be AllNegs -> [1]
        if positionA == positionB
            then
                undefined
            else
                Node positionB (Leaf False) (intersectionLocal @Neg1 c a neg_childB)
    intersectionLocal' c a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB _ _ _ _ _) =
        -- todo add posB == posA, then we consider node to be AllNegs -> [1]
        if positionA == positionB
            then
                undefined
            else
                Node positionA (Leaf False) (intersectionLocal @Neg1 c neg_childA b)
    intersectionLocal' c a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = intersectionMain ((Neg1,Norm):c) a b

    -- continue local traversal
    intersectionLocal' c a@(Node positionA pos_childA neg_childA) b@(EndInfNode childB) = applyElimRule @Neg1 $ intersectionLocal @Neg1 c neg_childA b
    intersectionLocal' c a@(EndInfNode childA) b@(Node positionB pos_childB neg_childB) = applyElimRule @Neg1 $ intersectionLocal @Neg1 c a neg_childB
    -- continue previous super domain traversal
    intersectionLocal' (c:cs) a@(EndInfNode childA)  b@(EndInfNode childB) = EndInfNode $ intersectionLocal_arg c cs childA childB
    intersectionLocal' [] a@(EndInfNode childA)  b@(EndInfNode childB) = EndInfNode $ intersection @True [] childA childB

    intersectionLocal' c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = intersectionInferB ((Neg1,Norm):c) a b
    intersectionLocal' c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = intersectionInferA ((Neg1,Norm):c) a b
    intersectionLocal' c a b = error (show a ++ show b ++ show c)


    unionLocal c a b = if debugFlag then trace ("unionLocal neg1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) $ unionLocal' @Neg1 c a b else unionLocal' @Neg1 c a b
    unionLocal' c a (Leaf False) =  a
    unionLocal' c (Leaf False) b =  b

    -- comparing nodes, allowed mis-matches based on each inference rule
    unionLocal' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

        -- no mismatch, only the appropriate ZDD elim is applied
        | positionA == positionB =
            let pos_result = unionLocal @Neg1 c pos_childA pos_childB
                neg_result = unionLocal @Neg1 c neg_childA neg_childB
            in if pos_result == Leaf False then Leaf False else Node positionA pos_result neg_result

        -- mismatch, but with dc inference we continue recursion with the highest (thus lowest valued) node
        -- refactor into two functions? one for mixed inference rules, one for single
        | positionA < positionB =
            let neg_result = unionLocal @Neg1 c neg_childA b
            in Node positionA pos_childA neg_result

        | positionA > positionB =
            let neg_result = unionLocal @Neg1 c a neg_childB
            in Node positionB pos_childB neg_result

    unionLocal' c a@(InfNodes positionA _ _ _ _ _)  b@(Node positionB pos_childB neg_childB) =
        -- todo add posB == posA, then we consider node to be AllNegs -> [1]
        if positionA == positionB
            then
                undefined
            else
                Node positionB (Leaf False) (unionLocal @Neg1 c a neg_childB)

    unionLocal' c a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) =
        -- todo add posB == posA, then we consider node to be AllNegs -> [1]
        if positionA == positionB
            then
                undefined
            else
                Node positionA (Leaf False) (unionLocal @Neg1 c neg_childA b)
    unionLocal' c  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = unionMain ((Neg1,Norm):c) a b

    unionLocal' c a@(Node positionA pos_childA neg_childA) b@(EndInfNode _) = applyElimRule @Neg1 $ Node positionA pos_childA (unionLocal @Neg1 c neg_childA b)
    unionLocal' c a@(EndInfNode _) b@(Node positionB pos_childB neg_childB) = applyElimRule @Neg1 $ Node positionB pos_childB (unionLocal @Neg1 c a neg_childB)
    unionLocal' (c:cs) a@(EndInfNode childA) b@(EndInfNode childB) = EndInfNode $ unionLocal_arg c cs childA childB
    unionLocal' [] a@(EndInfNode childA)  b@(EndInfNode childB) = EndInfNode $ union @True [] childA childB

    unionLocal' c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = unionInferB ((Neg1,Norm):c) a b
    unionLocal' c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = unionInferA ((Neg1,Norm):c) a b
    unionLocal' c a b = error (show a ++ show b ++ show c)
{-}
    unionLocal c a@(InfNodes {}) (Leaf True) = error ""
    unionLocal c (Leaf True) b@(InfNodes {}) = error ""
    unionLocal c a@(EndInfNode {}) (Leaf True) = error ""
    unionLocal c (Leaf True) b@(EndInfNode {}) = error ""
    unionLocal _ (Leaf True) (Leaf True) = error ""-}

-- ======================= Mixed Intersections =================================================================

    absorb c a b = if debugFlag then trace ("absorb neg1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) $ absorb' @Neg1 c a b else absorb' @Neg1 c a b
    absorb' c (Leaf False) dc = Leaf False
    -- absorb c (Leaf True) dc@(Node positionD pos_childD neg_childD)  = absorb @Neg1 c (Leaf True) neg_childD
    absorb' c (EndInfNode a) dc@(Node positionD pos_childD neg_childD)  = absorb @Neg1 c (EndInfNode a) neg_childD
    absorb' c a@(Node positionA pos_childA neg_childA) (EndInfNode dc)  =
        let pos_result = absorb @Neg1 c pos_childA (EndInfNode dc)
            neg_result = absorb @Neg1 c neg_childA (EndInfNode dc)
        in applyElimRule @Neg1 (Node positionA pos_result neg_result)
    absorb' c a@(EndInfNode a') dc@(EndInfNode dc') = if negation a' == dc' then Leaf False else a

    absorb' c a@(Node positionA pos_childA neg_childA)  dc@(Node positionD pos_childD neg_childD)
        -- No mismatch
        | positionA == positionD =
            let pos_result = absorb @Neg1 c pos_childA pos_childD
                neg_result = absorb @Neg1 c neg_childA neg_childD
            in applyElimRule @Neg1 (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionD = absorb @Neg1 c a neg_childD
        | positionA < positionD =
            let pos_result = absorb @Neg1 c pos_childA dc
                neg_result = absorb @Neg1 c neg_childA dc
            in applyElimRule @Neg1 (Node positionA pos_result neg_result)

    absorb' c a@(InfNodes positionA dcA n1A n0A p1A p0A) dc@(Node positionD pos_childD neg_childD) = undefined -- todo add posB == posA, then we consider node to be AllNegs -> [1]
    absorb' c a@(Node positionA pos_childD neg_childD) dc@(InfNodes positionD dcA n1A n0A p1A p0A) = undefined

    absorb' c a@(InfNodes{}) b@(EndInfNode _) = intersectionInferB ((Neg1, Mixed):c) a b
    absorb' c a@(EndInfNode _) b@(InfNodes{}) = intersectionInferB ((Neg1, Mixed):c) a b
    absorb' c a b = error ""

    mixedIntersection c a b = if debugFlag then trace ("mixedIntersection neg1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) $ mixedIntersection' @Neg1 c a b else mixedIntersection' @Neg1 c a b
    mixedIntersection' c (Leaf False) b = Leaf False
    -- No leafs involved
    mixedIntersection' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

        -- No mismatch
        | positionA == positionB =
            let pos_result = mixedIntersection @Neg1 c pos_childA pos_childB
                neg_result = mixedIntersection @Neg1 c neg_childA neg_childB
            in applyElimRule @Neg1 (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionB = mixedIntersection @Neg1 c a neg_childB
        | positionA < positionB =
            let pos_result = mixedIntersection @Neg1 c pos_childA b
                neg_result = mixedIntersection @Neg1 c neg_childA b
            in applyElimRule @Neg1 (Node positionA pos_result neg_result)

    -- Single InfNode has been reached, similar to single Leaf node cases.
    mixedIntersection' c a@(Node positionA pos_childA neg_childA)  b@(EndInfNode{}) =
                let pos_result = mixedIntersection @Neg1 c pos_childA b
                    neg_result = mixedIntersection @Neg1 c neg_childA b
                in applyElimRule @Neg1 (Node positionA pos_result neg_result)

    mixedIntersection' c a@(EndInfNode _) b@(Node positionB pos_childB neg_childB) =
                mixedIntersection @Neg1 c a neg_childB

    -- Both InfNodes have been reached - run the usual intersection.
    mixedIntersection' (c:cs) (EndInfNode a)  (EndInfNode b) = EndInfNode $ intersectionLocal_arg c cs a b
    mixedIntersection' [] (EndInfNode a)  (EndInfNode b) = EndInfNode $ intersection @True [] a b
    mixedIntersection' c a b = undefined `debug` ("neg1 - " ++ show a ++ "  :  " ++ show b)




instance DdF4 Neg0 where
    applyElimRule d@(Node _ posC negC) = if posC == Leaf True then posC else d
    applyElimRule d@(InfNodes pos dcR n1R n0R p1R p0R) =
        if (n1R, dcR, p1R, p0R) == (Leaf False, Leaf True, Leaf False, Leaf True) then
                        (if isInfNode n0R then n0R else
                            if n0R == Leaf False then Leaf False else
                                if n0R == Leaf True then Leaf True else
                                    InfNodes pos dcR n1R n0R p1R p0R)
                        else InfNodes pos dcR n1R n0R p1R p0R
    applyElimRule d = d

    false = Leaf True
    true = Leaf False
    inferNodeA_intersection c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) =
        intersectionLocal @Neg0 c neg_childA b
    inferNodeA_intersection _ _ _ = undefined
    inferNodeB_intersection c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) =
        intersectionLocal @Neg0 c a neg_childB
    inferNodeB_intersection _ _ _ = undefined
    nextInfDomain c a b f = f((Neg0, Norm):c) a b
    intersectionInferB_ c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = intersectionInferB ((Neg0, Norm):c) a b
    intersectionInferB_ _ _ _ = undefined
    intersectionInferA_ c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = intersectionInferA ((Neg0, Norm):c) a b
    intersectionInferA_ _ _ _ = undefined

        -- Leaf and node
    unionLocal c a b = if debugFlag then trace ("unionLocal neg0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) $ unionLocal' @Neg0 c a b else unionLocal' @Neg0 c a b
    unionLocal' c a (Leaf True) = Leaf True
    unionLocal' c (Leaf True) b = Leaf True

    -- comparing nodes, allowed mis-matches based on each inference rule
    unionLocal' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
        -- match
        | positionA == positionB =
            let pos_result = unionLocal @Neg0 c pos_childA pos_childB
                neg_result = unionLocal @Neg0 c neg_childA neg_childB
            in applyElimRule @Neg0 (Node positionA pos_result neg_result)

        -- mismatch with no Bot involved, thus with ZDD types inference we return bot
        | positionA < positionB =
            unionLocal @Neg0 c neg_childA b
        | positionA > positionB =
            unionLocal @Neg0 c a neg_childB

    unionLocal' c a@(InfNodes positionA dcA n1A n0A p1A p0A) b@(Node positionB pos_childB neg_childB) =
    -- todo add posB == posA, then we consider node to be AllNegs -> [0]
        if positionA == positionB
            then
                undefined
            else
                Node positionB (Leaf True) (unionLocal @Neg0 c a neg_childB)
    unionLocal' c a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB _ _ _ _ _) =
    -- todo add posB == posA, then we consider node to be AllNegs -> [0]
        if positionA == positionB
            then
                undefined
            else
                Node positionA (Leaf True) (unionLocal @Neg0 c neg_childA b)

    unionLocal'  c a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = unionMain ((Neg0,Norm):c) a b

    unionLocal' c a@(Node positionA pos_childA neg_childA) b@(EndInfNode _) = applyElimRule @Neg0 $ Node positionA pos_childA (unionLocal @Neg0 c neg_childA b)
    unionLocal' c a@(EndInfNode _) b@(Node positionB pos_childB neg_childB) = applyElimRule @Neg0 $ Node positionB pos_childB (unionLocal @Neg0 c a neg_childB)
    unionLocal' (c:cs) a@(EndInfNode childA) b@(EndInfNode childB) = EndInfNode $ unionLocal_arg c cs childA childB
    unionLocal' [] a@(EndInfNode childA)  b@(EndInfNode childB) = EndInfNode $ union @False [] childA childB

    unionLocal' c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = unionInferB ((Neg0,Norm):c) a b
    unionLocal' c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = unionInferA ((Neg0,Norm):c) a b

    unionLocal' _ _ _ = error "how did we get here?"

    intersectionLocal c a b = if debugFlag then trace ("intersectionLocal neg0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) $ intersectionLocal' @Neg0 c a b else intersectionLocal' @Neg0 c a b
    intersectionLocal' c (Leaf True) b = b
    intersectionLocal' c a (Leaf True) = a

    -- comparing nodes, allowed mis-matches based on each inference rule
    intersectionLocal' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

        -- no mismatch, only the appropriate ZDD elim is applied
        | positionA == positionB =
            let pos_result = intersectionLocal @Neg0 c pos_childA pos_childB
                neg_result = intersectionLocal @Neg0 c neg_childA neg_childB
            in if pos_result == Leaf True then Leaf True else Node positionA pos_result neg_result

        -- mismatch, but with dc inference we continue recursion with the highest (thus lowest valued) node
        -- refactor into two functions? one for mixed inference rules, one for single
        | positionA < positionB =
            let neg_result = intersectionLocal @Neg0 c neg_childA b
            in Node positionA pos_childA neg_result

        | positionA > positionB =
            let neg_result = intersectionLocal @Neg0 c a neg_childB
            in Node positionB pos_childB neg_result

    intersectionLocal' c a@(InfNodes positionA _ _ _ _ _)  b@(Node positionB pos_childB neg_childB) =
    -- todo add posB == posA, then we consider node to be AllNegs -> [0]
        if positionA == positionB
            then
                undefined
            else
                Node positionB (Leaf True) (intersectionLocal @Neg0 c a neg_childB)

    intersectionLocal' c a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) =
    -- todo add posB == posA, then we consider node to be AllNegs -> [0]
        if positionA == positionB
            then
                undefined
            else
                Node positionA (Leaf True) (intersectionLocal @Neg0 c neg_childA b)

    intersectionLocal' c  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = intersectionMain ((Neg0,Norm):c) a b

    intersectionLocal' c a@(Node positionA pos_childA neg_childA) b@(EndInfNode _) = applyElimRule @Neg0 $ intersectionLocal @Neg0 c neg_childA b
    intersectionLocal' c a@(EndInfNode _) b@(Node positionB pos_childB neg_childB) = applyElimRule @Neg0 $ intersectionLocal @Neg0 c a neg_childB
    intersectionLocal' (c:cs) a@(EndInfNode childA) b@(EndInfNode childB) = EndInfNode $ intersectionLocal_arg c cs childA childB
    intersectionLocal' [] a@(EndInfNode childA)  b@(EndInfNode childB) = EndInfNode $ intersection @False [] childA childB

    intersectionLocal' c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = intersectionInferB ((Neg0,Norm):c) a b
    intersectionLocal' c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = intersectionInferA ((Neg0,Norm):c) a b
    intersectionLocal' c a b = error ""


    absorb c a b =  absorb' @Neg0 c a b
        `debug2` ("absorb neg0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)
    absorb' c (Leaf True) dc = Leaf True
    -- absorb c (Leaf True) dc@(Node positionD pos_childD neg_childD)  = absorb @Neg1 c (Leaf True) neg_childD
    absorb' c (EndInfNode a) dc@(Node positionD pos_childD neg_childD)  = absorb @Neg0 c (EndInfNode a) neg_childD
    absorb' c a@(Node positionA pos_childA neg_childA) (EndInfNode dc)  =
        let pos_result = absorb @Neg0 c pos_childA (EndInfNode dc)
            neg_result = absorb @Neg0 c neg_childA (EndInfNode dc)
        in applyElimRule @Neg0 (Node positionA pos_result neg_result)
    absorb' c a@(EndInfNode a') dc@(EndInfNode dc') = if a' == dc' then Leaf True else a

    absorb' c a@(Node positionA pos_childA neg_childA)  dc@(Node positionD pos_childD neg_childD)
        -- No mismatch
        | positionA == positionD =
            let pos_result = absorb @Neg0 c pos_childA pos_childD
                neg_result = absorb @Neg0 c neg_childA neg_childD
            in applyElimRule @Neg0 (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionD = absorb @Neg0 c a neg_childD
        | positionA < positionD =
            let pos_result = absorb @Neg0 c pos_childA dc
                neg_result = absorb @Neg0 c neg_childA dc
            in applyElimRule @Neg0 (Node positionA pos_result neg_result)

    absorb' c a@(InfNodes positionA dcA n1A n0A p1A p0A) dc@(Node positionD pos_childD neg_childD) = undefined -- todo add posB == posA, then we consider node to be AllNegs -> [0]
    absorb' c a@(Node positionA pos_childD neg_childD) dc@(InfNodes positionD dcA n1A n0A p1A p0A) = undefined

    absorb' c a@(InfNodes{}) b@(EndInfNode _) = intersectionInferB ((Neg0, Absorb):c) a b
    absorb' c a@(EndInfNode _) b@(InfNodes{}) = intersectionInferB ((Neg0, Absorb):c) a b

    absorb' c a b = error ""


    mixedIntersection c a b = if debugFlag then trace ("mixedIntersection neg0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) $ mixedIntersection' @Neg0 c a b else mixedIntersection' @Neg0 c a b
    mixedIntersection' c (Leaf True) b = Leaf True

    -- No leafs involved
    mixedIntersection' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

        -- No mismatch
        | positionA == positionB =
            let pos_result = mixedIntersection @Neg0 c pos_childA pos_childB
                neg_result = mixedIntersection @Neg0 c neg_childA neg_childB
            in applyElimRule @Neg0 (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionB = mixedIntersection @Neg0 c a neg_childB
        | positionA < positionB =
            let pos_result = mixedIntersection @Neg0 c pos_childA b
                neg_result = mixedIntersection @Neg0 c neg_childA b
            in applyElimRule @Neg0 (Node positionA pos_result neg_result)

    -- Single InfNode has been reached, similar to single Leaf node cases.
    mixedIntersection' c a@(Node positionA pos_childA neg_childA)  b@(EndInfNode _) =
                let pos_result = mixedIntersection @Neg0 c pos_childA b
                    neg_result = mixedIntersection @Neg0 c neg_childA b
                in applyElimRule @Neg0 (Node positionA pos_result neg_result)
    mixedIntersection' c a@(EndInfNode _) b@(Node positionB pos_childB neg_childB) =
                mixedIntersection @Neg0 c a neg_childB

    -- Both InfNodes have been reached - run the usual intersection.
    mixedIntersection' [] (EndInfNode a)  (EndInfNode b) = EndInfNode $  intersection @True [] a b
    mixedIntersection' (c:cs) (EndInfNode a)  (EndInfNode b) = EndInfNode $ intersectionLocal_arg c cs a b
    mixedIntersection' c a b = undefined `debug` ("neg0 - " ++ show a ++ "  :  " ++ show b)



instance DdF4 Pos1 where
    applyElimRule d@(Node _ posC negC) = if negC == Leaf False then negC else d
    applyElimRule d@(InfNodes pos dcR n1R n0R p1R p0R) =
        if (n1R, n0R, dcR, p0R) == (Leaf False, Leaf True, Leaf False, Leaf True) then
            (if isInfNode p1R then p1R else
                if p1R == Leaf False then Leaf False else
                    if p1R == Leaf True then Leaf True else
                        InfNodes pos dcR n1R n0R p1R p0R)
            else InfNodes pos dcR n1R n0R p1R p0R
    applyElimRule d = d

    false = Leaf False
    true = Leaf True
    inferNodeA_intersection c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) =
        intersectionLocal @Pos1 c pos_childA b
    inferNodeA_intersection _ _ _ = undefined
    inferNodeB_intersection c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) =
        intersectionLocal @Pos1 c a pos_childB
    inferNodeB_intersection _ _ _ = undefined
    nextInfDomain c a b f = f((Pos1, Norm):c) a b
    intersectionInferB_ c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = intersectionInferB ((Pos1, Norm):c) a b
    intersectionInferB_ _ _ _ = undefined
    intersectionInferA_ c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = intersectionInferA ((Pos1, Norm):c) a b
    intersectionInferA_ _ _ _ = undefined

    intersectionLocal c a b = if debugFlag then trace ("intersectionLocal pos1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) $ intersectionLocal' @Pos1 c a b else intersectionLocal' @Pos1 c a b
    -- Leaf and node
    intersectionLocal' c a (Leaf False) =  Leaf False
    intersectionLocal' c (Leaf False) b =  Leaf False

    -- comparing nodes, allowed mis-matches based on each inference rule
    intersectionLocal' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
        -- match
        | positionA == positionB =
            let pos_result = intersectionLocal @Pos1 c pos_childA pos_childB
                neg_result = intersectionLocal @Pos1 c neg_childA neg_childB
            in applyElimRule @Pos1 (Node positionA pos_result neg_result)

        -- mismatch with no Bot involved, thus with ZDD types inference we return bot
        | positionA < positionB =
            intersectionLocal @Pos1 c pos_childA b
        | positionA > positionB =
            intersectionLocal @Pos1 c a pos_childB

    intersectionLocal' c a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
        if positionA == positionB
            then
                undefined
            else
                Node positionB (Leaf False) (intersectionLocal @Pos1 c a pos_childB)
    intersectionLocal' c a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB _ _ _ _ _) =
        if positionA == positionB
            then
                undefined
            else
                Node positionA (Leaf False) (intersectionLocal @Pos1 c pos_childA b)

    intersectionLocal' c a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = intersectionMain ((Pos1,Norm):c) a b


    intersectionLocal' c a@(Node positionA pos_childA neg_childA) b@(EndInfNode _) = applyElimRule @Pos1 $ intersectionLocal @Pos1 c pos_childA b
    intersectionLocal' c a@(EndInfNode _) b@(Node positionB pos_childB neg_childB) = applyElimRule @Pos1 $ intersectionLocal @Pos1 c a pos_childB
    intersectionLocal' (c:cs) a@(EndInfNode childA) b@(EndInfNode childB) = EndInfNode $ intersectionLocal_arg c cs childA childB
    intersectionLocal' [] a@(EndInfNode childA)  b@(EndInfNode childB) = EndInfNode $ intersection @True [] childA childB

    intersectionLocal' c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = intersectionInferB ((Pos1,Norm):c) a b
    intersectionLocal' c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = intersectionInferA ((Pos1,Norm):c) a b
    intersectionLocal' c a b = error (show a ++ show b ++ show c)

    unionLocal c a b = if debugFlag then trace ("unionLocal pos1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) $ unionLocal' @Pos1 c a b else unionLocal' @Pos1 c a b
    unionLocal' c a (Leaf False) =  a
    unionLocal' c (Leaf False) b =  b

    -- comparing nodes, allowed mis-matches based on each inference rule
    unionLocal' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
        -- no mismatch, only the appropriate ZDD elim is applied
        | positionA == positionB =
            let pos_result = unionLocal @Pos1 c pos_childA pos_childB
                neg_result = unionLocal @Pos1 c neg_childA neg_childB
            in if neg_result == Leaf False then Leaf False else Node positionA pos_result neg_result

        -- mismatch, but with dc inference we continue recursion with the highest (thus lowest valued) node
        -- refactor into two functions? one for mixed inference rules, one for single
        | positionA < positionB =
            let pos_result = unionLocal @Pos1 c pos_childA b
            in Node positionA pos_result neg_childA
        | positionA > positionB =
            let pos_result = unionLocal @Pos1 c a pos_childB
            in Node positionB pos_result neg_childB
    unionLocal' c a@(InfNodes positionA _ _ _ _ _)  b@(Node positionB pos_childB neg_childB) =
        if positionA == positionB
            then
                undefined
            else
                Node positionB (unionLocal @Pos1 c a pos_childB) (Leaf False)
    unionLocal' c a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) =
        if positionA == positionB
            then
                undefined
            else
                Node positionA (unionLocal @Pos1 c pos_childA b) (Leaf False)
    unionLocal' c  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = unionMain ((Pos1,Norm):c) a b

    unionLocal' c a@(Node positionA pos_childA neg_childA) b@(EndInfNode _) = applyElimRule @Pos1 $ Node positionA (unionLocal @Pos1 c pos_childA b) neg_childA
    unionLocal' c a@(EndInfNode _) b@(Node positionB pos_childB neg_childB) = applyElimRule @Pos1 $ Node positionB (unionLocal @Pos1 c a pos_childB) neg_childB
    unionLocal' (c:cs) a@(EndInfNode childA) b@(EndInfNode childB) = EndInfNode $ unionLocal_arg c cs childA childB
    unionLocal' [] a@(EndInfNode childA)  b@(EndInfNode childB) = EndInfNode $ union @True [] childA childB

    unionLocal' c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = unionInferB ((Pos1,Norm):c) a b
    unionLocal' c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = unionInferA ((Pos1,Norm):c) a b

    unionLocal' c a b = error (show a ++ show b ++ show c)

    absorb c a b = absorb' @Pos1 c a b
        `debug2` ("absorb pos1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b)
    absorb' c (Leaf False) dc = Leaf False
    absorb' c (EndInfNode a) dc@(Node positionD pos_childD neg_childD)  = absorb @Pos1 c (EndInfNode a) pos_childD
    absorb' c a@(Node positionA pos_childA neg_childA) (EndInfNode dc)  =
        let pos_result = absorb @Pos1 c pos_childA (EndInfNode dc)
            neg_result = absorb @Pos1 c neg_childA (EndInfNode dc)
        in applyElimRule @Pos1 (Node positionA pos_result neg_result)
    absorb' c a@(EndInfNode a') dc@(EndInfNode dc') = if a' == dc' then Leaf False else a

    absorb' c a@(Node positionA pos_childA neg_childA)  dc@(Node positionD pos_childD neg_childD)
        -- No mismatch
        | positionA == positionD =
            let pos_result = absorb @Pos1 c pos_childA pos_childD
                neg_result = absorb @Pos1 c neg_childA neg_childD
            in applyElimRule @Pos1 (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionD = absorb @Pos1 c a pos_childD
        | positionA < positionD =
            let pos_result = absorb @Pos1 c pos_childA dc
                neg_result = absorb @Pos1 c neg_childA dc
            in applyElimRule @Pos1 (Node positionA pos_result neg_result)

    absorb' c a@(InfNodes positionA dcA n1A n0A p1A p0A) dc@(Node positionD pos_childD neg_childD) = undefined -- todo add posB == posA, then we consider node to be AllNegs -> [0]
    absorb' c a@(Node positionA pos_childD neg_childD) dc@(InfNodes positionD dcA n1A n0A p1A p0A) = undefined

    absorb' c a@(InfNodes{}) b@(EndInfNode _) = intersectionInferB ((Pos1, Absorb):c) a b
    absorb' c a@(EndInfNode _) b@(InfNodes{}) = intersectionInferB ((Pos1, Absorb):c) a b
    absorb' c a b = error (show c ++ ", "++ show a ++ ", " ++ show b)

    mixedIntersection c a b = if debugFlag then trace ("mixedIntersection pos1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) $ mixedIntersection' @Pos1 c a b else mixedIntersection' @Pos1 c a b
    mixedIntersection' c (Leaf False) a = Leaf False
    -- No leafs involved
    mixedIntersection' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

        -- No mismatch
        | positionA == positionB =
            let pos_result = mixedIntersection @Pos1 c pos_childA pos_childB
                neg_result = mixedIntersection @Pos1 c neg_childA neg_childB
            in applyElimRule @Pos1 (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionB = mixedIntersection @Pos1 c a pos_childB
        | positionA < positionB =
            let pos_result = mixedIntersection @Pos1 c pos_childA b
                neg_result = mixedIntersection @Pos1 c neg_childA b
            in applyElimRule @Pos1 (Node positionA pos_result neg_result)

    -- Single InfNode has been reached, similar to single Leaf node cases.
    mixedIntersection' c a@(Node positionA pos_childA neg_childA)  b@(EndInfNode{}) =
                let pos_result = mixedIntersection @Pos1 c pos_childA b
                    neg_result = mixedIntersection @Pos1 c neg_childA b
                in applyElimRule @Pos1 (Node positionA pos_result neg_result)


    mixedIntersection' c a@(EndInfNode{}) b@(Node positionB pos_childB neg_childB) =
                mixedIntersection @Pos1 c a pos_childB

    mixedIntersection' [] (EndInfNode a)  (EndInfNode b) = EndInfNode $ intersection @True [] a b
    mixedIntersection' (c:cs) (EndInfNode a)  (EndInfNode b) = EndInfNode $ intersectionLocal_arg c cs a b

    mixedIntersection' c a b = undefined `debug` ("pos1" ++ show a ++ "  :  " ++ show b)


instance DdF4 Pos0 where
    applyElimRule d@(Node _ posC negC) = if negC == Leaf True then negC else d
    applyElimRule d@(InfNodes pos dcR n1R n0R p1R p0R) =
        if (n1R, n0R, p1R, dcR) == (Leaf False, Leaf True, Leaf False, Leaf True) then
                        (if isInfNode p0R then p0R else
                            if p0R == Leaf False then Leaf False else
                                if p0R == Leaf True then Leaf True else
                                    InfNodes pos dcR n1R n0R p1R p0R)
                        else InfNodes pos dcR n1R n0R p1R p0R
    applyElimRule d = d

    false = Leaf True
    true = Leaf False
    inferNodeA_intersection c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) =
        intersectionLocal' @Pos0 c neg_childA b
    inferNodeA_intersection _ _ _ = undefined
    inferNodeB_intersection c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) =
        intersectionLocal' @Pos0 c a neg_childB
    inferNodeB_intersection _ _ _ = undefined
    nextInfDomain c a b f = f((Pos0, Norm):c) a b

    intersectionInferB_ c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = intersectionInferB ((Pos0, Norm):c) a b
    intersectionInferB_ _ _ _ = undefined
    intersectionInferA_ c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = intersectionInferA ((Pos0, Norm):c) a b
    intersectionInferA_ _ _ _ = undefined
    unionInferB_ c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = unionInferB ((Pos0, Norm):c) a b
    unionInferB_ _ _ _ = undefined
    unionInferA_ c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = unionInferA ((Pos0, Norm):c) a b
    unionInferA_ _ _ _ = undefined

    -- Leaf and node
    unionLocal c a b = if debugFlag then trace ("unionLocal pos0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) $ unionLocal' @Pos0 c a b else unionLocal' @Pos0 c a b
    unionLocal' c a (Leaf True) = Leaf True
    unionLocal' c (Leaf True) b = Leaf True

    --unionLocal c a@(InfNodes positionA _ _ _ _ _) (Leaf False) = a
    --unionLocal c (Leaf False) b@(InfNodes positionB _ _ _ _ _) = b

    -- comparing nodes, allowed mis-matches based on each inference rule
    unionLocal' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
        -- match
        | positionA == positionB =
            let pos_result = unionLocal @Pos0 c pos_childA pos_childB
                neg_result = unionLocal @Pos0 c neg_childA neg_childB
            in applyElimRule @Pos0 (Node positionA pos_result neg_result)

        -- mismatch with no Bot involved, thus with ZDD types inference we return bot
        | positionA < positionB =
            unionLocal @Pos0 c pos_childA b
        | positionA > positionB =
            unionLocal @Pos0 c a pos_childB

    unionLocal' c a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
        if positionA == positionB
            then
                undefined
            else
                Node positionB (Leaf True) (unionLocal @Pos0 c a pos_childB)
    unionLocal' c a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB _ _ _ _ _) =
        if positionA == positionB
            then
                undefined
            else
                Node positionA (Leaf True) (unionLocal @Pos0 c pos_childA b)

    unionLocal'  c a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = unionMain ((Pos0,Norm):c) a b

    unionLocal' c a@(Node positionA pos_childA neg_childA) b@(EndInfNode _) = applyElimRule @Pos0 $ Node positionA (unionLocal @Pos0 c pos_childA b) neg_childA -- todo double check this
    unionLocal' c a@(EndInfNode _) b@(Node positionB pos_childB neg_childB) = applyElimRule @Pos0 $ Node positionB (unionLocal @Pos0 c a pos_childB) neg_childB
    unionLocal' (c:cs) a@(EndInfNode childA)  b@(EndInfNode childB) = EndInfNode $ unionLocal_arg c cs childA childB
    unionLocal' [] a@(EndInfNode childA)  b@(EndInfNode childB) = EndInfNode $ union @False [] childA childB
    unionLocal' c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = unionInferB ((Pos0,Norm):c) a b
    unionLocal' c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = unionInferA ((Pos0,Norm):c) a b


    unionLocal' _ _ _ = error "how did we get here?"

    --unionLocal c a@(InfNodes positionA dcA n1A n0A p1A p0A) (Leaf True) = union @False c a (inferInfNode c True a)
    --unionLocal c (Leaf True) b@(InfNodes positionB dcB n1B n0B p1B p0B) = union @False c (inferInfNode c True b) b
    intersectionLocal c a b = if debugFlag then trace ("intersectionLocal pos0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) $ intersectionLocal' @Pos0 c a b else intersectionLocal' @Pos0 c a b
    intersectionLocal' c a (Leaf True) =  a
    intersectionLocal' c (Leaf True) b =  b

    -- comparing nodes, allowed mis-matches based on each inference rule
    intersectionLocal' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

        -- no mismatch, only the appropriate ZDD elim is applied
        | positionA == positionB =
            let pos_result = intersectionLocal @Pos0 c pos_childA pos_childB
                neg_result = intersectionLocal @Pos0 c neg_childA neg_childB
            in if neg_result == Leaf True then Leaf True else Node positionA pos_result neg_result

        -- mismatch, but with dc inference we continue recursion with the highest (thus lowest valued) node
        -- refactor into two functions? one for mixed inference rules, one for single
        | positionA < positionB =
            let pos_result = intersectionLocal @Pos0 c pos_childA b
            in Node positionA pos_result neg_childA

        | positionA > positionB =
            let pos_result = intersectionLocal @Pos0 c a pos_childB
            in Node positionB pos_result neg_childB

    intersectionLocal' c a@(InfNodes positionA _ _ _ _ _)  b@(Node positionB pos_childB neg_childB) =
        if positionA == positionB
            then
                undefined
            else
                Node positionB (intersectionLocal @Pos0 c a pos_childB) (Leaf True)

    intersectionLocal' c a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) =
        if positionA == positionB
            then
                undefined
            else
                Node positionA (intersectionLocal @Pos0 c pos_childA b) (Leaf True)

    intersectionLocal' c a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = intersectionMain ((Pos0,Norm):c) a b

    intersectionLocal' c a@(Node positionA pos_childA neg_childA) b@(EndInfNode _) = applyElimRule @Pos0 $ intersectionLocal @Pos0 c pos_childA b
    intersectionLocal' c a@(EndInfNode _) b@(Node positionB pos_childB neg_childB) = applyElimRule @Pos0 $ intersectionLocal @Pos0 c pos_childB a
    intersectionLocal' (c:cs) a@(EndInfNode childA)  b@(EndInfNode childB) = EndInfNode $ intersectionLocal_arg c cs childA childB
    intersectionLocal' [] a@(EndInfNode childA)  b@(EndInfNode childB) = EndInfNode $ intersection @False [] childA childB

    intersectionLocal' c a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) = intersectionInferB ((Pos0,Norm):c) a b
    intersectionLocal' c a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) = intersectionInferA ((Pos0,Norm):c) a b

    intersectionLocal' c a b = error ""

    absorb c a b = if debugFlag then trace ("absorb pos0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) $ absorb' @Pos0 c a b else absorb' @Pos0 c a b
    absorb' c (Leaf True) dc = Leaf True
    absorb' c (EndInfNode a) dc@(Node positionD pos_childD neg_childD)  = absorb @Pos0 c (EndInfNode a) neg_childD
    absorb' c a@(Node positionA pos_childA neg_childA) (EndInfNode dc)  =
        let pos_result = absorb @Pos0 c pos_childA (EndInfNode dc)
            neg_result = absorb @Pos0 c neg_childA (EndInfNode dc)
        in applyElimRule @Pos0 (Node positionA pos_result neg_result)
    absorb' c a@(EndInfNode _) dc@(EndInfNode _) = if a == dc then Leaf True else a -- todo elim endinfnodes

    absorb' c a@(Node positionA pos_childA neg_childA)  dc@(Node positionD pos_childD neg_childD)
        -- No mismatch
        | positionA == positionD =
            let pos_result = absorb @Pos0 c pos_childA pos_childD
                neg_result = absorb @Pos0 c neg_childA neg_childD
            in applyElimRule @Pos0 (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionD = absorb @Pos0 c a neg_childD
        | positionA < positionD =
            let pos_result = absorb @Pos0 c pos_childA dc
                neg_result = absorb @Pos0 c neg_childA dc
            in applyElimRule @Pos0 (Node positionA pos_result neg_result)

    absorb' c a@(InfNodes positionA dcA n1A n0A p1A p0A) dc@(Node positionD pos_childD neg_childD) = undefined -- todo add posB == posA, then we consider node to be AllNegs -> [0]
    absorb' c a@(Node positionA pos_childD neg_childD) dc@(InfNodes positionD dcA n1A n0A p1A p0A) = undefined

    absorb' c a@(InfNodes{}) b@(EndInfNode _) = intersectionInferB ((Pos0, Absorb):c) a b
    absorb' c a@(EndInfNode _) b@(InfNodes{}) = intersectionInferB ((Pos0, Absorb):c) a b
    absorb' c a b = error ""

    --mixedIntersection c a (Leaf False) = Leaf True
    --mixedIntersection c a (Leaf True) = a
    mixedIntersection c a b = if debugFlag then trace ("mixedIntersection: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) $ mixedIntersection' @Pos0 c a b else mixedIntersection' @Pos0 c a b
    mixedIntersection' c (Leaf True) b = Leaf True
    mixedIntersection' c a@(EndInfNode{}) b@(Node positionB pos_childB neg_childB)  = mixedIntersection @Pos0 c a neg_childB
    mixedIntersection' c a@(EndInfNode{}) b@(InfNodes {}) = undefined

    -- No leafs involved
    mixedIntersection' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

        -- No mismatch
        | positionA == positionB =
            let pos_result = mixedIntersection @Pos0 c pos_childA pos_childB
                neg_result = mixedIntersection @Pos0 c neg_childA neg_childB
            in applyElimRule @Pos0 (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionB = mixedIntersection @Pos0 c a pos_childB
        | positionA < positionB =
            let pos_result = mixedIntersection @Pos0 c pos_childA b
                neg_result = mixedIntersection @Pos0 c neg_childA b
            in applyElimRule @Pos0 (Node positionA pos_result neg_result)

    -- Single InfNode has been reached, similar to single Leaf node cases.
    mixedIntersection' c a@(Node positionA pos_childA neg_childA)  b@(EndInfNode{}) =
                let pos_result = mixedIntersection @Pos0 c pos_childA b
                    neg_result = mixedIntersection @Pos0 c neg_childA b
                in applyElimRule @Pos0 (Node positionA pos_result neg_result)


    -- Both InfNodes have been reached - run the usual intersection.
    mixedIntersection' [] (EndInfNode a)  (EndInfNode b) = EndInfNode $ intersection @False [] a b
    mixedIntersection' (c:cs) (EndInfNode a)  (EndInfNode b) = EndInfNode $ intersectionLocal_arg c cs a b
    mixedIntersection' c a b = undefined `debug` ("pos0 - " ++ show a ++ "  :  " ++ show b)











remove_f0s1_from_f1s1 c a b = if debugFlag then trace ("remove_f0s1_from_f1s1: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) remove_f0s1_from_f1s1' c a b else remove_f0s1_from_f1s1' c a b
remove_f0s1_from_f1s1' :: FuncCtx -> Dd -> Dd -> Dd
remove_f0s1_from_f1s1' c a (Leaf False) = Leaf False
remove_f0s1_from_f1s1' c (Leaf True) b = b
remove_f0s1_from_f1s1' c a@(InfNodes {}) (Leaf True) = a
remove_f0s1_from_f1s1' c (Leaf False) (Leaf True) = Leaf False

remove_f0s1_from_f1s1' c a@(Node positionA pos_childA neg_childA) b@(EndInfNode d) = remove_f0s1_from_f1s1 c neg_childA b
remove_f0s1_from_f1s1' c a@(EndInfNode d) b@(Node positionB pos_childB neg_childB) = Node positionB pos_childB (remove_f0s1_from_f1s1 c a neg_childB)
remove_f0s1_from_f1s1' c (EndInfNode a) (EndInfNode b) = applyInfElimRule @True $ intersection @True c (negation a) b

-- No leafs involved
remove_f0s1_from_f1s1' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)-- no mismatch, thus no inference is needed

    -- No mismatch, only the appropriate ZDD elim is applied
    | positionA == positionB =
        let pos_result = remove_f0s1_from_f1s1 c pos_childA pos_childB
            neg_result = remove_f0s1_from_f1s1 c neg_childA neg_childB
        in applyElimRule @Neg1 (Node positionA pos_result neg_result)

    -- mismatch with no Bot involved, thus with ZDD types inference we return bot
    | positionA < positionB =
        remove_f0s1_from_f1s1 c neg_childA b
    | positionA > positionB =
        Node positionB pos_childB (remove_f0s1_from_f1s1 c a neg_childB)


remove_f0s1_from_f1s1' c a@(Node positionA pos_childA neg_childA)  b@(InfNodes{}) = undefined -- todo define inner recursion for lobsided intersectio/union: (-. a .^. b)?
remove_f0s1_from_f1s1' c a@(InfNodes{}) b@(Node positionB pos_childB neg_childB) = undefined
remove_f0s1_from_f1s1' c a@(InfNodes{}) b@(EndInfNode d) = undefined
remove_f0s1_from_f1s1' c a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B) = undefined
remove_f0s1_from_f1s1' c a b = undefined `debug` (show a ++ "  :  " ++ show b)


remove_f1s1_from_f0s1 c a b = if debugFlag then trace ("remove_f1s0_from_f0s0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) remove_f1s1_from_f0s1' c a b else remove_f1s1_from_f0s1' c a b
remove_f1s1_from_f0s1' :: FuncCtx -> Dd -> Dd -> Dd
remove_f1s1_from_f0s1' c a (Leaf True) = Leaf True
remove_f1s1_from_f0s1' c (Leaf False) b = b
remove_f1s1_from_f0s1' c a@(InfNodes {}) (Leaf False) = a
remove_f1s1_from_f0s1' c (Leaf True) (Leaf False) = Leaf True

remove_f1s1_from_f0s1' c a@(Node positionA pos_childA neg_childA) (Leaf False) = remove_f1s1_from_f0s1 c neg_childA (Leaf False)
remove_f1s1_from_f0s1' c a@(EndInfNode d) b@(Node positionB pos_childB neg_childB) = Node positionB pos_childB (remove_f1s1_from_f0s1 c a neg_childB) --if pos_child == Leaf False then pos_child else b@(Node positionB pos_childB neg_childB)
remove_f1s1_from_f0s1' c (EndInfNode a) (EndInfNode b) = applyInfElimRule @False $ intersection @True c (negation a) b -- todo apply elim rule on the EndInfNode, which could eliminate the @True parameter

-- No leafs involved
remove_f1s1_from_f0s1' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)-- no mismatch, thus no inference is needed

    -- No mismatch, only the appropriate ZDD elim is applied
    | positionA == positionB =
        let pos_result = remove_f1s1_from_f0s1 c pos_childA pos_childB
            neg_result = remove_f1s1_from_f0s1 c neg_childA neg_childB
        in applyElimRule @Neg0 (Node positionA pos_result neg_result)

    -- mismatch with no Bot involved, thus with ZDD types inference we return bot
    | positionA < positionB =
        remove_f1s1_from_f0s1 c neg_childA b
    | positionA > positionB =
        Node positionB pos_childB (remove_f1s1_from_f0s1 c a neg_childB)


remove_f1s1_from_f0s1' c a@(Node positionA pos_childA neg_childA)  b@(InfNodes{}) = undefined -- todo define inner recursion for lobsided intersectio/union: (-. a .^. b)?
remove_f1s1_from_f0s1' c a@(InfNodes{}) b@(Node positionB pos_childB neg_childB) = undefined
remove_f1s1_from_f0s1' c a@(InfNodes{}) b@(EndInfNode d) = undefined
remove_f1s1_from_f0s1' c a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B) = undefined
remove_f1s1_from_f0s1' c a b = undefined `debug` (show a ++ "  :  " ++ show b)


remove_f0s0_from_f1s0 c a b = if debugFlag then trace ("remove_f0s0_from_f1s0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) remove_f0s0_from_f1s0' c a b else remove_f0s0_from_f1s0' c a b

remove_f0s0_from_f1s0' :: FuncCtx -> Dd -> Dd -> Dd
remove_f0s0_from_f1s0' c a (Leaf False) = Leaf False
remove_f0s0_from_f1s0' c (Leaf True) b = b
remove_f0s0_from_f1s0' c a@(InfNodes {}) (Leaf True) = a
remove_f0s0_from_f1s0' c (Leaf False) (Leaf True) = Leaf False

remove_f0s0_from_f1s0' c a@(Node positionA pos_childA neg_childA) b@(EndInfNode d) = remove_f0s0_from_f1s0 c pos_childA b
remove_f0s0_from_f1s0' c a@(EndInfNode d) b@(Node positionB pos_childB neg_childB) = Node positionB (remove_f0s0_from_f1s0 c a pos_childB) neg_childB  --if pos_child == Leaf False then pos_child else b@(Node positionB pos_childB neg_childB)
remove_f0s0_from_f1s0' c (EndInfNode a) (EndInfNode b) = applyInfElimRule @True $ intersection @True c (negation a) b

-- No leafs involved
remove_f0s0_from_f1s0' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)-- no mismatch, thus no inference is needed

    -- No mismatch, only the appropriate ZDD elim is applied
    | positionA == positionB =
        let pos_result = remove_f0s0_from_f1s0 c pos_childA pos_childB
            neg_result = remove_f0s0_from_f1s0 c neg_childA neg_childB
        in applyElimRule @Pos1 (Node positionA pos_result neg_result)

    -- mismatch with no Bot involved, thus with ZDD types inference we return bot
    | positionA < positionB =
        remove_f0s0_from_f1s0 c pos_childA b
    | positionA > positionB =
        Node positionB (remove_f0s0_from_f1s0 c a pos_childB) neg_childB


remove_f0s0_from_f1s0' c a@(Node positionA pos_childA neg_childA)  b@(InfNodes{}) = undefined -- todo define inner recursion for lobsided intersectio/union: (-. a .^. b)?
remove_f0s0_from_f1s0' c a@(InfNodes{}) b@(Node positionB pos_childB neg_childB) = undefined
remove_f0s0_from_f1s0' c a@(InfNodes{}) b@(EndInfNode d) = undefined
remove_f0s0_from_f1s0' c a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B) = undefined
remove_f0s0_from_f1s0' c a b = undefined `debug` (show a ++ "  :  " ++ show b)



remove_f1s0_from_f0s0 c a b = if debugFlag then trace ("remove_f1s0_from_f0s0: " ++ show c ++ " ; " ++ show a ++ " ; "  ++ show b) remove_f1s0_from_f0s0' c a b else remove_f1s0_from_f0s0' c a b
remove_f1s0_from_f0s0' :: FuncCtx -> Dd -> Dd -> Dd
remove_f1s0_from_f0s0' c a (Leaf True) = Leaf True
remove_f1s0_from_f0s0' c (Leaf False) b = b
remove_f1s0_from_f0s0' c a@(InfNodes {}) (Leaf False) = a
remove_f1s0_from_f0s0' c (Leaf True) (Leaf False) = Leaf True

remove_f1s0_from_f0s0' c a@(Node positionA pos_childA neg_childA) (Leaf False) = remove_f1s0_from_f0s0 c pos_childA (Leaf False)
remove_f1s0_from_f0s0' c a@(EndInfNode d) b@(Node positionB pos_childB neg_childB) = Node positionB (remove_f1s0_from_f0s0 c a pos_childB) neg_childB  --if pos_child == Leaf False then pos_child else b@(Node positionB pos_childB neg_childB)
remove_f1s0_from_f0s0' c (EndInfNode a) (EndInfNode b)  =  applyInfElimRule @False $ intersection  @True c (negation a) b

-- No leafs involved
remove_f1s0_from_f0s0' c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)-- no mismatch, thus no inference is needed

    -- No mismatch, only the appropriate ZDD elim is applied
    | positionA == positionB =
        let pos_result = remove_f1s0_from_f0s0 c pos_childA pos_childB
            neg_result = remove_f1s0_from_f0s0 c neg_childA neg_childB
        in applyElimRule @Pos0 (Node positionA pos_result neg_result)

    -- mismatch with no Bot involved, thus with ZDD types inference we return bot
    | positionA < positionB =
        remove_f1s0_from_f0s0 c pos_childA b
    | positionA > positionB =
        Node positionB (remove_f1s0_from_f0s0 c a pos_childB) neg_childB


remove_f1s0_from_f0s0' c a@(Node positionA pos_childA neg_childA)  b@(InfNodes{}) = undefined -- todo define inner recursion for lobsided intersectio/union: (-. a .^. b)?
remove_f1s0_from_f0s0' c a@(InfNodes{}) b@(Node positionB pos_childB neg_childB) = undefined
remove_f1s0_from_f0s0' c a@(InfNodes{}) b@(EndInfNode d) = undefined
remove_f1s0_from_f0s0' c a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B) = undefined
remove_f1s0_from_f0s0' c a b = undefined `debug` (show a ++ "  :  " ++ show b)



debug :: c -> String -> c
debug f s = (flip trace f) s


debug2 :: a -> String -> a
debug2 f s = if debugFlag then trace (colorize s) f else f

colorize :: String -> String
colorize s = setSGRCode [SetColor Foreground Vivid Red] ++ s ++ setSGRCode [Reset]

--tr :: FuncCtx -> Dd -> Dd -> Dd
--tr