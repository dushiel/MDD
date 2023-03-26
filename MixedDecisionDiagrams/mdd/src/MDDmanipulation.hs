{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module MDDmanipulation where

import MDD
import Debug.Trace (trace)
import Data.Kind
import Data.List (foldl', dropWhileEnd)

-- todo continue local traversal with children and popped ontext when EndIfnode with EndIfnode is encountered

-- todo finish with Neg0, Pos variants and BDD
-- todo do also the other functions
-- todo shift the contexts: stack current only when diving deeper, not when starting.

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


type DdF4 :: Inf -> Constraint
type DdF2 :: Bool -> Constraint

class DdF2 a where
    restrict :: forall a . Dd -> Bool -> Ordinal -> Dd
    restrictSet :: forall a . Dd -> [(Ordinal, Bool)] -> Dd
    restrictGen :: forall a . Dd -> [((Ordinal, Ordinal), Bool)] -> Dd
    intersection :: forall a . Context -> Dd -> Dd  -> Dd
    union :: forall a . Context -> Dd -> Dd  -> Dd


instance DdF2 True where
    restrict d@(Leaf False) b n = Leaf False
    restrict d@(Leaf True) b n = if b then makeNode n Dc else negation $ makeNode n Dc
    restrict d b n = restrictMain d b n
    restrictSet d@(Leaf False) ((n, b) : ns) = Leaf False
    restrictSet d@(Leaf True) ((n, b) : ns) = if b
        then restrictSet @True (makeNode n Dc) ns
        else negation $ restrictSet @True (makeNode n Dc) ns
    restrictSet d b = restrictSetMain d b
    -- make a check/case for a finite distance or infinite distance, such that rGen dc with inf distance become a Neg1/etc
    -- similarly there should be a precheck for Neg1/etc such that we can immediatly rule out if neccessary.
    -- we can do this on the inf level.
    -- restrictGen d@(Leaf False) (((n1, n2), b) : ns) = Leaf False
    -- restrictGen d@(Leaf True) (((n1, n2), b) : ns) = if b
    --     then restrictGen @True (makePath n Dc) ns -- function that extracts local list?
    --     else negation $ restrictGen @True (makeNode n Dc) ns
    -- restrictGen d b = restrictGenMain d b

    intersection c a (Leaf False) = Leaf False
    intersection c (Leaf False) b = Leaf False
    intersection c a (Leaf True) = a
    intersection c (Leaf True) b = b
    intersection c a b = intersectionMain c a b
    union c a (Leaf True) = Leaf True
    union c (Leaf True) b = Leaf True
    union c a (Leaf False) = a
    union c (Leaf False) b = b
    union c a b = unionMain c a b



instance DdF2 False where
    restrict d@(Leaf False) b n = if b then makeNode n Dc else negation $ makeNode n Dc
    restrict d@(Leaf True) b n = Leaf True
    restrict d b n = restrictMain d b n
    restrictSet d@(Leaf False) ((n, b) : ns) = if b then
        restrictSet @False (makeNode n Dc) ns
        else negation $ restrictSet @False (makeNode n Dc) ns
    restrictSet d@(Leaf True) ((n, b) : ns) = Leaf True
    restrictSet d b = restrictSetMain d b
    intersection c a (Leaf True) = Leaf True
    intersection c (Leaf True) b = Leaf True
    intersection c a (Leaf False) = a
    intersection c (Leaf False) b = b
    intersection c a b = intersectionMain c a b
    union c a (Leaf False) = Leaf False
    union c (Leaf False) b = Leaf False
    union c a (Leaf True) = a
    union c (Leaf True) b = b
    union c a b = unionMain c a b










negation :: Dd -> Dd
negation (Node position pos_child neg_child) = Node position (negation pos_child) (negation neg_child)
negation (InfNodes position dc_n n1_n n0_n p1_n p0_n) = InfNodes position (negation dc_n) (negation n0_n) (negation n1_n) (negation p0_n) (negation p1_n)
negation (EndInfNode position a) = EndInfNode position (negation a)
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


intersectionLocal_arg :: Inf -> Context -> Dd -> Dd -> Dd
intersectionLocal_arg Dc c a b = intersectionLocal @Dc c a b
intersectionLocal_arg Neg1 c a b = intersectionLocal @Neg1 c a b
intersectionLocal_arg Neg0 c a b = intersectionLocal @Neg0 c a b
intersectionLocal_arg Pos1 c a b = intersectionLocal @Pos1 c a b
intersectionLocal_arg Pos0 c a b = intersectionLocal @Pos0 c a b

unionLocal_arg :: Inf -> Context -> Dd -> Dd -> Dd
unionLocal_arg Dc c a b = unionLocal @Dc c a b
unionLocal_arg Neg1 c a b = unionLocal @Neg1 c a b
unionLocal_arg Neg0 c a b = unionLocal @Neg0 c a b
unionLocal_arg Pos1 c a b = unionLocal @Pos1 c a b
unionLocal_arg Pos0 c a b = unionLocal @Pos0 c a b

restrictMain :: Dd -> Bool -> Ordinal -> Dd
restrictMain d@(InfNodes position dc n1 n0 p1 p0) b n = let
        dcR = restrictLocal @Dc dc b n
        n1R = restrictLocal @Neg1 n1 b n
        n0R = restrictLocal @Neg0 n0 b n
        p1R = restrictLocal @Pos1 p1 b n
        p0R = restrictLocal @Pos0 p0 b n
        in applyElimRule @Dc (InfNodes position dcR n1R n0R p1R p0R)
restrictMain _ _ _ = error "restrictMain"

restrictSetMain :: Dd -> [(Ordinal, Bool)] -> Dd
restrictSetMain d@(InfNodes position dc n1 n0 p1 p0) bs = let
        dcR = restrictSetLocal @Dc dc bs
        n1R = restrictSetLocal @Neg1 n1 bs
        n0R = restrictSetLocal @Neg0 n0 bs
        p1R = restrictSetLocal @Pos1 p1 bs
        p0R = restrictSetLocal @Pos0 p0 bs
        in applyElimRule @Dc (InfNodes position dcR n1R n0R p1R p0R)
restrictSetMain _ _ = error "restrictMain"


-- to keep track of what inference should be used on what (ordinal) level, we add it to a stack called the context.
-- whenever we meet a (inf)node which is domains ahead of the other (inf)node, we need to infer not only the nodes but also the infnodes in between.
-- currently we only infer Dc infnodes (Top), but it makes sense to infer allNeg for n1, allPos for p1, and their complements for their complements.
-- e.g. : [0,0,1] | [0,0,1] | [Neg1,Dc,Neg1] => [0,0,2] | [1,0,1], means to infer [0,0,2]B as neg, then to pass Dc for both and then infer [1,0,1]A as neg, which means to infer [1,0,0] as all neg infnode

-- [0,0,1] | [0,0,1]
-- [0,0,2] | [1,0,1]
-- do we have to check on what level the change is?
-- [2,0,2] | [1,0,1]
-- no there has to be an infnode for each change in top level, thus we can pop the context
-- although if it were just [1] or [1,0,0] as a node, then we need to remove the trailing 0's
-- todo and trim (by popping) the context to the same size
-- is there a method to do this without checking the sizes of the nodes for each step?
-- we can always have trailing 0s removed/inferred
-- there is always an infnode before a new class of nodes with semi recursive-MDDs (such that nodes and infnodes are never on the same level)

len :: Ordinal -> Int
len (Order l) = length l

lastN' :: Int -> [a] -> [a]
lastN' n xs = foldl' (const . drop 1) xs (drop n xs)

matchingInit :: Ordinal -> Ordinal -> Context -> (([Int], [Int]), [Inf])
matchingInit (Order a) (Order b) c = (loop a b [], lastN' (length $ fst $ loop a b []) c) where
    loop [] [] r = (r, [])
    loop a [] r = (r, [])
    loop [] b r = (r, b)
    loop (a: as) (b : bs) r = if a==b then loop as bs (a : r) else (r, b: bs)


-- builds an inf node leading to Dd a, where it conains the shared prefix,
-- then appended with inferred infnodes (depending on the last shared ) to the length of b
--
-- todo, optimise where this function is called.. i think not all infnodes have to be inferred if their result can immedialty be inferred
addInfNodes :: Dd -> (([Int], [Int]), [Inf]) -> Dd
addInfNodes conseq ((pref, diff), c)  = loop pref c diff where
    loop preffix (inf:cs) [n] =
        case inf of -- only for Dc we need to check the b, since after a hole we interpret the following sub domains in substance (1-set)
            Dc -> InfNodes (Order $ preffix ++ [n]) conseq (Leaf False) (Leaf True) (Leaf False) (Leaf True)
            Neg1 -> InfNodes (Order $ preffix ++ [n]) (Leaf False) conseq (Leaf True) (Leaf False) (Leaf True)
            Neg0 -> InfNodes (Order $ preffix ++ [n]) (Leaf True) (Leaf False) conseq (Leaf False) (Leaf True)
            Pos1 -> InfNodes (Order $ preffix ++ [n]) (Leaf False) (Leaf False) (Leaf True) conseq (Leaf True)
            Pos0 -> InfNodes (Order $ preffix ++ [n]) (Leaf True) (Leaf False) (Leaf True) (Leaf False) conseq
    loop preffix (inf:cs) (n:ns) =
        case inf of
            Dc -> InfNodes (Order $ preffix ++ [n]) (loop (preffix ++ [n]) (Dc:inf:cs) ns) (Leaf False) (Leaf True) (Leaf False) (Leaf True)
            Neg1 -> InfNodes (Order $ preffix ++ [n]) (Leaf False) (loop (preffix ++ [n]) (Dc:inf:cs) ns) (Leaf False) (Leaf False) (Leaf True)
            Neg0 -> InfNodes (Order $ preffix ++ [n]) (Leaf True) (Leaf False) (loop (preffix ++ [n]) (Dc:inf:cs) ns) (Leaf False) (Leaf True)
            Pos1 -> InfNodes (Order $ preffix ++ [n]) (Leaf False) (Leaf False) (Leaf True) (loop (preffix ++ [n]) (Dc:inf:cs) ns) (Leaf True)
            Pos0 -> InfNodes (Order $ preffix ++ [n]) (Leaf True) (Leaf False) (Leaf True) (Leaf True) (loop (preffix ++ [n]) (Dc:inf:cs) ns)

-- addInfNodes a $ matchingInit positionA positionB c

{-inferInfNode :: Context -> Bool -> Ordinal -> Dd -> Dd
inferInfNode c bool a b@(InfNodes positionB _ _ _ _ _) = let c = lastN' (len positionB) c in-- replace all the A stuf with (dc: a, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
        case inf of
            Dc -> InfNodes positionB (Leaf bool) (Leaf False) (Leaf True) (Leaf False) (Leaf True)
            -- todo go in depth also with Dc.. where else is this the case?
            -- check all Leaf node resulting cases
            Neg1 -> InfNodes positionB (Leaf $ not bool) (Leaf bool) (Leaf $ not bool) (Leaf False) (Leaf True)
            Neg0 -> InfNodes positionB (Leaf bool) (Leaf $ not bool) (Leaf bool) (Leaf False) (Leaf True)
            Pos1 -> InfNodes positionB (Leaf $ not bool) (Leaf False) (Leaf True) (Leaf $ not bool) (Leaf bool)
            Pos0 -> InfNodes positionB (Leaf bool) (Leaf False) (Leaf True) (Leaf bool) (Leaf $ not bool)
inferInfNode c bool a b@(Node positionB _ _ ) = error ("Node, in infInference: " ++ show c ++ show bool ++ show a ++ show b ++ show (lastN' (len positionB) c))
inferInfNode c bool a (Leaf b) = error ("Leaf: " ++ show b)-}


intersectionMain :: Context -> Dd -> Dd -> Dd
intersectionMain  c@(inf:_) a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B)
    | positionA == positionB =  let
        dcR = intersectionLocal @Dc c dcA dcB `debug` ("intersection A ("++ show positionA ++ ")==B (" ++ show positionB ++ "), with c = " ++ show c)

        n1R = unionLocal @Neg1 c
            (intersectionLocal @Neg1 c n1A n1B) -- overlapping points are by definition not inside the others dc, thus have to be preserved
            (if n0R' == Leaf True then n1R' else remove_f0s1_from_f1s1 c n0R' n1R') -- holes absorb points under intersection
        n1R' = unionLocal @Neg1 c -- guaranteed that dcA and dcB do not overlap around the finite points, thus they do not get absorbed
            (mixedIntersection @Neg1 c n1A dcB dcR) -- keep the points that fit inside B
            (mixedIntersection @Neg1 c n1B dcA dcR) -- keep the points that fit inside A

        n0R' = unionLocal @Neg0 c n0A n0B -- holes get unioned, because i keep the consequence of holes "uncomplemented" we get local union then intersection.
        n0R = mixedIntersection2 @Neg0 c n0R' dcR -- keep the holes that fit inside dcR
        -- if the local hole fits inside dcR but the consequence of n0R' does not fit inside the consequenc of dcR it should return n0R' -> Leaf false
        ------------------------------------
        p1R = unionLocal @Pos1 c
            (intersectionLocal @Pos1 c p1A p1B)
            (if p0R' == Leaf True then p1R' else remove_f0s0_from_f1s0 c p0R' p1R')
        p1R' = unionLocal @Pos1 c
            (mixedIntersection @Pos1 c p1A dcB dcR)
            (mixedIntersection @Pos1 c p1B dcA dcR)
        p0R' = unionLocal @Pos0 c p0A p0B -- local union then intersection
        p0R = mixedIntersection2 @Pos0 c p0R' dcR

        in applyElimRule @Dc $ InfNodes positionA dcR n1R n0R p1R p0R

    | positionA > positionB =
        case inf of
            Dc -> let -- replace all the A stuf with (dc: a, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
                dcR = intersectionLocal @Dc c a dcB
                n1R = (if n0B == Leaf True then
                    mixedIntersection @Neg1 c n1B a dcR  else
                    remove_f0s1_from_f1s1 c n0B (mixedIntersection @Neg1 c n1B a dcR))
                n0R = mixedIntersection2 @Neg0 c n0B dcR --`debug` ( "inter: " ++ show (mixedIntersection2 @Neg0 c n0A dcR) ++ "\n n0A: " ++ show n0A  ++ "\n dcR" ++ show dcR)
                p1R = if p0B == Leaf True then
                    mixedIntersection @Pos1 c p1B a dcR else
                    remove_f0s0_from_f1s0 c p0B (mixedIntersection @Pos1 c p1B a dcR)
                p0R = mixedIntersection2 @Pos0 c p0B dcR
                in applyElimRule @Dc $ InfNodes positionB dcR n1R n0R p1R p0R

            Neg1 -> let -- replace all the A stuf with (dc: 0, neg1: a, neg0: 1, pos1: 0, pos0: 1)
                n1R = unionLocal @Neg1 c
                    (intersectionLocal @Neg1 c a n1B)
                    (if n0B == Leaf True then n1R' else remove_f0s1_from_f1s1 c n0B n1R')
                n1R' = mixedIntersection2 @Neg1 c a dcB
                in applyElimRule @Neg1 $ InfNodes positionB (Leaf False) n1R (Leaf True) (Leaf False) (Leaf True)
            Neg0 -> let -- replace all the A stuf with (dc: 1, neg1: 0, neg0: a, pos1: 0, pos0: 1)
                n0R' = unionLocal @Neg0 c a n0B
                n0R = mixedIntersection2 @Neg0 c n0R' dcB
                in applyElimRule @Neg0 $ InfNodes positionB dcB (Leaf False) n0R (Leaf False) (Leaf True)
            Pos1 -> let -- replace all the A stuf with (dc: 0, neg1: 0, neg0: 1, pos1: a, pos0: 1)
                p1R = unionLocal @Pos1 c
                    (intersectionLocal @Pos1 c a n1B)
                    (if n0B == Leaf True then p1R' else remove_f0s1_from_f1s1 c n0B p1R')
                p1R' = mixedIntersection2 @Pos1 c a dcB
                in applyElimRule @Pos1 $ InfNodes positionB (Leaf False) (Leaf False) (Leaf True) p1R (Leaf True)
            Pos0 -> let -- replace all the A stuf with (dc: 1, neg1: 0, neg0: a, pos1: 0, pos0: 1)
                p0R' = unionLocal @Pos0 c a p0B
                p0R = mixedIntersection2 @Pos0 c p0R' dcB
                in applyElimRule @Pos0 $ InfNodes positionB dcB (Leaf False) (Leaf True) (Leaf False) p0R



    | positionA < positionB = -- replace all the A stuf with (dc: a, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
        case inf of
            Dc -> let
                dcR = intersectionLocal @Dc c dcA b
                n1R = (if n0A == Leaf True then
                    mixedIntersection @Neg1 c n1A b dcR  else
                    remove_f0s1_from_f1s1 c n0A (mixedIntersection @Neg1 c n1A b dcR))
                n0R = mixedIntersection2 @Neg0 c n0A dcR
                p1R = if p0A == Leaf True then
                    mixedIntersection @Pos1 c p1A b dcR else
                    remove_f0s0_from_f1s0 c p0A (mixedIntersection @Pos1 c p1A b dcR)
                p0R = mixedIntersection2 @Pos0 c p0A dcR
                in applyElimRule @Dc $ InfNodes positionA dcR n1R n0R p1R p0R

            Neg1 -> let -- replace all the B stuf with (dc: 0, neg1: b, neg0: 1, pos1: 0, pos0: 1)
                n1R = unionLocal @Neg1 c
                    (intersectionLocal @Neg1 c n1A b)
                    (if n0A == Leaf True then n1R' else remove_f0s1_from_f1s1 c n0A n1R')
                n1R' = mixedIntersection2 @Neg1 c b dcA
                in applyElimRule @Neg1 $ InfNodes positionA (Leaf False) n1R (Leaf True) (Leaf False) (Leaf True)
            Neg0 -> let -- replace all the B stuf with (dc: 1, neg1: 0, neg0: b, pos1: 0, pos0: 1)
                n0R' = unionLocal @Neg0 c n0A b
                n0R = mixedIntersection2 @Neg0 c n0R' dcA
                in applyElimRule @Neg0 $ InfNodes positionA dcA (Leaf False) n0R (Leaf False) (Leaf True)
            Pos1 -> let -- replace all the B stuf with (dc: 0, neg1: 0, neg0: 1, pos1: b, pos0: 1)
                p1R = unionLocal @Pos1 c
                    (intersectionLocal @Pos1 c n1A b )
                    (if p0A == Leaf True then p1R' else remove_f0s1_from_f1s1 c p0A p1R')
                p1R' = mixedIntersection2 @Pos1 c dcA b
                in applyElimRule @Pos1 $ InfNodes positionA (Leaf False) (Leaf False) (Leaf True) p1R (Leaf True)
            Pos0 -> let -- replace all the B stuf with (dc: 1, neg1: 0, neg0: b, pos1: 0, pos0: 1)
                p0R' = unionLocal @Pos0 c p0A b
                p0R = mixedIntersection2 @Pos0 c p0R' dcA
                in applyElimRule @Pos0 $ InfNodes positionA dcB (Leaf False) (Leaf True) (Leaf False) p0R

intersectionMain c a b = error "no 2 StartInfNode's in intersection main"



unionMain :: Context -> Dd -> Dd -> Dd
-- exclusive points (0's / holes) under union are filled unless they are present in both A and B (so only an intersection between them needs to be done)
-- inclusive point (1's ) under union are intersected with the opposite infinite subset (dc) before they are added together
unionMain  c@(inf : _) a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B)
    | positionA == positionB =  let

        dcR = unionLocal @Dc c  dcA dcB `debug` ("union A ("++ show positionA ++ ")==B (" ++ show positionB ++ "), with c = " ++ show c)

        n1R = mixedIntersection2 @Neg1 c n1R' dcR -- union the consequences of n1R with dcR, then if they are the same absorb them
        n1R' = unionLocal @Neg1 c n1A n1B --`debug` show (unionLocal @Neg1 n1A n1B) -- union all points

        n0R = unionLocal @Neg0 c -- union then intersection
            (intersectionLocal @Neg0 c n0A n0B) -- intersection then union
            (if n1R' == Leaf False then n0R' else remove_f1s1_from_f0s1 c n1R' n0R')
        n0R' = unionLocal @Neg0 c
            (mixedIntersection @Neg0 c n0A dcB dcR) -- remove the holes that do fit in B (unioned away) // note that in consequence this reverts back to to union and is absorbed if consequence of n0A == dcR
            (mixedIntersection @Neg0 c n0B dcA dcR) -- remove the holes that do fit in A (unioned away)
            --`debug` ("dcB: " ++ show dcB)


        ------------------------------------
        -- n0R = (n0A cap n0B) cup ((n0A cap neg dcB) cap n1B) cup ((n0B cap neg dcA) cap n1A) <-> (n0A cup n0B) cap n1R* cap neg dcR
        p1R = mixedIntersection2 @Pos1 c p1R' dcR
        p1R' = unionLocal @Pos1 c p1A p1B
        p0R = unionLocal @Pos0 c
            (intersectionLocal @Pos0 c p0A p0B)
            (if p1R' == Leaf False then p0R' else remove_f1s0_from_f0s0 c p1R' p0R')
        p0R' = unionLocal @Pos0 c
            (mixedIntersection @Pos0 c p0A dcB dcR) -- remove the holes that do fit in B: if the consequence of p0A after union is the same as the consequence of dcB, then it is also removed. If the consequence is smaller it is kept.
            (mixedIntersection @Pos0 c p0B dcA dcR)

        in applyElimRule @Dc (InfNodes positionA dcR n1R n0R p1R p0R)

    | positionA > positionB = -- replace all the A stuf with (dc: a, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
        case inf of
            Dc -> let
                dcR = unionLocal @Dc c  a dcB --pass along the consequence of B for both dcA and not dcA
                n1R = mixedIntersection2 @Neg1 c n1B dcR

                n0R = let n0R' = mixedIntersection @Neg0 c n0B a dcR in
                    if n1B == Leaf False then n0R' else remove_f1s1_from_f0s1 c n1B n0R'

                p1R = mixedIntersection2 @Pos1 c p1B dcR
                p0R = let p0R' = mixedIntersection @Pos0 c p0B a dcR in
                    if p1B == Leaf False then p0R' else remove_f1s0_from_f0s0 c p1B p0R'

                in applyElimRule @Dc (InfNodes positionB dcR n1R n0R p1R p0R)

            Neg1 -> let -- replace all the A stuf with (dc: 0, neg1: a, neg0: 1, pos1: 0, pos0: 1)
                n1R' = unionLocal @Neg1 c a n1B
                n1R = mixedIntersection2 @Neg1 c n1R' dcB
                in applyElimRule @Neg1 $ InfNodes positionB (Leaf False) n1R (Leaf True) (Leaf False) (Leaf True)
            Neg0 -> let -- replace all the A stuf with (dc: 1, neg1: 0, neg0: a, pos1: 0, pos0: 1)
                n0R = unionLocal @Neg0 c
                    (intersectionLocal @Neg0 c a n0B)
                    (if n1B == Leaf True then n0R' else remove_f1s1_from_f0s1 c n1B n0R')
                n0R' = mixedIntersection2 @Neg0 c a dcB
                in applyElimRule @Neg0 $ InfNodes positionB dcB (Leaf False) n0R (Leaf False) (Leaf True)
            Pos1 -> let -- replace all the A stuf with (dc: 0, neg1: 0, neg0: 1, pos1: a, pos0: 1)
                p1R' = unionLocal @Pos1 c a p1B
                p1R = mixedIntersection2 @Pos1 c p1R' dcB
                in applyElimRule @Pos1 $ InfNodes positionB (Leaf False) (Leaf False) (Leaf True) p1R (Leaf True)
            Pos0 -> let -- replace all the A stuf with (dc: 1, neg1: 0, neg0: a, pos1: 0, pos0: 1)
                p0R = unionLocal @Pos0 c
                    (intersectionLocal @Pos0 c a n0B)
                    (if p1B == Leaf True then p0R' else remove_f0s1_from_f1s1 c p1B p0R')
                p0R' = mixedIntersection2 @Pos0 c a dcB
                in applyElimRule @Pos0 $ InfNodes positionB dcB (Leaf False) (Leaf True) (Leaf False) p0R


    -- c cannot be empty..
    | positionA < positionB = -- replace all the A stuf with (dc: a, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
        case inf of
            Dc -> let
                dcR = unionLocal @Dc c b dcA
                n1R = mixedIntersection2 @Neg1 c n1A dcR

                n0R = let n0R' = mixedIntersection @Neg0 c n0A b dcR in
                    if n1A == Leaf False then n0R' else remove_f1s1_from_f0s1 c n1A n0R'

                p1R = mixedIntersection2 @Pos1 c p1A dcR
                p0R = let p0R' = mixedIntersection @Pos0 c p0A b dcR in
                    if p1A == Leaf False then p0R' else remove_f1s0_from_f0s0 c p1A p0R'

                in applyElimRule @Dc (InfNodes positionA dcR n1R n0R p1R p0R)
            Neg1 -> let -- replace all the B stuf with (dc: 0, neg1: b, neg0: 1, pos1: 0, pos0: 1)
                n1R' = unionLocal @Neg1 c n1A b
                n1R = mixedIntersection2 @Neg1 c n1R' dcA
                in applyElimRule @Neg1 $ InfNodes positionA (Leaf False) n1R (Leaf True) (Leaf False) (Leaf True)
            Neg0 -> let -- replace all the B stuf with (dc: 1, neg1: 0, neg0: b, pos1: 0, pos0: 1)
                n0R = unionLocal @Neg0 c
                    (intersectionLocal @Neg0 c n0A b)
                    (if n1A == Leaf True then n0R' else remove_f1s1_from_f0s1 c n1A n0R')
                n0R' = mixedIntersection2 @Neg0 c b dcA
                in applyElimRule @Neg0 $ InfNodes positionA dcA (Leaf False) n0R (Leaf False) (Leaf True)
            Pos1 -> let -- replace all the B stuf with (dc: 0, neg1: 0, neg0: 1, pos1: b, pos0: 1)
                p1R' = unionLocal @Pos1 c p1A b
                p1R = mixedIntersection2 @Pos1 c p1R' dcA
                in applyElimRule @Pos1 $ InfNodes positionA (Leaf False) (Leaf False) (Leaf True) p1R (Leaf True)
            Pos0 -> let -- replace all the B stuf with (dc: 1, neg1: 0, neg0: b, pos1: 0, pos0: 1)
                p0R = unionLocal @Pos0 c
                    (intersectionLocal @Pos0 c n0A b )
                    (if p1A == Leaf True then p0R' else remove_f1s1_from_f0s1 c p1A p0R')
                p0R' = mixedIntersection2 @Pos0 c dcA b
                in applyElimRule @Pos0 $ InfNodes positionA dcB (Leaf False) (Leaf True) (Leaf False) p0R

unionMain c a b = error "no 2 StartInfNode's in intersection main"





class DdF4 a where
    applyElimRule :: forall a . Dd -> Dd
    restrictLocal :: forall a . Dd -> Bool -> Ordinal -> Dd
    restrictSetLocal :: forall a . Dd -> [(Ordinal, Bool)] -> Dd
    intersectionLocal :: forall a . Context -> Dd -> Dd -> Dd
    unionLocal :: forall a . Context -> Dd -> Dd -> Dd
    mixedIntersection :: forall a b . Context -> Dd -> Dd -> Dd -> Dd
    mixedIntersection2 :: forall a b . Context -> Dd -> Dd -> Dd



instance DdF4 Dc where
    applyElimRule d@(Node _ posC negC) = if posC == negC then posC else d
    applyElimRule d@(InfNodes pos dcR n1R n0R p1R p0R) =
        if (n1R, n0R, p1R, p0R) == (Leaf False, Leaf True, Leaf False, Leaf True) then
                        (if isInfNode dcR then dcR else
                            if dcR == Leaf False then Leaf False else
                                if dcR == Leaf True then Leaf True else
                                    InfNodes pos dcR n1R n0R p1R p0R)
                        else InfNodes pos dcR n1R n0R p1R p0R
    applyElimRule (Leaf b) = Leaf b
    applyElimRule (EndInfNode _ _) = error "cannot end on end infnodlet c = lastN' (len positionA) c ine"
    {-restrictLocal d@(Node position pos_child neg_child) b n
        | n > position = applyElimRule @Dc $ Node position (restrictLocal @Dc pos_child b n) (restrictLocal @Dc neg_child b n)
        | n < position = d -- do not have to apply elimRule
        | n == position = applyElimRule @Dc $
            if b then Node position pos_child pos_child else Node position neg_child neg_child
    restrictLocal d@(InfNodes position _ _ _ _ _) b n -- check inference
        | n > position = restrict @True d b n
        | n < position = d
        | n == position = error "n is inf-node.."
    restrictLocal d@(Leaf _) b n = d

    restrictSetLocal d@(Node position pos_child neg_child) ((n, b) : ns)
        | n > position = applyElimRule @Dc $ Node position (restrictLocal @Dc pos_child b n) (restrictLocal @Dc neg_child b n)
        | n < position = d -- do not have to apply elimRule
        | n == position = applyElimRule @Dc $
            if b
                then Node position (restrictSetLocal @Dc pos_child ns) (restrictSetLocal @Dc pos_child ns)
                else Node position (restrictSetLocal @Dc neg_child ns) (restrictSetLocal @Dc neg_child ns)
    restrictSetLocal d@(InfNodes position _ _ _ _ _) ((n, b) : ns) -- check inference
        | n > position = restrictSet @True d ((n, b) : ns)
        | n < position = d
        | n == position = error "n is inf-node.."
    restrictSetLocal d@(Leaf _) _ = d
    restrictSetLocal d [(n, b)] = restrictLocal @Dc d b n-}

    -- Leaf and node
    -- intersectionLocal c a (Leaf False) = Leaf False
    -- intersectionLocal c (Leaf False) b = Leaf False
    -- intersectionLocal c a (Leaf True) = a
    -- intersectionLocal c (Leaf True) b = b
    -- todo add a "look forwards? to eable above quick checks?", after all the surrouding stack should be the same up to this point.. idk


    -- Two nodes
    intersectionLocal c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
        -- Match
        | positionA == positionB =
            let pos_result = intersectionLocal @Dc c pos_childA pos_childB
                neg_result = intersectionLocal @Dc c neg_childA neg_childB
            in applyElimRule @Dc (Node positionA pos_result neg_result)
        -- Mismatch, but with dc inference we ontinue recursion with the earliest (thus lowest valued) node.
        | positionA < positionB =
            let pos_result = intersectionLocal @Dc c pos_childA b
                neg_result = intersectionLocal @Dc c neg_childA b
            in applyElimRule @Dc (Node positionA pos_result neg_result)
        | positionA > positionB =
            let pos_result = intersectionLocal @Dc c a pos_childB
                neg_result = intersectionLocal @Dc c a neg_childB
            in applyElimRule @Dc (Node positionB pos_result neg_result)
    intersectionLocal c a@(InfNodes (Order positionA) dcA n1A n0A p1A p0A) b@(Node positionB pos_childB neg_childB) =
        if last positionA == positionB
            then
                error "undefined, multiple options possible for interpreting node in Dc context to sub nodes"
                -- depends on how you want to model: if property green is true, and you zoom in on that property
                -- (i.e. property of being green exists out of a bunch of subproperties) do you then get that those multiple properties have to be true together before you have green?
                -- Or does just 1 have to be true? (e.i. either all have to be true or none have to be true before Propertie is true)
            else
                let pos_result = intersectionLocal @Dc c a pos_childB
                    neg_result = intersectionLocal @Dc c a neg_childB
                in applyElimRule @Dc (Node positionB pos_result neg_result)
    intersectionLocal c a@(Node positionA pos_childA neg_childA) b@(InfNodes (Order positionB) _ _ _ _ _) =
        if positionA == last positionB then error "undefined, multiple options possible for interpreting node in Dc context to sub nodes" else
            let pos_result = intersectionLocal @Dc c pos_childA b
                neg_result = intersectionLocal @Dc c neg_childA b
            in applyElimRule @Dc (Node positionA pos_result neg_result)
    intersectionLocal  c a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = intersection @True (Dc:c) a b

    -- continue local traversal
    intersectionLocal c a@(Node positionA pos_childA neg_childA) b@(EndInfNode positionB childB) = Node positionA (intersectionLocal @Dc c pos_childA b) (intersectionLocal @Dc c neg_childA b)
    intersectionLocal c a@(EndInfNode positionA childA) b@(Node positionB pos_childB neg_childB) = Node positionB (intersectionLocal @Dc c a pos_childB) (intersectionLocal @Dc c a neg_childB)
    -- continue previous super domain traversal -- todo, do we the also need to remember the function calls on top? yes.. kind off
    intersectionLocal (c:cs) a@(EndInfNode positionA childA)  b@(EndInfNode positionB childB) = intersectionLocal_arg c cs a b

    intersectionLocal c a b = error ("how did we get here? " ++ show a ++ "  -  " ++ show b)

    -- unionLocal c (Leaf False) b = b
    -- unionLocal c a (Leaf True) =  Leaf True
    -- unionLocal c a (Leaf False) =  a
    -- unionLocal c (Leaf True) b = Leaf True

    -- comparing nodes, allowed mis-matches based on each inference rule
    unionLocal c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

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

    unionLocal c a@(InfNodes (Order positionA) _ _ _ _ _)  b@(Node positionB pos_childB neg_childB) =
        if last positionA == positionB then error "undefined, multiple options possible for interpreting node in Dc context to sub nodes" else
            let pos_result = unionLocal @Dc c a pos_childB
                neg_result = unionLocal @Dc c a neg_childB
            in applyElimRule @Dc (Node positionB pos_result neg_result)

    unionLocal c a@(Node positionA pos_childA neg_childA)  b@(InfNodes (Order positionB) _ _ _ _ _) =
        if positionA == last positionB then error "undefined, multiple options possible for interpreting node in Dc context to sub nodes" -- a possible option: (InfNodes (dcA .*. pos_childB) (n1A .*. pos_childB) (n0A .*. pos_childB) (p1A .*. pos_childB) (p0A .*. pos_childB))
        else let pos_result = unionLocal @Dc c pos_childA b
                 neg_result = unionLocal @Dc c neg_childA b
             in applyElimRule @Dc (Node positionA pos_result neg_result)

    unionLocal c a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = union @True c a b

    -- continue local traversal
    unionLocal c a@(Node positionA pos_childA neg_childA) b@(EndInfNode positionB childB) = Node positionA (unionLocal @Dc c pos_childA b) (unionLocal @Dc c neg_childA b)
    unionLocal c a@(EndInfNode positionA childA) b@(Node positionB pos_childB neg_childB) = Node positionB (unionLocal @Dc c a pos_childB) (unionLocal @Dc c a neg_childB)
    -- continue previous super domain traversal -- todo, do we the also need to remember the function calls on top? yes.. kind off
    unionLocal (c:cs) a@(EndInfNode positionA childA)  b@(EndInfNode positionB childB) = unionLocal_arg c cs a b

    mixedIntersection = error "mixedintersection only with finite kinds"
    mixedIntersection2 = error "mixedintersection only with finite kinds"



instance DdF4 Neg1 where
    applyElimRule d@(Node _ posC negC) = if posC == Leaf False then posC else d
    applyElimRule d@(InfNodes pos dcR n1R n0R p1R p0R) =
        if (dcR, n0R, p1R, p0R) == (Leaf False, Leaf True, Leaf False, Leaf True) then
                        (if isInfNode n1R then n1R else
                            if n1R == Leaf False then Leaf False else
                                if n1R == Leaf True then Leaf True else
                                    InfNodes pos dcR n1R n0R p1R p0R)
                        else InfNodes pos dcR n1R n0R p1R p0R
    applyElimRule (Leaf b) = Leaf b

{-}    restrictLocal d@(Node position pos_child neg_child) b n
        | n > position = applyElimRule @Neg1 $ Node position (restrictLocal @Neg1 pos_child b n) (restrictLocal @Neg1 neg_child b n)
        | n < position = if b then Leaf False else Node n d d -- do not have to apply elimRule
        | n == position = applyElimRule @Neg1 $
            if b then Node position pos_child pos_child else Node position neg_child neg_child
    restrictLocal d@(InfNodes position _ _ _ _ _) b n -- check inference
        | n > position = restrict @True d b n
        | n < position = if b then Leaf False else Node n d d
        | n == position = error "n is inf-node.."
    restrictLocal d@(Leaf _) b n = d

    restrictSetLocal d@(Node position pos_child neg_child) ((n, b) : ns)
        | n > position = applyElimRule @Neg1 $ Node position (restrictSetLocal @Neg1 pos_child ((n, b) : ns)) (restrictSetLocal @Neg1 neg_child ((n, b) : ns))
        | n < position = if b then Leaf False else restrictSetLocal @Neg1 (Node n d d) ns -- do not have to apply elimRule
        | n == position = applyElimRule @Neg1 $
            if b then Node position (restrictSetLocal @Neg1 pos_child ns) (restrictSetLocal @Neg1 pos_child ns)
                else Node position (restrictSetLocal @Neg1 neg_child ns) (restrictSetLocal @Neg1 neg_child ns)
    restrictSetLocal d@(InfNodes position _ _ _ _ _) ((n, b) : ns) -- check inference
        | n > position = restrictSet @True d ((n, b) : ns)
        | n < position = if b then Leaf False else restrictSetLocal @Neg1 (Node n d d) ns
        | n == position = error "n is inf-node.."
    restrictSetLocal d@(Leaf _) _ = d
    restrictSetLocal d [(n, b)] = restrictLocal @Neg1 d b n-}


    intersectionLocal c a (Leaf False) = Leaf False
    intersectionLocal c (Leaf False) b = Leaf False

   -- comparing nodes, allowed mis-matches based on each inference rule
    intersectionLocal c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
        -- match
        | positionA == positionB =
            let pos_result = intersectionLocal @Neg1 c pos_childA pos_childB
                neg_result = intersectionLocal @Neg1 c neg_childA neg_childB
            in applyElimRule @Neg1 (Node positionA pos_result neg_result)

        | positionA < positionB =
            intersectionLocal @Neg1 c neg_childA b
        | positionA > positionB =
            intersectionLocal @Neg1 c a neg_childB

    intersectionLocal c a@(InfNodes (Order positionA) _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
        -- todo add posB == posA, then we consider node to be AllNegs -> [1]
        if last positionA == positionB
            then
                undefined
            else
                Node positionB (Leaf False) (intersectionLocal @Neg1 c a neg_childB)
    intersectionLocal c a@(Node positionA pos_childA neg_childA) b@(InfNodes (Order positionB) _ _ _ _ _) =
        -- todo add posB == posA, then we consider node to be AllNegs -> [1]
        if positionA == last positionB
            then
                undefined
            else
                Node positionA (Leaf False) (intersectionLocal @Neg1 c neg_childA b)
    intersectionLocal c a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = intersection @True (Neg1:c) a b

    -- continue local traversal
    intersectionLocal c a@(Node positionA pos_childA neg_childA) b@(EndInfNode positionB childB) = intersectionLocal @Neg1 c neg_childA b
    intersectionLocal c a@(EndInfNode positionA childA) b@(Node positionB pos_childB neg_childB) = intersectionLocal @Neg1 c a neg_childB
    -- continue previous super domain traversal
    intersectionLocal (c:cs) a@(EndInfNode positionA childA)  b@(EndInfNode positionB childB) = intersectionLocal_arg c cs a b

    intersectionLocal c a b = error (show a ++ show b ++ show c)


    unionLocal c a (Leaf False) =  a
    unionLocal c (Leaf False) b =  b

    -- comparing nodes, allowed mis-matches based on each inference rule
    unionLocal c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

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

    unionLocal c a@(InfNodes (Order positionA) _ _ _ _ _)  b@(Node positionB pos_childB neg_childB) =
        -- todo add posB == posA, then we consider node to be AllNegs -> [1]
        if last positionA == positionB
            then
                undefined
            else
                Node positionB (Leaf False) (unionLocal @Neg1 c a neg_childB)

    unionLocal c a@(Node positionA pos_childA neg_childA)  b@(InfNodes (Order positionB) _ _ _ _ _) =
        -- todo add posB == posA, then we consider node to be AllNegs -> [1]
        if positionA == last positionB
            then
                undefined
            else
                Node positionA (Leaf False) (unionLocal @Neg1 c neg_childA b)
    unionLocal c  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = union @True (Neg1:c) a b

    unionLocal c a@(Node positionA pos_childA neg_childA) b@(EndInfNode _ _) = Node positionA pos_childA (unionLocal @Neg1 c neg_childA b)
    unionLocal c a@(EndInfNode _ _) b@(Node positionB pos_childB neg_childB) = Node positionB pos_childB (unionLocal @Neg1 c a neg_childB)
    unionLocal (c:cs) a@(EndInfNode _ _) b@(EndInfNode _ _) = unionLocal_arg c cs a b
    unionLocal c a b = error (show a ++ show b ++ show c)
{-}
    unionLocal c a@(InfNodes {}) (Leaf True) = error ""
    unionLocal c (Leaf True) b@(InfNodes {}) = error ""
    unionLocal c a@(EndInfNode {}) (Leaf True) = error ""
    unionLocal c (Leaf True) b@(EndInfNode {}) = error ""
    unionLocal _ (Leaf True) (Leaf True) = error ""-}

-- ======================= Mixed Intersections =================================================================



    mixedIntersection c a (Leaf False) dc = Leaf False
    mixedIntersection c a (Leaf True) dc = a
    mixedIntersection c (Leaf False) b dc = Leaf False
    mixedIntersection c (Leaf True) b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD)  = mixedIntersection @Neg1 c (Leaf True) neg_childB neg_childD
    mixedIntersection c (Leaf True) b@(Node positionB pos_childB neg_childB) dc  = mixedIntersection @Neg1 c (Leaf True) neg_childB dc
    mixedIntersection c (Leaf True) b@(InfNodes {}) dc = if dc == b then Leaf False else b

    -- No leafs involved
    mixedIntersection c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD)

        -- No mismatch
        | positionA == positionB =
            let pos_result = mixedIntersection @Neg1 c pos_childA pos_childB pos_childD
                neg_result = mixedIntersection @Neg1 c neg_childA neg_childB neg_childD
            in applyElimRule @Neg1 (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionB = mixedIntersection @Neg1 c a neg_childB neg_childD
        | positionA < positionB =
            let pos_result = mixedIntersection @Neg1 c pos_childA b pos_childD
                neg_result = mixedIntersection @Neg1 c neg_childA b neg_childD
            in applyElimRule @Neg1 (Node positionA pos_result neg_result)

    -- No leafs involved
    mixedIntersection c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) dc

        -- No mismatch
        | positionA == positionB =
            let pos_result = mixedIntersection @Neg1 c pos_childA pos_childB dc
                neg_result = mixedIntersection @Neg1 c neg_childA neg_childB dc
            in applyElimRule @Neg1 (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionB = mixedIntersection @Neg1 c a neg_childB dc
        | positionA < positionB =
            let pos_result = mixedIntersection @Neg1 c pos_childA b dc
                neg_result = mixedIntersection @Neg1 c neg_childA b dc
            in applyElimRule @Neg1 (Node positionA pos_result neg_result)

    -- Single InfNode has been reached, similar to single Leaf node cases.
    mixedIntersection c a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) dc =
        let pos_result = mixedIntersection @Neg1 c pos_childA b dc
            neg_result = mixedIntersection @Neg1 c neg_childA b dc
        in applyElimRule @Neg1 (Node positionA pos_result neg_result)

    mixedIntersection c a@(InfNodes (Order positionA) dcA n1A n0A p1A p0A) b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD) =
         --(InfNodes (dcA .*. neg_childB) (n1A .*. neg_childB) (n0A .*. neg_childB) (p1A .*. pos_childB) (p0A .*. neg_childB))
        -- todo add posB == posA, then we consider node to be AllNegs -> [1]
        if last positionA == positionB
            then
                undefined
            else
                mixedIntersection @Neg1 c a neg_childB neg_childD

    mixedIntersection c a@(InfNodes (Order positionA) _ _ _ _ _) b@(Node positionB pos_childB neg_childB) dc =
        -- todo add posB == posA, then we consider node to be AllNegs -> [1]
        if last positionA == positionB
            then
                undefined
            else
                mixedIntersection @Neg1 c a neg_childB dc

    -- Both InfNodes have been reached - run the usual intersection.
    mixedIntersection c a@(InfNodes {})  b@(InfNodes {}) dc = if intersection @True c a b == dc then Leaf False else intersection @True c a b
    mixedIntersection c a b dc = undefined `debug` ("neg1 - " ++ show a ++ "  :  " ++ show b)

    mixedIntersection2 c a (Leaf False) = a
    mixedIntersection2 c a (Leaf True) = Leaf False -- absorbed
    mixedIntersection2 c (Leaf False) b = Leaf False
    mixedIntersection2 c (Leaf True) b@(Node positionB pos_childB neg_childB)  = mixedIntersection2 @Neg1 c (Leaf True) neg_childB
    mixedIntersection2 c (Leaf True) b@(InfNodes {}) = Leaf True -- following is a union call where Leaf True is preserved

    -- No leafs involved
    mixedIntersection2 c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

        -- No mismatch
        | positionA == positionB =
            let pos_result = mixedIntersection2 @Neg1 c pos_childA pos_childB
                neg_result = mixedIntersection2 @Neg1 c neg_childA neg_childB
            in applyElimRule @Neg1 (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionB = mixedIntersection2 @Neg1 c a neg_childB
        | positionA < positionB =
            let pos_result = mixedIntersection2 @Neg1 c pos_childA b
                neg_result = mixedIntersection2 @Neg1 c neg_childA b
            in applyElimRule @Neg1 (Node positionA pos_result neg_result)

    -- Single InfNode has been reached, similar to single Leaf node cases.
    mixedIntersection2 c a@(Node positionA pos_childA neg_childA)  b@(InfNodes (Order positionB) _ _ _ _ _) =
        -- todo add posB == posA, then we consider node to be AllNegs -> [1]
        if positionA == last positionB
            then
                undefined
            else
                let pos_result = mixedIntersection2 @Neg1 c pos_childA b
                    neg_result = mixedIntersection2 @Neg1 c neg_childA b
                in applyElimRule @Neg1 (Node positionA pos_result neg_result)

    mixedIntersection2 c a@(InfNodes (Order positionA) _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
        -- todo add posB == posA, then we consider node to be AllNegs -> [1]
        if last positionA == positionB
            then
                undefined
            else
                mixedIntersection2 @Neg1 c a neg_childB

    -- Both InfNodes have been reached - run the usual intersection.
    mixedIntersection2 c a@(InfNodes {})  b@(InfNodes {}) = if union @True c a b == b then Leaf False else union @True c a b
    mixedIntersection2 c a b = undefined `debug` ("neg1 - " ++ show a ++ "  :  " ++ show b)




instance DdF4 Neg0 where
    applyElimRule d@(Node _ posC negC) = if posC == Leaf True then posC else d
    applyElimRule d@(InfNodes pos dcR n1R n0R p1R p0R) =
        if (n1R, dcR, p1R, p0R) == (Leaf False, Leaf True, Leaf False, Leaf True) then
                        (if isInfNode n0R then n0R else
                            if n0R == Leaf False then Leaf False else
                                if n0R == Leaf True then Leaf True else
                                    InfNodes pos dcR n1R n0R p1R p0R)
                        else InfNodes pos dcR n1R n0R p1R p0R
    applyElimRule (Leaf b) = Leaf b

    {-restrictLocal d@(Node position pos_child neg_child) b n
        | n > position = applyElimRule @Neg0 $ Node position (restrictLocal @Neg0 pos_child b n) (restrictLocal @Neg0 neg_child b n)
        | n < position = if b then Leaf True else Node n d d -- do not have to apply elimRule
        | n == position = applyElimRule @Neg0 $
            if b then Node position pos_child pos_child else Node position neg_child neg_child
    restrictLocal d@(InfNodes position _ _ _ _ _) b n -- check inference
        | n > position = restrict @False d b n
        | n < position = if b then Leaf True else Node n d d
        | n == position = error "n is inf-node.."
    restrictLocal d@(Leaf _) b n = d

    restrictSetLocal d@(Node position pos_child neg_child) ((n, b) : ns)
        | n > position = applyElimRule @Neg0 $ Node position
            (restrictSetLocal @Neg0 pos_child ((n, b) : ns))
            (restrictSetLocal @Neg0 neg_child ((n, b) : ns))
        | n < position = if b then Leaf True else restrictSetLocal @Neg0 (Node n d d) ns -- do not have to apply elimRule
        | n == position = applyElimRule @Neg0 $
            if b then Node position (restrictSetLocal @Neg0 pos_child ns) (restrictSetLocal @Neg0 pos_child ns)
                else Node position (restrictSetLocal @Neg0 neg_child ns) (restrictSetLocal @Neg0 neg_child ns)
    restrictSetLocal d@(InfNodes position _ _ _ _ _) ((n, b) : ns) -- check inference
        | n > position = restrictSet @False d ((n, b) : ns)
        | n < position = if b then Leaf True else restrictSetLocal @Neg0 (Node n d d) ns
        | n == position = error "n is inf-node.."
    restrictSetLocal d@(Leaf _) b = d
    restrictSetLocal d [(n, b)] = restrictLocal @Neg0 d b n-}

        -- Leaf and node
    intersectionLocal c a (Leaf True) = Leaf True
    intersectionLocal c (Leaf True) b = Leaf True

    -- comparing nodes, allowed mis-matches based on each inference rule
    intersectionLocal c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
        -- match
        | positionA == positionB =
            let pos_result = intersectionLocal @Neg0 c pos_childA pos_childB
                neg_result = intersectionLocal @Neg0 c neg_childA neg_childB
            in applyElimRule @Neg0 (Node positionA pos_result neg_result)

        -- mismatch with no Bot involved, thus with ZDD types inference we return bot
        | positionA < positionB =
            intersectionLocal @Neg0 c neg_childA b
        | positionA > positionB =
            intersectionLocal @Neg0 c a neg_childB

    intersectionLocal c a@(InfNodes (Order positionA) dcA n1A n0A p1A p0A) b@(Node positionB pos_childB neg_childB) =
    -- todo add posB == posA, then we consider node to be AllNegs -> [0]
        if last positionA == positionB
            then
                undefined
            else
                Node positionB (Leaf True) (intersectionLocal @Neg0 c a neg_childB)
    intersectionLocal c a@(Node positionA pos_childA neg_childA) b@(InfNodes (Order positionB) _ _ _ _ _) =
    -- todo add posB == posA, then we consider node to be AllNegs -> [0]
        if positionA == last positionB
            then
                undefined
            else
                Node positionA (Leaf True) (intersectionLocal @Neg0 c neg_childA b)

    intersectionLocal  c a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = union @False (Neg0 : c) a b

    intersectionLocal c a@(Node positionA pos_childA neg_childA) b@(EndInfNode _ _) = Node positionA pos_childA (intersectionLocal @Neg0 c neg_childA b)
    intersectionLocal c a@(EndInfNode _ _) b@(Node positionB pos_childB neg_childB) = Node positionB pos_childB (intersectionLocal @Neg0 c a neg_childB)
    intersectionLocal (c:cs) a@(EndInfNode _ _) b@(EndInfNode _ _) = intersectionLocal_arg c cs a b

    intersectionLocal _ _ _ = error "how did we get here?"

    unionLocal c (Leaf True) b = b
    unionLocal c a (Leaf True) = a

    -- comparing nodes, allowed mis-matches based on each inference rule
    unionLocal c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

        -- no mismatch, only the appropriate ZDD elim is applied
        | positionA == positionB =
            let pos_result = unionLocal @Neg0 c pos_childA pos_childB
                neg_result = unionLocal @Neg0 c neg_childA neg_childB
            in if pos_result == Leaf True then Leaf True else Node positionA pos_result neg_result

        -- mismatch, but with dc inference we continue recursion with the highest (thus lowest valued) node
        -- refactor into two functions? one for mixed inference rules, one for single
        | positionA < positionB =
            let neg_result = unionLocal @Neg0 c neg_childA b
            in Node positionA pos_childA neg_result

        | positionA > positionB =
            let neg_result = unionLocal @Neg0 c a neg_childB
            in Node positionB pos_childB neg_result

    unionLocal c a@(InfNodes (Order positionA) _ _ _ _ _)  b@(Node positionB pos_childB neg_childB) =
    -- todo add posB == posA, then we consider node to be AllNegs -> [0]
        if last positionA == positionB
            then
                undefined
            else
                Node positionB (Leaf True) (unionLocal @Neg0 c a neg_childB)

    unionLocal c a@(Node positionA pos_childA neg_childA)  b@(InfNodes (Order positionB) _ _ _ _ _) =
    -- todo add posB == posA, then we consider node to be AllNegs -> [0]
        if positionA == last positionB
            then
                undefined
            else
                Node positionA (Leaf True) (unionLocal @Neg0 c neg_childA b)

    unionLocal c  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = intersection @True (Neg0 : c) a b

    unionLocal c a@(Node positionA pos_childA neg_childA) b@(EndInfNode _ _) = unionLocal @Neg0 c neg_childA b
    unionLocal c a@(EndInfNode _ _) b@(Node positionB pos_childB neg_childB) = unionLocal @Neg0 c a neg_childB
    unionLocal (c:cs) a@(EndInfNode _ _) b@(EndInfNode _ _) = unionLocal_arg c cs a b


    mixedIntersection c a (Leaf False) dc = a
    mixedIntersection c a (Leaf True) dc = Leaf True

    mixedIntersection c (Leaf True) b dc = Leaf True
    mixedIntersection c (Leaf False) b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD)  = mixedIntersection @Neg0 c (Leaf False) neg_childB neg_childD
    mixedIntersection c (Leaf False) b@(Node positionB pos_childB neg_childB) dc  = mixedIntersection @Neg0 c (Leaf False) neg_childB dc
    mixedIntersection c (Leaf False) b@(InfNodes {}) dc = if b == dc then Leaf True else b
    -- following domain becomes union call, where Leaf False is interpreted as bot, thus b should be returned.

    -- No leafs involved
    mixedIntersection c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD)

        -- No mismatch
        | positionA == positionB =
            let pos_result = mixedIntersection @Neg0 c pos_childA pos_childB pos_childD
                neg_result = mixedIntersection @Neg0 c neg_childA neg_childB neg_childD
            in applyElimRule @Neg0 (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionB = mixedIntersection @Neg0 c a neg_childB neg_childD
        | positionA < positionB =
            let pos_result = mixedIntersection @Neg0 c pos_childA b dc
                neg_result = mixedIntersection @Neg0 c neg_childA b dc
            in applyElimRule @Neg0 (Node positionA pos_result neg_result)

    mixedIntersection c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) dc

        -- No mismatch
        | positionA == positionB =
            let pos_result = mixedIntersection @Neg0 c pos_childA pos_childB dc
                neg_result = mixedIntersection @Neg0 c neg_childA neg_childB dc
            in applyElimRule @Neg0 (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionB = mixedIntersection @Neg0 c a neg_childB dc
        | positionA < positionB =
            let pos_result = mixedIntersection @Neg0 c pos_childA b dc
                neg_result = mixedIntersection @Neg0 c neg_childA b dc
            in applyElimRule @Neg0 (Node positionA pos_result neg_result)

    -- Single InfNode has been reached, similar to single Leaf node cases.
    mixedIntersection c a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) dc =
        let pos_result = mixedIntersection @Neg0 c pos_childA b dc
            neg_result = mixedIntersection @Neg0 c neg_childA b dc
        in applyElimRule @Neg0 (Node positionA pos_result neg_result)
    mixedIntersection c a@(InfNodes (Order positionA) _ _ _ _ _) b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD) =
    -- todo add posB == posA, then we consider node to be AllNegs -> [0]
        if last positionA == positionB
            then
                undefined
            else
                mixedIntersection @Neg0 c a neg_childB neg_childD
    mixedIntersection c a@(InfNodes (Order positionA) _ _ _ _ _) b@(Node positionB pos_childB neg_childB) dc =
    -- todo add posB == posA, then we consider node to be AllNegs -> [0]
        if last positionA == positionB
            then
                undefined
            else
                mixedIntersection @Neg0 c a neg_childB dc

    -- Both InfNodes have been reached - run the usual intersection.
    mixedIntersection c a@(InfNodes {})  b@(InfNodes {}) dc =  if union @False c a b == dc then Leaf True else union @False c a b
    mixedIntersection c a b dc = error ("neg0 - " ++ show a ++ "  :  " ++ show b)

    mixedIntersection2 c a (Leaf False) = Leaf True
    mixedIntersection2 c a (Leaf True) = a
    mixedIntersection2 c (Leaf True) b = Leaf True
    mixedIntersection2 c (Leaf False) b@(Node positionB pos_childB neg_childB)  = Leaf False
    mixedIntersection2 c (Leaf False) b@(InfNodes {}) = Leaf False -- following domain becomes intersection call

    -- No leafs involved
    mixedIntersection2 c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

        -- No mismatch
        | positionA == positionB =
            let pos_result = mixedIntersection2 @Neg0 c pos_childA pos_childB
                neg_result = mixedIntersection2 @Neg0 c neg_childA neg_childB
            in applyElimRule @Neg0 (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionB = mixedIntersection2 @Neg0 c a neg_childB
        | positionA < positionB =
            let pos_result = mixedIntersection2 @Neg0 c pos_childA b
                neg_result = mixedIntersection2 @Neg0 c neg_childA b
            in applyElimRule @Neg0 (Node positionA pos_result neg_result)

    -- Single InfNode has been reached, similar to single Leaf node cases.
    mixedIntersection2 c a@(Node positionA pos_childA neg_childA)  b@(InfNodes (Order positionB) _ _ _ _ _) =
    -- todo add posB == posA, then we consider node to be AllNegs -> [0]
        if positionA == last positionB
            then
                undefined
            else
                let pos_result = mixedIntersection2 @Neg0 c pos_childA b
                    neg_result = mixedIntersection2 @Neg0 c neg_childA b
                in applyElimRule @Neg0 (Node positionA pos_result neg_result)
    mixedIntersection2 c a@(InfNodes (Order positionA) _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
    -- todo add posB == posA, then we consider node to be AllNegs -> [0]
        if last positionA == positionB
            then
                undefined
            else
                mixedIntersection2 @Neg0 c a neg_childB

    -- Both InfNodes have been reached - run the usual intersection.
    mixedIntersection2 c a@(InfNodes {})  b@(InfNodes {}) =  if intersection @True c a b == b then Leaf True else intersection @True c a b
    mixedIntersection2 c a b = undefined `debug` ("neg0 - " ++ show a ++ "  :  " ++ show b)



instance DdF4 Pos1 where
    applyElimRule d@(Node _ posC negC) = if negC == Leaf False then negC else d
    applyElimRule d@(InfNodes pos dcR n1R n0R p1R p0R) =
        if (n1R, n0R, dcR, p0R) == (Leaf False, Leaf True, Leaf False, Leaf True) then
            (if isInfNode p1R then p1R else
                if p1R == Leaf False then Leaf False else
                    if p1R == Leaf True then Leaf True else
                        InfNodes pos dcR n1R n0R p1R p0R)
            else InfNodes pos dcR n1R n0R p1R p0R
    applyElimRule (Leaf b) = Leaf b
    {-restrictLocal d@(Node position pos_child neg_child) b n
        | n > position = applyElimRule @Pos1 $ Node position (restrictLocal @Pos1 pos_child b n) (restrictLocal @Pos1 neg_child b n)
        | n < position = if b then Node n d d else Leaf False -- do not have to apply elimRule
        | n == position = applyElimRule @Pos1 $
            if b then Node position pos_child pos_child else Node position neg_child neg_child
    restrictLocal d@(InfNodes position _ _ _ _ _) b n -- check inference
        | n > position = restrict @True d b n
        | n < position = if b then Node n d d else Leaf False
        | n == position = error "n is inf-node.."
    restrictLocal d@(Leaf _) b n = d

    restrictSetLocal d@(Node position pos_child neg_child) ((n, b) : ns)
        | n > position = applyElimRule @Pos1 $ Node position
            (restrictSetLocal @Pos1 pos_child ((n, b) : ns))
            (restrictSetLocal @Pos1 neg_child ((n, b) : ns))
        | n < position = if b then restrictSetLocal @Pos1 (Node n d d) ns else Leaf False -- do not have to apply elimRule
        | n == position = applyElimRule @Pos1 $
            if b then Node position (restrictSetLocal @Pos1 pos_child ns) (restrictSetLocal @Pos1 pos_child ns)
                else Node position (restrictSetLocal @Pos1 neg_child ns) (restrictSetLocal @Pos1 neg_child ns)
    restrictSetLocal d@(InfNodes position _ _ _ _ _) ((n, b) : ns) -- check inference
        | n > position = restrictSet @True d ((n, b) : ns)
        | n < position = if b then restrictSetLocal @Pos1 (Node n d d) ns else Leaf False
        | n == position = error "n is inf-node.."
    restrictSetLocal d@(Leaf _) _ = d
    restrictSetLocal d [(n, b)] = restrictLocal @Pos1 d b n-}

    -- Leaf and node
    intersectionLocal c a (Leaf False) =  Leaf False
    intersectionLocal c (Leaf False) b =  Leaf False

    -- comparing nodes, allowed mis-matches based on each inference rule
    intersectionLocal c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
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

    intersectionLocal c a@(InfNodes (Order positionA) _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
        if last positionA == positionB
            then
                undefined
            else
                Node positionB (Leaf False) (intersectionLocal @Pos1 c a pos_childB)
    intersectionLocal c a@(Node positionA pos_childA neg_childA) b@(InfNodes (Order positionB) _ _ _ _ _) =
        if positionA == last positionB
            then
                undefined
            else
                Node positionA (Leaf False) (intersectionLocal @Pos1 c pos_childA b)

    intersectionLocal c a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = intersection @True (Pos1:c) a b

    intersectionLocal c a@(Node positionA pos_childA neg_childA) b@(EndInfNode _ _) = intersectionLocal @Pos1 c pos_childA b
    intersectionLocal c a@(EndInfNode _ _) b@(Node positionB pos_childB neg_childB) = intersectionLocal @Pos1 c a pos_childB
    intersectionLocal (c:cs) a@(EndInfNode _ _) b@(EndInfNode _ _) = intersectionLocal_arg c cs a b
    intersectionLocal c a b = error (show a ++ show b ++ show c)

    unionLocal c a (Leaf False) =  a
    unionLocal c (Leaf False) b =  b

    -- comparing nodes, allowed mis-matches based on each inference rule
    unionLocal c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
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
    unionLocal c a@(InfNodes (Order positionA) _ _ _ _ _)  b@(Node positionB pos_childB neg_childB) =
        if last positionA == positionB
            then
                undefined
            else
                Node positionB (unionLocal @Pos1 c a pos_childB) (Leaf False)
    unionLocal c a@(Node positionA pos_childA neg_childA)  b@(InfNodes (Order positionB) _ _ _ _ _) =
        if positionA == last positionB
            then
                undefined
            else
                Node positionA (unionLocal @Pos1 c pos_childA b) (Leaf False)
    unionLocal c  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = union @True c a b

    unionLocal c a@(Node positionA pos_childA neg_childA) b@(EndInfNode _ _) = Node positionA (unionLocal @Pos1 c pos_childA b) neg_childA
    unionLocal c a@(EndInfNode _ _) b@(Node positionB pos_childB neg_childB) = Node positionB (unionLocal @Pos1 c a pos_childB) neg_childB
    unionLocal (c:cs) a@(EndInfNode _ _) b@(EndInfNode _ _) = unionLocal_arg c cs a b
    unionLocal c a b = error (show a ++ show b ++ show c)

    mixedIntersection c a (Leaf False) dc = Leaf False
    mixedIntersection c a (Leaf True) dc = a
    mixedIntersection c (Leaf False) a dc = Leaf False
    mixedIntersection c (Leaf True) b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD) = mixedIntersection @Pos1 c (Leaf True) pos_childB pos_childD
    mixedIntersection c (Leaf True) b@(Node positionB pos_childB neg_childB) dc = mixedIntersection @Pos1 c (Leaf True) pos_childB dc
    mixedIntersection c (Leaf True) b@(InfNodes {}) dc = if b == dc then Leaf False else b

    -- No leafs involved
    mixedIntersection c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD)

        -- No mismatch
        | positionA == positionB =
            let pos_result = mixedIntersection @Pos1 c pos_childA pos_childB pos_childD
                neg_result = mixedIntersection @Pos1 c neg_childA neg_childB neg_childD
            in applyElimRule @Pos1 (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionB = mixedIntersection @Pos1 c a pos_childB pos_childD
        | positionA < positionB =
            let pos_result = mixedIntersection @Pos1 c pos_childA b dc
                neg_result = mixedIntersection @Pos1 c neg_childA b dc
            in applyElimRule @Pos1 (Node positionA pos_result neg_result)

    -- No leafs involved
    mixedIntersection c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) dc

        -- No mismatch
        | positionA == positionB =
            let pos_result = mixedIntersection @Pos1 c pos_childA pos_childB dc
                neg_result = mixedIntersection @Pos1 c neg_childA neg_childB dc
            in applyElimRule @Pos1 (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionB = mixedIntersection @Pos1 c a pos_childB dc
        | positionA < positionB =
            let pos_result = mixedIntersection @Pos1 c pos_childA b dc
                neg_result = mixedIntersection @Pos1 c neg_childA b dc
            in applyElimRule @Pos1 (Node positionA pos_result neg_result)

    -- Single InfNode has been reached, similar to single Leaf node cases.
    mixedIntersection c a@(Node positionA pos_childA neg_childA)  b@(InfNodes (Order positionB) _ _ _ _ _) dc =
        if positionA == last positionB
            then
                undefined
            else
                let pos_result = mixedIntersection @Pos1 c pos_childA b dc
                    neg_result = mixedIntersection @Pos1 c neg_childA b dc
                in applyElimRule @Pos1 (Node positionA pos_result neg_result)


    mixedIntersection c a@(InfNodes (Order positionA) _ _ _ _ _) b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD) =
        if last positionA == positionB
            then
                undefined
            else
                mixedIntersection @Pos1 c a pos_childB pos_childD
    mixedIntersection c a@(InfNodes (Order positionA) _ _ _ _ _) b@(Node positionB pos_childB neg_childB) dc =
        if last positionA == positionB
            then
                undefined
            else
                mixedIntersection @Pos1 c a pos_childB dc

    -- Both InfNodes have been reached - run the usual intersection.
    mixedIntersection c a@(InfNodes {})  b@(InfNodes {}) dc = if (intersection @True c a b) == dc then Leaf False else (intersection @True c a b)
    mixedIntersection c a b dc = undefined `debug` ("pos1" ++ show a ++ "  :  " ++ show b)

    mixedIntersection2 c a (Leaf False) = a
    mixedIntersection2 c a (Leaf True) = Leaf False --becomes a union call, should thus return Leaf True, but since the consequences are the same they are absrbed.
    mixedIntersection2 c (Leaf False) a = Leaf False
    mixedIntersection2 c (Leaf True) b@(Node positionB pos_childB neg_childB) = mixedIntersection2 @Pos1 c (Leaf True) pos_childB
    mixedIntersection2 c (Leaf True) b@(InfNodes {}) = Leaf True -- becomes union where leaf true dominates

    -- No leafs involved
    mixedIntersection2 c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

        -- No mismatch
        | positionA == positionB =
            let pos_result = mixedIntersection2 @Pos1 c pos_childA pos_childB
                neg_result = mixedIntersection2 @Pos1 c neg_childA neg_childB
            in applyElimRule @Pos1 (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionB = mixedIntersection2 @Pos1 c a pos_childB
        | positionA < positionB =
            let pos_result = mixedIntersection2 @Pos1 c pos_childA b
                neg_result = mixedIntersection2 @Pos1 c neg_childA b
            in applyElimRule @Pos1 (Node positionA pos_result neg_result)

    -- Single InfNode has been reached, similar to single Leaf node cases.
    mixedIntersection2 c a@(Node positionA pos_childA neg_childA)  b@(InfNodes (Order positionB) _ _ _ _ _) =
        if positionA == last positionB
            then
                undefined
            else
                let pos_result = mixedIntersection2 @Pos1 c pos_childA b
                    neg_result = mixedIntersection2 @Pos1 c neg_childA b
                in applyElimRule @Pos1 (Node positionA pos_result neg_result)


    mixedIntersection2 c a@(InfNodes (Order positionA) _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
        if last positionA == positionB
            then
                undefined
            else
                mixedIntersection2 @Pos1 c a pos_childB

    mixedIntersection2 c a@(InfNodes {})  b@(InfNodes {}) = if union @True c a b == b then Leaf False else union @True c a b
    mixedIntersection2 c a b = undefined `debug` ("pos1" ++ show a ++ "  :  " ++ show b)


instance DdF4 Pos0 where
    applyElimRule d@(Node _ posC negC) = if negC == Leaf True then negC else d
    applyElimRule d@(InfNodes pos dcR n1R n0R p1R p0R) =
        if (n1R, n0R, p1R, dcR) == (Leaf False, Leaf True, Leaf False, Leaf True) then
                        (if isInfNode p0R then p0R else
                            if p0R == Leaf False then Leaf False else
                                if p0R == Leaf True then Leaf True else
                                    InfNodes pos dcR n1R n0R p1R p0R)
                        else InfNodes pos dcR n1R n0R p1R p0R
    applyElimRule (Leaf b) = Leaf b


    {-restrictLocal d@(Node position pos_child neg_child) b n
        | n > position = applyElimRule @Pos0 $ Node position (restrictLocal @Pos0 pos_child b n) (restrictLocal @Pos0 neg_child b n)
        | n < position = if b then Node n d d else Leaf True -- do not have to apply elimRule
        | n == position = applyElimRule @Pos0 $
            if b then Node position pos_child pos_child else Node position neg_child neg_child
    restrictLocal d@(InfNodes position _ _ _ _ _) b n -- check inference
        | n > position = restrict @False d b n
        | n < position = if b then Node n d d else Leaf True
        | n == position = error "n is inf-node.."
    restrictLocal d@(Leaf _) b n = d

    restrictSetLocal d@(Node position pos_child neg_child) ((n, b) : ns)
        | n > position = applyElimRule @Pos0 $ Node position
            (restrictSetLocal @Pos0 pos_child ((n, b) : ns))
            (restrictSetLocal @Pos0 neg_child ((n, b) : ns))
        | n < position = if b then restrictSetLocal @Pos0 (Node n d d) ns else Leaf True -- do not have to apply elimRule
        | n == position = applyElimRule @Pos0 $
            if b then Node position (restrictSetLocal @Pos0 pos_child ns) (restrictSetLocal @Pos0 pos_child ns)
                else Node position (restrictSetLocal @Pos0 neg_child ns) (restrictSetLocal @Pos0 neg_child ns)
    restrictSetLocal d@(InfNodes position _ _ _ _ _) ((n, b) : ns) -- check inference
        | n > position = restrictSet @False d ((n, b) : ns)
        | n < position = if b then restrictSetLocal @Pos0 (Node n d d) ns else Leaf True
        | n == position = error "n is inf-node.."
    restrictSetLocal d@(Leaf _) _ = d
    restrictSetLocal d [(n, b)] = restrictLocal @Pos0 d b n-}


    -- Leaf and node
    intersectionLocal c a (Leaf True) = Leaf True
    intersectionLocal c (Leaf True) b = Leaf True

    --intersectionLocal c a@(InfNodes positionA _ _ _ _ _) (Leaf False) = a
    --intersectionLocal c (Leaf False) b@(InfNodes positionB _ _ _ _ _) = b

    -- comparing nodes, allowed mis-matches based on each inference rule
    intersectionLocal c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
        -- match
        | positionA == positionB =
            let pos_result = intersectionLocal @Pos0 c pos_childA pos_childB
                neg_result = intersectionLocal @Pos0 c neg_childA neg_childB
            in applyElimRule @Pos0 (Node positionA pos_result neg_result)

        -- mismatch with no Bot involved, thus with ZDD types inference we return bot
        | positionA < positionB =
            intersectionLocal @Pos0 c pos_childA b
        | positionA > positionB =
            intersectionLocal @Pos0 c a pos_childB

    intersectionLocal c a@(InfNodes (Order positionA) _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
        if last positionA == positionB
            then
                undefined
            else
                Node positionB (Leaf True) (intersectionLocal @Pos0 c a pos_childB)
    intersectionLocal c a@(Node positionA pos_childA neg_childA) b@(InfNodes (Order positionB) _ _ _ _ _) =
        if positionA == last positionB
            then
                undefined
            else
                Node positionA (Leaf True) (intersectionLocal @Pos0 c pos_childA b)

    intersectionLocal  c a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = union @False c a b

    intersectionLocal c a@(Node positionA pos_childA neg_childA) b@(EndInfNode _ _) = Node positionA (intersectionLocal @Pos0 c pos_childA b) neg_childA -- todo double check this
    intersectionLocal c a@(EndInfNode _ _) b@(Node positionB pos_childB neg_childB) = Node positionB (intersectionLocal @Pos0 c a pos_childB) neg_childB
    intersectionLocal (c:cs) a@(EndInfNode _ _)  b@(EndInfNode _ _) = intersectionLocal_arg c cs a b

    intersectionLocal _ _ _ = error "how did we get here?"

    --unionLocal c a@(InfNodes positionA dcA n1A n0A p1A p0A) (Leaf True) = union @False c a (inferInfNode c True a)
    --unionLocal c (Leaf True) b@(InfNodes positionB dcB n1B n0B p1B p0B) = union @False c (inferInfNode c True b) b
    unionLocal c a (Leaf True) =  a
    unionLocal c (Leaf True) b =  b

    -- comparing nodes, allowed mis-matches based on each inference rule
    unionLocal c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

        -- no mismatch, only the appropriate ZDD elim is applied
        | positionA == positionB =
            let pos_result = unionLocal @Pos0 c pos_childA pos_childB
                neg_result = unionLocal @Pos0 c neg_childA neg_childB
            in if neg_result == Leaf True then Leaf True else Node positionA pos_result neg_result

        -- mismatch, but with dc inference we continue recursion with the highest (thus lowest valued) node
        -- refactor into two functions? one for mixed inference rules, one for single
        | positionA < positionB =
            let pos_result = unionLocal @Pos0 c pos_childA b
            in Node positionA pos_result neg_childA

        | positionA > positionB =
            let pos_result = unionLocal @Pos0 c a pos_childB
            in Node positionB pos_result neg_childB

    unionLocal c a@(InfNodes (Order positionA) _ _ _ _ _)  b@(Node positionB pos_childB neg_childB) =
        if last positionA == positionB
            then
                undefined
            else
                Node positionB (unionLocal @Pos0 c a pos_childB) (Leaf True)

    unionLocal c a@(Node positionA pos_childA neg_childA)  b@(InfNodes (Order positionB) _ _ _ _ _) =
        if positionA == last positionB
            then
                undefined
            else
                Node positionA (unionLocal @Pos0 c pos_childA b) (Leaf True)

    unionLocal c a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = intersection @True c a b

    unionLocal c a@(Node positionA pos_childA neg_childA) b@(EndInfNode _ _) = unionLocal @Pos0 c pos_childA b
    unionLocal c a@(EndInfNode _ _) b@(Node positionB pos_childB neg_childB) = unionLocal @Pos0 c pos_childB a
    unionLocal (c:cs) a@(EndInfNode _ _)  b@(EndInfNode _ _) = unionLocal_arg c cs a b



    mixedIntersection c (Leaf True) b dc = Leaf True
    mixedIntersection c (Leaf False) b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD)  = mixedIntersection @Pos0 c (Leaf False) pos_childB pos_childD
    mixedIntersection c (Leaf False) b@(Node positionB pos_childB neg_childB) dc  = mixedIntersection @Pos0 c (Leaf False) pos_childB dc
    mixedIntersection c (Leaf False) b@(InfNodes {}) dc = Leaf True

    mixedIntersection c a (Leaf False) dc = a
    mixedIntersection c a (Leaf True) dc = Leaf True


    -- No leafs involved
    mixedIntersection c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD)

        -- No mismatch
        | positionA == positionB =
            let pos_result = mixedIntersection @Pos0 c pos_childA pos_childB pos_childD
                neg_result = mixedIntersection @Pos0 c neg_childA neg_childB neg_childD
            in applyElimRule @Pos0 (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionB = mixedIntersection @Pos0 c a pos_childB pos_childD
        | positionA < positionB =
            let pos_result = mixedIntersection @Pos0 c pos_childA b dc
                neg_result = mixedIntersection @Pos0 c neg_childA b dc
            in applyElimRule @Pos0 (Node positionA pos_result neg_result)

    -- No leafs involved
    mixedIntersection c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) dc

        -- No mismatch
        | positionA == positionB =
            let pos_result = mixedIntersection @Pos0 c pos_childA pos_childB dc
                neg_result = mixedIntersection @Pos0 c neg_childA neg_childB dc
            in applyElimRule @Pos0 (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionB = mixedIntersection @Pos0 c a pos_childB dc
        | positionA < positionB =
            let pos_result = mixedIntersection @Pos0 c pos_childA b dc
                neg_result = mixedIntersection @Pos0 c neg_childA b dc
            in applyElimRule @Pos0 (Node positionA pos_result neg_result)

    -- Single InfNode has been reached, similar to single Leaf node cases.
    mixedIntersection c a@(Node positionA pos_childA neg_childA)  b@(InfNodes (Order positionB) _ _ _ _ _) dc =
        if positionA == last positionB
            then
                undefined
            else
                let pos_result = mixedIntersection @Pos0 c pos_childA b dc
                    neg_result = mixedIntersection @Pos0 c neg_childA b dc
                in applyElimRule @Pos0 (Node positionA pos_result neg_result)

    mixedIntersection c a@(InfNodes (Order positionA) _ _ _ _ _) b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD) =
        if last positionA == positionB
            then
                undefined
            else
                mixedIntersection @Pos0 c a neg_childB neg_childD
    mixedIntersection c a@(InfNodes (Order positionA) _ _ _ _ _) b@(Node positionB pos_childB neg_childB) dc =
        if last positionA == positionB
            then
                undefined
            else
                mixedIntersection @Pos0 c a neg_childB dc

    -- Both InfNodes have been reached - run the usual intersection.
    mixedIntersection c a@(InfNodes {})  b@(InfNodes {}) dc = if (union @False c a b) == dc then Leaf True else union @False c a b
    mixedIntersection c a b dc = undefined `debug` ("pos0 - " ++ show a ++ "  :  " ++ show b)

    mixedIntersection2 c a (Leaf False) = Leaf True
    mixedIntersection2 c a (Leaf True) = a
    mixedIntersection2 c (Leaf True) b = Leaf True
    mixedIntersection2 c (Leaf False) b@(Node positionB pos_childB neg_childB)  = Leaf True
    mixedIntersection2 c (Leaf False) b@(InfNodes {}) = Leaf False

    -- No leafs involved
    mixedIntersection2 c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

        -- No mismatch
        | positionA == positionB =
            let pos_result = mixedIntersection2 @Pos0 c pos_childA pos_childB
                neg_result = mixedIntersection2 @Pos0 c neg_childA neg_childB
            in applyElimRule @Pos0 (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionB = mixedIntersection2 @Pos0 c a pos_childB
        | positionA < positionB =
            let pos_result = mixedIntersection2 @Pos0 c pos_childA b
                neg_result = mixedIntersection2 @Pos0 c neg_childA b
            in applyElimRule @Pos0 (Node positionA pos_result neg_result)

    -- Single InfNode has been reached, similar to single Leaf node cases.
    mixedIntersection2 c a@(Node positionA pos_childA neg_childA)  b@(InfNodes (Order positionB) _ _ _ _ _) =
        if positionA == last positionB
            then
                undefined
            else
                let pos_result = mixedIntersection2 @Pos0 c pos_childA b
                    neg_result = mixedIntersection2 @Pos0 c neg_childA b
                in applyElimRule @Pos0 (Node positionA pos_result neg_result)

    mixedIntersection2 c a@(InfNodes (Order positionA) _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
        if last positionA == positionB
            then
                undefined
            else
                mixedIntersection2 @Pos0 c a neg_childB

    -- Both InfNodes have been reached - run the usual intersection.
    mixedIntersection2 c a@(InfNodes {})  b@(InfNodes {}) = if (intersection @True c a b) == b then Leaf True else (intersection @True c a b)
    mixedIntersection2 c a b = undefined `debug` ("pos0 - " ++ show a ++ "  :  " ++ show b)



































remove_f0s1_from_f1s1 :: Context -> Dd -> Dd -> Dd
remove_f0s1_from_f1s1 c a (Leaf False) = Leaf False
remove_f0s1_from_f1s1 c a@(Node positionA pos_childA neg_childA) (Leaf True) = remove_f0s1_from_f1s1 c neg_childA (Leaf True)
remove_f0s1_from_f1s1 c (Leaf False) b@(Node positionB pos_childB neg_childB) = Node positionB pos_childB (remove_f0s1_from_f1s1 c (Leaf False) neg_childB) --if pos_child == Leaf False then pos_child else b@(Node positionB pos_childB neg_childB)
remove_f0s1_from_f1s1 c (Leaf True) b = b
remove_f0s1_from_f1s1 c a@(InfNodes {}) (Leaf True) = a
remove_f0s1_from_f1s1 c (Leaf False) (Leaf True)  =  Leaf False

-- No leafs involved
remove_f0s1_from_f1s1 c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)-- no mismatch, thus no inference is needed

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


-- Single InfNode has been reached, similar to single Leaf node cases.
remove_f0s1_from_f1s1 c a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) =
    Node positionA (Leaf False) (remove_f0s1_from_f1s1 c neg_childA b)
remove_f0s1_from_f1s1 c a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
    Node positionB (Leaf False) (remove_f0s1_from_f1s1 c a neg_childB)

-- Both InfNodes have been reached - run the usual intersection.
remove_f0s1_from_f1s1 c  a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B) = intersection @True c a b
remove_f0s1_from_f1s1 c a b = undefined `debug` (show a ++ "  :  " ++ show b)


remove_f1s1_from_f0s1 :: Context -> Dd -> Dd -> Dd
remove_f1s1_from_f0s1 c a (Leaf True) = Leaf True
remove_f1s1_from_f0s1 c a@(Node positionA pos_childA neg_childA) (Leaf False) = remove_f1s1_from_f0s1 c neg_childA (Leaf False)
remove_f1s1_from_f0s1 c (Leaf True) b@(Node positionB pos_childB neg_childB) = Node positionB pos_childB (remove_f1s1_from_f0s1 c (Leaf True) neg_childB) --if pos_child == Leaf False then pos_child else b@(Node positionB pos_childB neg_childB)
remove_f1s1_from_f0s1 c (Leaf False) b = b
remove_f1s1_from_f0s1 c a@(InfNodes {}) (Leaf False) = a

remove_f1s1_from_f0s1 c (Leaf True) (Leaf False)  =  Leaf True

-- No leafs involved
remove_f1s1_from_f0s1 c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)-- no mismatch, thus no inference is needed

    -- No mismatch, only the appropriate ZDD elim is applied
    | positionA == positionB =
        let pos_result = remove_f1s1_from_f0s1 c pos_childA pos_childB
            neg_result = remove_f1s1_from_f0s1 c neg_childA neg_childB
        in if pos_result == Leaf True then Leaf True else Node positionA pos_result neg_result

    -- mismatch with no Bot involved, thus with ZDD types inference we return bot
    | positionA < positionB =
        remove_f1s1_from_f0s1 c neg_childA b
    | positionA > positionB =
        Node positionB pos_childB (remove_f1s1_from_f0s1 c a neg_childB)


-- Single InfNode has been reached, similar to single Leaf node cases.
remove_f1s1_from_f0s1 c a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) =
    Node positionA (Leaf True) (remove_f1s1_from_f0s1 c neg_childA b)
remove_f1s1_from_f0s1 c a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
    Node positionB (Leaf True) (remove_f1s1_from_f0s1 c a neg_childB)

-- Both InfNodes have been reached - run the usual intersection.
remove_f1s1_from_f0s1 c  a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B) = intersection @True c a b
remove_f1s1_from_f0s1 c a b = undefined `debug` (show a ++ "  :  " ++ show b)


remove_f0s0_from_f1s0 :: Context -> Dd -> Dd -> Dd
remove_f0s0_from_f1s0 c a (Leaf False) = Leaf False
remove_f0s0_from_f1s0 c a@(Node positionA pos_childA neg_childA) (Leaf True) = remove_f0s0_from_f1s0 c pos_childA (Leaf True)
remove_f0s0_from_f1s0 c (Leaf False) b@(Node positionB pos_childB neg_childB) = Node positionB (remove_f0s0_from_f1s0 c (Leaf False) pos_childB) neg_childB  --if pos_child == Leaf False then pos_child else b@(Node positionB pos_childB neg_childB)
remove_f0s0_from_f1s0 c (Leaf True) b = b
remove_f0s0_from_f1s0 c a@(InfNodes {}) (Leaf True) = a
remove_f0s0_from_f1s0 c (Leaf False) (Leaf True)  =  Leaf False

-- No leafs involved
remove_f0s0_from_f1s0 c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)-- no mismatch, thus no inference is needed

    -- No mismatch, only the appropriate ZDD elim is applied
    | positionA == positionB =
        let pos_result = remove_f0s0_from_f1s0 c pos_childA pos_childB
            neg_result = remove_f0s0_from_f1s0 c neg_childA neg_childB
        in if neg_result == Leaf False then Leaf False else Node positionA pos_result neg_result

    -- mismatch with no Bot involved, thus with ZDD types inference we return bot
    | positionA < positionB =
        remove_f0s0_from_f1s0 c pos_childA b
    | positionA > positionB =
        Node positionB (remove_f0s0_from_f1s0 c a pos_childB) neg_childB


-- Single InfNode has been reached, similar to single Leaf node cases.
remove_f0s0_from_f1s0 c a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) =
    Node positionA (Leaf False) (remove_f0s0_from_f1s0 c pos_childA b)
remove_f0s0_from_f1s0 c a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
    Node positionB (Leaf False) (remove_f0s0_from_f1s0 c a pos_childB)

-- Both InfNodes have been reached - run the usual intersection.
remove_f0s0_from_f1s0 c  a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B) = intersection @True c a b
remove_f0s0_from_f1s0 c a b = undefined `debug` (show a ++ "  :  " ++ show b)



remove_f1s0_from_f0s0 :: Context -> Dd -> Dd -> Dd
remove_f1s0_from_f0s0 c a (Leaf True) = Leaf True
remove_f1s0_from_f0s0 c a@(Node positionA pos_childA neg_childA) (Leaf False) = remove_f1s0_from_f0s0 c pos_childA (Leaf False)
remove_f1s0_from_f0s0 c (Leaf True) b@(Node positionB pos_childB neg_childB) = Node positionB (remove_f1s0_from_f0s0 c (Leaf True) pos_childB) neg_childB  --if pos_child == Leaf False then pos_child else b@(Node positionB pos_childB neg_childB)
remove_f1s0_from_f0s0 c (Leaf False) b = b
remove_f1s0_from_f0s0 c a@(InfNodes {}) (Leaf False) = a

remove_f1s0_from_f0s0 c (Leaf True) (Leaf False)  =  Leaf True

-- No leafs involved
remove_f1s0_from_f0s0 c a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)-- no mismatch, thus no inference is needed

    -- No mismatch, only the appropriate ZDD elim is applied
    | positionA == positionB =
        let pos_result = remove_f1s0_from_f0s0 c pos_childA pos_childB
            neg_result = remove_f1s0_from_f0s0 c neg_childA neg_childB
        in if neg_result == Leaf True then Leaf True else Node positionA pos_result neg_result

    -- mismatch with no Bot involved, thus with ZDD types inference we return bot
    | positionA < positionB =
        remove_f1s0_from_f0s0 c pos_childA b
    | positionA > positionB =
        Node positionB (remove_f1s0_from_f0s0 c a pos_childB) neg_childB


-- Single InfNode has been reached, similar to single Leaf node cases.
remove_f1s0_from_f0s0 c a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) =
    Node positionA (Leaf True) (remove_f1s0_from_f0s0 c pos_childA b)
remove_f1s0_from_f0s0 c a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
    Node positionB (Leaf True) (remove_f1s0_from_f0s0 c a pos_childB)

-- Both InfNodes have been reached - run the usual intersection.
remove_f1s0_from_f0s0 c  a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B) = intersection @True c a b
remove_f1s0_from_f0s0 c a b = undefined `debug` (show a ++ "  :  " ++ show b)




debug :: c -> String -> c
debug = flip trace
