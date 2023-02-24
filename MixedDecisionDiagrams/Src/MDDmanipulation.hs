{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module MixedDecisionDiagrams.Src.MDDmanipulation where

import MixedDecisionDiagrams.Src.MDD
import Debug.Trace (trace)
import Data.Kind
import MixedDecisionDiagrams.Src.DrawMDD

type DdF4 :: Inf -> Constraint
type DdF2 :: Bool -> Constraint

class DdF2 a where
    restrict :: forall a . Dd Ordinal -> Bool -> Ordinal -> Dd Ordinal
    restrictSet :: forall a . Dd Ordinal -> [(Ordinal, Bool)] -> Dd Ordinal
    restrictGen :: forall a . Dd Ordinal -> [((Ordinal, Ordinal), Bool)] -> Dd Ordinal
    intersection :: forall a . Dd Ordinal -> Dd Ordinal  -> Dd Ordinal
    union :: forall a . Dd Ordinal -> Dd Ordinal  -> Dd Ordinal


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

    intersection a (Leaf False) = Leaf False
    intersection (Leaf False) b = Leaf False
    intersection a (Leaf True) = a
    intersection (Leaf True) b = b
    intersection a b = intersectionMain a b
    union a (Leaf True) = Leaf True
    union (Leaf True) b = Leaf True
    union a (Leaf False) = a
    union (Leaf False) b = b
    union a b = unionMain a b


instance DdF2 False where
    restrict d@(Leaf False) b n = if b then makeNode n Dc else negation $ makeNode n Dc
    restrict d@(Leaf True) b n = Leaf True
    restrict d b n = restrictMain d b n
    restrictSet d@(Leaf False) ((n, b) : ns) = if b then
        restrictSet @False (makeNode n Dc) ns
        else negation $ restrictSet @False (makeNode n Dc) ns
    restrictSet d@(Leaf True) ((n, b) : ns) = Leaf True
    restrictSet d b = restrictSetMain d b
    intersection a (Leaf True) = Leaf True
    intersection (Leaf True) b = Leaf True
    intersection a (Leaf False) = a
    intersection (Leaf False) b = b
    intersection a b = intersectionMain a b
    union a (Leaf False) = Leaf False
    union (Leaf False) b = Leaf False
    union a (Leaf True) = a
    union (Leaf True) b = b
    union a b = unionMain a b










negation :: Dd Ordinal -> Dd Ordinal
negation (Node position pos_child neg_child) = Node position (negation pos_child) (negation neg_child)
negation (InfNodes position dc_n n1_n n0_n p1_n p0_n) = InfNodes position (negation dc_n) (negation n0_n) (negation n1_n) (negation p0_n) (negation p1_n)
negation (Leaf b) = Leaf $ not b

isInfNode :: Dd a -> Bool
isInfNode(InfNodes _ _ _ _ _ _) = True
isInfNode _ = False

applyElimRule2 :: Inf -> Dd Ordinal -> Dd Ordinal
applyElimRule2 Dc d@(Node _ posC negC) = if posC == negC then posC else d
applyElimRule2 Neg0 d@(Node _ posC negC) = if posC == Leaf True then posC else d
applyElimRule2 Pos0 d@(Node _ posC negC) = if negC == Leaf True then negC else d
applyElimRule2 Neg1 d@(Node _ posC negC) = if posC == Leaf False then posC else d
applyElimRule2 Pos1 d@(Node _ posC negC) = if negC == Leaf False then negC else d
applyElimRule2 _ _ = error "applyElimRule2 got wrong parameters"

elimInfNode :: Dd Ordinal -> Dd Ordinal
elimInfNode d@(InfNodes pos dcR n1R n0R p1R p0R) =
    if (n1R, n0R, p1R, p0R) == (Leaf False, Leaf True, Leaf False, Leaf True) then
                    (if isInfNode dcR then dcR else
                        if dcR == Leaf False then Leaf False else
                            if dcR == Leaf True then Leaf True else
                                InfNodes pos dcR n1R n0R p1R p0R)
                    else InfNodes pos dcR n1R n0R p1R p0R


restrictMain :: Dd Ordinal -> Bool -> Ordinal -> Dd Ordinal
restrictMain d@(InfNodes position dc n1 n0 p1 p0) b n = let
        dcR = restrictLocal @Dc dc b n
        n1R = restrictLocal @Neg1 n1 b n
        n0R = restrictLocal @Neg0 n0 b n
        p1R = restrictLocal @Pos1 p1 b n
        p0R = restrictLocal @Pos0 p0 b n
        in elimInfNode (InfNodes position dcR n1R n0R p1R p0R)
restrictMain _ _ _ = error "restrictMain"

restrictSetMain :: Dd Ordinal -> [(Ordinal, Bool)] -> Dd Ordinal
restrictSetMain d@(InfNodes position dc n1 n0 p1 p0) bs = let
        dcR = restrictSetLocal @Dc dc bs
        n1R = restrictSetLocal @Neg1 n1 bs
        n0R = restrictSetLocal @Neg0 n0 bs
        p1R = restrictSetLocal @Pos1 p1 bs
        p0R = restrictSetLocal @Pos0 p0 bs
        in elimInfNode (InfNodes position dcR n1R n0R p1R p0R)
restrictSetMain _ _ = error "restrictMain"


intersectionMain :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
intersectionMain  a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B)
        | positionA == positionB =  let
            dcR = intersectionLocal @Dc dcA dcB

            n1R = unionLocal @Neg1
                (intersectionLocal @Neg1 n1A n1B) -- overlapping points are by definition not inside the others dc, thus have to be preserved
                (if n0R' == Leaf True then n1R' else remove_f0s1_from_f1s1 n0R' n1R') -- holes absorb points under intersection
            n1R' = unionLocal @Neg1 -- guaranteed that dcA and dcB do not overlap around the finite points, thus they do not get absorbed
                (mixedIntersection_neg1_dc n1A dcB dcR) -- keep the points that fit inside B
                (mixedIntersection_neg1_dc n1B dcA dcR) -- keep the points that fit inside A

            n0R' = unionLocal @Neg0 n0A n0B -- holes get unioned, because i keep the consequence of holes "uncomplemented" we get local union then intersection.
            n0R = local_mixedIntersection2_neg0_dc n0R' dcR -- keep the holes that fit inside dcR
            -- if the local hole fits inside dcR but the consequence of n0R' does not fit inside the consequenc of dcR it should return n0R' -> Leaf false
            ------------------------------------
            p1R = unionLocal @Pos1
                (intersectionLocal @Pos1 p1A p1B)
                (if p0R' == Leaf True then p1R' else remove_f0s0_from_f1s0 p0R' p1R')
            p1R' = unionLocal @Pos1
                (mixedIntersection_pos1_dc p1A dcB dcR)
                (mixedIntersection_pos1_dc p1B dcA dcR)
            p0R' = unionLocal @Pos0 p0A p0B -- local union then intersection
            p0R = local_mixedIntersection2_pos0_dc p0R' dcR
            in elimInfNode $ InfNodes positionA dcR n1R n0R p1R p0R

        | positionA > positionB = let -- replace all the A stuf with (dc: a, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
            dcR = intersectionLocal @Dc a dcB
            n1R = if n0B == Leaf True then
                mixedIntersection_neg1_dc n1B a dcR  else
                remove_f0s1_from_f1s1 n0B (mixedIntersection_neg1_dc n1B a dcR)
            n0R = local_mixedIntersection2_neg0_dc n0B dcR --`debug` ( "inter: " ++ show (local_mixedIntersection2_neg0_dc n0A dcR) ++ "\n n0A: " ++ show n0A  ++ "\n dcR" ++ show dcR)
            p1R = if p0B == Leaf True then
                mixedIntersection_pos1_dc p1B a dcR else
                remove_f0s0_from_f1s0 p0B (mixedIntersection_pos1_dc p1B a dcR)
            p0R = local_mixedIntersection2_pos0_dc p0B dcR
            in elimInfNode $ InfNodes positionB dcR n1R n0R p1R p0R

        | positionA < positionB = let -- replace all the B stuf with (dc: b, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
            dcR = intersectionLocal @Dc dcA b
            n1R = if n0A == Leaf True then
                mixedIntersection_neg1_dc n1A b dcR  else
                remove_f0s1_from_f1s1 n0A (mixedIntersection_neg1_dc n1A b dcR)
            n0R = local_mixedIntersection2_neg0_dc n0A dcR --`debug` ( "inter: " ++ show (local_mixedIntersection2_neg0_dc n0A dcR) ++ "\n n0A: " ++ show n0A  ++ "\n dcR" ++ show dcR)
            p1R = if p0A == Leaf True then
                mixedIntersection_pos1_dc p1A b dcR else
                remove_f0s0_from_f1s0 p0A (mixedIntersection_pos1_dc p1A b dcR)
            p0R = local_mixedIntersection2_pos0_dc p0A dcR
            in elimInfNode $ InfNodes positionA dcR n1R n0R p1R p0R --`debug` ("dcR" ++ show dcR ++ "\n p0A" ++ show p0A)
intersectionMain a b = error "no infnodes in intersection main"



unionMain :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
-- exclusive points (0's / holes) under union are filled unless they are present in both A and B (so only an intersection between them needs to be done)
-- inclusive point (1's ) under union are intersected with the opposite infinite subset (dc) before they are added together
unionMain  a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B)
    | positionA == positionB =  let
        dcR = unionLocal @Dc dcA dcB

        n1R = local_mixedIntersection_neg1_dc n1R' dcR -- union the consequences of n1R with dcR, then if they are the same absorb them
        n1R' = unionLocal @Neg1 n1A n1B --`debug` show (unionLocal @Neg1 n1A n1B) -- union all points

        n0R = unionLocal @Neg0 -- union then intersection
            (intersectionLocal @Neg0 n0A n0B) -- intersection then union
            (if n1R' == Leaf False then n0R' else remove_f1s1_from_f0s1 n1R' n0R')
        n0R' = unionLocal @Neg0
            (local_mixedIntersection_neg0_dc n0A dcB dcR) -- remove the holes that do fit in B (unioned away) // note that in consequence this reverts back to to union and is absorbed if consequence of n0A == dcR
            (local_mixedIntersection_neg0_dc n0B dcA dcR) -- remove the holes that do fit in A (unioned away)
            --`debug` ("dcB: " ++ show dcB)


        ------------------------------------
        -- n0R = (n0A cap n0B) cup ((n0A cap neg dcB) cap n1B) cup ((n0B cap neg dcA) cap n1A) <-> (n0A cup n0B) cap n1R* cap neg dcR
        p1R = local_mixedIntersection_pos1_dc p1R' dcR
        p1R' = unionLocal @Pos1 p1A p1B
        p0R = unionLocal @Pos0
            (intersectionLocal @Pos0 p0A p0B)
            (if p1R' == Leaf False then p0R' else remove_f1s0_from_f0s0 p1R' p0R')
        p0R' = unionLocal @Pos0
            (local_mixedIntersection_pos0_dc p0A dcB dcR) -- remove the holes that do fit in B: if the consequence of p0A after union is the same as the consequence of dcB, then it is also removed. If the consequence is smaller it is kept.
            (local_mixedIntersection_pos0_dc p0B dcA dcR)

        in elimInfNode (InfNodes positionA dcR n1R n0R p1R p0R)

    | positionA > positionB = let -- A is inferred to be Top
        dcR = unionLocal @Dc a dcB --pass along the consequence of B for both dcA and not dcA
        n1R = local_mixedIntersection_neg1_dc n1B dcR

        n0R = let n0R' = local_mixedIntersection_neg0_dc n0B a dcR in
            if n1B == Leaf False then n0R' else remove_f1s1_from_f0s1 n1B n0R'

        p1R = local_mixedIntersection_pos1_dc p1B dcR
        p0R = let p0R' = local_mixedIntersection_pos0_dc p0B a dcR in
            if p1B == Leaf False then p0R' else remove_f1s0_from_f0s0 p1B p0R'

        in elimInfNode (InfNodes positionB dcR n1R n0R p1R p0R)

    | positionA < positionB = let
        dcR = unionLocal @Dc b dcA
        n1R = local_mixedIntersection_neg1_dc n1A dcR

        n0R = let n0R' = local_mixedIntersection_neg0_dc n0A b dcR in
            if n1A == Leaf False then n0R' else remove_f1s1_from_f0s1 n1A n0R'

        p1R = local_mixedIntersection_pos1_dc p1A dcR
        p0R = let p0R' = local_mixedIntersection_pos0_dc p0A b dcR in
            if p1A == Leaf False then p0R' else remove_f1s0_from_f0s0 p1A p0R'

        in elimInfNode (InfNodes positionA dcR n1R n0R p1R p0R)
unionMain _ _ = error "missed case?"









class DdF4 a where
    applyElimRule :: forall a . Dd Ordinal -> Dd Ordinal
    restrictLocal :: forall a . Dd Ordinal -> Bool -> Ordinal -> Dd Ordinal
    restrictSetLocal :: forall a . Dd Ordinal -> [(Ordinal, Bool)] -> Dd Ordinal
    intersectionLocal :: forall a . Dd Ordinal -> Dd Ordinal -> Dd Ordinal
    unionLocal :: forall a . Dd Ordinal -> Dd Ordinal -> Dd Ordinal



instance DdF4 Dc where
    applyElimRule d@(Node _ posC negC) = if posC == negC then posC else d
    restrictLocal d@(Node position pos_child neg_child) b n
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
    restrictSetLocal d [(n, b)] = restrictLocal @Dc d b n

    -- Leaf and node
    intersectionLocal a (Leaf False) = Leaf False
    intersectionLocal (Leaf False) b = Leaf False
    intersectionLocal a (Leaf True) = a
    intersectionLocal (Leaf True) b = b
    -- Two nodes
    intersectionLocal a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
        -- Match
        | positionA == positionB =
            let pos_result = intersectionLocal @Dc pos_childA pos_childB
                neg_result = intersectionLocal @Dc neg_childA neg_childB
            in applyElimRule @Dc (Node positionA pos_result neg_result)
        -- Mismatch, but with dc inference we ontinue recursion with the earliest (thus lowest valued) node.
        | positionA < positionB =
            let pos_result = intersectionLocal @Dc pos_childA b
                neg_result = intersectionLocal @Dc neg_childA b
            in applyElimRule @Dc (Node positionA pos_result neg_result)
        | positionA > positionB =
            let pos_result = intersectionLocal @Dc a pos_childB
                neg_result = intersectionLocal @Dc a neg_childB
            in applyElimRule @Dc (Node positionB pos_result neg_result)
    intersectionLocal a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
        let pos_result = intersectionLocal @Dc a pos_childB
            neg_result = intersectionLocal @Dc a neg_childB
        in applyElimRule @Dc (Node positionB pos_result neg_result)
    intersectionLocal a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB _ _ _ _ _) =
        let pos_result = intersectionLocal @Dc pos_childA b
            neg_result = intersectionLocal @Dc neg_childA b
        in applyElimRule @Dc (Node positionA pos_result neg_result)
    intersectionLocal  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = intersection @True a b
    intersectionLocal a b = error ("how did we get here? " ++ show a ++ "  -  " ++ show b)

    unionLocal (Leaf False) b = b
    unionLocal a (Leaf True) =  Leaf True
    unionLocal a (Leaf False) =  a
    unionLocal (Leaf True) b = Leaf True

    -- comparing nodes, allowed mis-matches based on each inference rule
    unionLocal a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

        -- no mismatch, only the appropriate ZDD elim is applied
        | positionA == positionB =
            let pos_result = unionLocal @Dc pos_childA pos_childB
                neg_result = unionLocal @Dc neg_childA neg_childB
            in applyElimRule @Dc (Node positionA pos_result neg_result)

        -- mismatch, but with dc inference we continue recursion with the highest (thus lowest valued) node
        -- refactor into two functions? one for mixed inference rules, one for single
        | positionA < positionB =
            let pos_result = unionLocal @Dc pos_childA b
                neg_result = unionLocal @Dc neg_childA b
            in applyElimRule @Dc (Node positionA pos_result neg_result)

        | positionA > positionB =
            let pos_result = unionLocal @Dc a pos_childB
                neg_result = unionLocal @Dc a neg_childB
            in applyElimRule @Dc (Node positionB pos_result neg_result)

    unionLocal a@(InfNodes positionA _ _ _ _ _)  b@(Node positionB pos_childB neg_childB) =
        let pos_result = unionLocal @Dc a pos_childB
            neg_result = unionLocal @Dc a neg_childB
        in applyElimRule @Dc (Node positionB pos_result neg_result)

    unionLocal a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) =
        let pos_result = unionLocal @Dc pos_childA b
            neg_result = unionLocal @Dc neg_childA b
        in applyElimRule @Dc (Node positionA pos_result neg_result)

    unionLocal  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = union @True a b




instance DdF4 Neg1 where
    applyElimRule d@(Node _ posC negC) = if posC == Leaf False then posC else d

    restrictLocal d@(Node position pos_child neg_child) b n
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
    restrictSetLocal d [(n, b)] = restrictLocal @Neg1 d b n

    -- Leaf and node
    intersectionLocal a (Leaf False) = Leaf False
    intersectionLocal (Leaf False) b = Leaf False
    intersectionLocal a@(Node positionA pos_childA neg_childA) (Leaf True) = intersectionLocal @Neg1 neg_childA (Leaf True)
    intersectionLocal (Leaf True) b@(Node positionB pos_childB neg_childB) = intersectionLocal @Neg1 (Leaf True) neg_childB
    intersectionLocal (Leaf True) b = b
    intersectionLocal a (Leaf True) = a
    -- comparing nodes, allowed mis-matches based on each inference rule
    intersectionLocal a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
        -- match
        | positionA == positionB =
            let pos_result = intersectionLocal @Neg1 pos_childA pos_childB
                neg_result = intersectionLocal @Neg1 neg_childA neg_childB
            in applyElimRule @Neg1 (Node positionA pos_result neg_result)
        -- mismatch with no Bot involved, thus with ZDD types inference we return bot
        | positionA < positionB =
            intersectionLocal @Neg1 neg_childA b
        | positionA > positionB =
            intersectionLocal @Neg1 a neg_childB
    intersectionLocal a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
        Node positionB (Leaf False) (intersectionLocal @Neg1 a neg_childB)
    intersectionLocal a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB _ _ _ _ _) =
        Node positionA (Leaf False) (intersectionLocal @Neg1 neg_childA b)
    intersectionLocal  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = intersection @True a b
    intersectionLocal _ _ = error "how did we get here?"

    unionLocal a (Leaf False) =  a
    unionLocal (Leaf False) b =  b

    unionLocal a@(Node positionA pos_childA neg_childA) (Leaf True) = Node positionA pos_childA (unionLocal @Neg1 neg_childA (Leaf True))
    unionLocal (Leaf True) b@(Node positionB pos_childB neg_childB) = Node positionB pos_childB (unionLocal @Neg1 neg_childB (Leaf True))
    unionLocal (Leaf True) _ = Leaf True
    unionLocal _ (Leaf True) =   Leaf True

    -- comparing nodes, allowed mis-matches based on each inference rule
    unionLocal a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

        -- no mismatch, only the appropriate ZDD elim is applied
        | positionA == positionB =
            let pos_result = unionLocal @Neg1 pos_childA pos_childB
                neg_result = unionLocal @Neg1 neg_childA neg_childB
            in if pos_result == Leaf False then Leaf False else Node positionA pos_result neg_result

        -- mismatch, but with dc inference we continue recursion with the highest (thus lowest valued) node
        -- refactor into two functions? one for mixed inference rules, one for single
        | positionA < positionB =
            let neg_result = unionLocal @Neg1 neg_childA b
            in Node positionA pos_childA neg_result

        | positionA > positionB =
            let neg_result = unionLocal @Neg1 a neg_childB
            in Node positionB pos_childB neg_result

    unionLocal a@(InfNodes positionA _ _ _ _ _)  b@(Node positionB pos_childB neg_childB)
        = Node positionB (Leaf False) (unionLocal @Neg1 a neg_childB)

    unionLocal a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _)
        = Node positionA (Leaf False) (unionLocal @Neg1 neg_childA b)

    unionLocal  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = union @True a b


instance DdF4 Neg0 where
    applyElimRule d@(Node _ posC negC) = if posC == Leaf True then posC else d

    restrictLocal d@(Node position pos_child neg_child) b n
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
    restrictSetLocal d [(n, b)] = restrictLocal @Neg0 d b n

        -- Leaf and node
    intersectionLocal a (Leaf True) = Leaf True
    intersectionLocal (Leaf True) b = Leaf True

    intersectionLocal a@(Node positionA pos_childA neg_childA) (Leaf False) = intersectionLocal @Neg0 neg_childA (Leaf False)
    intersectionLocal (Leaf False) b@(Node positionB pos_childB neg_childB) = intersectionLocal @Neg0 (Leaf False) neg_childB
    intersectionLocal a@(InfNodes positionA _ _ _ _ _) (Leaf False) = a
    intersectionLocal (Leaf False) b@(InfNodes positionB _ _ _ _ _) = b
    intersectionLocal (Leaf False) (Leaf False) = Leaf False

    -- comparing nodes, allowed mis-matches based on each inference rule
    intersectionLocal a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
        -- match
        | positionA == positionB =
            let pos_result = intersectionLocal @Neg0 pos_childA pos_childB
                neg_result = intersectionLocal @Neg0 neg_childA neg_childB
            in applyElimRule @Neg0 (Node positionA pos_result neg_result)

        -- mismatch with no Bot involved, thus with ZDD types inference we return bot
        | positionA < positionB =
            intersectionLocal @Neg0 neg_childA b
        | positionA > positionB =
            intersectionLocal @Neg0 a neg_childB

    intersectionLocal a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
        Node positionB (Leaf True) (intersectionLocal @Neg0 a neg_childB)
    intersectionLocal a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB _ _ _ _ _) =
        Node positionA (Leaf True) (intersectionLocal @Neg0 neg_childA b)

    intersectionLocal  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = union @False a b
    intersectionLocal _ _ = error "how did we get here?"

    unionLocal a (Leaf True) =  a
    unionLocal (Leaf True) b =  b

    unionLocal a@(Node positionA pos_childA neg_childA) (Leaf False) = Node positionA pos_childA (unionLocal @Neg0 neg_childA (Leaf False))
    unionLocal (Leaf False) b@(Node positionB pos_childB neg_childB) = Node positionB pos_childB (unionLocal @Neg0 neg_childB (Leaf False))
    unionLocal a@(InfNodes positionA _ _ _ _ _) (Leaf False) = Leaf False -- because in the next domain we call intersection, thus Leaf False stays
    unionLocal (Leaf False) b@(InfNodes positionB _ _ _ _ _) = Leaf False
    unionLocal (Leaf False) (Leaf False) = Leaf False
    -- comparing nodes, allowed mis-matches based on each inference rule
    unionLocal a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

        -- no mismatch, only the appropriate ZDD elim is applied
        | positionA == positionB =
            let pos_result = unionLocal @Neg0 pos_childA pos_childB
                neg_result = unionLocal @Neg0 neg_childA neg_childB
            in if pos_result == Leaf True then Leaf True else Node positionA pos_result neg_result

        -- mismatch, but with dc inference we continue recursion with the highest (thus lowest valued) node
        -- refactor into two functions? one for mixed inference rules, one for single
        | positionA < positionB =
            let neg_result = unionLocal @Neg0 neg_childA b
            in Node positionA pos_childA neg_result

        | positionA > positionB =
            let neg_result = unionLocal @Neg0 a neg_childB
            in Node positionB pos_childB neg_result

    unionLocal a@(InfNodes positionA _ _ _ _ _)  b@(Node positionB pos_childB neg_childB)
        = Node positionB (Leaf True) (unionLocal @Neg0 a neg_childB)

    unionLocal a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _)
        = Node positionA (Leaf True) (unionLocal @Neg0 neg_childA b)

    unionLocal  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = intersection @True a b

instance DdF4 Pos1 where
    applyElimRule d@(Node _ posC negC) = if negC == Leaf False then negC else d
    restrictLocal d@(Node position pos_child neg_child) b n
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
    restrictSetLocal d [(n, b)] = restrictLocal @Pos1 d b n

    -- Leaf and node
    intersectionLocal a (Leaf False) =  Leaf False
    intersectionLocal (Leaf False) b =  Leaf False

    intersectionLocal a@(Node positionA pos_childA neg_childA) (Leaf True) = intersectionLocal @Pos1 pos_childA (Leaf True)
    intersectionLocal (Leaf True) b@(Node positionB pos_childB neg_childB) = intersectionLocal @Pos1 (Leaf True) pos_childB
    intersectionLocal (Leaf True) b = b
    intersectionLocal a (Leaf True) = a

    -- comparing nodes, allowed mis-matches based on each inference rule
    intersectionLocal a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
        -- match
        | positionA == positionB =
            let pos_result = intersectionLocal @Pos1 pos_childA pos_childB
                neg_result = intersectionLocal @Pos1 neg_childA neg_childB
            in applyElimRule @Pos1 (Node positionA pos_result neg_result)

        -- mismatch with no Bot involved, thus with ZDD types inference we return bot
        | positionA < positionB =
            intersectionLocal @Pos1 pos_childA b
        | positionA > positionB =
            intersectionLocal @Pos1 a pos_childB

    intersectionLocal a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
        Node positionB (Leaf False) (intersectionLocal @Pos1 a pos_childB)
    intersectionLocal a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB _ _ _ _ _) =
        Node positionA (Leaf False) (intersectionLocal @Pos1 pos_childA b)

    intersectionLocal  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = intersection @True a b

    intersectionLocal _ _ = error "how did we get here?"

    unionLocal a (Leaf False) =  a
    unionLocal (Leaf False) b =  b

    unionLocal a@(Node positionA pos_childA neg_childA) (Leaf True) = Node positionA (unionLocal @Pos1 pos_childA (Leaf True)) neg_childA
    unionLocal (Leaf True) b@(Node positionB pos_childB neg_childB) = Node positionB (unionLocal @Pos1 pos_childB (Leaf True)) neg_childB
    unionLocal a@(InfNodes positionA _ _ _ _ _) (Leaf True) = Leaf True
    unionLocal (Leaf True) b@(InfNodes positionB _ _ _ _ _) = Leaf True
    unionLocal (Leaf True) (Leaf True) = Leaf True

    -- comparing nodes, allowed mis-matches based on each inference rule
    unionLocal a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
        -- no mismatch, only the appropriate ZDD elim is applied
        | positionA == positionB =
            let pos_result = unionLocal @Pos1 pos_childA pos_childB
                neg_result = unionLocal @Pos1 neg_childA neg_childB
            in if neg_result == Leaf False then Leaf False else Node positionA pos_result neg_result

        -- mismatch, but with dc inference we continue recursion with the highest (thus lowest valued) node
        -- refactor into two functions? one for mixed inference rules, one for single
        | positionA < positionB =
            let pos_result = unionLocal @Pos1 pos_childA b
            in Node positionA pos_result neg_childA
        | positionA > positionB =
            let pos_result = unionLocal @Pos1 a pos_childB
            in Node positionB pos_result neg_childB
    unionLocal a@(InfNodes positionA _ _ _ _ _)  b@(Node positionB pos_childB neg_childB)
        = Node positionB (unionLocal @Pos1 a pos_childB) (Leaf False)
    unionLocal a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _)
        = Node positionA (unionLocal @Pos1 pos_childA b) (Leaf False)
    unionLocal  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = union @True a b

instance DdF4 Pos0 where
    applyElimRule d@(Node _ posC negC) = if negC == Leaf True then negC else d


    restrictLocal d@(Node position pos_child neg_child) b n
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
    restrictSetLocal d [(n, b)] = restrictLocal @Pos0 d b n


    -- Leaf and node
    intersectionLocal a (Leaf True) = Leaf True
    intersectionLocal (Leaf True) b = Leaf True

    intersectionLocal a@(Node positionA pos_childA neg_childA) (Leaf False) = intersectionLocal @Pos0 pos_childA (Leaf False)
    intersectionLocal (Leaf False) b@(Node positionB pos_childB neg_childB) = intersectionLocal @Pos0 (Leaf False) pos_childB
    intersectionLocal a@(InfNodes positionA _ _ _ _ _) (Leaf False) = a
    intersectionLocal (Leaf False) b@(InfNodes positionB _ _ _ _ _) = b
    intersectionLocal (Leaf False) (Leaf False) = Leaf False

    -- comparing nodes, allowed mis-matches based on each inference rule
    intersectionLocal a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
        -- match
        | positionA == positionB =
            let pos_result = intersectionLocal @Pos0 pos_childA pos_childB
                neg_result = intersectionLocal @Pos0 neg_childA neg_childB
            in applyElimRule @Pos0 (Node positionA pos_result neg_result)

        -- mismatch with no Bot involved, thus with ZDD types inference we return bot
        | positionA < positionB =
            intersectionLocal @Pos0 pos_childA b
        | positionA > positionB =
            intersectionLocal @Pos0 a pos_childB

    intersectionLocal a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
        Node positionB (Leaf True) (intersectionLocal @Pos0 a pos_childB)
    intersectionLocal a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB _ _ _ _ _) =
        Node positionA (Leaf True) (intersectionLocal @Pos0 pos_childA b)

    intersectionLocal  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = union @False a b
    intersectionLocal _ _ = error "how did we get here?"

    unionLocal a (Leaf True) =  a
    unionLocal (Leaf True) b =  b

    unionLocal a@(Node positionA pos_childA neg_childA) (Leaf False) = Node positionA (unionLocal @Pos0 pos_childA (Leaf False)) neg_childA
    unionLocal (Leaf False) b@(Node positionB pos_childB neg_childB) = Node positionB (unionLocal @Pos0 pos_childB (Leaf False)) neg_childB
    unionLocal a@(InfNodes positionA _ _ _ _ _) (Leaf False) = Leaf False
    unionLocal (Leaf False) b@(InfNodes positionB _ _ _ _ _) = Leaf False
    unionLocal (Leaf False) (Leaf False) = Leaf False

    -- comparing nodes, allowed mis-matches based on each inference rule
    unionLocal a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

        -- no mismatch, only the appropriate ZDD elim is applied
        | positionA == positionB =
            let pos_result = unionLocal @Pos0 pos_childA pos_childB
                neg_result = unionLocal @Pos0 neg_childA neg_childB
            in if neg_result == Leaf True then Leaf True else Node positionA pos_result neg_result

        -- mismatch, but with dc inference we continue recursion with the highest (thus lowest valued) node
        -- refactor into two functions? one for mixed inference rules, one for single
        | positionA < positionB =
            let pos_result = unionLocal @Pos0 pos_childA b
            in Node positionA pos_result neg_childA

        | positionA > positionB =
            let pos_result = unionLocal @Pos0 a pos_childB
            in Node positionB pos_result neg_childB

    unionLocal a@(InfNodes positionA _ _ _ _ _)  b@(Node positionB pos_childB neg_childB)
        = Node positionB (unionLocal @Pos0 a pos_childB) (Leaf True)

    unionLocal a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _)
        = Node positionA (unionLocal @Pos0 pos_childA b) (Leaf True)

    unionLocal  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = intersection @True a b









-- ======================= Mixed Intersections =================================================================




mixedIntersection_dc_neg1 :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal -> Dd Ordinal
mixedIntersection_dc_neg1 a b = mixedIntersection_neg1_dc b a

local_mixedIntersection_dc_neg0 :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal -> Dd Ordinal
local_mixedIntersection_dc_neg0 a b = local_mixedIntersection_neg0_dc b a

mixedIntersection_dc_pos1 :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal -> Dd Ordinal
mixedIntersection_dc_pos1 a b = mixedIntersection_pos1_dc b a

local_mixedIntersection_dc_pos0 :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal -> Dd Ordinal
local_mixedIntersection_dc_pos0 a b = local_mixedIntersection_pos0_dc b a



mixedIntersection_neg1_dc :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal -> Dd Ordinal
mixedIntersection_neg1_dc a (Leaf False) dc = Leaf False
mixedIntersection_neg1_dc a (Leaf True) dc = a
mixedIntersection_neg1_dc (Leaf False) b dc = Leaf False
mixedIntersection_neg1_dc (Leaf True) b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD)  = mixedIntersection_neg1_dc (Leaf True) neg_childB neg_childD
mixedIntersection_neg1_dc (Leaf True) b@(Node positionB pos_childB neg_childB) dc  = mixedIntersection_neg1_dc (Leaf True) neg_childB dc
mixedIntersection_neg1_dc (Leaf True) b@(InfNodes {}) dc = if dc == b then Leaf False else b

-- No leafs involved
mixedIntersection_neg1_dc a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD)

    -- No mismatch
    | positionA == positionB =
        let pos_result = mixedIntersection_neg1_dc pos_childA pos_childB pos_childD
            neg_result = mixedIntersection_neg1_dc neg_childA neg_childB neg_childD
        in applyElimRule @Neg1 (Node positionA pos_result neg_result)

    -- Mismatch
    | positionA > positionB = mixedIntersection_neg1_dc a neg_childB neg_childD
    | positionA < positionB =
        let pos_result = mixedIntersection_neg1_dc pos_childA b pos_childD
            neg_result = mixedIntersection_neg1_dc neg_childA b neg_childD
        in applyElimRule @Neg1 (Node positionA pos_result neg_result)

-- No leafs involved
mixedIntersection_neg1_dc a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) dc

    -- No mismatch
    | positionA == positionB =
        let pos_result = mixedIntersection_neg1_dc pos_childA pos_childB dc
            neg_result = mixedIntersection_neg1_dc neg_childA neg_childB dc
        in applyElimRule @Neg1 (Node positionA pos_result neg_result)

    -- Mismatch
    | positionA > positionB = mixedIntersection_neg1_dc a neg_childB dc
    | positionA < positionB =
        let pos_result = mixedIntersection_neg1_dc pos_childA b dc
            neg_result = mixedIntersection_neg1_dc neg_childA b dc
        in applyElimRule @Neg1 (Node positionA pos_result neg_result)

-- Single InfNode has been reached, similar to single Leaf node cases.
mixedIntersection_neg1_dc a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) dc =
    let pos_result = mixedIntersection_neg1_dc pos_childA b dc
        neg_result = mixedIntersection_neg1_dc neg_childA b dc
    in applyElimRule @Neg1 (Node positionA pos_result neg_result)

mixedIntersection_neg1_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD) =
    mixedIntersection_neg1_dc a neg_childB neg_childD

mixedIntersection_neg1_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) dc =
    mixedIntersection_neg1_dc a neg_childB dc

-- Both InfNodes have been reached - run the usual intersection.
mixedIntersection_neg1_dc a@(InfNodes {})  b@(InfNodes {}) dc = if (intersection @True a b) == dc then Leaf False else (intersection @True a b)
mixedIntersection_neg1_dc a b dc = undefined `debug` ("neg1 - " ++ show a ++ "  :  " ++ show b)


local_mixedIntersection_neg1_dc :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
local_mixedIntersection_neg1_dc a (Leaf False) = a
local_mixedIntersection_neg1_dc a (Leaf True) = Leaf False -- absorbed
local_mixedIntersection_neg1_dc (Leaf False) b = Leaf False
local_mixedIntersection_neg1_dc (Leaf True) b@(Node positionB pos_childB neg_childB)  = local_mixedIntersection_neg1_dc (Leaf True) neg_childB
local_mixedIntersection_neg1_dc (Leaf True) b@(InfNodes {}) = Leaf True -- following is a union call where Leaf True is preserved

-- No leafs involved
local_mixedIntersection_neg1_dc a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

    -- No mismatch
    | positionA == positionB =
        let pos_result = local_mixedIntersection_neg1_dc pos_childA pos_childB
            neg_result = local_mixedIntersection_neg1_dc neg_childA neg_childB
        in applyElimRule @Neg1 (Node positionA pos_result neg_result)

    -- Mismatch
    | positionA > positionB = local_mixedIntersection_neg1_dc a neg_childB
    | positionA < positionB =
        let pos_result = local_mixedIntersection_neg1_dc pos_childA b
            neg_result = local_mixedIntersection_neg1_dc neg_childA b
        in applyElimRule @Neg1 (Node positionA pos_result neg_result)

-- Single InfNode has been reached, similar to single Leaf node cases.
local_mixedIntersection_neg1_dc a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) =
    let pos_result = local_mixedIntersection_neg1_dc pos_childA b
        neg_result = local_mixedIntersection_neg1_dc neg_childA b
    in applyElimRule @Neg1 (Node positionA pos_result neg_result)

local_mixedIntersection_neg1_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
    local_mixedIntersection_neg1_dc a neg_childB

-- Both InfNodes have been reached - run the usual intersection.
local_mixedIntersection_neg1_dc a@(InfNodes {})  b@(InfNodes {}) = if (union @True a b) == b then Leaf False else (union @True a b)
local_mixedIntersection_neg1_dc a b = undefined `debug` ("neg1 - " ++ show a ++ "  :  " ++ show b)






local_mixedIntersection_neg0_dc :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal -> Dd Ordinal

local_mixedIntersection_neg0_dc a (Leaf False) dc = a
local_mixedIntersection_neg0_dc a (Leaf True) dc = Leaf True

local_mixedIntersection_neg0_dc (Leaf True) b dc = Leaf True
local_mixedIntersection_neg0_dc (Leaf False) b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD)  = local_mixedIntersection_neg0_dc (Leaf False) neg_childB neg_childD
local_mixedIntersection_neg0_dc (Leaf False) b@(Node positionB pos_childB neg_childB) dc  = local_mixedIntersection_neg0_dc (Leaf False) neg_childB dc
local_mixedIntersection_neg0_dc (Leaf False) b@(InfNodes {}) dc = if b == dc then Leaf True else b
-- following domain becomes union call, where Leaf False is interpreted as bot, thus b should be returned. -- todo the resulting return should still be removed if it equals dcR

-- No leafs involved
local_mixedIntersection_neg0_dc a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD)

    -- No mismatch
    | positionA == positionB =
        let pos_result = local_mixedIntersection_neg0_dc pos_childA pos_childB pos_childD
            neg_result = local_mixedIntersection_neg0_dc neg_childA neg_childB neg_childD
        in applyElimRule @Neg0 (Node positionA pos_result neg_result)

    -- Mismatch
    | positionA > positionB = local_mixedIntersection_neg0_dc a neg_childB neg_childD
    | positionA < positionB =
        let pos_result = local_mixedIntersection_neg0_dc pos_childA b dc
            neg_result = local_mixedIntersection_neg0_dc neg_childA b dc
        in applyElimRule @Neg0 (Node positionA pos_result neg_result)

local_mixedIntersection_neg0_dc a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) dc

    -- No mismatch
    | positionA == positionB =
        let pos_result = local_mixedIntersection_neg0_dc pos_childA pos_childB dc
            neg_result = local_mixedIntersection_neg0_dc neg_childA neg_childB dc
        in applyElimRule @Neg0 (Node positionA pos_result neg_result)

    -- Mismatch
    | positionA > positionB = local_mixedIntersection_neg0_dc a neg_childB dc
    | positionA < positionB =
        let pos_result = local_mixedIntersection_neg0_dc pos_childA b dc
            neg_result = local_mixedIntersection_neg0_dc neg_childA b dc
        in applyElimRule @Neg0 (Node positionA pos_result neg_result)

-- Single InfNode has been reached, similar to single Leaf node cases.
local_mixedIntersection_neg0_dc a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) dc =
    let pos_result = local_mixedIntersection_neg0_dc pos_childA b dc
        neg_result = local_mixedIntersection_neg0_dc neg_childA b dc
    in applyElimRule @Neg0 (Node positionA pos_result neg_result)
local_mixedIntersection_neg0_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD) =
    local_mixedIntersection_neg0_dc a neg_childB neg_childD
local_mixedIntersection_neg0_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) dc =
    local_mixedIntersection_neg0_dc a neg_childB dc

-- Both InfNodes have been reached - run the usual intersection.
local_mixedIntersection_neg0_dc a@(InfNodes {})  b@(InfNodes {}) dc =  if (union @False a b) == dc then Leaf True else (union @False a b)
local_mixedIntersection_neg0_dc a b dc = error ("neg0 - " ++ show a ++ "  :  " ++ show b)

local_mixedIntersection2_neg0_dc :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
local_mixedIntersection2_neg0_dc a (Leaf False) = Leaf True
local_mixedIntersection2_neg0_dc a (Leaf True) = a
local_mixedIntersection2_neg0_dc (Leaf True) b = Leaf True
local_mixedIntersection2_neg0_dc (Leaf False) b@(Node positionB pos_childB neg_childB)  = Leaf False
local_mixedIntersection2_neg0_dc (Leaf False) b@(InfNodes {}) = Leaf False -- following domain becomes intersection call

-- No leafs involved
local_mixedIntersection2_neg0_dc a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

    -- No mismatch
    | positionA == positionB =
        let pos_result = local_mixedIntersection2_neg0_dc pos_childA pos_childB
            neg_result = local_mixedIntersection2_neg0_dc neg_childA neg_childB
        in applyElimRule @Neg0 (Node positionA pos_result neg_result)

    -- Mismatch
    | positionA > positionB = local_mixedIntersection2_neg0_dc a neg_childB
    | positionA < positionB =
        let pos_result = local_mixedIntersection2_neg0_dc pos_childA b
            neg_result = local_mixedIntersection2_neg0_dc neg_childA b
        in applyElimRule @Neg0 (Node positionA pos_result neg_result)

-- Single InfNode has been reached, similar to single Leaf node cases.
local_mixedIntersection2_neg0_dc a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) =
    let pos_result = local_mixedIntersection2_neg0_dc pos_childA b
        neg_result = local_mixedIntersection2_neg0_dc neg_childA b
    in applyElimRule @Neg0 (Node positionA pos_result neg_result)
local_mixedIntersection2_neg0_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
    local_mixedIntersection2_neg0_dc a neg_childB

-- Both InfNodes have been reached - run the usual intersection.
local_mixedIntersection2_neg0_dc a@(InfNodes {})  b@(InfNodes {}) =  if (intersection @True a b) == b then Leaf True else (intersection @True a b)
local_mixedIntersection2_neg0_dc a b = undefined `debug` ("neg0 - " ++ show a ++ "  :  " ++ show b)


mixedIntersection_pos1_dc :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal -> Dd Ordinal
mixedIntersection_pos1_dc a (Leaf False) dc = Leaf False
mixedIntersection_pos1_dc a (Leaf True) dc = a
mixedIntersection_pos1_dc (Leaf False) a dc = Leaf False
mixedIntersection_pos1_dc (Leaf True) b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD) = mixedIntersection_pos1_dc (Leaf True) pos_childB pos_childD
mixedIntersection_pos1_dc (Leaf True) b@(Node positionB pos_childB neg_childB) dc = mixedIntersection_pos1_dc (Leaf True) pos_childB dc
mixedIntersection_pos1_dc (Leaf True) b@(InfNodes {}) dc = if b == dc then Leaf False else b

-- No leafs involved
mixedIntersection_pos1_dc a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD)

    -- No mismatch
    | positionA == positionB =
        let pos_result = mixedIntersection_pos1_dc pos_childA pos_childB pos_childD
            neg_result = mixedIntersection_pos1_dc neg_childA neg_childB neg_childD
        in applyElimRule @Pos1 (Node positionA pos_result neg_result)

    -- Mismatch
    | positionA > positionB = mixedIntersection_pos1_dc a pos_childB pos_childD
    | positionA < positionB =
        let pos_result = mixedIntersection_pos1_dc pos_childA b dc
            neg_result = mixedIntersection_pos1_dc neg_childA b dc
        in applyElimRule @Pos1 (Node positionA pos_result neg_result)

-- No leafs involved
mixedIntersection_pos1_dc a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) dc

    -- No mismatch
    | positionA == positionB =
        let pos_result = mixedIntersection_pos1_dc pos_childA pos_childB dc
            neg_result = mixedIntersection_pos1_dc neg_childA neg_childB dc
        in applyElimRule @Pos1 (Node positionA pos_result neg_result)

    -- Mismatch
    | positionA > positionB = mixedIntersection_pos1_dc a pos_childB dc
    | positionA < positionB =
        let pos_result = mixedIntersection_pos1_dc pos_childA b dc
            neg_result = mixedIntersection_pos1_dc neg_childA b dc
        in applyElimRule @Pos1 (Node positionA pos_result neg_result)

-- Single InfNode has been reached, similar to single Leaf node cases.
mixedIntersection_pos1_dc a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) dc =
    let pos_result = mixedIntersection_pos1_dc pos_childA b dc
        neg_result = mixedIntersection_pos1_dc neg_childA b dc
    in applyElimRule @Pos1 (Node positionA pos_result neg_result)


mixedIntersection_pos1_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD) =
    mixedIntersection_pos1_dc a pos_childB pos_childD
mixedIntersection_pos1_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) dc =
    mixedIntersection_pos1_dc a pos_childB dc

-- Both InfNodes have been reached - run the usual intersection.
mixedIntersection_pos1_dc a@(InfNodes {})  b@(InfNodes {}) dc = if (intersection @True a b) == dc then Leaf False else (intersection @True a b)
mixedIntersection_pos1_dc a b dc = undefined `debug` ("pos1" ++ show a ++ "  :  " ++ show b)

local_mixedIntersection_pos1_dc :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
local_mixedIntersection_pos1_dc a (Leaf False) = a
local_mixedIntersection_pos1_dc a (Leaf True) = Leaf False --becomes a union call, should thus return Leaf True, but since the consequences are the same they are absrbed.
local_mixedIntersection_pos1_dc (Leaf False) a = Leaf False
local_mixedIntersection_pos1_dc (Leaf True) b@(Node positionB pos_childB neg_childB) = local_mixedIntersection_pos1_dc (Leaf True) pos_childB
local_mixedIntersection_pos1_dc (Leaf True) b@(InfNodes {}) = Leaf True -- becomes union where leaf true dominates

-- No leafs involved
local_mixedIntersection_pos1_dc a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

    -- No mismatch
    | positionA == positionB =
        let pos_result = local_mixedIntersection_pos1_dc pos_childA pos_childB
            neg_result = local_mixedIntersection_pos1_dc neg_childA neg_childB
        in applyElimRule @Pos1 (Node positionA pos_result neg_result)

    -- Mismatch
    | positionA > positionB = local_mixedIntersection_pos1_dc a pos_childB
    | positionA < positionB =
        let pos_result = local_mixedIntersection_pos1_dc pos_childA b
            neg_result = local_mixedIntersection_pos1_dc neg_childA b
        in applyElimRule @Pos1 (Node positionA pos_result neg_result)

-- Single InfNode has been reached, similar to single Leaf node cases.
local_mixedIntersection_pos1_dc a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) =
    let pos_result = local_mixedIntersection_pos1_dc pos_childA b
        neg_result = local_mixedIntersection_pos1_dc neg_childA b
    in applyElimRule @Pos1 (Node positionA pos_result neg_result)


local_mixedIntersection_pos1_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
    local_mixedIntersection_pos1_dc a pos_childB

local_mixedIntersection_pos1_dc a@(InfNodes {})  b@(InfNodes {}) = if (union @True a b) == b then Leaf False else (union @True a b)
local_mixedIntersection_pos1_dc a b = undefined `debug` ("pos1" ++ show a ++ "  :  " ++ show b)



local_mixedIntersection_pos0_dc :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal -> Dd Ordinal

local_mixedIntersection_pos0_dc (Leaf True) b dc = Leaf True
local_mixedIntersection_pos0_dc (Leaf False) b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD)  = local_mixedIntersection_pos0_dc (Leaf False) pos_childB pos_childD
local_mixedIntersection_pos0_dc (Leaf False) b@(Node positionB pos_childB neg_childB) dc  = local_mixedIntersection_pos0_dc (Leaf False) pos_childB dc
local_mixedIntersection_pos0_dc (Leaf False) b@(InfNodes {}) dc = Leaf True

local_mixedIntersection_pos0_dc a (Leaf False) dc = a
local_mixedIntersection_pos0_dc a (Leaf True) dc = Leaf True


-- No leafs involved
local_mixedIntersection_pos0_dc a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD)

    -- No mismatch
    | positionA == positionB =
        let pos_result = local_mixedIntersection_pos0_dc pos_childA pos_childB pos_childD
            neg_result = local_mixedIntersection_pos0_dc neg_childA neg_childB neg_childD
        in applyElimRule @Pos0 (Node positionA pos_result neg_result)

    -- Mismatch
    | positionA > positionB = local_mixedIntersection_pos0_dc a pos_childB pos_childD
    | positionA < positionB =
        let pos_result = local_mixedIntersection_pos0_dc pos_childA b dc
            neg_result = local_mixedIntersection_pos0_dc neg_childA b dc
        in applyElimRule @Pos0 (Node positionA pos_result neg_result)

-- No leafs involved
local_mixedIntersection_pos0_dc a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) dc

    -- No mismatch
    | positionA == positionB =
        let pos_result = local_mixedIntersection_pos0_dc pos_childA pos_childB dc
            neg_result = local_mixedIntersection_pos0_dc neg_childA neg_childB dc
        in applyElimRule @Pos0 (Node positionA pos_result neg_result)

    -- Mismatch
    | positionA > positionB = local_mixedIntersection_pos0_dc a pos_childB dc
    | positionA < positionB =
        let pos_result = local_mixedIntersection_pos0_dc pos_childA b dc
            neg_result = local_mixedIntersection_pos0_dc neg_childA b dc
        in applyElimRule @Pos0 (Node positionA pos_result neg_result)

-- Single InfNode has been reached, similar to single Leaf node cases.
local_mixedIntersection_pos0_dc a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) dc =
    let pos_result = local_mixedIntersection_pos0_dc pos_childA b dc
        neg_result = local_mixedIntersection_pos0_dc neg_childA b dc
    in applyElimRule @Pos0 (Node positionA pos_result neg_result)

local_mixedIntersection_pos0_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD) =
    local_mixedIntersection_pos0_dc a neg_childB neg_childD
local_mixedIntersection_pos0_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) dc =
    local_mixedIntersection_pos0_dc a neg_childB dc

-- Both InfNodes have been reached - run the usual intersection.
local_mixedIntersection_pos0_dc a@(InfNodes {})  b@(InfNodes {}) dc = if (union @False a b) == dc then Leaf True else (union @False a b)
local_mixedIntersection_pos0_dc a b dc = undefined `debug` ("pos0 - " ++ show a ++ "  :  " ++ show b)




local_mixedIntersection2_pos0_dc :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
local_mixedIntersection2_pos0_dc a (Leaf False) = Leaf True
local_mixedIntersection2_pos0_dc a (Leaf True) = a
local_mixedIntersection2_pos0_dc (Leaf True) b = Leaf True
local_mixedIntersection2_pos0_dc (Leaf False) b@(Node positionB pos_childB neg_childB)  = Leaf True
local_mixedIntersection2_pos0_dc (Leaf False) b@(InfNodes {}) = Leaf False

-- No leafs involved
local_mixedIntersection2_pos0_dc a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

    -- No mismatch
    | positionA == positionB =
        let pos_result = local_mixedIntersection2_pos0_dc pos_childA pos_childB
            neg_result = local_mixedIntersection2_pos0_dc neg_childA neg_childB
        in applyElimRule @Pos0 (Node positionA pos_result neg_result)

    -- Mismatch
    | positionA > positionB = local_mixedIntersection2_pos0_dc a pos_childB
    | positionA < positionB =
        let pos_result = local_mixedIntersection2_pos0_dc pos_childA b
            neg_result = local_mixedIntersection2_pos0_dc neg_childA b
        in applyElimRule @Pos0 (Node positionA pos_result neg_result)

-- Single InfNode has been reached, similar to single Leaf node cases.
local_mixedIntersection2_pos0_dc a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) =
    let pos_result = local_mixedIntersection2_pos0_dc pos_childA b
        neg_result = local_mixedIntersection2_pos0_dc neg_childA b
    in applyElimRule @Pos0 (Node positionA pos_result neg_result)

local_mixedIntersection2_pos0_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
    local_mixedIntersection2_pos0_dc a neg_childB

-- Both InfNodes have been reached - run the usual intersection.
local_mixedIntersection2_pos0_dc a@(InfNodes {})  b@(InfNodes {}) = if (intersection @True a b) == b then Leaf True else (intersection @True a b)
local_mixedIntersection2_pos0_dc a b = undefined `debug` ("pos0 - " ++ show a ++ "  :  " ++ show b)


























remove_f0s1_from_f1s1 :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
remove_f0s1_from_f1s1 a (Leaf False) = Leaf False
remove_f0s1_from_f1s1 a@(Node positionA pos_childA neg_childA) (Leaf True) = remove_f0s1_from_f1s1 neg_childA (Leaf True)
remove_f0s1_from_f1s1 (Leaf False) b@(Node positionB pos_childB neg_childB) = Node positionB pos_childB (remove_f0s1_from_f1s1 (Leaf False) neg_childB) --if pos_child == Leaf False then pos_child else b@(Node positionB pos_childB neg_childB)
remove_f0s1_from_f1s1 (Leaf True) b = b
remove_f0s1_from_f1s1 (Leaf False) (Leaf True)  =  Leaf False

-- No leafs involved
remove_f0s1_from_f1s1 a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)-- no mismatch, thus no inference is needed

    -- No mismatch, only the appropriate ZDD elim is applied
    | positionA == positionB =
        let pos_result = remove_f0s1_from_f1s1 pos_childA pos_childB
            neg_result = remove_f0s1_from_f1s1 neg_childA neg_childB
        in applyElimRule @Neg1 (Node positionA pos_result neg_result)

    -- mismatch with no Bot involved, thus with ZDD types inference we return bot
    | positionA < positionB =
        remove_f0s1_from_f1s1 neg_childA b
    | positionA > positionB =
        Node positionB pos_childB (remove_f0s1_from_f1s1 a neg_childB)


-- Single InfNode has been reached, similar to single Leaf node cases.
remove_f0s1_from_f1s1 a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) =
    Node positionA (Leaf False) (remove_f0s1_from_f1s1 neg_childA b)
remove_f0s1_from_f1s1 a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
    Node positionB (Leaf False) (remove_f0s1_from_f1s1 a neg_childB)

-- Both InfNodes have been reached - run the usual intersection.
remove_f0s1_from_f1s1  a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B) = intersection @True a b
remove_f0s1_from_f1s1 a b = undefined `debug` (show a ++ "  :  " ++ show b)


remove_f1s1_from_f0s1 :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
remove_f1s1_from_f0s1 a (Leaf True) = Leaf True
remove_f1s1_from_f0s1 a@(Node positionA pos_childA neg_childA) (Leaf False) = remove_f1s1_from_f0s1 neg_childA (Leaf False)
remove_f1s1_from_f0s1 (Leaf True) b@(Node positionB pos_childB neg_childB) = Node positionB pos_childB (remove_f1s1_from_f0s1 (Leaf True) neg_childB) --if pos_child == Leaf False then pos_child else b@(Node positionB pos_childB neg_childB)
remove_f1s1_from_f0s1 (Leaf False) b = b

remove_f1s1_from_f0s1 (Leaf True) (Leaf False)  =  Leaf True

-- No leafs involved
remove_f1s1_from_f0s1 a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)-- no mismatch, thus no inference is needed

    -- No mismatch, only the appropriate ZDD elim is applied
    | positionA == positionB =
        let pos_result = remove_f1s1_from_f0s1 pos_childA pos_childB
            neg_result = remove_f1s1_from_f0s1 neg_childA neg_childB
        in if pos_result == Leaf True then Leaf True else Node positionA pos_result neg_result

    -- mismatch with no Bot involved, thus with ZDD types inference we return bot
    | positionA < positionB =
        remove_f1s1_from_f0s1 neg_childA b
    | positionA > positionB =
        Node positionB pos_childB (remove_f1s1_from_f0s1 a neg_childB)


-- Single InfNode has been reached, similar to single Leaf node cases.
remove_f1s1_from_f0s1 a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) =
    Node positionA (Leaf True) (remove_f1s1_from_f0s1 neg_childA b)
remove_f1s1_from_f0s1 a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
    Node positionB (Leaf True) (remove_f1s1_from_f0s1 a neg_childB)

-- Both InfNodes have been reached - run the usual intersection.
remove_f1s1_from_f0s1  a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B) = intersection @True a b
remove_f1s1_from_f0s1 a b = undefined `debug` (show a ++ "  :  " ++ show b)


remove_f0s0_from_f1s0 :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
remove_f0s0_from_f1s0 a (Leaf False) = Leaf False
remove_f0s0_from_f1s0 a@(Node positionA pos_childA neg_childA) (Leaf True) = remove_f0s0_from_f1s0 pos_childA (Leaf True)
remove_f0s0_from_f1s0 (Leaf False) b@(Node positionB pos_childB neg_childB) = Node positionB (remove_f0s0_from_f1s0 (Leaf False) pos_childB) neg_childB  --if pos_child == Leaf False then pos_child else b@(Node positionB pos_childB neg_childB)
remove_f0s0_from_f1s0 (Leaf True) b = b

remove_f0s0_from_f1s0 (Leaf False) (Leaf True)  =  Leaf False

-- No leafs involved
remove_f0s0_from_f1s0 a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)-- no mismatch, thus no inference is needed

    -- No mismatch, only the appropriate ZDD elim is applied
    | positionA == positionB =
        let pos_result = remove_f0s0_from_f1s0 pos_childA pos_childB
            neg_result = remove_f0s0_from_f1s0 neg_childA neg_childB
        in if neg_result == Leaf False then Leaf False else Node positionA pos_result neg_result

    -- mismatch with no Bot involved, thus with ZDD types inference we return bot
    | positionA < positionB =
        remove_f0s0_from_f1s0 pos_childA b
    | positionA > positionB =
        Node positionB (remove_f0s0_from_f1s0 a pos_childB) neg_childB


-- Single InfNode has been reached, similar to single Leaf node cases.
remove_f0s0_from_f1s0 a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) =
    Node positionA (Leaf False) (remove_f0s0_from_f1s0 pos_childA b)
remove_f0s0_from_f1s0 a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
    Node positionB (Leaf False) (remove_f0s0_from_f1s0 a pos_childB)

-- Both InfNodes have been reached - run the usual intersection.
remove_f0s0_from_f1s0  a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B) = intersection @True a b
remove_f0s0_from_f1s0 a b = undefined `debug` (show a ++ "  :  " ++ show b)



remove_f1s0_from_f0s0 :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
remove_f1s0_from_f0s0 a (Leaf True) = Leaf True
remove_f1s0_from_f0s0 a@(Node positionA pos_childA neg_childA) (Leaf False) = remove_f1s0_from_f0s0 pos_childA (Leaf False)
remove_f1s0_from_f0s0 (Leaf True) b@(Node positionB pos_childB neg_childB) = Node positionB (remove_f1s0_from_f0s0 (Leaf True) pos_childB) neg_childB  --if pos_child == Leaf False then pos_child else b@(Node positionB pos_childB neg_childB)
remove_f1s0_from_f0s0 (Leaf False) b = b

remove_f1s0_from_f0s0 (Leaf True) (Leaf False)  =  Leaf True

-- No leafs involved
remove_f1s0_from_f0s0 a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)-- no mismatch, thus no inference is needed

    -- No mismatch, only the appropriate ZDD elim is applied
    | positionA == positionB =
        let pos_result = remove_f1s0_from_f0s0 pos_childA pos_childB
            neg_result = remove_f1s0_from_f0s0 neg_childA neg_childB
        in if neg_result == Leaf True then Leaf True else Node positionA pos_result neg_result

    -- mismatch with no Bot involved, thus with ZDD types inference we return bot
    | positionA < positionB =
        remove_f1s0_from_f0s0 pos_childA b
    | positionA > positionB =
        Node positionB (remove_f1s0_from_f0s0 a pos_childB) neg_childB


-- Single InfNode has been reached, similar to single Leaf node cases.
remove_f1s0_from_f0s0 a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) =
    Node positionA (Leaf True) (remove_f1s0_from_f0s0 pos_childA b)
remove_f1s0_from_f0s0 a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
    Node positionB (Leaf True) (remove_f1s0_from_f0s0 a pos_childB)

-- Both InfNodes have been reached - run the usual intersection.
remove_f1s0_from_f0s0  a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B) = intersection @True a b
remove_f1s0_from_f0s0 a b = undefined `debug` (show a ++ "  :  " ++ show b)




debug :: c -> String -> c
debug = flip trace
