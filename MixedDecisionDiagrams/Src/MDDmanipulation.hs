{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module MixedDecisionDiagrams.Src.MDDmanipulation where

import MixedDecisionDiagrams.Src.MDD
import Debug.Trace (trace)



negation :: Dd Ordinal -> Dd Ordinal
negation (Node position pos_child neg_child) = Node position (negation pos_child) (negation neg_child)
negation (InfNodes position dc_n n1_n n0_n p1_n p0_n) = InfNodes position (negation dc_n) (negation n0_n) (negation n1_n) (negation p0_n) (negation p1_n)
negation (Leaf b) = Leaf $ not b

isInfNode :: Dd a -> Bool
isInfNode(InfNodes _ _ _ _ _ _) = True
isInfNode _ = False

restrict :: Dd Ordinal -> Bool -> Ordinal -> Dd Ordinal
restrict d@(InfNodes position dc n1 n0 p1 p0) b n = undefined
restrict d@(Node position pos_child neg_child) b n = undefined
restrict d@(Leaf _) b n = d

-- if above n then skip and continue
-- if equal then check context, in Dc and f1 do normal restrict, in f0 do oposite. s1 and s0 do not matter.
-- if below n then return whatever
-- is there a has function which preserves level? that would be very useful..
-- apply all apriopriate reduction steps wherever needed


intersection :: Dd Ordinal -> Dd Ordinal  -> Dd Ordinal
intersection  a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B)
    | positionA == positionB =  let
        dcR = intersection_dc dcA dcB

        n1R = union_neg1
            (intersection_neg1 n1A n1B) -- overlapping points are by definition not inside the others dc, thus have to be preserved
            (if n0R' == Leaf True then n1R' else remove_f0s1_from_f1s1 n0R' n1R') -- holes absorb points under intersection
        n1R' = union_neg1 -- guaranteed that dcA and dcB do not overlap around the finite points, thus they do not get absorbed
            (mixedIntersection_neg1_dc n1A dcB dcR) -- keep the points that fit inside B
            (mixedIntersection_neg1_dc n1B dcA dcR) -- keep the points that fit inside A

        n0R' = local_union_neg0 n0A n0B -- holes get unioned, because i keep the consequence of holes "uncomplemented" we get local union then intersection.
        n0R = local_mixedIntersection2_neg0_dc n0R' dcR -- keep the holes that fit inside dcR
        -- if the local hole fits inside dcR but the consequence of n0R' does not fit inside the consequenc of dcR it should return n0R' -> Leaf false
        ------------------------------------
        p1R = union_pos1
            (intersection_pos1 p1A p1B)
            (if p0R' == Leaf True then p1R' else remove_f0s0_from_f1s0 p0R' p1R')
        p1R' = union_pos1
            (mixedIntersection_pos1_dc p1A dcB dcR)
            (mixedIntersection_pos1_dc p1B dcA dcR)
        p0R' = local_union_pos0 p0A p0B -- local union then intersection
        p0R = local_mixedIntersection2_pos0_dc p0R' dcR
        in elimInfNode positionA dcR n1R n0R p1R p0R

    | positionA > positionB = let -- replace all the A stuf with (dc: a, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
        dcR = intersection_dc a dcB
        n1R = if n0B == Leaf True then
            mixedIntersection_neg1_dc n1B a dcR  else
            remove_f0s1_from_f1s1 n0B (mixedIntersection_neg1_dc n1B a dcR)
        n0R = local_mixedIntersection2_neg0_dc n0B dcR --`debug` ( "inter: " ++ show (local_mixedIntersection2_neg0_dc n0A dcR) ++ "\n n0A: " ++ show n0A  ++ "\n dcR" ++ show dcR)
        p1R = if p0B == Leaf True then
            mixedIntersection_pos1_dc p1B a dcR else
            remove_f0s0_from_f1s0 p0B (mixedIntersection_pos1_dc p1B a dcR)
        p0R = local_mixedIntersection2_pos0_dc p0B dcR
        in elimInfNode positionB dcR n1R n0R p1R p0R

    | positionA < positionB = let -- replace all the B stuf with (dc: b, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
        dcR = intersection_dc dcA b
        n1R = if n0A == Leaf True then
            mixedIntersection_neg1_dc n1A b dcR  else
            remove_f0s1_from_f1s1 n0A (mixedIntersection_neg1_dc n1A b dcR)
        n0R = local_mixedIntersection2_neg0_dc n0A dcR --`debug` ( "inter: " ++ show (local_mixedIntersection2_neg0_dc n0A dcR) ++ "\n n0A: " ++ show n0A  ++ "\n dcR" ++ show dcR)
        p1R = if p0A == Leaf True then
            mixedIntersection_pos1_dc p1A b dcR else
            remove_f0s0_from_f1s0 p0A (mixedIntersection_pos1_dc p1A b dcR)
        p0R = local_mixedIntersection2_pos0_dc p0A dcR
        in elimInfNode positionA dcR n1R n0R p1R p0R --`debug` ("dcR" ++ show dcR ++ "\n p0A" ++ show p0A)

    where
        elimInfNode pos dcR n1R n0R p1R p0R = if (n1R, n0R, p1R, p0R) == (Leaf False, Leaf True, Leaf False, Leaf True) then
                    (if isInfNode dcR then dcR else
                        if dcR == Leaf True then Leaf True else
                            if dcR == Leaf False then Leaf False else
                                InfNodes pos dcR n1R n0R p1R p0R)
                    else InfNodes pos dcR n1R n0R p1R p0R
intersection a (Leaf False) = (Leaf False)
intersection (Leaf False) b = (Leaf False)
intersection a (Leaf True) = a
intersection (Leaf True) b = b
intersection _ _ = error "missed case?"

intersection_0 :: Dd Ordinal -> Dd Ordinal  -> Dd Ordinal
intersection_0  a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B)
    | positionA == positionB =  let
        dcR = intersection_dc dcA dcB
        n1R = union_neg1
            (intersection_neg1 n1A n1B)
            (if n0R' == Leaf True then n1R' else remove_f0s1_from_f1s1 n0R' n1R')
        n1R' = union_neg1
            (mixedIntersection_neg1_dc n1A dcB dcR) -- remove the points that fit inside B
            (mixedIntersection_neg1_dc n1B dcA dcR)
        n0R' = local_union_neg0 n0A n0B
        n0R = local_mixedIntersection2_neg0_dc n0R' dcR
        ------------------------------------
        p1R = union_pos1
            (intersection_pos1 p1A p1B)
            (if p0R' == Leaf True then p1R' else remove_f0s0_from_f1s0 p0R' p1R')
        p1R' = union_pos1
            (mixedIntersection_pos1_dc p1A dcB dcR)
            (mixedIntersection_pos1_dc p1B dcA dcR)
        p0R' = local_union_pos0 p0A p0B
        p0R = local_mixedIntersection2_pos0_dc p0R' dcR
        in elimInfNode positionA dcR n1R n0R p1R p0R

    | positionA > positionB = let -- replace all the A stuf with (dc: a, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
        dcR = intersection_dc a dcB
        n1R = if n0B == Leaf True then
            mixedIntersection_neg1_dc n1B a dcR  else
            remove_f0s1_from_f1s1 n0B (mixedIntersection_neg1_dc n1B a dcR)
        n0R = local_mixedIntersection2_neg0_dc n0B dcR
        p1R = if p0B == Leaf True then
            mixedIntersection_pos1_dc p1B a dcR else
            remove_f0s0_from_f1s0 p0B (mixedIntersection_pos1_dc p1B a dcR)
        p0R = local_mixedIntersection2_pos0_dc p0B dcR
        in elimInfNode positionB dcR n1R n0R p1R p0R

    | positionA < positionB = let -- replace all the B stuf with (dc: b, neg1: 0, neg0: 1, pos1: 0, pos0: 1)
        dcR = intersection_dc dcA b
        n1R = if n0A == Leaf True then
            mixedIntersection_neg1_dc n1A b dcR  else
            remove_f0s1_from_f1s1 n0A (mixedIntersection_neg1_dc n1A b dcR)
        n0R = local_mixedIntersection2_neg0_dc n0A dcR
        p1R = if p0A == Leaf True then
            mixedIntersection_pos1_dc p1A b dcR else
            remove_f0s0_from_f1s0 p0A (mixedIntersection_pos1_dc p1A b dcR)
        p0R = local_mixedIntersection2_pos0_dc p0A dcR -- read pos0 until next subdomain, then just intersect with dcR
        in elimInfNode positionA dcR n1R n0R p1R p0R

    where
        elimInfNode pos dcR n1R n0R p1R p0R = if (n1R, n0R, p1R, p0R) == (Leaf False, Leaf True, Leaf False, Leaf True) then
                    (if isInfNode dcR then dcR else
                        if dcR == Leaf False then Leaf False else
                            if dcR == Leaf True then Leaf True else
                                InfNodes pos dcR n1R n0R p1R p0R)
                    else InfNodes pos dcR n1R n0R p1R p0R
intersection_0 a (Leaf True) = (Leaf True)
intersection_0 (Leaf True) b = (Leaf True)
intersection_0 a (Leaf False) = a
intersection_0 (Leaf False) b = b
intersection_0 _ _ = error "missed case?"

union :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
-- exclusive points (0's / holes) under union are filled unless they are present in both A and B (so only an intersection between them needs to be done)
-- inclusive point (1's ) under union are intersected with the opposite infinite subset (dc) before they are added together
union  a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B)
    | positionA == positionB =  let
        dcR = union_dc dcA dcB

        n1R = local_mixedIntersection_neg1_dc n1R' dcR -- union the consequences of n1R with dcR, then if they are the same absorb them
        n1R' = union_neg1 n1A n1B --`debug` show (union_neg1 n1A n1B) -- union all points

        n0R = local_union_neg0 -- union then intersection
            (local_intersection_neg0 n0A n0B) -- intersection then union
            (if n1R' == Leaf False then n0R' else remove_f1s1_from_f0s1 n1R' n0R')
        n0R' = local_union_neg0
            (local_mixedIntersection_neg0_dc n0A dcB dcR) -- remove the holes that do fit in B (unioned away) // note that in consequence this reverts back to to union and is absorbed if consequence of n0A == dcR
            (local_mixedIntersection_neg0_dc n0B dcA dcR) -- remove the holes that do fit in A (unioned away)
            --`debug` ("dcB: " ++ show dcB)


        ------------------------------------
        -- n0R = (n0A cap n0B) cup ((n0A cap neg dcB) cap n1B) cup ((n0B cap neg dcA) cap n1A) <-> (n0A cup n0B) cap n1R* cap neg dcR
        p1R = local_mixedIntersection_pos1_dc p1R' dcR
        p1R' = union_pos1 p1A p1B
        p0R = local_union_pos0
            (local_intersection_pos0 p0A p0B)
            (if p1R' == Leaf False then p0R' else remove_f1s0_from_f0s0 p1R' p0R')
        p0R' = local_union_pos0
            (local_mixedIntersection_pos0_dc p0A dcB dcR) -- remove the holes that do fit in B: if the consequence of p0A after union is the same as the consequence of dcB, then it is also removed. If the consequence is smaller it is kept.
            (local_mixedIntersection_pos0_dc p0B dcA dcR)

        in elimInfNode positionA dcR n1R n0R p1R p0R

    | positionA > positionB = let -- A is inferred to be Top
        dcR = union_dc a dcB --pass along the consequence of B for both dcA and not dcA
        n1R = local_mixedIntersection_neg1_dc n1B dcR

        n0R = let n0R' = local_mixedIntersection_neg0_dc n0B a dcR in
            if n1B == Leaf False then n0R' else remove_f1s1_from_f0s1 n1B n0R'

        p1R = local_mixedIntersection_pos1_dc p1B dcR
        p0R = let p0R' = local_mixedIntersection_pos0_dc p0B a dcR in
            if p1B == Leaf False then p0R' else remove_f1s0_from_f0s0 p1B p0R'

        in elimInfNode positionB dcR n1R n0R p1R p0R

    | positionA < positionB = let
        dcR = union_dc b dcA
        n1R = local_mixedIntersection_neg1_dc n1A dcR

        n0R = let n0R' = local_mixedIntersection_neg0_dc n0A b dcR in
            if n1A == Leaf False then n0R' else remove_f1s1_from_f0s1 n1A n0R'


        p1R = local_mixedIntersection_pos1_dc p1A dcR
        p0R = let p0R' = local_mixedIntersection_pos0_dc p0A b dcR in
            if p1A == Leaf False then p0R' else remove_f1s0_from_f0s0 p1A p0R'

        in elimInfNode positionA dcR n1R n0R p1R p0R

        where
            elimInfNode pos dcR n1R n0R p1R p0R = if (n1R, n0R, p1R, p0R) == (Leaf False, Leaf True, Leaf False, Leaf True) then
                    (if isInfNode dcR then dcR else
                        if dcR == Leaf True then Leaf True else
                            if dcR == Leaf False then Leaf False else
                                InfNodes pos dcR n1R n0R p1R p0R)
                    else InfNodes pos dcR n1R n0R p1R p0R
union a (Leaf True) = (Leaf True)
union (Leaf True) b = (Leaf True)
union a (Leaf False) = a
union (Leaf False) b = b
union _ _ = error "missed case?"


union_0 :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
-- exclusive points (0's / holes) under union are filled unless they are present in both A and B (so only an intersection between them needs to be done)
-- inclusive point (1's ) under union are intersected with the opposite infinite subset (dc) before they are added together
union_0  a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B)
    | positionA == positionB =  let
        dcR = union_dc dcA dcB
        n1R = local_mixedIntersection_neg1_dc n1R' dcR -- remove the points that fit inside R
        n1R' = union_neg1 n1A n1B
        n0R = local_union_neg0
            (local_intersection_neg0 n0A n0B)
            (if n1R' == Leaf False then n0R' else remove_f1s1_from_f0s1 n1R' n0R')
        n0R' = local_union_neg0
            (local_mixedIntersection_neg0_dc n0A dcB dcR) -- remove the holes that do fit in B
            (local_mixedIntersection_neg0_dc n0B dcA dcR)
        ------------------------------------
        -- n0R = (n0A cap n0B) cup ((n0A cap neg dcB) cap n1B) cup ((n0B cap neg dcA) cap n1A) <-> (n0A cup n0B) cap n1R* cap neg dcR
        p1R = local_mixedIntersection_pos1_dc p1R' dcR -- remove the points that fit inside R
        p1R' = union_pos1 p1A p1B

        p0R = local_union_pos0
            (local_intersection_pos0 p0A p0B)
            (if p1R' == Leaf False then p0R' else remove_f1s0_from_f0s0 p1R' p0R') --`debug` ("local intersection: " ++ show (local_intersection_pos0 p0A p0B) ++ "\n" ++ show p0A ++ "\n" ++ show p0B)
        p0R' = local_union_pos0
            (local_mixedIntersection_pos0_dc p0A dcB dcR) -- remove the holes that do fit in B
            (local_mixedIntersection_pos0_dc p0B dcA dcR)

        in elimInfNode positionA dcR n1R n0R p1R p0R

    | positionA > positionB = let
        dcR = union_dc a dcB

        n1R = local_mixedIntersection_neg1_dc n1B dcR
        n0R = let n0R' = local_mixedIntersection_neg0_dc n0B a dcR in
            if n1B == Leaf False then n0R' else remove_f1s1_from_f0s1 n1B n0R'

        p1R = local_mixedIntersection_pos1_dc p1B dcR
        p0R = let p0R' = local_mixedIntersection_pos0_dc p0B a dcR in
            if p1B == Leaf False then p0R' else remove_f1s0_from_f0s0 p1B p0R'

        in elimInfNode positionB dcR n1R n0R p1R p0R

    | positionA < positionB = let
        dcR = union_dc b dcA

        n1R = local_mixedIntersection_neg1_dc n1A dcR
        n0R = let n0R' = local_mixedIntersection_neg0_dc n0A b dcR in
            if n1A == Leaf False then n0R' else remove_f1s1_from_f0s1 n1A n0R'

        p1R = local_mixedIntersection_pos1_dc p1A dcR
        p0R = let p0R' = local_mixedIntersection_pos0_dc p0A b dcR in
            if p1A == Leaf False then p0R' else remove_f1s0_from_f0s0 p1A p0R'

        in elimInfNode positionA dcR n1R n0R p1R p0R

        where
            elimInfNode pos dcR n1R n0R p1R p0R = if (n1R, n0R, p1R, p0R) == (Leaf False, Leaf True, Leaf False, Leaf True) then
                    (if isInfNode dcR then dcR else
                        if dcR == Leaf False then Leaf False else
                            if dcR == Leaf True then Leaf True else
                                InfNodes pos dcR n1R n0R p1R p0R)
                    else InfNodes pos dcR n1R n0R p1R p0R
union_0 a (Leaf False) = (Leaf False)
union_0 (Leaf False) b = (Leaf False)
union_0 a (Leaf True) = a
union_0 (Leaf True) b = b
union_0 _ _ = error "missed case?"























intersection_dc :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal

-- Leaf and node
intersection_dc a (Leaf False) = Leaf False
intersection_dc (Leaf False) b = Leaf False
intersection_dc a (Leaf True) = a
intersection_dc (Leaf True) b = b


-- Two nodes
intersection_dc a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
    -- Match
    | positionA == positionB =
        let pos_result = intersection_dc pos_childA pos_childB
            neg_result = intersection_dc neg_childA neg_childB
        in if pos_result == neg_result then pos_result else Node positionA pos_result neg_result

    -- Mismatch, but with dc inference we ontinue recursion with the earliest (thus lowest valued) node.
    | positionA < positionB =
        let pos_result = intersection_dc pos_childA b
            neg_result = intersection_dc neg_childA b
        in (if pos_result == neg_result then pos_result else Node positionA pos_result neg_result)

    | positionA > positionB =
        let pos_result = intersection_dc a pos_childB
            neg_result = intersection_dc a neg_childB
        in (if pos_result == neg_result then pos_result else Node positionB pos_result neg_result)

intersection_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
    let pos_result = intersection_dc a pos_childB
        neg_result = intersection_dc a neg_childB
    in (if pos_result == neg_result then pos_result else Node positionB pos_result neg_result)
intersection_dc a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB _ _ _ _ _) =
    let pos_result = intersection_dc pos_childA b
        neg_result = intersection_dc neg_childA b
    in (if pos_result == neg_result then pos_result else Node positionA pos_result neg_result)

intersection_dc  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = intersection a b
intersection_dc a b = error ("how did we get here? " ++ show a ++ "  -  " ++ show b)


intersection_neg1 :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
-- Leaf and node
intersection_neg1 a (Leaf False) = Leaf False
intersection_neg1 (Leaf False) b = Leaf False

intersection_neg1 a@(Node positionA pos_childA neg_childA) (Leaf True) = intersection_neg1 neg_childA (Leaf True)
intersection_neg1 (Leaf True) b@(Node positionB pos_childB neg_childB) = intersection_neg1 (Leaf True) neg_childB
intersection_neg1 (Leaf True) b = b
intersection_neg1 a (Leaf True) = a


-- comparing nodes, allowed mis-matches based on each inference rule
intersection_neg1 a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
    -- match
    | positionA == positionB =
        let pos_result = intersection_neg1 pos_childA pos_childB
            neg_result = intersection_neg1 neg_childA neg_childB
        in if pos_result == Leaf False then pos_result else Node positionA pos_result neg_result

    -- mismatch with no Bot involved, thus with ZDD types inference we return bot
    | positionA < positionB =
        intersection_neg1 neg_childA b
    | positionA > positionB =
        intersection_neg1 a neg_childB

intersection_neg1 a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
    Node positionB (Leaf False) (intersection_neg1 a neg_childB)
intersection_neg1 a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB _ _ _ _ _) =
    Node positionA (Leaf False) (intersection_neg1 neg_childA b)

intersection_neg1  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = intersection a b

intersection_neg1 _ _ = error "how did we get here?"



local_intersection_neg0 :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
-- Leaf and node
local_intersection_neg0 a (Leaf True) = Leaf True
local_intersection_neg0 (Leaf True) b = Leaf True

local_intersection_neg0 a@(Node positionA pos_childA neg_childA) (Leaf False) = local_intersection_neg0 neg_childA (Leaf False)
local_intersection_neg0 (Leaf False) b@(Node positionB pos_childB neg_childB) = local_intersection_neg0 (Leaf False) neg_childB
local_intersection_neg0 a@(InfNodes positionA _ _ _ _ _) (Leaf False) = a
local_intersection_neg0 (Leaf False) b@(InfNodes positionB _ _ _ _ _) = b
local_intersection_neg0 (Leaf False) (Leaf False) = Leaf False

-- comparing nodes, allowed mis-matches based on each inference rule
local_intersection_neg0 a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
    -- match
    | positionA == positionB =
        let pos_result = local_intersection_neg0 pos_childA pos_childB
            neg_result = local_intersection_neg0 neg_childA neg_childB
        in if pos_result == Leaf True then pos_result else Node positionA pos_result neg_result

    -- mismatch with no Bot involved, thus with ZDD types inference we return bot
    | positionA < positionB =
        local_intersection_neg0 neg_childA b
    | positionA > positionB =
        local_intersection_neg0 a neg_childB

local_intersection_neg0 a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
    Node positionB (Leaf True) (local_intersection_neg0 a neg_childB)
local_intersection_neg0 a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB _ _ _ _ _) =
    Node positionA (Leaf True) (local_intersection_neg0 neg_childA b)

local_intersection_neg0  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = union_0 a b
local_intersection_neg0 _ _ = error "how did we get here?"

intersection_pos1 :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
-- Leaf and node
intersection_pos1 a (Leaf False) =  Leaf False
intersection_pos1 (Leaf False) b =  Leaf False

intersection_pos1 a@(Node positionA pos_childA neg_childA) (Leaf True) = intersection_pos1 pos_childA (Leaf True)
intersection_pos1 (Leaf True) b@(Node positionB pos_childB neg_childB) = intersection_pos1 (Leaf True) pos_childB
intersection_pos1 (Leaf True) b = b
intersection_pos1 a (Leaf True) = a

-- comparing nodes, allowed mis-matches based on each inference rule
intersection_pos1 a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
    -- match
    | positionA == positionB =
        let pos_result = intersection_pos1 pos_childA pos_childB
            neg_result = intersection_pos1 neg_childA neg_childB
        in if neg_result == Leaf False then neg_result else Node positionA pos_result neg_result

    -- mismatch with no Bot involved, thus with ZDD types inference we return bot
    | positionA < positionB =
        intersection_pos1 pos_childA b
    | positionA > positionB =
        intersection_pos1 a pos_childB

intersection_pos1 a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
    Node positionB (Leaf False) (intersection_pos1 a pos_childB)
intersection_pos1 a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB _ _ _ _ _) =
    Node positionA (Leaf False) (intersection_pos1 pos_childA b)

intersection_pos1  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = intersection a b

intersection_pos1 _ _ = error "how did we get here?"



local_intersection_pos0 :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
-- Leaf and node
local_intersection_pos0 a (Leaf True) = Leaf True
local_intersection_pos0 (Leaf True) b = Leaf True

local_intersection_pos0 a@(Node positionA pos_childA neg_childA) (Leaf False) = local_intersection_pos0 pos_childA (Leaf False)
local_intersection_pos0 (Leaf False) b@(Node positionB pos_childB neg_childB) = local_intersection_pos0 (Leaf False) pos_childB
local_intersection_pos0 a@(InfNodes positionA _ _ _ _ _) (Leaf False) = a
local_intersection_pos0 (Leaf False) b@(InfNodes positionB _ _ _ _ _) = b
local_intersection_pos0 (Leaf False) (Leaf False) = Leaf False

-- comparing nodes, allowed mis-matches based on each inference rule
local_intersection_pos0 a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
    -- match
    | positionA == positionB =
        let pos_result = local_intersection_pos0 pos_childA pos_childB
            neg_result = local_intersection_pos0 neg_childA neg_childB
        in if neg_result == Leaf True then neg_result else Node positionA pos_result neg_result

    -- mismatch with no Bot involved, thus with ZDD types inference we return bot
    | positionA < positionB =
        local_intersection_pos0 pos_childA b
    | positionA > positionB =
        local_intersection_pos0 a pos_childB

local_intersection_pos0 a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
    Node positionB (Leaf True) (local_intersection_pos0 a pos_childB)
local_intersection_pos0 a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB _ _ _ _ _) =
    Node positionA (Leaf True) (local_intersection_pos0 pos_childA b)

local_intersection_pos0  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = union_0 a b
local_intersection_pos0 _ _ = error "how did we get here?"
















union_dc :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
union_dc (Leaf False) b = b
union_dc a (Leaf True) =  Leaf True
union_dc a (Leaf False) =  a
union_dc (Leaf True) b = Leaf True

-- comparing nodes, allowed mis-matches based on each inference rule
union_dc a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

    -- no mismatch, only the appropriate ZDD elim is applied
    | positionA == positionB =
        let pos_result = union_dc pos_childA pos_childB
            neg_result = union_dc neg_childA neg_childB
        in if pos_result == neg_result then pos_result else Node positionA pos_result neg_result

    -- mismatch, but with dc inference we continue recursion with the highest (thus lowest valued) node
    -- refactor into two functions? one for mixed inference rules, one for single
    | positionA < positionB =
        let pos_result = union_dc pos_childA b
            neg_result = union_dc neg_childA b
        in (if pos_result == neg_result then pos_result  else Node positionA pos_result neg_result)

    | positionA > positionB =
        let pos_result = union_dc a pos_childB
            neg_result = union_dc a neg_childB
        in (if pos_result == neg_result then pos_result else Node positionB pos_result neg_result)

union_dc a@(InfNodes positionA _ _ _ _ _)  b@(Node positionB pos_childB neg_childB) =
    let pos_result = union_dc a pos_childB
        neg_result = union_dc a neg_childB
    in (if pos_result == neg_result then pos_result else Node positionB pos_result neg_result)

union_dc a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) =
    let pos_result = union_dc pos_childA b
        neg_result = union_dc neg_childA b
    in (if pos_result == neg_result then pos_result  else Node positionA pos_result neg_result)

union_dc  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = union a b

union_neg1 :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
union_neg1 a (Leaf False) =  a
union_neg1 (Leaf False) b =  b

union_neg1 a@(Node positionA pos_childA neg_childA) (Leaf True) = Node positionA pos_childA (union_neg1 neg_childA (Leaf True))
union_neg1 (Leaf True) b@(Node positionB pos_childB neg_childB) = Node positionB pos_childB (union_neg1 neg_childB (Leaf True))
union_neg1 (Leaf True) _ = Leaf True
union_neg1 _ (Leaf True) =   Leaf True

-- comparing nodes, allowed mis-matches based on each inference rule
union_neg1 a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

    -- no mismatch, only the appropriate ZDD elim is applied
    | positionA == positionB =
        let pos_result = union_neg1 pos_childA pos_childB
            neg_result = union_neg1 neg_childA neg_childB
        in if pos_result == Leaf False then Leaf False else Node positionA pos_result neg_result

    -- mismatch, but with dc inference we continue recursion with the highest (thus lowest valued) node
    -- refactor into two functions? one for mixed inference rules, one for single
    | positionA < positionB =
        let neg_result = union_neg1 neg_childA b
        in Node positionA pos_childA neg_result

    | positionA > positionB =
        let neg_result = union_neg1 a neg_childB
        in Node positionB pos_childB neg_result

union_neg1 a@(InfNodes positionA _ _ _ _ _)  b@(Node positionB pos_childB neg_childB)
     = Node positionB (Leaf False) (union_neg1 a neg_childB)

union_neg1 a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _)
    = Node positionA (Leaf False) (union_neg1 neg_childA b)

union_neg1  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = union a b



local_union_neg0 :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
local_union_neg0 a (Leaf True) =  a
local_union_neg0 (Leaf True) b =  b

local_union_neg0 a@(Node positionA pos_childA neg_childA) (Leaf False) = Node positionA pos_childA (local_union_neg0 neg_childA (Leaf False))
local_union_neg0 (Leaf False) b@(Node positionB pos_childB neg_childB) = Node positionB pos_childB (local_union_neg0 neg_childB (Leaf False))
local_union_neg0 a@(InfNodes positionA _ _ _ _ _) (Leaf False) = Leaf False -- because in the next domain we call intersection, thus Leaf False stays
local_union_neg0 (Leaf False) b@(InfNodes positionB _ _ _ _ _) = Leaf False
local_union_neg0 (Leaf False) (Leaf False) = Leaf False
-- comparing nodes, allowed mis-matches based on each inference rule
local_union_neg0 a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

    -- no mismatch, only the appropriate ZDD elim is applied
    | positionA == positionB =
        let pos_result = local_union_neg0 pos_childA pos_childB
            neg_result = local_union_neg0 neg_childA neg_childB
        in if pos_result == Leaf True then Leaf True else Node positionA pos_result neg_result

    -- mismatch, but with dc inference we continue recursion with the highest (thus lowest valued) node
    -- refactor into two functions? one for mixed inference rules, one for single
    | positionA < positionB =
        let neg_result = local_union_neg0 neg_childA b
        in Node positionA pos_childA neg_result

    | positionA > positionB =
        let neg_result = local_union_neg0 a neg_childB
        in Node positionB pos_childB neg_result

local_union_neg0 a@(InfNodes positionA _ _ _ _ _)  b@(Node positionB pos_childB neg_childB)
     = Node positionB (Leaf True) (local_union_neg0 a neg_childB)

local_union_neg0 a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _)
    = Node positionA (Leaf True) (local_union_neg0 a neg_childA)

local_union_neg0  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = intersection_0 a b



union_pos1 :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
union_pos1 a (Leaf False) =  a
union_pos1 (Leaf False) b =  b

union_pos1 a@(Node positionA pos_childA neg_childA) (Leaf True) = Node positionA (union_pos1 pos_childA (Leaf True)) neg_childA
union_pos1 (Leaf True) b@(Node positionB pos_childB neg_childB) = Node positionB (union_pos1 pos_childB (Leaf True)) neg_childB
union_pos1 (Leaf True) _ = Leaf True
union_pos1 _ (Leaf True) = Leaf True

-- comparing nodes, allowed mis-matches based on each inference rule
union_pos1 a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

    -- no mismatch, only the appropriate ZDD elim is applied
    | positionA == positionB =
        let pos_result = union_pos1 pos_childA pos_childB
            neg_result = union_pos1 neg_childA neg_childB
        in if neg_result == Leaf False then Leaf False else Node positionA pos_result neg_result

    -- mismatch, but with dc inference we continue recursion with the highest (thus lowest valued) node
    -- refactor into two functions? one for mixed inference rules, one for single
    | positionA < positionB =
        let pos_result = union_pos1 pos_childA b
        in Node positionA pos_result neg_childA

    | positionA > positionB =
        let pos_result = union_pos1 a pos_childB
        in Node positionB pos_result neg_childB

union_pos1 a@(InfNodes positionA _ _ _ _ _)  b@(Node positionB pos_childB neg_childB)
     = Node positionB (union_pos1 a pos_childB) (Leaf False)

union_pos1 a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _)
    = Node positionA (union_pos1 pos_childA b) (Leaf False)

union_pos1  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = union a b



local_union_pos0 :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
local_union_pos0 a (Leaf True) =  a
local_union_pos0 (Leaf True) b =  b

local_union_pos0 a@(Node positionA pos_childA neg_childA) (Leaf False) = Node positionA (local_union_pos0 pos_childA (Leaf False)) neg_childA
local_union_pos0 (Leaf False) b@(Node positionB pos_childB neg_childB) = Node positionB (local_union_pos0 pos_childB (Leaf False)) neg_childB
local_union_pos0 a@(InfNodes positionA _ _ _ _ _) (Leaf False) = Leaf False
local_union_pos0 (Leaf False) b@(InfNodes positionB _ _ _ _ _) = Leaf False
local_union_pos0 (Leaf False) (Leaf False) = Leaf False

-- comparing nodes, allowed mis-matches based on each inference rule
local_union_pos0 a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)

    -- no mismatch, only the appropriate ZDD elim is applied
    | positionA == positionB =
        let pos_result = local_union_pos0 pos_childA pos_childB
            neg_result = local_union_pos0 neg_childA neg_childB
        in if neg_result == Leaf True then Leaf True else Node positionA pos_result neg_result

    -- mismatch, but with dc inference we continue recursion with the highest (thus lowest valued) node
    -- refactor into two functions? one for mixed inference rules, one for single
    | positionA < positionB =
        let pos_result = local_union_pos0 pos_childA b
        in Node positionA pos_result neg_childA

    | positionA > positionB =
        let pos_result = local_union_pos0 a pos_childB
        in Node positionB pos_result neg_childB

local_union_pos0 a@(InfNodes positionA _ _ _ _ _)  b@(Node positionB pos_childB neg_childB)
     = Node positionB (local_union_pos0 a pos_childB) (Leaf True)

local_union_pos0 a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _)
    = Node positionA (local_union_pos0 pos_childA b) (Leaf True)

local_union_pos0  a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _) = intersection_0 a b



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
        in if pos_result == Leaf False then pos_result else Node positionA pos_result neg_result

    -- Mismatch
    | positionA > positionB = mixedIntersection_neg1_dc a neg_childB neg_childD
    | positionA < positionB =
        let pos_result = mixedIntersection_neg1_dc pos_childA b pos_childD
            neg_result = mixedIntersection_neg1_dc neg_childA b neg_childD
        in if pos_result == Leaf False then pos_result else Node positionA pos_result neg_result

-- No leafs involved
mixedIntersection_neg1_dc a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) dc

    -- No mismatch
    | positionA == positionB =
        let pos_result = mixedIntersection_neg1_dc pos_childA pos_childB dc
            neg_result = mixedIntersection_neg1_dc neg_childA neg_childB dc
        in if pos_result == Leaf False then pos_result else Node positionA pos_result neg_result

    -- Mismatch
    | positionA > positionB = mixedIntersection_neg1_dc a neg_childB dc
    | positionA < positionB =
        let pos_result = mixedIntersection_neg1_dc pos_childA b dc
            neg_result = mixedIntersection_neg1_dc neg_childA b dc
        in if pos_result == Leaf False then pos_result else Node positionA pos_result neg_result

-- Single InfNode has been reached, similar to single Leaf node cases.
mixedIntersection_neg1_dc a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) dc =
    let pos_result = mixedIntersection_neg1_dc pos_childA b dc
        neg_result = mixedIntersection_neg1_dc neg_childA b dc
    in if pos_result == Leaf False then pos_result else Node positionA pos_result neg_result

mixedIntersection_neg1_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD) =
    mixedIntersection_neg1_dc a neg_childB neg_childD

mixedIntersection_neg1_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) dc =
    mixedIntersection_neg1_dc a neg_childB dc

-- Both InfNodes have been reached - run the usual intersection.
mixedIntersection_neg1_dc a@(InfNodes {})  b@(InfNodes {}) dc = if (intersection a b) == dc then Leaf False else (intersection a b)
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
        in if pos_result == Leaf False then pos_result else Node positionA pos_result neg_result

    -- Mismatch
    | positionA > positionB = local_mixedIntersection_neg1_dc a neg_childB
    | positionA < positionB =
        let pos_result = local_mixedIntersection_neg1_dc pos_childA b
            neg_result = local_mixedIntersection_neg1_dc neg_childA b
        in if pos_result == Leaf False then pos_result else Node positionA pos_result neg_result

-- Single InfNode has been reached, similar to single Leaf node cases.
local_mixedIntersection_neg1_dc a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) =
    let pos_result = local_mixedIntersection_neg1_dc pos_childA b
        neg_result = local_mixedIntersection_neg1_dc neg_childA b
    in if pos_result == Leaf False then pos_result else Node positionA pos_result neg_result

local_mixedIntersection_neg1_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
    local_mixedIntersection_neg1_dc a neg_childB

-- Both InfNodes have been reached - run the usual intersection.
local_mixedIntersection_neg1_dc a@(InfNodes {})  b@(InfNodes {}) = if (union a b) == b then Leaf False else (union a b)
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
        in if pos_result == Leaf True then pos_result else Node positionA pos_result neg_result

    -- Mismatch
    | positionA > positionB = local_mixedIntersection_neg0_dc a neg_childB neg_childD
    | positionA < positionB =
        let pos_result = local_mixedIntersection_neg0_dc pos_childA b dc
            neg_result = local_mixedIntersection_neg0_dc neg_childA b dc
        in if pos_result == Leaf True then pos_result else Node positionA pos_result neg_result

local_mixedIntersection_neg0_dc a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) dc

    -- No mismatch
    | positionA == positionB =
        let pos_result = local_mixedIntersection_neg0_dc pos_childA pos_childB dc
            neg_result = local_mixedIntersection_neg0_dc neg_childA neg_childB dc
        in if pos_result == Leaf True then pos_result else Node positionA pos_result neg_result

    -- Mismatch
    | positionA > positionB = local_mixedIntersection_neg0_dc a neg_childB dc
    | positionA < positionB =
        let pos_result = local_mixedIntersection_neg0_dc pos_childA b dc
            neg_result = local_mixedIntersection_neg0_dc neg_childA b dc
        in if pos_result == Leaf True then pos_result else Node positionA pos_result neg_result

-- Single InfNode has been reached, similar to single Leaf node cases.
local_mixedIntersection_neg0_dc a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) dc =
    let pos_result = local_mixedIntersection_neg0_dc pos_childA b dc
        neg_result = local_mixedIntersection_neg0_dc neg_childA b dc
    in if pos_result == Leaf True then pos_result else Node positionA pos_result neg_result
local_mixedIntersection_neg0_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD) =
    local_mixedIntersection_neg0_dc a neg_childB neg_childD
local_mixedIntersection_neg0_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) dc =
    local_mixedIntersection_neg0_dc a neg_childB dc

-- Both InfNodes have been reached - run the usual intersection.
local_mixedIntersection_neg0_dc a@(InfNodes {})  b@(InfNodes {}) dc =  if (union_0 a b) == dc then Leaf True else (union_0 a b)
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
        in if pos_result == Leaf True then pos_result else Node positionA pos_result neg_result

    -- Mismatch
    | positionA > positionB = local_mixedIntersection2_neg0_dc a neg_childB
    | positionA < positionB =
        let pos_result = local_mixedIntersection2_neg0_dc pos_childA b
            neg_result = local_mixedIntersection2_neg0_dc neg_childA b
        in if pos_result == Leaf True then pos_result else Node positionA pos_result neg_result

-- Single InfNode has been reached, similar to single Leaf node cases.
local_mixedIntersection2_neg0_dc a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) =
    let pos_result = local_mixedIntersection2_neg0_dc pos_childA b
        neg_result = local_mixedIntersection2_neg0_dc neg_childA b
    in if pos_result == Leaf True then pos_result else Node positionA pos_result neg_result
local_mixedIntersection2_neg0_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
    local_mixedIntersection2_neg0_dc a neg_childB

-- Both InfNodes have been reached - run the usual intersection.
local_mixedIntersection2_neg0_dc a@(InfNodes {})  b@(InfNodes {}) =  if (intersection_0 a b) == b then Leaf True else (intersection_0 a b)
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
        in if neg_result == Leaf False then neg_result else Node positionA pos_result neg_result

    -- Mismatch
    | positionA > positionB = mixedIntersection_pos1_dc a pos_childB pos_childD
    | positionA < positionB =
        let pos_result = mixedIntersection_pos1_dc pos_childA b dc
            neg_result = mixedIntersection_pos1_dc neg_childA b dc
        in if neg_result == Leaf False then neg_result else Node positionA pos_result neg_result

-- No leafs involved
mixedIntersection_pos1_dc a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) dc

    -- No mismatch
    | positionA == positionB =
        let pos_result = mixedIntersection_pos1_dc pos_childA pos_childB dc
            neg_result = mixedIntersection_pos1_dc neg_childA neg_childB dc
        in if neg_result == Leaf False then neg_result else Node positionA pos_result neg_result

    -- Mismatch
    | positionA > positionB = mixedIntersection_pos1_dc a pos_childB dc
    | positionA < positionB =
        let pos_result = mixedIntersection_pos1_dc pos_childA b dc
            neg_result = mixedIntersection_pos1_dc neg_childA b dc
        in if neg_result == Leaf False then neg_result else Node positionA pos_result neg_result

-- Single InfNode has been reached, similar to single Leaf node cases.
mixedIntersection_pos1_dc a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) dc =
    let pos_result = mixedIntersection_pos1_dc pos_childA b dc
        neg_result = mixedIntersection_pos1_dc neg_childA b dc
    in if neg_result == Leaf False then neg_result else Node positionA pos_result neg_result


mixedIntersection_pos1_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD) =
    mixedIntersection_pos1_dc a pos_childB pos_childD
mixedIntersection_pos1_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) dc =
    mixedIntersection_pos1_dc a pos_childB dc

-- Both InfNodes have been reached - run the usual intersection.
mixedIntersection_pos1_dc a@(InfNodes {})  b@(InfNodes {}) dc = if (intersection a b) == dc then Leaf False else (intersection a b)
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
        in if neg_result == Leaf False then neg_result else Node positionA pos_result neg_result

    -- Mismatch
    | positionA > positionB = local_mixedIntersection_pos1_dc a pos_childB
    | positionA < positionB =
        let pos_result = local_mixedIntersection_pos1_dc pos_childA b
            neg_result = local_mixedIntersection_pos1_dc neg_childA b
        in if neg_result == Leaf False then neg_result else Node positionA pos_result neg_result

-- Single InfNode has been reached, similar to single Leaf node cases.
local_mixedIntersection_pos1_dc a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) =
    let pos_result = local_mixedIntersection_pos1_dc pos_childA b
        neg_result = local_mixedIntersection_pos1_dc neg_childA b
    in if neg_result == Leaf False then neg_result else Node positionA pos_result neg_result


local_mixedIntersection_pos1_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
    local_mixedIntersection_pos1_dc a pos_childB

local_mixedIntersection_pos1_dc a@(InfNodes {})  b@(InfNodes {}) = if (union a b) == b then Leaf False else (union a b)
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
        in if neg_result == Leaf True then neg_result else Node positionA pos_result neg_result

    -- Mismatch
    | positionA > positionB = local_mixedIntersection_pos0_dc a pos_childB pos_childD
    | positionA < positionB =
        let pos_result = local_mixedIntersection_pos0_dc pos_childA b dc
            neg_result = local_mixedIntersection_pos0_dc neg_childA b dc
        in if neg_result == Leaf True then neg_result else Node positionA pos_result neg_result

-- No leafs involved
local_mixedIntersection_pos0_dc a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB) dc

    -- No mismatch
    | positionA == positionB =
        let pos_result = local_mixedIntersection_pos0_dc pos_childA pos_childB dc
            neg_result = local_mixedIntersection_pos0_dc neg_childA neg_childB dc
        in if neg_result == Leaf True then neg_result else Node positionA pos_result neg_result

    -- Mismatch
    | positionA > positionB = local_mixedIntersection_pos0_dc a pos_childB dc
    | positionA < positionB =
        let pos_result = local_mixedIntersection_pos0_dc pos_childA b dc
            neg_result = local_mixedIntersection_pos0_dc neg_childA b dc
        in if neg_result == Leaf True then neg_result else Node positionA pos_result neg_result

-- Single InfNode has been reached, similar to single Leaf node cases.
local_mixedIntersection_pos0_dc a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) dc =
    let pos_result = local_mixedIntersection_pos0_dc pos_childA b dc
        neg_result = local_mixedIntersection_pos0_dc neg_childA b dc
    in if neg_result == Leaf True then neg_result else Node positionA pos_result neg_result

local_mixedIntersection_pos0_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) dc@(Node positionD pos_childD neg_childD) =
    local_mixedIntersection_pos0_dc a neg_childB neg_childD
local_mixedIntersection_pos0_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) dc =
    local_mixedIntersection_pos0_dc a neg_childB dc

-- Both InfNodes have been reached - run the usual intersection.
local_mixedIntersection_pos0_dc a@(InfNodes {})  b@(InfNodes {}) dc = if (union_0 a b) == dc then Leaf True else (union_0 a b)
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
        in if neg_result == Leaf True then neg_result else Node positionA pos_result neg_result

    -- Mismatch
    | positionA > positionB = local_mixedIntersection2_pos0_dc a pos_childB
    | positionA < positionB =
        let pos_result = local_mixedIntersection2_pos0_dc pos_childA b
            neg_result = local_mixedIntersection2_pos0_dc neg_childA b
        in if neg_result == Leaf True then neg_result else Node positionA pos_result neg_result

-- Single InfNode has been reached, similar to single Leaf node cases.
local_mixedIntersection2_pos0_dc a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _) =
    let pos_result = local_mixedIntersection2_pos0_dc pos_childA b
        neg_result = local_mixedIntersection2_pos0_dc neg_childA b
    in if neg_result == Leaf True then neg_result else Node positionA pos_result neg_result

local_mixedIntersection2_pos0_dc a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB) =
    local_mixedIntersection2_pos0_dc a neg_childB

-- Both InfNodes have been reached - run the usual intersection.
local_mixedIntersection2_pos0_dc a@(InfNodes {})  b@(InfNodes {}) = if (intersection_0 a b) == b then Leaf True else (intersection_0 a b)
local_mixedIntersection2_pos0_dc a b = undefined `debug` ("pos0 - " ++ show a ++ "  :  " ++ show b)

































-- No mixed union???
-- mixed inference rules union
{-  | c == Dc && (c == Neg1 || c == Neg0) && positionA < positionB =
    let pos_result = Leaf (c == Neg0) --If describing the 0 set, it infers true - otherwise false
        neg_result = union neg_childA b c
    in Node positionA pos_result neg_result

| c == Dc && (c == Pos1 || c == Pos0) && positionA > positionB =
    let pos_result = union a pos_childB c
        neg_result = Leaf (c == Pos0)
    in Node positionB pos_result neg_result-}





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
        in if pos_result == Leaf False then pos_result else Node positionA pos_result neg_result

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
remove_f0s1_from_f1s1  a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B) = intersection a b
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
remove_f1s1_from_f0s1  a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B) = intersection_0 a b
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
remove_f0s0_from_f1s0  a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B) = intersection a b
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
remove_f1s0_from_f0s0  a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B) = intersection_0 a b
remove_f1s0_from_f0s0 a b = undefined `debug` (show a ++ "  :  " ++ show b)




debug :: c -> String -> c
debug = flip trace
