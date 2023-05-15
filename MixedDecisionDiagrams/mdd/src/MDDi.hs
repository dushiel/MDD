
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
module MDDi where
import MDD
import MDDmanipulation
import DrawMDD

-- todo sophisticated test suite,
-- have arbitrary formulas, then
-- restrict should be equal replacing with Top / Bot (for Dc at least or any local type)
-- negate formula and read all n1 as n0 and p1 as p0 to check symmetries
--

-- |======================================== Dd Manipulation operators ==============================================

infixl 4 -.
(-.) :: Dd -> Dd
(-.) = negation
-- i dont think negation needs to keep track of context, right?

infix 2 .*. -- F1 Conjunction / product | F0 Disjunction / sum
(.*.) :: Dd -> Dd -> Dd
(.*.) = intersection @True [(Dc, Norm)]

infixl 3 .+.
(.+.) :: Dd -> Dd -> Dd
(.+.) = union @True [(Dc, Norm)]

ite :: Dd -> Dd -> Dd -> Dd
ite x y z = (x .+. y) .*. ((-.) x .+. z)


infixl 1 .->.
(.->.) :: Dd -> Dd -> Dd
(.->.) a b = (-.) a .+. b

infixl 1 .<->.
(.<->.) :: Dd -> Dd -> Dd
(.<->.) a b = (a .*. b) .+. ((-.) a .*. (-.) b)

------------------------------------ Test

dc1 = path [(0, Dc)] [2]
dc2 = path [(0, Dc)] [3]
dc_2 = path [(1, Dc)] [2]
dc__2 = path [(3, Dc),(3,Dc)] [2]
dc = dc1 .*. dc2
b1 = path [(0, Neg1)] [2]
b2 = path [(0, Neg1)] [3]
b3 = path [(0, Neg1)] [2,3]
b_2 = path [(1, Neg1)] [2]
b__2 = path [(3, Neg1), (3, Neg1)] [2]
b = b1 .+. b2
c1 = path [(0, Pos0)] [2]
c2 = path [(0, Pos0)] [3]
c_2 = path [(1, Pos0)] [2]
c__2 = path [(3, Pos0),(3, Pos0)] [2]
c = c1 .*. c2
d1 = path [(0, Pos1)] [2]
d2 = path [(0, Pos1)] [3]
d_2 = path [(1,Pos1)] [2]
d__2 = path [(3, Pos1),(3, Pos1)] [2]

e1 = path [(0, Neg0)] [2]
e2 = path [(0, Neg0)] [3]
e_2 = path [(1,Neg0)] [2]
e__2 = path [(3, Neg0),(3, Neg0)] [2]

x = (e_2 .*. e__2) .*. e2
y= e2 .*. e__2

z = path [(3, Neg1),(2,Pos1)] [1,2]

-- <[0,0]> -> ([0,1]) -> <[0,2,0]> -> ([0,2,1]) -> [1]
--dcZ =  (path (Order [0]) [1] Dc .->. path (Order [0,2]) [1] Dc) .*. path (Order [0]) [1] Dc
--neg1Z =  (path (Order [0]) [1] Neg1 .*. path (Order [0,2]) [1] Neg1) .*. path (Order [0]) [3] Neg1



test :: IO ()
test = do
    mapM_ print ([show $ snd x | x <- zip results [0 ..], not $ fst x])
    where
        results =
            [ (c1 .*. d1) == bot
            , (c1 .+. d1) == top
--            , (dc .+. (-.) dc) == top
--            , (dc .*. (-.) dc) == bot
--
--            , ((b1 .+. b2) .*. b2) == b2
--            , ((b1 .+. b2) .*. b1) == b1
--
--            -- double domain (6)
--            , ((dc1 .+. dc_2) .*. dc_2) == dc_2
--            , ((dc1 .+. dc_2) .*. dc1) == dc1
--
--            -- inclusive finite subset dominance and submission (8)
--            , (dc1 .*. (b1 .+. b3)) == (b1 .+. b3)
--            , (dc1 .+. (b1 .+. b3)) == dc1
--            --exclusive
--            , ((dc1 .*. e1) .+. e1) == e1
--            , ((dc1 .*. e1) .+. dc1) == dc1
--
--            --double domain inclusive (12)
--            , ((b1 .*. b_2) .+. b1) == b1
--            , ((b1 .*. b_2) .+. b_2) == b_2
--            , ((b1 .+. b_2) .*. b1) == b1
--            , ((b1 .+. b_2) .+. b_2) == (b1 .+. b_2)
--            , ((b1 .*. b_2) .*. b1) == (b1 .*. b_2)
--            , ((b1 .*. b_2) .+. b_2) == b_2
--
--            --double domain exclusive (18)
--            , ((c1 .+. c_2) .*. c1) == c1
--            , ((c1 .+. c_2) .*. c_2) == c_2
--            , ((c1 .*. c_2) .+. c1) == c1
--            , ((c1 .*. c_2) .*. c_2) == (c1 .*. c_2)
--            , ((c1 .+. c_2) .+. c1) == (c1 .+. c_2)
--
--            --double domain inclusive s0 (23)
--            , ((d1 .*. d_2) .+. d1) == d1
--            , ((d1 .*. d_2) .+. d_2) == d_2
--            , ((d1 .+. d_2) .*. d1) == d1
--            , ((d1 .+. d_2) .+. d_2) == (d1 .+. d_2)
--            , ((d1 .*. d_2) .*. d1) == (d1 .*. d_2)
--            , ((d1 .*. d_2) .+. d_2) == d_2
--
--            --double domain exclusive s0 (29)
--            , ((e1 .*. e_2) .+. e1) == e1
--            , ((e1 .*. e_2) .+. e_2) == e_2
--            , ((e1 .+. e_2) .*. e1) == e1
--            , ((e1 .+. e_2) .+. e_2) == (e1 .+. e_2)
--            , ((e1 .*. e_2) .*. e1) == (e1 .*. e_2)
--            , ((e1 .*. e_2) .+. e_2) == e_2
--
--            -- some triple domain cases (35)
--            , ((e_2 .*. e__2).+. e_2) == e_2
--            , ((c_2 .*. c__2).+. c_2) == c_2
--            , ((d_2 .*. d__2).+. d_2) == d_2
--            , ((b_2 .*. b__2).+. b_2) == b_2
--            , (((e_2 .*. e__2) .*. e2) .+. (e__2 .*. e2)) == (e__2 .*. e2)
--            , (((c_2 .*. c__2) .*. c2) .+. (c__2 .*. c2)) == (c__2 .*. c2)
--            , (((d_2 .*. d__2) .*. d2) .+. (d__2 .*. d2)) == (d__2 .*. d2)
--            , (((b_2 .*. b__2) .*. b2) .+. (b__2 .*. b2)) == (b__2 .*. b2)
--
--            , (((e_2 .+. e__2) .+. e2) .*. (e__2 .+. e2)) == (e__2 .+. e2)
--            , (((c_2 .+. c__2) .+. c2) .*. (c__2 .+. c2)) == (c__2 .+. c2)
--            , (((d_2 .+. d__2) .+. d2) .*. (d__2 .+. d2)) == (d__2 .+. d2)
--            , (((b_2 .+. b__2) .+. b2) .*. (b__2 .+. b2)) == (b__2 .+. b2)
--
--            -- mixing all domains (48)
--            , (((e_2 .+. c__2) .+. d2) .*. (c__2 .+. d2)) == (c__2 .+. d2)
--            , ((dc1 .*. (dc2 .*. b2)) .+. (((e_2 .*. c__2) .+. d2) .*. (c__2 .+. d2))) == ((dc1 .*. (dc2 .*. b2)) .+. ((e_2 .*. c__2) .+. d2))
--            , ((b1 .*. (c2 .*. dc2)) .+. (((d__2 .*. c__2) .+. d2) .*. (b__2 .+. d2))) == ((b1 .*. (c2 .*. dc2)) .+. ((d__2 .*. b__2) .+. d2))
            ]

{-}
dc = (path (Order [0]) [2] Dc) .*. (path (Order [1]) [2] Dc)
b = path (Order [1]) [2] Neg1

(dc .*. a) .+. dc == dc
(dc .+. a) .*. dc == dc

(dc .*. a) .+. a == a
(dc .+. a) .*. a == a
-}