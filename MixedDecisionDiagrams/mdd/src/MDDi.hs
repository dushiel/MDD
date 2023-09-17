
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
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
(.*.) = intersection @True [(Dc, Inter)]

infixl 3 .+.
(.+.) :: Dd -> Dd -> Dd
(.+.) = union @True [(Dc, Union)]

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
    mapM_ print ([show $ snd x | x <- zip results [(0 :: Int) .. ], not $ fst x])
    where
        results =
            [ (c1 .*. d1) == bot `debug` ("############# Test nr: 0 \n\n")
            , (c1 .+. d1) == top  `debug` ("############# Test nr: 1 \n\n")
            , (dc .+. (-.) dc) == top  `debug` ("############# Test nr: 2 \n\n")
            , (dc .*. (-.) dc) == bot  `debug` ("############# Test nr: 3 \n\n")

            , ((b1 .+. b2) .*. b2) == b2  `debug` ("############# Test nr: 4 \n\n")
            , ((b1 .+. b2) .*. b1) == b1  `debug` ("############# Test nr: 5 \n\n")

            -- double domain (6)
            , ((dc1 .+. dc_2) .*. dc_2) == dc_2  `debug` ("############# Test nr: 6 \n\n")
            , ((dc1 .+. dc_2) .*. dc1) == dc1  `debug` ("############# Test nr: 7 \n\n")

            -- inclusive finite subset dominance and submission (8)
            , (dc1 .*. (b1 .+. b3)) == (b1 .+. b3)  `debug` ("############# Test nr: 8 \n\n")
            , (dc1 .+. (b1 .+. b3)) == dc1  `debug` ("############# Test nr: 9 \n\n")
            --exclusive
            , ((dc1 .*. e1) .+. e1) == e1  `debug` ("############# Test nr: 10 \n\n")
            , ((dc1 .*. e1) .+. dc1) == dc1  `debug` ("############# Test nr: 11 \n\n")

            --double domain inclusive (12)
            , ((b1 .*. b_2) .+. b1) == b1  `debug` ("############# Test nr: 12 \n\n")
            , ((b1 .*. b_2) .+. b_2) == b_2  `debug` ("############# Test nr: 13 \n\n")
            , ((b1 .+. b_2) .*. b1) == b1  `debug` ("############# Test nr: 14 \n\n")
            , ((b1 .+. b_2) .+. b_2) == (b1 .+. b_2)  `debug` ("############# Test nr: 15 \n\n")
            , ((b1 .*. b_2) .*. b1) == (b1 .*. b_2)  `debug` ("############# Test nr: 16 \n\n")
            , ((b1 .*. b_2) .+. b_2) == b_2  `debug` ("############# Test nr: 17 \n\n")

            --double domain exclusive (18)
            , ((c1 .+. c_2) .*. c1) == c1  `debug` ("############# Test nr: 18 \n\n")
            , ((c1 .+. c_2) .*. c_2) == c_2  `debug` ("############# Test nr: 19 \n\n")
            , ((c1 .*. c_2) .+. c1) == c1  `debug` ("############# Test nr: 20 \n\n")
            , ((c1 .*. c_2) .*. c_2) == (c1 .*. c_2)  `debug` ("############# Test nr: 21 \n\n")
            , ((c1 .+. c_2) .+. c1) == (c1 .+. c_2)  `debug` ("############# Test nr: 22 \n\n")

--            --double domain inclusive s0 (23)
--            , ((d1 .*. d_2) .+. d1) == d1  `debug` ("############# Test nr: _ \n\n")
--            , ((d1 .*. d_2) .+. d_2) == d_2  `debug` ("############# Test nr: _ \n\n")
--            , ((d1 .+. d_2) .*. d1) == d1  `debug` ("############# Test nr: _ \n\n")
--            , ((d1 .+. d_2) .+. d_2) == (d1 .+. d_2)  `debug` ("############# Test nr: _ \n\n")
--            , ((d1 .*. d_2) .*. d1) == (d1 .*. d_2)  `debug` ("############# Test nr: _ \n\n")
--            , ((d1 .*. d_2) .+. d_2) == d_2  `debug` ("############# Test nr: _ \n\n")
--
--            --double domain exclusive s0 (29)
--            , ((e1 .*. e_2) .+. e1) == e1  `debug` ("############# Test nr: _ \n\n")
--            , ((e1 .*. e_2) .+. e_2) == e_2  `debug` ("############# Test nr: _ \n\n")
--            , ((e1 .+. e_2) .*. e1) == e1  `debug` ("############# Test nr: _ \n\n")
--            , ((e1 .+. e_2) .+. e_2) == (e1 .+. e_2)  `debug` ("############# Test nr: _ \n\n")
--            , ((e1 .*. e_2) .*. e1) == (e1 .*. e_2)  `debug` ("############# Test nr: _ \n\n")
--            , ((e1 .*. e_2) .+. e_2) == e_2  `debug` ("############# Test nr: _ \n\n")
--
--            -- some triple domain cases (35)
--            , ((e_2 .*. e__2).+. e_2) == e_2  `debug` ("############# Test nr: _ \n\n")
--            , ((c_2 .*. c__2).+. c_2) == c_2  `debug` ("############# Test nr: _ \n\n")
--            , ((d_2 .*. d__2).+. d_2) == d_2  `debug` ("############# Test nr: _ \n\n")
--            , ((b_2 .*. b__2).+. b_2) == b_2  `debug` ("############# Test nr: _ \n\n")
--            , (((e_2 .*. e__2) .*. e2) .+. (e__2 .*. e2)) == (e__2 .*. e2)  `debug` ("############# Test nr: _ \n\n")
--            , (((c_2 .*. c__2) .*. c2) .+. (c__2 .*. c2)) == (c__2 .*. c2)  `debug` ("############# Test nr: _ \n\n")
--            , (((d_2 .*. d__2) .*. d2) .+. (d__2 .*. d2)) == (d__2 .*. d2)  `debug` ("############# Test nr: _ \n\n")
--            , (((b_2 .*. b__2) .*. b2) .+. (b__2 .*. b2)) == (b__2 .*. b2)  `debug` ("############# Test nr: _ \n\n")
--
--            , (((e_2 .+. e__2) .+. e2) .*. (e__2 .+. e2)) == (e__2 .+. e2)  `debug` ("############# Test nr: _ \n\n")
--            , (((c_2 .+. c__2) .+. c2) .*. (c__2 .+. c2)) == (c__2 .+. c2)  `debug` ("############# Test nr: _ \n\n")
--            , (((d_2 .+. d__2) .+. d2) .*. (d__2 .+. d2)) == (d__2 .+. d2)  `debug` ("############# Test nr: _ \n\n")
--            , (((b_2 .+. b__2) .+. b2) .*. (b__2 .+. b2)) == (b__2 .+. b2)  `debug` ("############# Test nr: _ \n\n")
--
--            -- mixing all domains (48)
--            , (((e_2 .+. c__2) .+. d2) .*. (c__2 .+. d2)) == (c__2 .+. d2)  `debug` ("############# Test nr: _ \n\n")
--            , ((dc1 .*. (dc2 .*. b2)) .+. (((e_2 .*. c__2) .+. d2) .*. (c__2 .+. d2))) == ((dc1 .*. (dc2 .*. b2)) .+. ((e_2 .*. c__2) .+. d2))  `debug` ("############# Test nr: _ \n\n")
--            , ((b1 .*. (c2 .*. dc2)) .+. (((d__2 .*. c__2) .+. d2) .*. (b__2 .+. d2))) == ((b1 .*. (c2 .*. dc2)) .+. ((d__2 .*. b__2) .+. d2))  `debug` ("############# Test nr: _ \n\n")
            ]

{-}
dc = (path (Order [0]) [2] Dc) .*. (path (Order [1]) [2] Dc)
b = path (Order [1]) [2] Neg1

(dc .*. a) .+. dc == dc
(dc .+. a) .*. dc == dc

(dc .*. a) .+. a == a
(dc .+. a) .*. a == a
-}