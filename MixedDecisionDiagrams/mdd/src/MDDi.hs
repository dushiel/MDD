
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
dc__2 = path [(1, Dc),(2,Dc)] [2]
dc = dc1 .*. dc2
n2 = path [(0, Neg1)] [2]
n3 = path [(0, Neg1)] [3]
n23 = path [(0, Neg1)] [2,3]
n_2 = path [(1, Neg1)] [2]
n__2 = path [(3, Neg1), (4, Neg1)] [2]
b = n2 .+. n3
p'2 = path [(0, Pos0)] [2]
p'3 = path [(0, Pos0)] [3]
p'_2 = path [(1, Pos0)] [2]
p'__2 = path [(3, Pos0),(4, Pos0)] [2]
c = p'2 .*. p'3
p2 = path [(0, Pos1)] [2]
p3 = path [(0, Pos1)] [3]
p_2 = path [(1,Pos1)] [2]
p__2 = path [(3, Pos1),(4, Pos1)] [2]

n'2 = path [(0, Neg0)] [2]
n'3 = path [(0, Neg0)] [3]
n'_2 = path [(1,Neg0)] [2]
n'__2 = path [(3, Neg0),(4, Neg0)] [2]

x = (n'_2 .*. n'__2) .*. n'3
y= n'3 .*. n'__2

z = path [(3, Neg1),(2,Pos1)] [1,2]

-- <[0,0]> -> ([0,1]) -> <[0,2,0]> -> ([0,2,1]) -> [1]
--dcZ =  (path (Order [0]) [1] Dc .->. path (Order [0,2]) [1] Dc) .*. path (Order [0]) [1] Dc
--neg1Z =  (path (Order [0]) [1] Neg1 .*. path (Order [0,2]) [1] Neg1) .*. path (Order [0]) [3] Neg1



test :: IO ()
test = do
    mapM_ print ([show $ snd x | x <- zip results [(0 :: Int) .. ], not $ fst x])
    where
        results =
            [ (p'2 .*. p2) == bot `debug` ("############# Test nr: 0 \n\n")
            , (p'2 .+. p2) == top  `debug` ("############# Test nr: 1 \n\n")
            , (dc .+. (-.) dc) == top  `debug` ("############# Test nr: 2 \n\n")
            , (dc .*. (-.) dc) == bot  `debug` ("############# Test nr: 3 \n\n")

            , ((n2 .+. n3) .*. n3) == n3  `debug` ("############# Test nr: 4 \n\n")
            , ((n2 .+. n3) .*. n2) == n2  `debug` ("############# Test nr: 5 \n\n")

            -- double domain (6)
            , ((dc1 .+. dc_2) .*. dc_2) == dc_2  `debug` ("############# Test nr: 6 \n\n")
            , ((dc1 .+. dc_2) .*. dc1) == dc1  `debug` ("############# Test nr: 7 \n\n")

            -- inclusive finite subset dominance and submission (8)
            , (dc1 .*. (n2 .+. n23)) == (n2 .+. n23)  `debug` ("############# Test nr: 8 \n\n")
            , (dc1 .+. (n2 .+. n23)) == dc1  `debug` ("############# Test nr: 9 \n\n")
            --exclusive
            , ((dc1 .*. n'2) .+. n'2) == n'2  `debug` ("############# Test nr: 10 \n\n")
            , ((dc1 .*. n'2) .+. dc1) == dc1  `debug` ("############# Test nr: 11 \n\n")

            --double domain inclusive (12)
            , ((n2 .*. n_2) .+. n2) == n2  `debug` ("############# Test nr: 12 \n\n")
            , ((n2 .*. n_2) .+. n_2) == n_2  `debug` ("############# Test nr: 13 \n\n")
            , ((n2 .+. n_2) .*. n2) == n2  `debug` ("############# Test nr: 14 \n\n")
            , ((n2 .+. n_2) .+. n_2) == (n2 .+. n_2)  `debug` ("############# Test nr: 15 \n\n")
            , ((n2 .*. n_2) .*. n2) == (n2 .*. n_2)  `debug` ("############# Test nr: 16 \n\n")
            , ((n2 .*. n_2) .+. n_2) == n_2  `debug` ("############# Test nr: 17 \n\n")

            --double domain exclusive (18)
            , ((p'2 .+. p'_2) .*. p'2) == p'2  `debug` ("############# Test nr: 18 \n\n")
            , ((p'2 .+. p'_2) .*. p'_2) == p'_2  `debug` ("############# Test nr: 19 \n\n")
            , ((p'2 .*. p'_2) .+. p'2) == p'2  `debug` ("############# Test nr: 20 \n\n")
            , ((p'2 .*. p'_2) .*. p'_2) == (p'2 .*. p'_2)  `debug` ("############# Test nr: 21 \n\n")
            , ((p'2 .+. p'_2) .+. p'2) == (p'2 .+. p'_2)  `debug` ("############# Test nr: 22 \n\n")

--            --double domain inclusive s0 (23)
--            , ((p2 .*. p_2) .+. p2) == p2  `debug` ("############# Test nr: _ \n\n")
--            , ((p2 .*. p_2) .+. p_2) == p_2  `debug` ("############# Test nr: _ \n\n")
--            , ((p2 .+. p_2) .*. p2) == p2  `debug` ("############# Test nr: _ \n\n")
--            , ((p2 .+. p_2) .+. p_2) == (p2 .+. p_2)  `debug` ("############# Test nr: _ \n\n")
--            , ((p2 .*. p_2) .*. p2) == (p2 .*. p_2)  `debug` ("############# Test nr: _ \n\n")
--            , ((p2 .*. p_2) .+. p_2) == p_2  `debug` ("############# Test nr: _ \n\n")
--
--            --double domain exclusive s0 (29)
--            , ((n'2 .*. n'_2) .+. n'2) == n'2  `debug` ("############# Test nr: _ \n\n")
--            , ((n'2 .*. n'_2) .+. n'_2) == n'_2  `debug` ("############# Test nr: _ \n\n")
--            , ((n'2 .+. n'_2) .*. n'2) == n'2  `debug` ("############# Test nr: _ \n\n")
--            , ((n'2 .+. n'_2) .+. n'_2) == (n'2 .+. n'_2)  `debug` ("############# Test nr: _ \n\n")
--            , ((n'2 .*. n'_2) .*. n'2) == (n'2 .*. n'_2)  `debug` ("############# Test nr: _ \n\n")
--            , ((n'2 .*. n'_2) .+. n'_2) == n'_2  `debug` ("############# Test nr: _ \n\n")
--
--            -- some triple domain cases (35)
--            , ((n'_2 .*. n'__2).+. n'_2) == n'_2  `debug` ("############# Test nr: _ \n\n")
--            , ((p'_2 .*. p'__2).+. p'_2) == p'_2  `debug` ("############# Test nr: _ \n\n")
--            , ((p_2 .*. p__2).+. p_2) == p_2  `debug` ("############# Test nr: _ \n\n")
--            , ((n_2 .*. n__2).+. n_2) == n_2  `debug` ("############# Test nr: _ \n\n")
--            , (((n'_2 .*. n'__2) .*. n'3) .+. (n'__2 .*. n'3)) == (n'__2 .*. n'3)  `debug` ("############# Test nr: _ \n\n")
--            , (((p'_2 .*. p'__2) .*. p'3) .+. (p'__2 .*. p'3)) == (p'__2 .*. p'3)  `debug` ("############# Test nr: _ \n\n")
--            , (((p_2 .*. p__2) .*. p3) .+. (p__2 .*. p3)) == (p__2 .*. p3)  `debug` ("############# Test nr: _ \n\n")
--            , (((n_2 .*. n__2) .*. n3) .+. (n__2 .*. n3)) == (n__2 .*. n3)  `debug` ("############# Test nr: _ \n\n")
--
--            , (((n'_2 .+. n'__2) .+. n'3) .*. (n'__2 .+. n'3)) == (n'__2 .+. n'3)  `debug` ("############# Test nr: _ \n\n")
--            , (((p'_2 .+. p'__2) .+. p'3) .*. (p'__2 .+. p'3)) == (p'__2 .+. p'3)  `debug` ("############# Test nr: _ \n\n")
--            , (((p_2 .+. p__2) .+. p3) .*. (p__2 .+. p3)) == (p__2 .+. p3)  `debug` ("############# Test nr: _ \n\n")
--            , (((n_2 .+. n__2) .+. n3) .*. (n__2 .+. n3)) == (n__2 .+. n3)  `debug` ("############# Test nr: _ \n\n")
--
--            -- mixing all domains (48)
--            , (((n'_2 .+. p'__2) .+. p3) .*. (p'__2 .+. p3)) == (p'__2 .+. p3)  `debug` ("############# Test nr: _ \n\n")
--            , ((dc1 .*. (dc2 .*. n3)) .+. (((n'_2 .*. p'__2) .+. p3) .*. (p'__2 .+. p3))) == ((dc1 .*. (dc2 .*. n3)) .+. ((n'_2 .*. p'__2) .+. p3))  `debug` ("############# Test nr: _ \n\n")
--            , ((n2 .*. (p'3 .*. dc2)) .+. (((p__2 .*. p'__2) .+. p3) .*. (n__2 .+. p3))) == ((n2 .*. (p'3 .*. dc2)) .+. ((p__2 .*. n__2) .+. p3))  `debug` ("############# Test nr: _ \n\n")
            ]

{-}
dc = (path (Order [0]) [2] Dc) .*. (path (Order [1]) [2] Dc)
b = path (Order [1]) [2] Neg1

(dc .*. a) .+. dc == dc
(dc .+. a) .*. dc == dc

(dc .*. a) .+. a == a
(dc .+. a) .*. a == a
-}