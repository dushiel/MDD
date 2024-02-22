
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module MDDi where
import MDD
-- import MDDmanipulation
import DrawMDD
import qualified Data.HashMap.Lazy as HashMap
import Data.GraphViz.Attributes.Complete (OutputMode(NodesFirst))


-- todo sophisticated test suite,
-- have arbitrary formulas, then
-- restrict should be equal replacing with Top / Bot (for Dc at least or any local type)
-- negate formula and read all n1 as n0 and p1 as p0 to check symmetries
--

-- |======================================== Dd Manipulation operators ==============================================

infixl 4 -.
(-.) :: Context -> Dd -> (Context, Dd)
(-.) = negation
-- i dont think negation needs to keep track of context, right?

-- infix 2 .*. -- F1 Conjunction / product | F0 Disjunction / sum
-- (.*.) :: Dd -> Dd -> Dd
-- (.*.) a b = applyElimRule @'Dc $ intersection [(Dc, Inter)] a b

-- infixl 3 .+.
-- (.+.) :: Dd -> Dd -> Dd
-- (.+.) a b = applyElimRule @'Dc $ union [(Dc, Union)] a b

-- ite :: Dd -> Dd -> Dd -> Dd
-- ite x y z = (x .+. y) .*. ((-.) x .+. z)


-- infixl 1 .->.
-- (.->.) :: Dd -> Dd -> Dd
-- (.->.) a b = (-.) a .+. b

-- infixl 1 .<-.
-- (.<-.) :: Dd -> Dd -> Dd
-- (.<-.) a b = (-.) a .+. b

-- infixl 1 .<->.
-- (.<->.) :: Dd -> Dd -> Dd
-- (.<->.) a b = (a .*. b) .+. ((-.) a .*. (-.) b)

------------------------------------ Test
c = Context{
    nodelookup = HashMap.fromList [(0, (0, Leaf False)), (1, (0, Leaf True))] :: HashMap.HashMap NodeId (NodeId, Dd),
    cache = HashMap.empty :: HashMap.HashMap (NodeId, NodeId) Dd,
    cache_ = HashMap.empty :: HashMap.HashMap NodeId Dd,
    func_context = []
    }
x = makeNode c (L [(0, Dc)] 2)
x' = path c [(0,Dc)] [2,3]

-- dc2 = path [(0, Dc)] [2]
-- dc3 = path [(0, Dc)] [3]
-- dc_2 = path [(1, Dc)] [2]
-- dc__2 = path [(2,Dc)] [2]
-- dc = dc2 .*. dc3
-- n2 = path [(0, Neg1)] [2]
-- n3 = path [(0, Neg1)] [3]
-- n23 = path [(0, Neg1)] [2,3]
-- n_2 = path [(1, Neg1)] [2]
-- n__2 = path [(3, Neg1)] [2]
-- b = n2 .+. n3
-- p'2 = path [(0, Pos0)] [2]
-- p'3 = path [(0, Pos0)] [3]
-- p'_2 = path [(1, Pos0)] [2]
-- p'__2 = path [(3, Pos0)] [2]
-- c = p'2 .*. p'3
-- p2 = path [(0, Pos1)] [2]
-- p3 = path [(0, Pos1)] [3]
-- p_2 = path [(1,Pos1)] [2]
-- p__2 = path [(3, Pos1)] [2]

-- n'2 = path [(0, Neg0)] [2]
-- n'3 = path [(0, Neg0)] [3]
-- n'_2 = path [(1,Neg0)] [2]
-- n'__2 = path [(3, Neg0)] [2]

-- dcn1 = path [(0, Dc), (0, Neg1)] [1]
-- dcn'1 = path [(0, Dc), (0, Neg0)] [1]

-- nn1 = path [(0, Neg1), (0, Neg1)] [1]
-- nn2 = path [(0, Neg1), (0, Neg1)] [2]
-- n_n1 = path [(0, Neg1), (1, Neg1)] [1]
-- n_n2 = path [(0, Neg1), (1, Neg1)] [2]
-- n'n'1 = path [(0, Neg0), (0, Neg0)] [1]
-- n'n1 = path [(0, Neg0), (0, Neg1)] [1]
-- n'n2 = path [(0, Neg0), (0, Neg1)] [2]
-- n'_n1 = path [(0, Neg0), (1, Neg1)] [1]
-- n'_n2 = path [(0, Neg0), (1, Neg1)] [2]

-- nn'1 = path [(0, Neg1), (0, Neg0)] [1]
-- -- <[0,0]> -> ([0,1]) -> <[0,2,0]> -> ([0,2,1]) -> [1]
-- --dcZ =  (path (Order [0]) [1] Dc .->. path (Order [0,2]) [1] Dc) .*. path (Order [0]) [1] Dc
-- --neg1Z =  (path (Order [0]) [1] Neg1 .*. path (Order [0,2]) [1] Neg1) .*. path (Order [0]) [3] Neg1




-- test :: IO ()
-- test = do
--     mapM_ print ([show $ snd x | x <- zip results [(0 :: Int) .. ], not $ fst x])
--     where
--         results =
--             [ (p'2 .*. p2) == bot `debug5` ("############# Test nr: 0 \n\n")
--             , (p'2 .+. p2) == top  `debug5` ("############# Test nr: 1 \n\n")
--             , (dc .+. (-.) dc) == top  `debug5` ("############# Test nr: 2 \n\n")
--             , (dc .*. (-.) dc) == bot  `debug5` ("############# Test nr: 3 \n\n")

--             , ((n2 .+. n3) .*. n3) == n3  `debug5` ("############# Test nr: 4 \n\n")
--             , ((n2 .+. n3) .*. n2) == n2  `debug5` ("############# Test nr: 5 \n\n")

--             -- double domain (6)
--             , ((dc2 .+. dc_2) .*. dc_2) == dc_2  `debug5` ("############# Test nr: 6 \n\n")
--             , ((dc2 .+. dc_2) .*. dc2) == dc2  `debug5` ("############# Test nr: 7 \n\n")

--             -- inclusive finite subset dominance and submission (8)
--             , (dc2 .*. (n2 .+. n23)) == (n2 .+. n23)  `debug5` ("############# Test nr: 8 \n\n")
--             , (dc2 .+. (n2 .+. n23)) == dc2  `debug5` ("############# Test nr: 9 \n\n")
--             --exclusive
--             , ((dc2 .*. n'2) .+. n'2) == n'2  `debug5` ("############# Test nr: 10 \n\n")
--             , ((dc2 .*. n'2) .+. dc2) == dc2  `debug5` ("############# Test nr: 11 \n\n")

--             --double domain inclusive (12)
--             , ((n2 .*. n_2) .+. n2) == n2  `debug5` ("############# Test nr: 12 \n\n")
--             , ((n2 .*. n_2) .+. n_2) == n_2  `debug5` ("############# Test nr: 13 \n\n")
--             , ((n2 .+. n_2) .*. n2) == n2  `debug5` ("############# Test nr: 14 \n\n")
--             , ((n2 .+. n_2) .+. n_2) == (n2 .+. n_2)  `debug5` ("############# Test nr: 15 \n\n")
--             , ((n2 .*. n_2) .*. n2) == (n2 .*. n_2)  `debug5` ("############# Test nr: 16 \n\n")
--             , ((n2 .*. n_2) .+. n_2) == n_2  `debug5` ("############# Test nr: 17 \n\n")

--             --double domain exclusive (18)
--             , ((p'2 .+. p'_2) .*. p'2) == p'2  `debug5` ("############# Test nr: 18 \n\n")
--             , ((p'2 .+. p'_2) .*. p'_2) == p'_2  `debug5` ("############# Test nr: 19 \n\n")
--             , ((p'2 .*. p'_2) .+. p'2) == p'2  `debug5` ("############# Test nr: 20 \n\n")
--             , ((p'2 .*. p'_2) .*. p'_2) == (p'2 .*. p'_2)  `debug5` ("############# Test nr: 21 \n\n")
--             , ((p'2 .+. p'_2) .+. p'2) == (p'2 .+. p'_2)  `debug5` ("############# Test nr: 22 \n\n")

--             --double domain inclusive s0 (23)
--             , ((p2 .*. p_2) .+. p2) == p2  `debug5` ("############# Test nr: 23 \n\n")
--             , ((p2 .*. p_2) .+. p_2) == p_2  `debug5` ("############# Test nr: 24 \n\n")
--             , ((p2 .+. p_2) .*. p2) == p2  `debug5` ("############# Test nr: 25 \n\n")
--             , ((p2 .+. p_2) .+. p_2) == (p2 .+. p_2)  `debug5` ("############# Test nr: 26 \n\n")
--             , ((p2 .*. p_2) .*. p2) == (p2 .*. p_2)  `debug5` ("############# Test nr: 27 \n\n")
--             , ((p2 .*. p_2) .+. p_2) == p_2  `debug5` ("############# Test nr: 28 \n\n")

--             --double domain exclusive s0 (29)
--             , ((n'2 .*. n'_2) .+. n'2) == n'2  `debug5` ("############# Test nr: 29 \n\n")
--             , ((n'2 .*. n'_2) .+. n'_2) == n'_2  `debug5` ("############# Test nr: 30 \n\n")
--             , ((n'2 .+. n'_2) .*. n'2) == n'2  `debug5` ("############# Test nr: 31 \n\n")
--             , ((n'2 .+. n'_2) .+. n'_2) == (n'2 .+. n'_2)  `debug5` ("############# Test nr: 32 \n\n")
--             , ((n'2 .*. n'_2) .*. n'2) == (n'2 .*. n'_2)  `debug5` ("############# Test nr: 33 \n\n")
--             , ((n'2 .*. n'_2) .+. n'_2) == n'_2  `debug5` ("############# Test nr: 34 \n\n")

--             -- some triple domain cases (35)
--             , ((n'_2 .*. n'__2).+. n'_2) == n'_2  `debug5` ("############# Test nr: 35 \n\n")
--             , ((p'_2 .*. p'__2).+. p'_2) == p'_2  `debug5` ("############# Test nr: 36 \n\n")
--             , ((p_2 .*. p__2).+. p_2) == p_2  `debug5` ("############# Test nr: 37 \n\n")
--             , ((n_2 .*. n__2).+. n_2) == n_2  `debug5` ("############# Test nr: 38 \n\n")
--             , (((n'_2 .*. n'__2) .*. n'3) .+. (n'__2 .*. n'3)) == (n'__2 .*. n'3)  `debug5` ("############# Test nr: 39 \n\n")
--             , (((p'_2 .*. p'__2) .*. p'3) .+. (p'__2 .*. p'3)) == (p'__2 .*. p'3)  `debug5` ("############# Test nr: 40 \n\n")
--             , (((p_2 .*. p__2) .*. p3) .+. (p__2 .*. p3)) == (p__2 .*. p3)  `debug5` ("############# Test nr: 41 \n\n")
--             , (((n_2 .*. n__2) .*. n3) .+. (n__2 .*. n3)) == (n__2 .*. n3)  `debug5` ("############# Test nr: 42 \n\n")

--             , (((n'_2 .+. n'__2) .+. n'3) .*. (n'__2 .+. n'3)) == (n'__2 .+. n'3)  `debug5` ("############# Test nr: 43 \n\n")
--             , (((p'_2 .+. p'__2) .+. p'3) .*. (p'__2 .+. p'3)) == (p'__2 .+. p'3)  `debug5` ("############# Test nr: 44 \n\n")
--             , (((p_2 .+. p__2) .+. p3) .*. (p__2 .+. p3)) == (p__2 .+. p3)  `debug5` ("############# Test nr: 45 \n\n")
--             , (((n_2 .+. n__2) .+. n3) .*. (n__2 .+. n3)) == (n__2 .+. n3)  `debug5` ("############# Test nr: 46 \n\n")

--             -- mixing all domains (48)
--             , (((n'_2 .+. p'__2) .+. p3) .*. (p'__2 .+. p3)) == (p'__2 .+. p3)  `debug5` ("############# Test nr: 47 \n\n")
--             , ((dc2 .*. (dc3 .*. n3)) .+. (((n'_2 .*. p'__2) .+. p3) .*. (p'__2 .+. p3))) == ((dc2 .*. (dc3 .*. n3)) .+. ((n'_2 .*. p'__2) .+. p3))  `debug5` ("############# Test nr: 48 \n\n")
--             , ((n2 .*. (p'3 .*. dc3)) .+. (((p__2 .*. p'__2) .+. p3) .*. (n__2 .+. p3))) == ((n2 .*. (p'3 .*. dc3)) .+. ((p__2 .*. n__2) .+. p3))  `debug5` ("############# Test nr: 49 \n\n")

--             -- recursive
--             , ((dcn1 .->. nn1) .+. (n'n1)) == top `debug5` ("############# Test nr: 50 \n\n")
--             , (dcn1 .<-. nn1) == bot `debug5` ("############# Test nr: 51 \n\n")
--             , (dcn1 .<-. n'n1) == top `debug5` ("############# Test nr: 52 \n\n")
--             , (dcn1 .->. n'n1) == bot `debug5` ("############# Test nr: 53 \n\n")
--             , (nn1 .*. n'n1) == bot `debug4` ("############# Test nr: 54 \n\n")
--             , (nn1 .+. n'n1) == top `debug4` ("############# Test nr: 55 \n\n")

--             -- n1/no/p1/p0/dc outer shell and inner shell

--             -- tripple time
--             ]

-- {-}
-- dc = (path (Order [0]) [2] Dc) .*. (path (Order [1]) [2] Dc)
-- b = path (Order [1]) [2] Neg1

-- (dc .*. a) .+. dc == dc
-- (dc .+. a) .*. dc == dc

-- (dc .*. a) .+. a == a
-- (dc .+. a) .*. a == a
-- -}

-- test2 :: IO ()
-- test2 = do
--     mapM_ print ([show $ snd x | x <- zip results2 [(0 :: Int) .. ], not $ fst x])
--     where
--         results2 =
--             [
--                 (n'2 .*. n2) == bot `debug` ("############# Test nr: 2.0 \n\n")
--             ,   (n3 .*. n2) == bot `debug` ("############# Test nr: 2.0 \n\n")
--             ,   (n'3 .+. n'2) == top `debug` ("############# Test nr: 2.0 \n\n")
--             ,   (p3 .*. p2) == bot `debug` ("############# Test nr: 2.0 \n\n")
--             ,   (p'3 .+. p'2) == top `debug` ("############# Test nr: 2.0 \n\n")

--             , ((n2 .*. n3) .+. n3) == n3  `debug` ("############# Test nr: 4 \n\n")
--             , ((n2 .*. n3) .+. n2) == n2  `debug` ("############# Test nr: 5 \n\n")
--             , ((dc2 .*. dc3) .+. dc3) == dc3  `debug` ("############# Test nr: 4 \n\n")
--             , ((dc2 .*. dc3) .+. dc2) == dc2  `debug` ("############# Test nr: 5 \n\n")
--             , ((dc2 .+. dc3) .*. dc3) == dc3  `debug` ("############# Test nr: 4 \n\n")
--             , ((dc2 .+. dc3) .*. dc2) == dc2  `debug` ("############# Test nr: 5 \n\n")]