
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
module MixedDecisionDiagrams.Src.MDDi where
import MixedDecisionDiagrams.Src.MDD
import MixedDecisionDiagrams.Src.MDDmanipulation
import MixedDecisionDiagrams.Src.DrawMDD
import Data.List(sortBy)
import Data.Function

-- todo sophisticated test suite,

-- |======================================== Dd Manipulation operators ==============================================

infixl 4 -.
(-.) :: Dd Ordinal -> Dd Ordinal
(-.) = negation

infix 2 .*. -- F1 Conjunction / product | F0 Disjunction / sum
(.*.) :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
(.*.) = intersection @True []

infixl 3 .+.
(.+.) :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
(.+.) = union @True []

ite :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal -> Dd Ordinal
ite x y z = (x .+. y) .*. ((-.) x .+. z)

r0 :: Dd Ordinal -> Ordinal -> Dd Ordinal
r0 d = restrict @True d False

r1 :: Dd Ordinal -> Ordinal -> Dd Ordinal
r1 d = restrict @True d True

rSet :: Dd Ordinal -> [(Ordinal, Bool)] -> Dd Ordinal
rSet d b = restrictSet @True d (sortBy (compare `on` fst) b)

-- rSet, but then with ranges, such that we can restrict over an infinite domain
rGen :: Dd Ordinal -> [((Ordinal, Ordinal), Bool)] -> Dd Ordinal
rGen d b = restrictGen @True d (sortBy (compare `on` (fst . fst)) b)

infixl 1 .->.
(.->.) :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
(.->.) a b = (-.) a .+. b

infixl 1 .<->.
(.<->.) :: Dd Ordinal -> Dd Ordinal -> Dd Ordinal
(.<->.) a b = (a .*. b) .+. ((-.) a .*. (-.) b)

------------------------------------ Test

a1 = path (Order [0]) [2] Dc
a2 = path (Order [0]) [3] Dc
a_2 = path (Order [1]) [2] Dc
a__2 = path (Order [3,3]) [2] Dc
a = a1 .*. a2
b1 = path (Order [0]) [2] Neg1
b2 = path (Order [0]) [3] Neg1
b3 = path (Order [0]) [2,3] Neg1
b_2 = path (Order [1]) [2] Neg1
b__2 = path (Order [3,3]) [2] Neg1
b = b1 .+. b2
c1 = path (Order [0]) [2] Pos0
c2 = path (Order [0]) [3] Pos0
c_2 = path (Order [1]) [2] Pos0
c__2 = path (Order [3,3]) [2] Pos0
c = c1 .*. c2
d1 = path (Order [0]) [2] Pos1
d2 = path (Order [0]) [3] Pos1
d_2 = path (Order [1]) [2] Pos1
d__2 = path (Order [3,3]) [2] Pos1

e1 = path (Order [0]) [2] Neg0
e2 = path (Order [0]) [3] Neg0
e_2 = path (Order [1]) [2] Neg0
e__2 = path (Order [3,3]) [2] Neg0

x = (e_2 .*. e__2) .*. e2
y= e2 .*. e__2

z = makePathWithContext (Order [3,2]) [Neg1,Pos1] [1,2] Neg1

test :: IO ()
test = do
    print [show $ snd x | x <- zip results [0 ..], not $ fst x]
    where
        results =
            [ (c1 .*. d1) == bot
            , (c1 .+. d1) == top
            , (a .+. (-.) a) == top
            , (a .*. (-.) a) == bot

            , ((b1 .+. b2) .*. b2) == b2
            , ((b1 .+. b2) .*. b1) == b1

            -- double domain (6)
            , ((a1 .+. a_2) .*. a_2) == a_2
            , ((a1 .+. a_2) .*. a1) == a1

            -- inclusive finite subset dominance and submission (8)
            , (a1 .*. (b1 .+. b3)) == (b1 .+. b3)
            , (a1 .+. (b1 .+. b3)) == a1
            --exclusive
            , ((a1 .*. e1) .+. e1) == e1
            , ((a1 .*. e1) .+. a1) == a1

            --double domain inclusive (12)
            , ((b1 .*. b_2) .+. b1) == b1
            , ((b1 .*. b_2) .+. b_2) == b_2
            , ((b1 .+. b_2) .*. b1) == b1
            , ((b1 .+. b_2) .+. b_2) == (b1 .+. b_2)
            , ((b1 .*. b_2) .*. b1) == (b1 .*. b_2)
            , ((b1 .*. b_2) .+. b_2) == b_2

            --double domain exclusive (18)
            , ((c1 .+. c_2) .*. c1) == c1
            , ((c1 .+. c_2) .*. c_2) == c_2
            , ((c1 .*. c_2) .+. c1) == c1
            , ((c1 .*. c_2) .*. c_2) == (c1 .*. c_2)
            , ((c1 .+. c_2) .+. c1) == (c1 .+. c_2)

            --double domain inclusive s0 (23)
            , ((d1 .*. d_2) .+. d1) == d1
            , ((d1 .*. d_2) .+. d_2) == d_2
            , ((d1 .+. d_2) .*. d1) == d1
            , ((d1 .+. d_2) .+. d_2) == (d1 .+. d_2)
            , ((d1 .*. d_2) .*. d1) == (d1 .*. d_2)
            , ((d1 .*. d_2) .+. d_2) == d_2

            --double domain exclusive s0 (29)
            , ((e1 .*. e_2) .+. e1) == e1
            , ((e1 .*. e_2) .+. e_2) == e_2
            , ((e1 .+. e_2) .*. e1) == e1
            , ((e1 .+. e_2) .+. e_2) == (e1 .+. e_2)
            , ((e1 .*. e_2) .*. e1) == (e1 .*. e_2)
            , ((e1 .*. e_2) .+. e_2) == e_2

            -- some triple domain cases (35)
            , ((e_2 .*. e__2).+. e_2) == e_2
            , ((c_2 .*. c__2).+. c_2) == c_2
            , ((d_2 .*. d__2).+. d_2) == d_2
            , ((b_2 .*. b__2).+. b_2) == b_2
            , (((e_2 .*. e__2) .*. e2) .+. (e__2 .*. e2)) == (e__2 .*. e2)
            , (((c_2 .*. c__2) .*. c2) .+. (c__2 .*. c2)) == (c__2 .*. c2)
            , (((d_2 .*. d__2) .*. d2) .+. (d__2 .*. d2)) == (d__2 .*. d2)
            , (((b_2 .*. b__2) .*. b2) .+. (b__2 .*. b2)) == (b__2 .*. b2)

            , (((e_2 .+. e__2) .+. e2) .*. (e__2 .+. e2)) == (e__2 .+. e2)
            , (((c_2 .+. c__2) .+. c2) .*. (c__2 .+. c2)) == (c__2 .+. c2)
            , (((d_2 .+. d__2) .+. d2) .*. (d__2 .+. d2)) == (d__2 .+. d2)
            , (((b_2 .+. b__2) .+. b2) .*. (b__2 .+. b2)) == (b__2 .+. b2)

            -- mixing all domains (48)
            , (((e_2 .+. c__2) .+. d2) .*. (c__2 .+. d2)) == (c__2 .+. d2)
            , ((a1 .*. (a2 .*. b2)) .+. (((e_2 .*. c__2) .+. d2) .*. (c__2 .+. d2))) == ((a1 .*. (a2 .*. b2)) .+. ((e_2 .*. c__2) .+. d2))
            , ((b1 .*. (c2 .*. a2)) .+. (((d__2 .*. c__2) .+. d2) .*. (b__2 .+. d2))) == ((b1 .*. (c2 .*. a2)) .+. ((d__2 .*. b__2) .+. d2))
            ]

{-}
dc = (path (Order [0]) [2] Dc) .*. (path (Order [1]) [2] Dc)
b = path (Order [1]) [2] Neg1

(dc .*. a) .+. dc == dc
(dc .+. a) .*. dc == dc

(dc .*. a) .+. a == a
(dc .+. a) .*. a == a
-}