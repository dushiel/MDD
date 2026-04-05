{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module MDD.Test.NestedDomains where

import Test.Tasty
import Test.Tasty.HUnit

import MDD.Extra.Interface
import SMCDEL.Symbolic.Bool
import MDD.Test.Fixtures

tests :: TestTree
tests = testGroup "Nested Domains"
  [ nestedDc
  , nestedNeg
  , nestedPos
  , nestedMixed
  , nestedDcAlgebraic
  , nestedNegAlgebraic
  , nestedPosAlgebraic
  , nestedMixedAlgebraic
  , crossContextDcStack
  , applyDcCrossClassRegression
  , absorbPositionCatchup
  , fourLevelNesting
  , crossContextNested
  ]

-- ============================================================
-- Nested Dc inside Dc
-- ============================================================

nestedDc :: TestTree
nestedDc = testGroup "Dc nested in Dc"
  [ testCase "dcdc2 AND (NOT dcdc2) == Bot" $
      ddOf t_c (And (Var dcdc2) (Negate $ Var dcdc2)) @?= ddOf t_c Bot

  , testCase "dcdc3 AND dcdc3 == dcdc3 (idempotent)" $
      ddOf t_c (And (Var dcdc3) (Var dcdc3)) @?= ddOf t_c (Var dcdc3)

  , testCase "dcdc2 OR (NOT dcdc2) == Top" $
      ddOf t_c (Or (Var dcdc2) (Negate $ Var dcdc2)) @?= ddOf t_c Top

  , testCase "dcdc2 OR dcdc3 == dcdc3 OR dcdc2 (commutative)" $
      ddOf t_c (Or (Var dcdc2) (Var dcdc3))
        @?= ddOf t_c (Or (Var dcdc3) (Var dcdc2))
  ]

-- ============================================================
-- Nested Neg inside Neg
-- ============================================================

nestedNeg :: TestTree
nestedNeg = testGroup "Neg nested in Neg"
  [ testCase "nn'2 AND nn2 == Bot (opposite inner backgrounds)" $
      ddOf t_c (And (Var nn'2) (Var nn2)) @?= ddOf t_c Bot

  , testCase "nn3 AND nn2 == Bot (different items)" $
      ddOf t_c (And (Var nn3) (Var nn2)) @?= ddOf t_c Bot

  , testCase "nn2 AND nn3 == Bot (commutative)" $
      ddOf t_c (And (Var nn2) (Var nn3)) @?= ddOf t_c Bot

  , testCase "nn'2 OR nn'3 == ndc" $
      ddOf t_c (Or (Var nn'2) (Var nn'3)) @?= ddOf t_c (Var ndc)

  , testCase "n'n2 AND n'n1 == n'dc'" $
      ddOf t_c (And (Var n'n2) (Var n'n1)) @?= ddOf t_c (Var n'dc')
  ]

-- ============================================================
-- Nested Pos inside Pos
-- ============================================================

nestedPos :: TestTree
nestedPos = testGroup "Pos nested in Pos"
  [ testCase "pp'3 OR p'p'1 == Top" $
      ddOf t_c (Or (Var pp'3) (Var p'p'1)) @?= ddOf t_c Top

  , testCase "pp3 AND pp3 == pp3 (idempotent)" $
      ddOf t_c (And (Var pp3) (Var pp3)) @?= ddOf t_c (Var pp3)

  , testCase "p'p2 AND pp2 == pp2" $
      ddOf t_c (And (Var p'p2) (Var pp2)) @?= ddOf t_c (Var pp2)

  , testCase "p'p'1 AND p'p'2 == NOT (pp1 OR pp2)" $
      ddOf t_c (And (Var p'p'1) (Var p'p'2))
        @?= ddOf t_c (Impl (Or (Var pp1) (Var pp2)) Bot)

  , testCase "pp1 AND pp2 == Bot" $
      ddOf t_c (And (Var pp1) (Var pp2)) @?= ddOf t_c Bot
  ]

-- ============================================================
-- Mixed nested: Dc with Neg, various combinations
-- ============================================================

nestedMixed :: TestTree
nestedMixed = testGroup "Mixed nested domains"
  [ testCase "dcdc2 AND (dcn1 OR dcn23) == dcn23 AND dcdc2" $
      ddOf t_c (And (Var dcdc2) (Or (Var dcn1) (Var dcn23)))
        @?= ddOf t_c (And (Var dcn23) (Var dcdc2))

  , testCase "dc'2 AND (p2 OR p23) == p2 OR p23" $
      ddOf t_c (And (Var dc'2) (Or (Var p2) (Var p23)))
        @?= ddOf t_c (Or (Var p2) (Var p23))

  , testCase "dc2 OR (n2 OR n23) == dc2" $
      ddOf t_c (Or (Var dc2) (Or (Var n2) (Var n23)))
        @?= ddOf t_c (Var dc2)

  , testCase "dc'2 OR (p2 OR p23) == dc'2" $
      ddOf t_c (Or (Var dc'2) (Or (Var p2) (Var p23)))
        @?= ddOf t_c (Var dc'2)

  , testCase "(dc2 AND n'2) OR n'2 == n'2" $
      ddOf t_c (Or (And (Var dc2) (Var n'2)) (Var n'2))
        @?= ddOf t_c (Var n'2)

  , testCase "(dc2 AND p'2) OR p'2 == p'2" $
      ddOf t_c (Or (And (Var dc2) (Var p'2)) (Var p'2))
        @?= ddOf t_c (Var p'2)

  , testCase "(dc2 AND n'2) OR dc2 == dc2" $
      ddOf t_c (Or (And (Var dc2) (Var n'2)) (Var dc2))
        @?= ddOf t_c (Var dc2)
  ]

-- ############################################################
-- Gap 10: Nested algebraic property tests
-- ############################################################

-- ============================================================
-- Nested Dc-in-Dc: algebraic laws
-- dcdc2, dcdc3, dcdc'2 are all independent (Dc context)
-- ============================================================

nestedDcAlgebraic :: TestTree
nestedDcAlgebraic = testGroup "Dc-in-Dc algebraic laws"
  [ testGroup "Associativity"
    [ testCase "(dcdc2 AND dcdc3) AND dcdc'2 == dcdc2 AND (dcdc3 AND dcdc'2)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcdc3)
            c = ddOf t_c (Var dcdc'2)
        in ((a .*. b) .*. c) @?= (a .*. (b .*. c))

    , testCase "(dcdc2 OR dcdc3) OR dcdc'2 == dcdc2 OR (dcdc3 OR dcdc'2)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcdc3)
            c = ddOf t_c (Var dcdc'2)
        in ((a .+. b) .+. c) @?= (a .+. (b .+. c))
    ]

  , testGroup "Distributivity"
    [ testCase "dcdc2 AND (dcdc3 OR dcdc'2) == (dcdc2 AND dcdc3) OR (dcdc2 AND dcdc'2)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcdc3)
            c = ddOf t_c (Var dcdc'2)
        in (a .*. (b .+. c)) @?= ((a .*. b) .+. (a .*. c))

    , testCase "dcdc2 OR (dcdc3 AND dcdc'2) == (dcdc2 OR dcdc3) AND (dcdc2 OR dcdc'2)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcdc3)
            c = ddOf t_c (Var dcdc'2)
        in (a .+. (b .*. c)) @?= ((a .+. b) .*. (a .+. c))
    ]

  , testGroup "Absorption"
    [ testCase "dcdc2 AND (dcdc2 OR dcdc3) == dcdc2" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcdc3)
        in (a .*. (a .+. b)) @?= a

    , testCase "dcdc2 OR (dcdc2 AND dcdc3) == dcdc2" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcdc3)
        in (a .+. (a .*. b)) @?= a
    ]

  , testGroup "De Morgan"
    [ testCase "NOT (dcdc2 AND dcdc3) == (NOT dcdc2) OR (NOT dcdc3)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcdc3)
        in (-.) (a .*. b) @?= ((-.) a .+. (-.) b)

    , testCase "NOT (dcdc2 OR dcdc3) == (NOT dcdc2) AND (NOT dcdc3)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcdc3)
        in (-.) (a .+. b) @?= ((-.) a .*. (-.) b)
    ]
  ]

-- ============================================================
-- Nested Neg-in-Neg: algebraic laws
-- Same inner class (nn1, nn2, nn3): coupled (mutual exclusion)
-- Cross inner class (nn1 vs n_n1, n_n2): independent
-- ============================================================

nestedNegAlgebraic :: TestTree
nestedNegAlgebraic = testGroup "Neg-in-Neg algebraic laws"
  [ testGroup "Same inner class (coupled)"
    [ testCase "Associativity AND: (nn1 AND nn2) AND nn3 == nn1 AND (nn2 AND nn3) (trivial Bot)" $
        let a = ddOf t_c (Var nn1)
            b = ddOf t_c (Var nn2)
            c = ddOf t_c (Var nn3)
        in ((a .*. b) .*. c) @?= (a .*. (b .*. c))

    , testCase "Associativity OR: (nn1 OR nn2) OR nn3 == nn1 OR (nn2 OR nn3)" $
        let a = ddOf t_c (Var nn1)
            b = ddOf t_c (Var nn2)
            c = ddOf t_c (Var nn3)
        in ((a .+. b) .+. c) @?= (a .+. (b .+. c))

    , testCase "Distributivity: nn1 AND (nn2 OR nn3) == (nn1 AND nn2) OR (nn1 AND nn3)" $
        let a = ddOf t_c (Var nn1)
            b = ddOf t_c (Var nn2)
            c = ddOf t_c (Var nn3)
        in (a .*. (b .+. c)) @?= ((a .*. b) .+. (a .*. c))

    , testCase "Absorption: nn2 AND (nn2 OR nn3) == nn2" $
        let a = ddOf t_c (Var nn2)
            b = ddOf t_c (Var nn3)
        in (a .*. (a .+. b)) @?= a

    , testCase "Absorption: nn2 OR (nn2 AND nn3) == nn2" $
        let a = ddOf t_c (Var nn2)
            b = ddOf t_c (Var nn3)
        in (a .+. (a .*. b)) @?= a

    , testCase "De Morgan: NOT (nn2 AND nn3) == (NOT nn2) OR (NOT nn3)" $
        let a = ddOf t_c (Var nn2)
            b = ddOf t_c (Var nn3)
        in (-.) (a .*. b) @?= ((-.) a .+. (-.) b)

    , testCase "De Morgan: NOT (nn2 OR nn3) == (NOT nn2) AND (NOT nn3)" $
        let a = ddOf t_c (Var nn2)
            b = ddOf t_c (Var nn3)
        in (-.) (a .+. b) @?= ((-.) a .*. (-.) b)
    ]

  , testGroup "Cross inner class (independent)"
    [ testCase "Associativity AND: (nn1 AND n_n1) AND n_n2 == nn1 AND (n_n1 AND n_n2)" $
        let a = ddOf t_c (Var nn1)
            b = ddOf t_c (Var n_n1)
            c = ddOf t_c (Var n_n2)
        in ((a .*. b) .*. c) @?= (a .*. (b .*. c))

    , testCase "Associativity OR: (nn1 OR n_n1) OR n_n2 == nn1 OR (n_n1 OR n_n2)" $
        let a = ddOf t_c (Var nn1)
            b = ddOf t_c (Var n_n1)
            c = ddOf t_c (Var n_n2)
        in ((a .+. b) .+. c) @?= (a .+. (b .+. c))

    , testCase "Distributivity: nn1 AND (n_n1 OR n_n2) == (nn1 AND n_n1) OR (nn1 AND n_n2)" $
        let a = ddOf t_c (Var nn1)
            b = ddOf t_c (Var n_n1)
            c = ddOf t_c (Var n_n2)
        in (a .*. (b .+. c)) @?= ((a .*. b) .+. (a .*. c))

    , testCase "Distributivity: nn1 OR (n_n1 AND n_n2) == (nn1 OR n_n1) AND (nn1 OR n_n2)" $
        let a = ddOf t_c (Var nn1)
            b = ddOf t_c (Var n_n1)
            c = ddOf t_c (Var n_n2)
        in (a .+. (b .*. c)) @?= ((a .+. b) .*. (a .+. c))

    , testCase "Absorption: nn1 AND (nn1 OR n_n1) == nn1" $
        let a = ddOf t_c (Var nn1)
            b = ddOf t_c (Var n_n1)
        in (a .*. (a .+. b)) @?= a

    , testCase "Absorption: nn1 OR (nn1 AND n_n1) == nn1" $
        let a = ddOf t_c (Var nn1)
            b = ddOf t_c (Var n_n1)
        in (a .+. (a .*. b)) @?= a

    , testCase "De Morgan: NOT (nn1 AND n_n1) == (NOT nn1) OR (NOT n_n1)" $
        let a = ddOf t_c (Var nn1)
            b = ddOf t_c (Var n_n1)
        in (-.) (a .*. b) @?= ((-.) a .+. (-.) b)

    , testCase "De Morgan: NOT (nn1 OR n_n1) == (NOT nn1) AND (NOT n_n1)" $
        let a = ddOf t_c (Var nn1)
            b = ddOf t_c (Var n_n1)
        in (-.) (a .+. b) @?= ((-.) a .*. (-.) b)
    ]
  ]

-- ============================================================
-- Nested Pos-in-Pos: algebraic laws
-- Same inner class (pp1, pp2, pp3): coupled (mutual exclusion)
-- Cross inner class (pp1 vs p_p1, p_p2): independent
-- ============================================================

nestedPosAlgebraic :: TestTree
nestedPosAlgebraic = testGroup "Pos-in-Pos algebraic laws"
  [ testGroup "Same inner class (coupled)"
    [ testCase "Associativity AND: (pp1 AND pp2) AND pp3 == pp1 AND (pp2 AND pp3) (trivial Bot)" $
        let a = ddOf t_c (Var pp1)
            b = ddOf t_c (Var pp2)
            c = ddOf t_c (Var pp3)
        in ((a .*. b) .*. c) @?= (a .*. (b .*. c))

    , testCase "Associativity OR: (pp1 OR pp2) OR pp3 == pp1 OR (pp2 OR pp3)" $
        let a = ddOf t_c (Var pp1)
            b = ddOf t_c (Var pp2)
            c = ddOf t_c (Var pp3)
        in ((a .+. b) .+. c) @?= (a .+. (b .+. c))

    , testCase "Distributivity: pp1 AND (pp2 OR pp3) == (pp1 AND pp2) OR (pp1 AND pp3)" $
        let a = ddOf t_c (Var pp1)
            b = ddOf t_c (Var pp2)
            c = ddOf t_c (Var pp3)
        in (a .*. (b .+. c)) @?= ((a .*. b) .+. (a .*. c))

    , testCase "Absorption: pp2 AND (pp2 OR pp3) == pp2" $
        let a = ddOf t_c (Var pp2)
            b = ddOf t_c (Var pp3)
        in (a .*. (a .+. b)) @?= a

    , testCase "Absorption: pp2 OR (pp2 AND pp3) == pp2" $
        let a = ddOf t_c (Var pp2)
            b = ddOf t_c (Var pp3)
        in (a .+. (a .*. b)) @?= a

    , testCase "De Morgan: NOT (pp2 AND pp3) == (NOT pp2) OR (NOT pp3)" $
        let a = ddOf t_c (Var pp2)
            b = ddOf t_c (Var pp3)
        in (-.) (a .*. b) @?= ((-.) a .+. (-.) b)

    , testCase "De Morgan: NOT (pp2 OR pp3) == (NOT pp2) AND (NOT pp3)" $
        let a = ddOf t_c (Var pp2)
            b = ddOf t_c (Var pp3)
        in (-.) (a .+. b) @?= ((-.) a .*. (-.) b)
    ]

  , testGroup "Cross inner class (independent)"
    [ testCase "Associativity AND: (pp1 AND p_p1) AND p_p2 == pp1 AND (p_p1 AND p_p2)" $
        let a = ddOf t_c (Var pp1)
            b = ddOf t_c (Var p_p1)
            c = ddOf t_c (Var p_p2)
        in ((a .*. b) .*. c) @?= (a .*. (b .*. c))

    , testCase "Associativity OR: (pp1 OR p_p1) OR p_p2 == pp1 OR (p_p1 OR p_p2)" $
        let a = ddOf t_c (Var pp1)
            b = ddOf t_c (Var p_p1)
            c = ddOf t_c (Var p_p2)
        in ((a .+. b) .+. c) @?= (a .+. (b .+. c))

    , testCase "Distributivity: pp1 AND (p_p1 OR p_p2) == (pp1 AND p_p1) OR (pp1 AND p_p2)" $
        let a = ddOf t_c (Var pp1)
            b = ddOf t_c (Var p_p1)
            c = ddOf t_c (Var p_p2)
        in (a .*. (b .+. c)) @?= ((a .*. b) .+. (a .*. c))

    , testCase "Distributivity: pp1 OR (p_p1 AND p_p2) == (pp1 OR p_p1) AND (pp1 OR p_p2)" $
        let a = ddOf t_c (Var pp1)
            b = ddOf t_c (Var p_p1)
            c = ddOf t_c (Var p_p2)
        in (a .+. (b .*. c)) @?= ((a .+. b) .*. (a .+. c))

    , testCase "Absorption: pp1 AND (pp1 OR p_p1) == pp1" $
        let a = ddOf t_c (Var pp1)
            b = ddOf t_c (Var p_p1)
        in (a .*. (a .+. b)) @?= a

    , testCase "Absorption: pp1 OR (pp1 AND p_p1) == pp1" $
        let a = ddOf t_c (Var pp1)
            b = ddOf t_c (Var p_p1)
        in (a .+. (a .*. b)) @?= a

    , testCase "De Morgan: NOT (pp1 AND p_p1) == (NOT pp1) OR (NOT p_p1)" $
        let a = ddOf t_c (Var pp1)
            b = ddOf t_c (Var p_p1)
        in (-.) (a .*. b) @?= ((-.) a .+. (-.) b)

    , testCase "De Morgan: NOT (pp1 OR p_p1) == (NOT pp1) AND (NOT p_p1)" $
        let a = ddOf t_c (Var pp1)
            b = ddOf t_c (Var p_p1)
        in (-.) (a .+. b) @?= ((-.) a .*. (-.) b)
    ]
  ]

-- ============================================================
-- Mixed nested (Dc outer, Neg inner): algebraic laws
-- dcn1, dcn23 are independent (Dc outer context)
-- These stress the dc_stack most: outer Dc and inner Neg
-- require different inference rules at different traversal levels.
-- ============================================================

nestedMixedAlgebraic :: TestTree
nestedMixedAlgebraic = testGroup "Mixed nested (Dc/Neg) algebraic laws"
  [ testGroup "Associativity"
    [ testCase "(dcn1 AND dcn23) AND dcdc2 == dcn1 AND (dcn23 AND dcdc2)" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcn23)
            c = ddOf t_c (Var dcdc2)
        in ((a .*. b) .*. c) @?= (a .*. (b .*. c))

    , testCase "(dcn1 OR dcn23) OR dcdc2 == dcn1 OR (dcn23 OR dcdc2)" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcn23)
            c = ddOf t_c (Var dcdc2)
        in ((a .+. b) .+. c) @?= (a .+. (b .+. c))

    , testCase "(dcn1 AND dcn'1) AND dcn23 == dcn1 AND (dcn'1 AND dcn23)" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcn'1)
            c = ddOf t_c (Var dcn23)
        in ((a .*. b) .*. c) @?= (a .*. (b .*. c))

    , testCase "(dcn1 OR dcn'1) OR dcn23 == dcn1 OR (dcn'1 OR dcn23)" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcn'1)
            c = ddOf t_c (Var dcn23)
        in ((a .+. b) .+. c) @?= (a .+. (b .+. c))
    ]

  , testGroup "Distributivity"
    [ testCase "dcn1 AND (dcn23 OR dcdc2) == (dcn1 AND dcn23) OR (dcn1 AND dcdc2)" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcn23)
            c = ddOf t_c (Var dcdc2)
        in (a .*. (b .+. c)) @?= ((a .*. b) .+. (a .*. c))

    , testCase "dcn1 OR (dcn23 AND dcdc2) == (dcn1 OR dcn23) AND (dcn1 OR dcdc2)" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcn23)
            c = ddOf t_c (Var dcdc2)
        in (a .+. (b .*. c)) @?= ((a .+. b) .*. (a .+. c))

    , testCase "dcdc2 AND (dcn1 OR dcn'1) == (dcdc2 AND dcn1) OR (dcdc2 AND dcn'1)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
            c = ddOf t_c (Var dcn'1)
        in (a .*. (b .+. c)) @?= ((a .*. b) .+. (a .*. c))

    , testCase "dcdc2 OR (dcn1 AND dcn'1) == (dcdc2 OR dcn1) AND (dcdc2 OR dcn'1)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
            c = ddOf t_c (Var dcn'1)
        in (a .+. (b .*. c)) @?= ((a .+. b) .*. (a .+. c))
    ]

  , testGroup "Absorption"
    [ testCase "dcn1 AND (dcn1 OR dcn23) == dcn1" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcn23)
        in (a .*. (a .+. b)) @?= a

    , testCase "dcn1 OR (dcn1 AND dcn23) == dcn1" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcn23)
        in (a .+. (a .*. b)) @?= a

    , testCase "dcn1 AND (dcn1 OR dcdc2) == dcn1" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcdc2)
        in (a .*. (a .+. b)) @?= a

    , testCase "dcdc2 OR (dcdc2 AND dcn1) == dcdc2" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
        in (a .+. (a .*. b)) @?= a
    ]

  , testGroup "De Morgan"
    [ testCase "NOT (dcn1 AND dcn23) == (NOT dcn1) OR (NOT dcn23)" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcn23)
        in (-.) (a .*. b) @?= ((-.) a .+. (-.) b)

    , testCase "NOT (dcn1 OR dcn23) == (NOT dcn1) AND (NOT dcn23)" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcn23)
        in (-.) (a .+. b) @?= ((-.) a .*. (-.) b)

    , testCase "NOT (dcn1 AND dcdc2) == (NOT dcn1) OR (NOT dcdc2)" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcdc2)
        in (-.) (a .*. b) @?= ((-.) a .+. (-.) b)

    , testCase "NOT (dcn1 OR dcdc2) == (NOT dcn1) AND (NOT dcdc2)" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcdc2)
        in (-.) (a .+. b) @?= ((-.) a .*. (-.) b)
    ]

  , testGroup "Complement and identity"
    [ testCase "dcn1 AND (NOT dcn1) == bot" $
        let a = ddOf t_c (Var dcn1)
        in (a .*. (-.) a) @?= bot

    , testCase "dcn1 OR (NOT dcn1) == top" $
        let a = ddOf t_c (Var dcn1)
        in (a .+. (-.) a) @?= top

    , testCase "dcn'1 AND (NOT dcn'1) == bot" $
        let a = ddOf t_c (Var dcn'1)
        in (a .*. (-.) a) @?= bot

    , testCase "dcn'1 OR (NOT dcn'1) == top" $
        let a = ddOf t_c (Var dcn'1)
        in (a .+. (-.) a) @?= top

    , testCase "NOT (NOT dcn1) == dcn1 (double negation)" $
        let a = ddOf t_c (Var dcn1)
        in (-.) ((-.) a) @?= a

    , testCase "NOT (NOT dcn'23) == dcn'23 (double negation)" $
        let a = ddOf t_c (Var dcn'23)
        in (-.) ((-.) a) @?= a
    ]
  ]

-- ############################################################
-- Cross-context dc_stack interaction tests
-- ############################################################
--
-- These tests exercise the pattern that triggered the traverse_dc
-- bug: binary operations on nested MDDs where the two operands
-- have *different inner inference types* (e.g. Neg1 inner vs Dc1
-- inner). This forces the dc_stack to carry information across
-- inference boundaries during Unknown resolution.
--
-- The key structural pattern is:
--   operand A has inner Neg content (explicit items)
--   operand B has inner Dc content (partial specification)
--   combining them must preserve both contributions

crossContextDcStack :: TestTree
crossContextDcStack = testGroup "Cross-context dc_stack interactions"
  [ testGroup "Distributivity: Neg-inner with Dc-inner"
    [
    -- The original bug: (dcn1 + dcn23) * (dcn1 + dcdc2)
    -- dcn1 and dcn23 are disjoint Neg items at different positions
    -- dcdc2 is a Dc-context variable at position 2
    -- The intersection must preserve dcn23's contribution
      testCase "dcn1 OR (dcn23 AND dcdc2) == (dcn1 OR dcn23) AND (dcn1 OR dcdc2)" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcn23)
            c = ddOf t_c (Var dcdc2)
        in (a .+. (b .*. c)) @?= ((a .+. b) .*. (a .+. c))

    -- Symmetric: swap which side has Dc-inner
    , testCase "dcdc2 AND (dcn1 OR dcn23) == (dcdc2 AND dcn1) OR (dcdc2 AND dcn23)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
            c = ddOf t_c (Var dcn23)
        in (a .*. (b .+. c)) @?= ((a .*. b) .+. (a .*. c))

    -- Dc-inner with two different Neg-inner terms
    , testCase "dcdc2 OR (dcn1 AND dcn23) == (dcdc2 OR dcn1) AND (dcdc2 OR dcn23)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
            c = ddOf t_c (Var dcn23)
        in (a .+. (b .*. c)) @?= ((a .+. b) .*. (a .+. c))

    -- Three-way mixed: all different inner types
    , testCase "dcn1 AND (dcdc2 OR dcn23) == (dcn1 AND dcdc2) OR (dcn1 AND dcn23)" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcdc2)
            c = ddOf t_c (Var dcn23)
        in (a .*. (b .+. c)) @?= ((a .*. b) .+. (a .*. c))
    ]

  , testGroup "Distributivity: Neg0-inner with Dc-inner"
    [
    -- dcn'1 is Neg0-inner (background=True), dcdc2 is Dc-inner
      testCase "dcn'1 AND (dcn'23 OR dcdc2) == (dcn'1 AND dcn'23) OR (dcn'1 AND dcdc2)" $
        let a = ddOf t_c (Var dcn'1)
            b = ddOf t_c (Var dcn'23)
            c = ddOf t_c (Var dcdc2)
        in (a .*. (b .+. c)) @?= ((a .*. b) .+. (a .*. c))

    , testCase "dcn'1 OR (dcn'23 AND dcdc2) == (dcn'1 OR dcn'23) AND (dcn'1 OR dcdc2)" $
        let a = ddOf t_c (Var dcn'1)
            b = ddOf t_c (Var dcn'23)
            c = ddOf t_c (Var dcdc2)
        in (a .+. (b .*. c)) @?= ((a .+. b) .*. (a .+. c))
    ]

  , testGroup "Absorption: Neg-inner with Dc-inner"
    [
    -- dcn1 absorbed by union with broader Dc-inner term
      testCase "dcdc2 AND (dcdc2 OR dcn1) == dcdc2" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
        in (a .*. (a .+. b)) @?= a

    , testCase "dcdc2 OR (dcdc2 AND dcn1) == dcdc2" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
        in (a .+. (a .*. b)) @?= a

    , testCase "dcdc2 AND (dcdc2 OR dcn23) == dcdc2" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn23)
        in (a .*. (a .+. b)) @?= a

    , testCase "dcn23 AND (dcn23 OR dcdc2) == dcn23" $
        let a = ddOf t_c (Var dcn23)
            b = ddOf t_c (Var dcdc2)
        in (a .*. (a .+. b)) @?= a

    , testCase "dcn23 OR (dcn23 AND dcdc2) == dcn23" $
        let a = ddOf t_c (Var dcn23)
            b = ddOf t_c (Var dcdc2)
        in (a .+. (a .*. b)) @?= a
    ]

  , testGroup "Commutativity: Neg-inner with Dc-inner"
    [
      testCase "dcn1 AND dcdc2 == dcdc2 AND dcn1" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcdc2)
        in (a .*. b) @?= (b .*. a)

    , testCase "dcn1 OR dcdc2 == dcdc2 OR dcn1" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcdc2)
        in (a .+. b) @?= (b .+. a)

    , testCase "dcn23 AND dcdc3 == dcdc3 AND dcn23" $
        let a = ddOf t_c (Var dcn23)
            b = ddOf t_c (Var dcdc3)
        in (a .*. b) @?= (b .*. a)

    , testCase "dcn23 OR dcdc3 == dcdc3 OR dcn23" $
        let a = ddOf t_c (Var dcn23)
            b = ddOf t_c (Var dcdc3)
        in (a .+. b) @?= (b .+. a)
    ]

  , testGroup "Associativity: mixed inner contexts"
    [
    -- All three operands have different inner inference types
      testCase "(dcn1 AND dcdc2) AND dcn'23 == dcn1 AND (dcdc2 AND dcn'23)" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcdc2)
            c = ddOf t_c (Var dcn'23)
        in ((a .*. b) .*. c) @?= (a .*. (b .*. c))

    , testCase "(dcn1 OR dcdc2) OR dcn'23 == dcn1 OR (dcdc2 OR dcn'23)" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcdc2)
            c = ddOf t_c (Var dcn'23)
        in ((a .+. b) .+. c) @?= (a .+. (b .+. c))

    , testCase "(dcdc2 AND dcn1) AND dcdc3 == dcdc2 AND (dcn1 AND dcdc3)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
            c = ddOf t_c (Var dcdc3)
        in ((a .*. b) .*. c) @?= (a .*. (b .*. c))

    , testCase "(dcdc2 OR dcn1) OR dcdc3 == dcdc2 OR (dcn1 OR dcdc3)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
            c = ddOf t_c (Var dcdc3)
        in ((a .+. b) .+. c) @?= (a .+. (b .+. c))
    ]

  , testGroup "De Morgan: Neg-inner with Dc-inner"
    [
      testCase "NOT (dcn1 AND dcdc2) == (NOT dcn1) OR (NOT dcdc2)" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcdc2)
        in (-.) (a .*. b) @?= ((-.) a .+. (-.) b)

    , testCase "NOT (dcn1 OR dcdc2) == (NOT dcn1) AND (NOT dcdc2)" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcdc2)
        in (-.) (a .+. b) @?= ((-.) a .*. (-.) b)

    , testCase "NOT (dcn23 AND dcdc3) == (NOT dcn23) OR (NOT dcdc3)" $
        let a = ddOf t_c (Var dcn23)
            b = ddOf t_c (Var dcdc3)
        in (-.) (a .*. b) @?= ((-.) a .+. (-.) b)

    , testCase "NOT (dcn23 OR dcdc3) == (NOT dcn23) AND (NOT dcdc3)" $
        let a = ddOf t_c (Var dcn23)
            b = ddOf t_c (Var dcdc3)
        in (-.) (a .+. b) @?= ((-.) a .*. (-.) b)
    ]
  ]

-- ============================================================
-- applyDc cross-class regression (applyClassAAs, dc_stack Unknown)
-- ============================================================
--
-- These tests target binary traversal where the dc-sourced operand (A or B)
-- meets a ClassNode while applyDcA'/applyDcB' is active: the code must wrap
-- the synthetic EndClassNode on the *Dc* slot (inferClassNode @Dc) but keep
-- the outer inference rule for applyClass (@Neg / @Pos / @Dc) — see
-- applyClassAAs / applyClassBAs in MDD.Traversal.Binary.
--
-- They also exercise Unknown resolution from dcA/dcB when the popped
-- subgraph contains nested ClassNodes (dc_stack carries the dc branch).

applyDcCrossClassRegression :: TestTree
applyDcCrossClassRegression = testGroup "applyDc cross-class regression"
  [ testGroup "Leaf constant vs nested ClassNode (applyClassAAs / symmetric)"
    [
      testCase "top AND dcdc2 == dcdc2" $
        (top .*. ddOf t_c (Var dcdc2)) @?= ddOf t_c (Var dcdc2)

    , testCase "dcdc2 AND top == dcdc2" $
        (ddOf t_c (Var dcdc2) .*. top) @?= ddOf t_c (Var dcdc2)

    , testCase "top AND dcn1 == dcn1 (Dc outer, Neg inner vs leaf)" $
        (top .*. ddOf t_c (Var dcn1)) @?= ddOf t_c (Var dcn1)

    , testCase "dcn1 AND top == dcn1" $
        (ddOf t_c (Var dcn1) .*. top) @?= ddOf t_c (Var dcn1)

    , testCase "bot OR dcdc2 == dcdc2" $
        (bot .+. ddOf t_c (Var dcdc2)) @?= ddOf t_c (Var dcdc2)

    , testCase "dcdc2 OR bot == dcdc2" $
        (ddOf t_c (Var dcdc2) .+. bot) @?= ddOf t_c (Var dcdc2)
    ]

  , testGroup "Unknown from dc_stack with nested class (absorption + re-entry)"
    [
      testCase "dcdc2 AND (dcdc2 OR dcn1) == dcdc2" $
        let d2 = ddOf t_c (Var dcdc2)
            n1 = ddOf t_c (Var dcn1)
        in (d2 .*. (d2 .+. n1)) @?= d2

    , testCase "dcdc3 AND (dcdc3 OR dcn23) == dcdc3" $
        let d3 = ddOf t_c (Var dcdc3)
            dcn23M = ddOf t_c (Var dcn23)
        in (d3 .*. (d3 .+. dcn23M)) @?= d3

    , testCase "nn2 AND (dcdc2 OR (nn2 AND bot)) == nn2 AND dcdc2" $
        let n2 = ddOf t_c (Var nn2)
            d2 = ddOf t_c (Var dcdc2)
        in (n2 .*. (d2 .+. (n2 .*. bot))) @?= (n2 .*. d2)
    ]
  ]

-- ============================================================
-- Absorb position catchup
-- ============================================================
-- Tests targeting the absorb' fix where dcR is at a higher inner
-- position than the Neg/Pos result being absorbed. The bug pattern:
-- a Dc-inner term (position 2+) combined with complementary
-- Neg/Pos terms (position 1) whose intersection/union collapses,
-- leaving a result that is semantically redundant with dcR but at
-- a lower structural level.

absorbPositionCatchup :: TestTree
absorbPositionCatchup = testGroup "Absorb position catchup"
  [ testGroup "Complementary Neg-inner with Dc-inner (distributivity)"
    [
      testCase "dcdc2 OR (dcn1 AND dcn'1) == (dcdc2 OR dcn1) AND (dcdc2 OR dcn'1)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
            c = ddOf t_c (Var dcn'1)
        in (a .+. (b .*. c)) @?= ((a .+. b) .*. (a .+. c))

    , testCase "dcdc2 AND (dcn1 OR dcn'1) == (dcdc2 AND dcn1) OR (dcdc2 AND dcn'1)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
            c = ddOf t_c (Var dcn'1)
        in (a .*. (b .+. c)) @?= ((a .*. b) .+. (a .*. c))

    , testCase "dcn1 OR (dcdc2 AND dcn'1) == (dcn1 OR dcdc2) AND (dcn1 OR dcn'1)" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcdc2)
            c = ddOf t_c (Var dcn'1)
        in (a .+. (b .*. c)) @?= ((a .+. b) .*. (a .+. c))

    , testCase "dcn'1 OR (dcdc2 AND dcn1) == (dcn'1 OR dcdc2) AND (dcn'1 OR dcn1)" $
        let a = ddOf t_c (Var dcn'1)
            b = ddOf t_c (Var dcdc2)
            c = ddOf t_c (Var dcn1)
        in (a .+. (b .*. c)) @?= ((a .+. b) .*. (a .+. c))
    ]

  , testGroup "Complementary Neg-inner with higher Dc-inner (position 3)"
    [
      testCase "dcdc3 OR (dcn1 AND dcn'1) == (dcdc3 OR dcn1) AND (dcdc3 OR dcn'1)" $
        let a = ddOf t_c (Var dcdc3)
            b = ddOf t_c (Var dcn1)
            c = ddOf t_c (Var dcn'1)
        in (a .+. (b .*. c)) @?= ((a .+. b) .*. (a .+. c))

    , testCase "dcdc3 AND (dcn1 OR dcn'1) == (dcdc3 AND dcn1) OR (dcdc3 AND dcn'1)" $
        let a = ddOf t_c (Var dcdc3)
            b = ddOf t_c (Var dcn1)
            c = ddOf t_c (Var dcn'1)
        in (a .*. (b .+. c)) @?= ((a .*. b) .+. (a .*. c))

    , testCase "dcdc3 OR (dcn23 AND dcn'23) == (dcdc3 OR dcn23) AND (dcdc3 OR dcn'23)" $
        let a = ddOf t_c (Var dcdc3)
            b = ddOf t_c (Var dcn23)
            c = ddOf t_c (Var dcn'23)
        in (a .+. (b .*. c)) @?= ((a .+. b) .*. (a .+. c))
    ]

  , testGroup "Complementary Pos-inner with Dc-inner (distributivity)"
    [
      testCase "dcdc2 OR (dcp1 AND dcp'1) == (dcdc2 OR dcp1) AND (dcdc2 OR dcp'1)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcp1)
            c = ddOf t_c (Var dcp'1)
        in (a .+. (b .*. c)) @?= ((a .+. b) .*. (a .+. c))

    , testCase "dcdc2 AND (dcp1 OR dcp'1) == (dcdc2 AND dcp1) OR (dcdc2 AND dcp'1)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcp1)
            c = ddOf t_c (Var dcp'1)
        in (a .*. (b .+. c)) @?= ((a .*. b) .+. (a .*. c))

    , testCase "dcdc3 OR (dcp1 AND dcp'1) == (dcdc3 OR dcp1) AND (dcdc3 OR dcp'1)" $
        let a = ddOf t_c (Var dcdc3)
            b = ddOf t_c (Var dcp1)
            c = ddOf t_c (Var dcp'1)
        in (a .+. (b .*. c)) @?= ((a .+. b) .*. (a .+. c))

    , testCase "dcdc3 AND (dcp23 OR dcp'1) == (dcdc3 AND dcp23) OR (dcdc3 AND dcp'1)" $
        let a = ddOf t_c (Var dcdc3)
            b = ddOf t_c (Var dcp23)
            c = ddOf t_c (Var dcp'1)
        in (a .*. (b .+. c)) @?= ((a .*. b) .+. (a .*. c))
    ]

  , testGroup "Complementary collapse to identity/zero"
    [
      testCase "dcn1 AND dcn'1 == bot" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcn'1)
        in (a .*. b) @?= bot

    , testCase "dcn23 AND dcn'23 == bot" $
        let a = ddOf t_c (Var dcn23)
            b = ddOf t_c (Var dcn'23)
        in (a .*. b) @?= bot

    , testCase "dcdc2 OR (dcn1 AND dcn'1) == dcdc2" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
            c = ddOf t_c (Var dcn'1)
        in (a .+. (b .*. c)) @?= a

    , testCase "dcdc3 OR (dcn1 AND dcn'1) == dcdc3" $
        let a = ddOf t_c (Var dcdc3)
            b = ddOf t_c (Var dcn1)
            c = ddOf t_c (Var dcn'1)
        in (a .+. (b .*. c)) @?= a
    ]

  , testGroup "Three-operand chains with position mismatch"
    [
      testCase "(dcdc2 OR dcn1) AND (dcdc2 OR dcn'1) AND (dcdc2 OR dcn23) == dcdc2 OR (dcn1 AND dcn'1 AND dcn23)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
            c = ddOf t_c (Var dcn'1)
            d = ddOf t_c (Var dcn23)
        in (((a .+. b) .*. (a .+. c)) .*. (a .+. d)) @?= (a .+. ((b .*. c) .*. d))

    , testCase "dcdc2 OR (dcn1 AND dcn'1 AND dcn23) == dcdc2" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
            c = ddOf t_c (Var dcn'1)
            d = ddOf t_c (Var dcn23)
        in (a .+. ((b .*. c) .*. d)) @?= a

    , testCase "dcdc3 OR (dcn1 AND dcn'23) == (dcdc3 OR dcn1) AND (dcdc3 OR dcn'23)" $
        let a = ddOf t_c (Var dcdc3)
            b = ddOf t_c (Var dcn1)
            c = ddOf t_c (Var dcn'23)
        in (a .+. (b .*. c)) @?= ((a .+. b) .*. (a .+. c))
    ]

  , testGroup "Idempotency and self-interaction after absorb"
    [
      testCase "(dcdc2 OR dcn1) AND (dcdc2 OR dcn1) == dcdc2 OR dcn1" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
            ab = a .+. b
        in (ab .*. ab) @?= ab

    , testCase "(dcdc2 OR dcn'1) AND (dcdc2 OR dcn'1) == dcdc2 OR dcn'1" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn'1)
            ab = a .+. b
        in (ab .*. ab) @?= ab

    , testCase "(dcdc3 AND dcn1) OR (dcdc3 AND dcn1) == dcdc3 AND dcn1" $
        let a = ddOf t_c (Var dcdc3)
            b = ddOf t_c (Var dcn1)
            ab = a .*. b
        in (ab .+. ab) @?= ab

    -- Dc/Pos-inner union: same structure as Dc/Neg but with Pos inner context
    , testCase "(dcdc2 OR dcp1) AND (dcdc2 OR dcp1) == dcdc2 OR dcp1" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcp1)
            ab = a .+. b
        in (ab .*. ab) @?= ab

    -- Dc/Pos-inner with background=True inner
    , testCase "(dcdc3 OR dcp'1) AND (dcdc3 OR dcp'1) == dcdc3 OR dcp'1" $
        let a = ddOf t_c (Var dcdc3)
            b = ddOf t_c (Var dcp'1)
            ab = a .+. b
        in (ab .*. ab) @?= ab

    -- Intersection of mixed terms: AND then idempotent OR
    , testCase "(dcdc2 AND dcn23) OR (dcdc2 AND dcn23) == dcdc2 AND dcn23" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn23)
            ab = a .*. b
        in (ab .+. ab) @?= ab

    -- Three-term union then idempotency
    , testCase "(dcdc2 OR dcn1 OR dcp1) AND (dcdc2 OR dcn1 OR dcp1) == dcdc2 OR dcn1 OR dcp1" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
            c = ddOf t_c (Var dcp1)
            abc = a .+. b .+. c
        in (abc .*. abc) @?= abc

    -- Negated compound: NOT of a mixed union, then idempotent AND
    , testCase "NOT(dcdc2 OR dcn1) AND NOT(dcdc2 OR dcn1) == NOT(dcdc2 OR dcn1)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
            nab = (-.) (a .+. b)
        in (nab .*. nab) @?= nab

    -- Neg-inside-Neg nested terms: homogeneous nested context
    , testCase "(nn2 OR nn'3) AND (nn2 OR nn'3) == nn2 OR nn'3" $
        let a = ddOf t_c (Var nn2)
            b = ddOf t_c (Var nn'3)
            ab = a .+. b
        in (ab .*. ab) @?= ab

    -- Cross-background compound: mixing Neg1-inner and Neg0-inner
    , testCase "(dcn1 OR dcn'23) AND (dcn1 OR dcn'23) == dcn1 OR dcn'23" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcn'23)
            ab = a .+. b
        in (ab .*. ab) @?= ab

    -- Compound of compounds: build two mixed unions, combine, then idempotency
    , testCase "((dcdc2 OR dcn1) AND (dcdc3 OR dcn'1)) is idempotent under OR" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
            c = ddOf t_c (Var dcdc3)
            d = ddOf t_c (Var dcn'1)
            x = (a .+. b) .*. (c .+. d)
        in (x .+. x) @?= x

    -- Distributivity result then idempotency: the full expression from the
    -- complementary-pair distributivity test, checked for self-intersection
    , testCase "dcdc2 OR (dcn1 AND dcn'1) is idempotent under AND" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
            c = ddOf t_c (Var dcn'1)
            x = a .+. (b .*. c)
        in (x .*. x) @?= x

    -- Four-term mixed union with all inner context types, then idempotency
    , testCase "(dcdc2 OR dcn1 OR dcp1 OR dcn'23) is idempotent under AND" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
            c = ddOf t_c (Var dcp1)
            d = ddOf t_c (Var dcn'23)
            x = a .+. b .+. c .+. d
        in (x .*. x) @?= x
    ]
  ]

-- ############################################################
-- Gap D: 4-level deep nesting tests
-- ############################################################

fourLevelNesting :: TestTree
fourLevelNesting = testGroup "Four-level nesting"
  [ testGroup "Homogeneous Dc (dddd)"
    [ testCase "Idempotence AND: dddd2 AND dddd2 == dddd2" $
        let a = ddOf t_c (Var dddd2)
        in (a .*. a) @?= a

    , testCase "Idempotence OR: dddd2 OR dddd2 == dddd2" $
        let a = ddOf t_c (Var dddd2)
        in (a .+. a) @?= a

    , testCase "Complement: dddd2 AND (NOT dddd2) == bot" $
        let a = ddOf t_c (Var dddd2)
        in (a .*. (-.) a) @?= bot

    , testCase "Complement: dddd2 OR (NOT dddd2) == top" $
        let a = ddOf t_c (Var dddd2)
        in (a .+. (-.) a) @?= top

    , testCase "Double negation: NOT (NOT dddd2) == dddd2" $
        let a = ddOf t_c (Var dddd2)
        in (-.) ((-.) a) @?= a

    , testCase "Commutativity AND: dddd2 AND dddd3 == dddd3 AND dddd2" $
        let a = ddOf t_c (Var dddd2)
            b = ddOf t_c (Var dddd3)
        in (a .*. b) @?= (b .*. a)

    , testCase "Commutativity OR: dddd2 OR dddd3 == dddd3 OR dddd2" $
        let a = ddOf t_c (Var dddd2)
            b = ddOf t_c (Var dddd3)
        in (a .+. b) @?= (b .+. a)

    , testCase "Absorption: dddd2 AND (dddd2 OR dddd3) == dddd2" $
        let a = ddOf t_c (Var dddd2)
            b = ddOf t_c (Var dddd3)
        in (a .*. (a .+. b)) @?= a

    , testCase "Absorption: dddd2 OR (dddd2 AND dddd3) == dddd2" $
        let a = ddOf t_c (Var dddd2)
            b = ddOf t_c (Var dddd3)
        in (a .+. (a .*. b)) @?= a

    , testCase "De Morgan: NOT (dddd2 AND dddd3) == (NOT dddd2) OR (NOT dddd3)" $
        let a = ddOf t_c (Var dddd2)
            b = ddOf t_c (Var dddd3)
        in (-.) (a .*. b) @?= ((-.) a .+. (-.) b)

    , testCase "De Morgan: NOT (dddd2 OR dddd3) == (NOT dddd2) AND (NOT dddd3)" $
        let a = ddOf t_c (Var dddd2)
            b = ddOf t_c (Var dddd3)
        in (-.) (a .+. b) @?= ((-.) a .*. (-.) b)
    ]

  , testGroup "Mixed Dc-Neg-Pos-Dc (dnpd)"
    [ testCase "Idempotence AND: dnpd2 AND dnpd2 == dnpd2" $
        let a = ddOf t_c (Var dnpd2)
        in (a .*. a) @?= a

    , testCase "Complement: dnpd2 AND (NOT dnpd2) == bot" $
        let a = ddOf t_c (Var dnpd2)
        in (a .*. (-.) a) @?= bot

    , testCase "Complement: dnpd2 OR (NOT dnpd2) == top" $
        let a = ddOf t_c (Var dnpd2)
        in (a .+. (-.) a) @?= top

    , testCase "Double negation: NOT (NOT dnpd2) == dnpd2" $
        let a = ddOf t_c (Var dnpd2)
        in (-.) ((-.) a) @?= a

    , testCase "Commutativity AND: dnpd2 AND dnpd3 == dnpd3 AND dnpd2" $
        let a = ddOf t_c (Var dnpd2)
            b = ddOf t_c (Var dnpd3)
        in (a .*. b) @?= (b .*. a)

    , testCase "Absorption: dnpd2 AND (dnpd2 OR dnpd3) == dnpd2" $
        let a = ddOf t_c (Var dnpd2)
            b = ddOf t_c (Var dnpd3)
        in (a .*. (a .+. b)) @?= a

    , testCase "Absorption: dnpd2 OR (dnpd2 AND dnpd3) == dnpd2" $
        let a = ddOf t_c (Var dnpd2)
            b = ddOf t_c (Var dnpd3)
        in (a .+. (a .*. b)) @?= a

    , testCase "De Morgan: NOT (dnpd2 AND dnpd3) == (NOT dnpd2) OR (NOT dnpd3)" $
        let a = ddOf t_c (Var dnpd2)
            b = ddOf t_c (Var dnpd3)
        in (-.) (a .*. b) @?= ((-.) a .+. (-.) b)

    , testCase "De Morgan: NOT (dnpd2 OR dnpd3) == (NOT dnpd2) AND (NOT dnpd3)" $
        let a = ddOf t_c (Var dnpd2)
            b = ddOf t_c (Var dnpd3)
        in (-.) (a .+. b) @?= ((-.) a .*. (-.) b)

    , testCase "Distributivity: dnpd2 AND (dnpd3 OR dddd2) == (dnpd2 AND dnpd3) OR (dnpd2 AND dddd2)" $
        let a = ddOf t_c (Var dnpd2)
            b = ddOf t_c (Var dnpd3)
            c = ddOf t_c (Var dddd2)
        in (a .*. (b .+. c)) @?= ((a .*. b) .+. (a .*. c))

    , testCase "Distributivity: dnpd2 OR (dnpd3 AND dddd2) == (dnpd2 OR dnpd3) AND (dnpd2 OR dddd2)" $
        let a = ddOf t_c (Var dnpd2)
            b = ddOf t_c (Var dnpd3)
            c = ddOf t_c (Var dddd2)
        in (a .+. (b .*. c)) @?= ((a .+. b) .*. (a .+. c))
    ]

  , testGroup "Alternating Neg-Dc-Neg-Dc (ndnd)"
    [ testCase "Idempotence AND: ndnd2 AND ndnd2 == ndnd2" $
        let a = ddOf t_c (Var ndnd2)
        in (a .*. a) @?= a

    , testCase "Complement: ndnd2 AND (NOT ndnd2) == bot" $
        let a = ddOf t_c (Var ndnd2)
        in (a .*. (-.) a) @?= bot

    , testCase "Complement: ndnd2 OR (NOT ndnd2) == top" $
        let a = ddOf t_c (Var ndnd2)
        in (a .+. (-.) a) @?= top

    , testCase "Double negation: NOT (NOT ndnd2) == ndnd2" $
        let a = ddOf t_c (Var ndnd2)
        in (-.) ((-.) a) @?= a

    , testCase "Commutativity AND: ndnd2 AND ndnd3 == ndnd3 AND ndnd2" $
        let a = ddOf t_c (Var ndnd2)
            b = ddOf t_c (Var ndnd3)
        in (a .*. b) @?= (b .*. a)

    , testCase "Absorption: ndnd2 AND (ndnd2 OR ndnd3) == ndnd2" $
        let a = ddOf t_c (Var ndnd2)
            b = ddOf t_c (Var ndnd3)
        in (a .*. (a .+. b)) @?= a

    , testCase "De Morgan: NOT (ndnd2 AND ndnd3) == (NOT ndnd2) OR (NOT ndnd3)" $
        let a = ddOf t_c (Var ndnd2)
            b = ddOf t_c (Var ndnd3)
        in (-.) (a .*. b) @?= ((-.) a .+. (-.) b)

    , testCase "De Morgan: NOT (ndnd2 OR ndnd3) == (NOT ndnd2) AND (NOT ndnd3)" $
        let a = ddOf t_c (Var ndnd2)
            b = ddOf t_c (Var ndnd3)
        in (-.) (a .+. b) @?= ((-.) a .*. (-.) b)
    ]

  , testGroup "Cross 4-level types (mixed dnpd x dddd x ndnd)"
    [ testCase "Associativity AND: (dnpd2 AND dddd2) AND ndnd2 == dnpd2 AND (dddd2 AND ndnd2)" $
        let a = ddOf t_c (Var dnpd2)
            b = ddOf t_c (Var dddd2)
            c = ddOf t_c (Var ndnd2)
        in ((a .*. b) .*. c) @?= (a .*. (b .*. c))

    , testCase "Associativity OR: (dnpd2 OR dddd2) OR ndnd2 == dnpd2 OR (dddd2 OR ndnd2)" $
        let a = ddOf t_c (Var dnpd2)
            b = ddOf t_c (Var dddd2)
            c = ddOf t_c (Var ndnd2)
        in ((a .+. b) .+. c) @?= (a .+. (b .+. c))

    , testCase "Distributivity: dddd2 AND (dnpd2 OR ndnd2) == (dddd2 AND dnpd2) OR (dddd2 AND ndnd2)" $
        let a = ddOf t_c (Var dddd2)
            b = ddOf t_c (Var dnpd2)
            c = ddOf t_c (Var ndnd2)
        in (a .*. (b .+. c)) @?= ((a .*. b) .+. (a .*. c))

    , testCase "Distributivity: dddd2 OR (dnpd2 AND ndnd2) == (dddd2 OR dnpd2) AND (dddd2 OR ndnd2)" $
        let a = ddOf t_c (Var dddd2)
            b = ddOf t_c (Var dnpd2)
            c = ddOf t_c (Var ndnd2)
        in (a .+. (b .*. c)) @?= ((a .+. b) .*. (a .+. c))

    , testCase "Absorption: dddd2 AND (dddd2 OR dnpd2) == dddd2" $
        let a = ddOf t_c (Var dddd2)
            b = ddOf t_c (Var dnpd2)
        in (a .*. (a .+. b)) @?= a

    , testCase "De Morgan: NOT (dddd2 AND dnpd2) == (NOT dddd2) OR (NOT dnpd2)" $
        let a = ddOf t_c (Var dddd2)
            b = ddOf t_c (Var dnpd2)
        in (-.) (a .*. b) @?= ((-.) a .+. (-.) b)

    , testCase "De Morgan: NOT (dddd2 OR ndnd2) == (NOT dddd2) AND (NOT ndnd2)" $
        let a = ddOf t_c (Var dddd2)
            b = ddOf t_c (Var ndnd2)
        in (-.) (a .+. b) @?= ((-.) a .*. (-.) b)
    ]
  ]

-- ############################################################
-- Gap E: Cross-context tests at nested/multi-level depth
-- ############################################################

crossContextNested :: TestTree
crossContextNested = testGroup "Cross-context nested"
  [ testGroup "Dc-inner x Neg-inner (same outer Dc)"
    [ testCase "Commutativity AND: dcdc2 AND dcn1 == dcn1 AND dcdc2" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
        in (a .*. b) @?= (b .*. a)

    , testCase "Commutativity OR: dcdc2 OR dcn1 == dcn1 OR dcdc2" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
        in (a .+. b) @?= (b .+. a)

    , testCase "Distributivity: dcdc2 AND (dcn1 OR dcn23) == (dcdc2 AND dcn1) OR (dcdc2 AND dcn23)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
            c = ddOf t_c (Var dcn23)
        in (a .*. (b .+. c)) @?= ((a .*. b) .+. (a .*. c))

    , testCase "Distributivity: dcdc2 OR (dcn1 AND dcn23) == (dcdc2 OR dcn1) AND (dcdc2 OR dcn23)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
            c = ddOf t_c (Var dcn23)
        in (a .+. (b .*. c)) @?= ((a .+. b) .*. (a .+. c))

    , testCase "Absorption: dcdc2 AND (dcdc2 OR dcn1) == dcdc2" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
        in (a .*. (a .+. b)) @?= a

    , testCase "Absorption: dcn1 OR (dcn1 AND dcdc2) == dcn1" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcdc2)
        in (a .+. (a .*. b)) @?= a

    , testCase "De Morgan: NOT (dcdc2 AND dcn1) == (NOT dcdc2) OR (NOT dcn1)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
        in (-.) (a .*. b) @?= ((-.) a .+. (-.) b)

    , testCase "De Morgan: NOT (dcdc2 OR dcn1) == (NOT dcdc2) AND (NOT dcn1)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcn1)
        in (-.) (a .+. b) @?= ((-.) a .*. (-.) b)
    ]

  , testGroup "Dc-inner x Pos-inner (same outer Dc)"
    [ testCase "Commutativity AND: dcdc2 AND dcp1 == dcp1 AND dcdc2" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcp1)
        in (a .*. b) @?= (b .*. a)

    , testCase "Distributivity: dcdc2 AND (dcp1 OR dcp23) == (dcdc2 AND dcp1) OR (dcdc2 AND dcp23)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcp1)
            c = ddOf t_c (Var dcp23)
        in (a .*. (b .+. c)) @?= ((a .*. b) .+. (a .*. c))

    , testCase "Absorption: dcdc2 AND (dcdc2 OR dcp1) == dcdc2" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcp1)
        in (a .*. (a .+. b)) @?= a

    , testCase "De Morgan: NOT (dcdc2 AND dcp1) == (NOT dcdc2) OR (NOT dcp1)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcp1)
        in (-.) (a .*. b) @?= ((-.) a .+. (-.) b)

    , testCase "De Morgan: NOT (dcdc2 OR dcp1) == (NOT dcdc2) AND (NOT dcp1)" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var dcp1)
        in (-.) (a .+. b) @?= ((-.) a .*. (-.) b)
    ]

  , testGroup "Neg-inner x Pos-inner (same outer Dc)"
    [ testCase "Commutativity AND: dcn1 AND dcp1 == dcp1 AND dcn1" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcp1)
        in (a .*. b) @?= (b .*. a)

    , testCase "Distributivity: dcn1 AND (dcp1 OR dcp23) == (dcn1 AND dcp1) OR (dcn1 AND dcp23)" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcp1)
            c = ddOf t_c (Var dcp23)
        in (a .*. (b .+. c)) @?= ((a .*. b) .+. (a .*. c))

    , testCase "Absorption: dcn1 AND (dcn1 OR dcp1) == dcn1" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcp1)
        in (a .*. (a .+. b)) @?= a

    , testCase "De Morgan: NOT (dcn1 AND dcp1) == (NOT dcn1) OR (NOT dcp1)" $
        let a = ddOf t_c (Var dcn1)
            b = ddOf t_c (Var dcp1)
        in (-.) (a .*. b) @?= ((-.) a .+. (-.) b)
    ]

  , testGroup "Different outer contexts (Neg-nested x Dc-nested)"
    [ testCase "Commutativity AND: nn2 AND dcdc2 == dcdc2 AND nn2" $
        let a = ddOf t_c (Var nn2)
            b = ddOf t_c (Var dcdc2)
        in (a .*. b) @?= (b .*. a)

    , testCase "Commutativity OR: nn2 OR dcdc2 == dcdc2 OR nn2" $
        let a = ddOf t_c (Var nn2)
            b = ddOf t_c (Var dcdc2)
        in (a .+. b) @?= (b .+. a)

    , testCase "Distributivity: nn2 AND (dcdc2 OR dcdc3) == (nn2 AND dcdc2) OR (nn2 AND dcdc3)" $
        let a = ddOf t_c (Var nn2)
            b = ddOf t_c (Var dcdc2)
            c = ddOf t_c (Var dcdc3)
        in (a .*. (b .+. c)) @?= ((a .*. b) .+. (a .*. c))

    , testCase "Absorption: nn2 AND (nn2 OR dcdc2) == nn2" $
        let a = ddOf t_c (Var nn2)
            b = ddOf t_c (Var dcdc2)
        in (a .*. (a .+. b)) @?= a

    , testCase "Absorption: dcdc2 OR (dcdc2 AND nn2) == dcdc2" $
        let a = ddOf t_c (Var dcdc2)
            b = ddOf t_c (Var nn2)
        in (a .+. (a .*. b)) @?= a

    , testCase "De Morgan: NOT (nn2 AND dcdc2) == (NOT nn2) OR (NOT dcdc2)" $
        let a = ddOf t_c (Var nn2)
            b = ddOf t_c (Var dcdc2)
        in (-.) (a .*. b) @?= ((-.) a .+. (-.) b)

    , testCase "De Morgan: NOT (nn2 OR dcdc2) == (NOT nn2) AND (NOT dcdc2)" $
        let a = ddOf t_c (Var nn2)
            b = ddOf t_c (Var dcdc2)
        in (-.) (a .+. b) @?= ((-.) a .*. (-.) b)
    ]

  , testGroup "Pos-nested x Dc-nested"
    [ testCase "Commutativity AND: pp2 AND dcdc2 == dcdc2 AND pp2" $
        let a = ddOf t_c (Var pp2)
            b = ddOf t_c (Var dcdc2)
        in (a .*. b) @?= (b .*. a)

    , testCase "Absorption: pp2 AND (pp2 OR dcdc2) == pp2" $
        let a = ddOf t_c (Var pp2)
            b = ddOf t_c (Var dcdc2)
        in (a .*. (a .+. b)) @?= a

    , testCase "De Morgan: NOT (pp2 AND dcdc2) == (NOT pp2) OR (NOT dcdc2)" $
        let a = ddOf t_c (Var pp2)
            b = ddOf t_c (Var dcdc2)
        in (-.) (a .*. b) @?= ((-.) a .+. (-.) b)

    , testCase "De Morgan: NOT (pp2 OR dcdc2) == (NOT pp2) AND (NOT dcdc2)" $
        let a = ddOf t_c (Var pp2)
            b = ddOf t_c (Var dcdc2)
        in (-.) (a .+. b) @?= ((-.) a .*. (-.) b)
    ]
  ]
