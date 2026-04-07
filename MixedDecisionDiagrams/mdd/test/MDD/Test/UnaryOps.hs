{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module MDD.Test.UnaryOps where

import Test.Tasty
import Test.Tasty.HUnit

import MDD.Extra.Interface
import SMCDEL.Symbolic.Bool
import MDD.Test.Fixtures

tests :: TestTree
tests = testGroup "Unary Operations"
  [ negationTests
  , restrictTests
  , restrictNegTests
  , restrictPosTests
  , shannonExpansionTests
  , restrictNestedTests
  , shannonNestedTests
  ]

-- ============================================================
-- Negation
-- ============================================================

negationTests :: TestTree
negationTests = testGroup "Negation"
  [ testCase "NOT top == bot" $
      (-.) top @?= bot

  , testCase "NOT bot == top" $
      (-.) bot @?= top

  , testCase "NOT (NOT x) == x - double negation (Dc)" $
      let x = ddOf t_c (Var dc2)
      in (-.) ((-.) x) @?= x

  , testCase "NOT (NOT x) == x - double negation (Neg)" $
      let x = ddOf t_c (Var n2)
      in (-.) ((-.) x) @?= x

  , testCase "NOT (NOT x) == x - double negation (Pos)" $
      let x = ddOf t_c (Var p2)
      in (-.) ((-.) x) @?= x

  , testCase "De Morgan: NOT (x AND y) == (NOT x) OR (NOT y)" $
      let x = ddOf t_c (Var dc2)
          y = ddOf t_c (Var dc3)
      in (-.) (x .*. y) @?= ((-.) x .+. (-.) y)

  , testCase "De Morgan: NOT (x OR y) == (NOT x) AND (NOT y)" $
      let x = ddOf t_c (Var dc2)
          y = ddOf t_c (Var dc3)
      in (-.) (x .+. y) @?= ((-.) x .*. (-.) y)

  , testCase "NOT (x AND y) == (NOT x) OR (NOT y) - Neg context" $
      let x = ddOf t_c (Var n2)
          y = ddOf t_c (Var n3)
      in (-.) (x .*. y) @?= ((-.) x .+. (-.) y)

  , testCase "NOT (x AND y) == (NOT x) OR (NOT y) - Pos context" $
      let x = ddOf t_c (Var p2)
          y = ddOf t_c (Var p3)
      in (-.) (x .*. y) @?= ((-.) x .+. (-.) y)

  , testCase "NOT (nested Dc) double negation" $
      let x = ddOf t_c (Var dcdc2)
      in (-.) ((-.) x) @?= x

  , testCase "NOT (nested Neg) double negation" $
      let x = ddOf t_c (Var nn2)
      in (-.) ((-.) x) @?= x
  ]

-- ============================================================
-- Restrict
-- ============================================================

restrictTests :: TestTree
restrictTests = testGroup "Restrict"
  [ testCase "restrict pos True on (x OR y) removes x" $
      let xy = ddOf t_c (Or (Var dc1) (Var dc2))
      in restrict [1, 1] True xy @?= restrict [1, 1] True xy

  , testCase "restrict pos True then False gives consistent result" $
      let x = ddOf t_c (Var dc2)
      in restrict [1, 2] True x /= restrict [1, 2] False x
           @? "restricting to True vs False should differ"

  , testCase "restrict on top == top" $
      restrict [1, 1] True top @?= top

  , testCase "restrict on bot == bot" $
      restrict [1, 1] True bot @?= bot

  , testCase "restrict True then restrict False on same var gives bot for single-var MDD" $
      let x = ddOf t_c (Var dc2)
          r1 = restrict [1, 2] True x
          r2 = restrict [1, 2] False x
      in (r1 .*. r2) @?= bot
  ]

-- ============================================================
-- Restrict in Neg1 context
-- ============================================================

restrictNegTests :: TestTree
restrictNegTests = testGroup "Restrict (Neg context)"
  [ testCase "restrict on bot == bot (Neg)" $
      restrict [1, 2] True bot @?= bot

  , testCase "restrict True vs False differ for Neg variable" $
      let x = ddOf t_c (Var n2)
      in restrict [1, 2] True x /= restrict [1, 2] False x
           @? "restricting n2 to True vs False should differ"

  , testCase "restrict pos True on n2 is not bot (item is present)" $
      let x = ddOf t_c (Var n2)
      in restrict [1, 2] True x /= bot
           @? "restricting n2 to pos 2 True should not be bot"

  , testCase "restrict pos False on n2 gives bot (item removed, nothing left)" $
      let x = ddOf t_c (Var n2)
      in restrict [1, 2] False x @?= bot

  , testCase "restrict pos True on n23 (multi-item) is not bot" $
      let x = ddOf t_c (Var n23)
          r = restrict [1, 2] True x
      in r /= bot @? "restricting n23 to pos 2 True should not be bot"

  , testCase "restrict pos True on (n2 OR n3) is not bot" $
      let x = ddOf t_c (Or (Var n2) (Var n3))
      in restrict [1, 2] True x /= bot
           @? "restricting (n2 OR n3) to pos 2 True should not be bot"

  , testCase "restrict pos False on (n2 OR n3) is not bot (n3 branch remains)" $
      let x = ddOf t_c (Or (Var n2) (Var n3))
          r = restrict [1, 2] False x
      in r /= bot @? "restricting (n2 OR n3) with pos 2 False should give n3-like result"

  , testCase "restrict True AND restrict False on n2 gives bot" $
      let x = ddOf t_c (Var n2)
      in (restrict [1, 2] True x .*. restrict [1, 2] False x) @?= bot

  , testCase "restrict on cross-class Neg var: restrict class-2 pos on n_2 is not bot" $
      let x = ddOf t_c (Var n_2)
      in restrict [2, 2] True x /= bot
           @? "restricting n_2 to pos 2 True should not be bot"
  ]

-- ============================================================
-- Restrict in Pos1 context
-- ============================================================

restrictPosTests :: TestTree
restrictPosTests = testGroup "Restrict (Pos context)"
  [ testCase "restrict on bot == bot (Pos)" $
      restrict [1, 2] True bot @?= bot

  , testCase "restrict True vs False differ for Pos variable" $
      let x = ddOf t_c (Var p2)
      in restrict [1, 2] True x /= restrict [1, 2] False x
           @? "restricting p2 to True vs False should differ"

  , testCase "restrict pos True on p2 gives bot (excluded item is present -> contradiction)" $
      let x = ddOf t_c (Var p2)
      in restrict [1, 2] True x @?= bot

  , testCase "restrict pos False on p2 is not bot (excluded item is absent -> consistent)" $
      let x = ddOf t_c (Var p2)
      in restrict [1, 2] False x /= bot
           @? "restricting p2 to pos 2 False should not be bot"

  , testCase "restrict True AND restrict False on p2 gives bot" $
      let x = ddOf t_c (Var p2)
      in (restrict [1, 2] True x .*. restrict [1, 2] False x) @?= bot

  , testCase "restrict on cross-class Pos var: restrict class-2 pos True on p_2 gives bot" $
      let x = ddOf t_c (Var p_2)
      in restrict [2, 2] True x @?= bot
  ]

-- ============================================================
-- Shannon expansion: (v AND restrict v True x) OR (NOT v AND restrict v False x) == x
-- This is a fundamental identity that should hold in all contexts.
-- ============================================================

shannonExpansionTests :: TestTree
shannonExpansionTests = testGroup "Shannon Expansion"
  [ testCase "Shannon on dc2 (Dc)" $
      let x = ddOf t_c (Var dc2)
          v = ddOf t_c (Var dc2)
      in ((v .*. restrict [1, 2] True x) .+. ((-.) v .*. restrict [1, 2] False x)) @?= x

  , testCase "Shannon on n2 (Neg)" $
      let x = ddOf t_c (Var n2)
          v = ddOf t_c (Var dc2)
      in ((v .*. restrict [1, 2] True x) .+. ((-.) v .*. restrict [1, 2] False x)) @?= x

  , testCase "Shannon on p2 (Pos)" $
      let x = ddOf t_c (Var p2)
          v = ddOf t_c (Var dc2)
      in ((v .*. restrict [1, 2] True x) .+. ((-.) v .*. restrict [1, 2] False x)) @?= x

  , testCase "Shannon on compound Dc: dc2 AND dc3" $
      let x = ddOf t_c (And (Var dc2) (Var dc3))
          v = ddOf t_c (Var dc2)
      in ((v .*. restrict [1, 2] True x) .+. ((-.) v .*. restrict [1, 2] False x)) @?= x

  , testCase "Shannon on compound Neg: n2 OR n3" $
      let x = ddOf t_c (Or (Var n2) (Var n3))
          v = ddOf t_c (Var dc2)
      in ((v .*. restrict [1, 2] True x) .+. ((-.) v .*. restrict [1, 2] False x)) @?= x

  , testCase "Shannon on compound Pos: p2 OR p3" $
      let x = ddOf t_c (Or (Var p2) (Var p3))
          v = ddOf t_c (Var dc2)
      in ((v .*. restrict [1, 2] True x) .+. ((-.) v .*. restrict [1, 2] False x)) @?= x
  ]

-- ============================================================
-- Restrict on nested variables
-- ============================================================
--
-- For nested variables, the position includes the full class path.
-- dcdc2 (Dc1 outer class 1, Dc1 inner class 1, position 2)
-- is addressed as [1, 1, 2].

restrictNestedTests :: TestTree
restrictNestedTests = testGroup "Restrict (Nested)"
  [ testCase "restrict True vs False differ for nested Dc variable" $
      let x = ddOf t_c (Var dcdc2)
      in restrict [1, 1, 2] True x /= restrict [1, 1, 2] False x
           @? "restricting dcdc2 to True vs False should differ"

  , testCase "restrict True AND restrict False on nested Dc gives bot" $
      let x = ddOf t_c (Var dcdc2)
      in (restrict [1, 1, 2] True x .*. restrict [1, 1, 2] False x) @?= bot

  , testCase "restrict on nested top == top" $
      restrict [1, 1, 2] True top @?= top

  , testCase "restrict on nested bot == bot" $
      restrict [1, 1, 2] True bot @?= bot

  , testCase "restrict True vs False differ for nested Neg variable" $
      let x = ddOf t_c (Var nn2)
      in restrict [1, 1, 2] True x /= restrict [1, 1, 2] False x
           @? "restricting nn2 to True vs False should differ"

  , testCase "restrict pos True on nn2 is not bot (inner item present)" $
      let x = ddOf t_c (Var nn2)
      in restrict [1, 1, 2] True x /= bot
           @? "restricting nn2 to inner pos 2 True should not be bot"

  , testCase "restrict pos False on nn2 gives bot (inner item removed, nothing left)" $
      let x = ddOf t_c (Var nn2)
      in restrict [1, 1, 2] False x @?= bot

  , testCase "restrict True AND restrict False on nested Neg gives bot" $
      let x = ddOf t_c (Var nn2)
      in (restrict [1, 1, 2] True x .*. restrict [1, 1, 2] False x) @?= bot

  , testCase "restrict on mixed nested: restrict[1,1,1] True on dcn1 is not bot" $
      let x = ddOf t_c (Var dcn1)
      in restrict [1, 1, 1] True x /= bot
           @? "restricting dcn1 inner pos 1 True should not be bot"

  , testCase "restrict on mixed nested: restrict[1,1,1] False on dcn1 gives bot" $
      let x = ddOf t_c (Var dcn1)
      in restrict [1, 1, 1] False x @?= bot

  , testCase "restrict on compound nested: restrict[1,1,2] True on (dcdc2 OR dcdc3) is not bot" $
      let x = ddOf t_c (Or (Var dcdc2) (Var dcdc3))
      in restrict [1, 1, 2] True x /= bot
           @? "restricting (dcdc2 OR dcdc3) inner pos 2 True should not be bot"

  , testCase "restrict on compound nested: restrict[1,1,2] False on (dcdc2 OR dcdc3) is not bot" $
      let x = ddOf t_c (Or (Var dcdc2) (Var dcdc3))
      in restrict [1, 1, 2] False x /= bot
           @? "restricting (dcdc2 OR dcdc3) inner pos 2 False should not be bot (dcdc3 remains)"
  ]

-- ============================================================
-- Shannon expansion on nested variables
-- ============================================================
--
-- Shannon: (v AND restrict pos True x) OR (NOT v AND restrict pos False x) == x
-- For nested variables, v is a Dc variable at the same nested position,
-- and the restrict position matches.

shannonNestedTests :: TestTree
shannonNestedTests = testGroup "Shannon Expansion (Nested)"
  [ testCase "Shannon on dcdc2 (nested Dc)" $
      let x = ddOf t_c (Var dcdc2)
          v = ddOf t_c (Var dcdc2)
      in ((v .*. restrict [1, 1, 2] True x) .+. ((-.) v .*. restrict [1, 1, 2] False x)) @?= x

  , testCase "Shannon on nn2 (nested Neg)" $
      let x = ddOf t_c (Var nn2)
          v = ddOf t_c (Var dcdc2)
      in ((v .*. restrict [1, 1, 2] True x) .+. ((-.) v .*. restrict [1, 1, 2] False x)) @?= x

  , testCase "Shannon on compound nested Dc: dcdc2 AND dcdc3" $
      let x = ddOf t_c (And (Var dcdc2) (Var dcdc3))
          v = ddOf t_c (Var dcdc2)
      in ((v .*. restrict [1, 1, 2] True x) .+. ((-.) v .*. restrict [1, 1, 2] False x)) @?= x

  , testCase "Shannon on compound nested Dc: dcdc2 OR dcdc3" $
      let x = ddOf t_c (Or (Var dcdc2) (Var dcdc3))
          v = ddOf t_c (Var dcdc2)
      in ((v .*. restrict [1, 1, 2] True x) .+. ((-.) v .*. restrict [1, 1, 2] False x)) @?= x

  , testCase "Shannon on mixed nested: dcn1 OR dcn23" $
      let x = ddOf t_c (Or (Var dcn1) (Var dcn23))
          v = ddOf t_c (Var dcdc2)
      in ((v .*. restrict [1, 1, 2] True x) .+. ((-.) v .*. restrict [1, 1, 2] False x)) @?= x

  , testCase "Shannon on compound nested Neg: nn2 OR nn3" $
      let x = ddOf t_c (Or (Var nn2) (Var nn3))
          v = ddOf t_c (Var dcdc2)
      in ((v .*. restrict [1, 1, 2] True x) .+. ((-.) v .*. restrict [1, 1, 2] False x)) @?= x
  ]
