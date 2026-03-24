{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module MDD.Test.BinaryOps where

import Test.Tasty
import Test.Tasty.HUnit

import MDD.Extra.Interface
import SMCDEL.Symbolic.Bool
import MDD.Test.Fixtures

tests :: TestTree
tests = testGroup "Binary Operations"
  [ intersectionDc
  , intersectionNeg
  , intersectionPos
  , intersectionMixed
  , unionDc
  , unionNeg
  , unionPos
  , unionAndIntersectionDc
  , unionAndIntersectionNeg
  , multiLevelDc
  , multiLevelNeg1
  , multiLevelNeg0
  , multiLevelPos1
  , multiLevelPos0
  , multiLevelMixed
  , threeLevelOps
  , threeLevelMixed
  , contextSwitchingTests
  , negSpecificTautologies
  , posSpecificTautologies
  , crossContextTautologies
  ]

-- ============================================================
-- Intersection in Dc context
-- ============================================================

intersectionDc :: TestTree
intersectionDc = testGroup "Intersection (Dc)"
  [ testCase "x AND (NOT x) == Bot" $
      ddOf t_c (And (Var dc2) (Negate $ Var dc2)) @?= ddOf t_c Bot

  , testCase "x AND x == x (idempotent)" $
      ddOf t_c (And (Var dc3) (Var dc3)) @?= ddOf t_c (Var dc3)

  , testCase "x AND y == y AND x (commutative)" $
      ddOf t_c (And (Var dc2) (Var dc3)) @?= ddOf t_c (And (Var dc3) (Var dc2))
  ]

-- ============================================================
-- Intersection in Neg context
-- ============================================================

intersectionNeg :: TestTree
intersectionNeg = testGroup "Intersection (Neg)"
  [ testCase "n'2 AND n2 == Bot (opposite backgrounds)" $
      ddOf t_c (And (Var n'2) (Var n2)) @?= ddOf t_c Bot

  , testCase "n3 AND n2 == Bot (different items in same Neg class)" $
      ddOf t_c (And (Var n3) (Var n2)) @?= ddOf t_c Bot

  , testCase "n2 AND n3 == Bot (commutative check)" $
      ddOf t_c (And (Var n2) (Var n3)) @?= ddOf t_c Bot
  ]

-- ============================================================
-- Intersection in Pos context
-- ============================================================

intersectionPos :: TestTree
intersectionPos = testGroup "Intersection (Pos)"
  [ testCase "p3 AND p2 == Bot" $
      ddOf t_c (And (Var p3) (Var p2)) @?= ddOf t_c Bot

  , testCase "p3 AND p3 == p3 (idempotent)" $
      ddOf t_c (And (Var p3) (Var p3)) @?= ddOf t_c (Var p3)

  , testCase "p'3 AND p3 == Bot (opposite backgrounds)" $
      ddOf t_c (And (Var p'3) (Var p3)) @?= ddOf t_c Bot

  , testCase "p'2 AND p2 == Bot (opposite backgrounds)" $
      ddOf t_c (And (Var p'2) (Var p2)) @?= ddOf t_c Bot
  ]

-- ============================================================
-- Intersection with mixed contexts
-- ============================================================

intersectionMixed :: TestTree
intersectionMixed = testGroup "Intersection (Mixed)"
  [ testCase "dc2 AND (n2 OR n23) == (n2 OR n23) - Dc absorbs Neg" $
      ddOf t_c (And (Var dc2) (Or (Var n2) (Var n23)))
        @?= ddOf t_c (Or (Var n2) (Var n23))

  , testCase "dc'2 AND (p2 OR p23) == (p2 OR p23) - Dc absorbs Pos" $
      ddOf t_c (And (Var dc'2) (Or (Var p2) (Var p23)))
        @?= ddOf t_c (Or (Var p2) (Var p23))

  , testCase "dc2 OR (n2 OR n23) == dc2 - Dc subsumes Neg under union" $
      ddOf t_c (Or (Var dc2) (Or (Var n2) (Var n23)))
        @?= ddOf t_c (Var dc2)

  , testCase "dc'2 OR (p2 OR p23) == dc'2 - Dc subsumes Pos under union" $
      ddOf t_c (Or (Var dc'2) (Or (Var p2) (Var p23)))
        @?= ddOf t_c (Var dc'2)

  , testCase "(dc2 AND n'2) OR n'2 == n'2 - absorption" $
      ddOf t_c (Or (And (Var dc2) (Var n'2)) (Var n'2))
        @?= ddOf t_c (Var n'2)

  , testCase "(dc2 AND p'2) OR p'2 == p'2 - absorption" $
      ddOf t_c (Or (And (Var dc2) (Var p'2)) (Var p'2))
        @?= ddOf t_c (Var p'2)

  , testCase "(dc2 AND n'2) OR dc2 == dc2 - absorption" $
      ddOf t_c (Or (And (Var dc2) (Var n'2)) (Var dc2))
        @?= ddOf t_c (Var dc2)
  ]

-- ============================================================
-- Union in various contexts
-- ============================================================

unionDc :: TestTree
unionDc = testGroup "Union (Dc)"
  [ testCase "x OR (NOT x) == Top" $
      ddOf t_c (Or (Var dc2) (Negate $ Var dc2)) @?= ddOf t_c Top
  ]

unionNeg :: TestTree
unionNeg = testGroup "Union (Neg)"
  [ testCase "n'3 OR n'2 == Top" $
      ddOf t_c (Or (Var n'3) (Var n'2)) @?= ddOf t_c Top
  ]

unionPos :: TestTree
unionPos = testGroup "Union (Pos)"
  [ testCase "p'3 OR p'2 == Top" $
      ddOf t_c (Or (Var p'3) (Var p'2)) @?= ddOf t_c Top

  , testCase "p'2 OR p2 == Top" $
      ddOf t_c (Or (Var p'2) (Var p2)) @?= ddOf t_c Top
  ]

-- ============================================================
-- Union and intersection combined (Dc)
-- ============================================================

unionAndIntersectionDc :: TestTree
unionAndIntersectionDc = testGroup "Union+Intersection (Dc)"
  [ testCase "(dc2 AND dc3) OR dc3 == dc3 - absorption" $
      ddOf t_c (Or (And (Var dc2) (Var dc3)) (Var dc3))
        @?= ddOf t_c (Var dc3)

  , testCase "(dc2 AND dc3) OR dc2 == dc2 - absorption" $
      ddOf t_c (Or (And (Var dc2) (Var dc3)) (Var dc2))
        @?= ddOf t_c (Var dc2)

  , testCase "(dc2 OR dc3) AND dc3 == dc3 - absorption" $
      ddOf t_c (And (Or (Var dc2) (Var dc3)) (Var dc3))
        @?= ddOf t_c (Var dc3)

  , testCase "(dc2 OR dc3) AND dc2 == dc2 - absorption" $
      ddOf t_c (And (Or (Var dc2) (Var dc3)) (Var dc2))
        @?= ddOf t_c (Var dc2)
  ]

-- ============================================================
-- Union and intersection combined (Neg)
-- ============================================================

unionAndIntersectionNeg :: TestTree
unionAndIntersectionNeg = testGroup "Union+Intersection (Neg)"
  [ testCase "(n2 OR n3) AND n3 == n3" $
      ddOf t_c (And (Or (Var n2) (Var n3)) (Var n3))
        @?= ddOf t_c (Var n3)

  , testCase "(n2 OR n3) AND n2 == n2" $
      ddOf t_c (And (Or (Var n2) (Var n3)) (Var n2))
        @?= ddOf t_c (Var n2)

  , testCase "(n2 AND n3) OR n3 == n3" $
      ddOf t_c (Or (And (Var n2) (Var n3)) (Var n3))
        @?= ddOf t_c (Var n3)

  , testCase "(n2 AND n3) OR n2 == n2" $
      ddOf t_c (Or (And (Var n2) (Var n3)) (Var n2))
        @?= ddOf t_c (Var n2)
  ]

-- ============================================================
-- Multi-level: 2 levels of class hierarchy (Dc only)
-- ============================================================

multiLevelDc :: TestTree
multiLevelDc = testGroup "Multi-level (Dc)"
  [ testCase "(dc2 OR dc_2) AND dc_2 == dc_2" $
      ddOf t_c (And (Or (Var dc2) (Var dc_2)) (Var dc_2))
        @?= ddOf t_c (Var dc_2)

  , testCase "(dc2 OR dc_2) AND dc2 == dc2" $
      ddOf t_c (And (Or (Var dc2) (Var dc_2)) (Var dc2))
        @?= ddOf t_c (Var dc2)

  , testCase "(dc_2 AND dc__2) AND dc_2 == dc_2 AND dc__2" $
      ddOf t_c (And (And (Var dc_2) (Var dc__2)) (Var dc_2))
        @?= ddOf t_c (And (Var dc_2) (Var dc__2))
  ]

-- ============================================================
-- Multi-level: 2 levels (Neg1)
-- ============================================================

multiLevelNeg1 :: TestTree
multiLevelNeg1 = testGroup "Multi-level (Neg1)"
  [ testCase "(n2 AND n_2) OR n2 == n2" $
      ddOf t_c (Or (And (Var n2) (Var n_2)) (Var n2))
        @?= ddOf t_c (Var n2)

  , testCase "(n2 AND n_2) OR n_2 == n_2" $
      ddOf t_c (Or (And (Var n2) (Var n_2)) (Var n_2))
        @?= ddOf t_c (Var n_2)

  , testCase "(n2 OR n_2) AND n2 == n2" $
      ddOf t_c (And (Or (Var n2) (Var n_2)) (Var n2))
        @?= ddOf t_c (Var n2)

  , testCase "(n2 OR n_2) OR n_2 == n2 OR n_2" $
      ddOf t_c (Or (Or (Var n2) (Var n_2)) (Var n_2))
        @?= ddOf t_c (Or (Var n2) (Var n_2))

  , testCase "(n2 AND n_2) AND n2 == n2 AND n_2" $
      ddOf t_c (And (And (Var n2) (Var n_2)) (Var n2))
        @?= ddOf t_c (And (Var n2) (Var n_2))

  , testCase "(n2 AND n_2) OR n_2 == n_2" $
      ddOf t_c (Or (And (Var n2) (Var n_2)) (Var n_2))
        @?= ddOf t_c (Var n_2)

  , testCase "(n_2 AND n__2) AND n_2 == n_2 AND n__2" $
      ddOf t_c (And (And (Var n_2) (Var n__2)) (Var n_2))
        @?= ddOf t_c (And (Var n_2) (Var n__2))

  , testCase "n_2 AND (n_2 AND n__2) == n_2 AND n__2" $
      ddOf t_c (And (Var n_2) (And (Var n_2) (Var n__2)))
        @?= ddOf t_c (And (Var n_2) (Var n__2))
  ]

-- ============================================================
-- Multi-level: 2 levels (Neg0)
-- ============================================================

multiLevelNeg0 :: TestTree
multiLevelNeg0 = testGroup "Multi-level (Neg0)"
  [ testCase "(n'2 AND n'_2) OR n'2 == n'2" $
      ddOf t_c (Or (And (Var n'2) (Var n'_2)) (Var n'2))
        @?= ddOf t_c (Var n'2)

  , testCase "(n'2 AND n'_2) OR n'_2 == n'_2" $
      ddOf t_c (Or (And (Var n'2) (Var n'_2)) (Var n'_2))
        @?= ddOf t_c (Var n'_2)

  , testCase "(n'2 OR n'_2) AND n'2 == n'2" $
      ddOf t_c (And (Or (Var n'2) (Var n'_2)) (Var n'2))
        @?= ddOf t_c (Var n'2)

  , testCase "(n'2 OR n'_2) OR n'_2 == n'2 OR n'_2" $
      ddOf t_c (Or (Or (Var n'2) (Var n'_2)) (Var n'_2))
        @?= ddOf t_c (Or (Var n'2) (Var n'_2))

  , testCase "(n'2 AND n'_2) AND n'2 == n'2 AND n'_2" $
      ddOf t_c (And (And (Var n'2) (Var n'_2)) (Var n'2))
        @?= ddOf t_c (And (Var n'2) (Var n'_2))

  , testCase "(n'2 AND n'_2) OR n'_2 == n'_2" $
      ddOf t_c (Or (And (Var n'2) (Var n'_2)) (Var n'_2))
        @?= ddOf t_c (Var n'_2)
  ]

-- ============================================================
-- Multi-level: 2 levels (Pos1)
-- ============================================================

multiLevelPos1 :: TestTree
multiLevelPos1 = testGroup "Multi-level (Pos1)"
  [ testCase "(p_2 AND p__2) AND p_2 == p_2 AND p__2" $
      ddOf t_c (And (And (Var p_2) (Var p__2)) (Var p_2))
        @?= ddOf t_c (And (Var p_2) (Var p__2))

  , testCase "p_2 AND (p__2 AND p_2) == p_2 AND p__2" $
      ddOf t_c (And (Var p_2) (And (Var p__2) (Var p_2)))
        @?= ddOf t_c (And (Var p_2) (Var p__2))

  , testCase "(p2 AND p_2) OR p2 == p2" $
      ddOf t_c (Or (And (Var p2) (Var p_2)) (Var p2))
        @?= ddOf t_c (Var p2)

  , testCase "(p2 AND p_2) OR p_2 == p_2" $
      ddOf t_c (Or (And (Var p2) (Var p_2)) (Var p_2))
        @?= ddOf t_c (Var p_2)

  , testCase "(p2 OR p_2) AND p2 == p2" $
      ddOf t_c (And (Or (Var p2) (Var p_2)) (Var p2))
        @?= ddOf t_c (Var p2)

  , testCase "(p2 OR p_2) OR p_2 == p2 OR p_2" $
      ddOf t_c (Or (Or (Var p2) (Var p_2)) (Var p_2))
        @?= ddOf t_c (Or (Var p2) (Var p_2))

  , testCase "(p2 AND p_2) AND p2 == p2 AND p_2" $
      ddOf t_c (And (And (Var p2) (Var p_2)) (Var p2))
        @?= ddOf t_c (And (Var p2) (Var p_2))

  , testCase "(p2 AND p_2) OR p_2 == p_2" $
      ddOf t_c (Or (And (Var p2) (Var p_2)) (Var p_2))
        @?= ddOf t_c (Var p_2)
  ]

-- ============================================================
-- Multi-level: 2 levels (Pos0)
-- ============================================================

multiLevelPos0 :: TestTree
multiLevelPos0 = testGroup "Multi-level (Pos0)"
  [ testCase "(p'2 OR p'_2) AND p'2 == p'2" $
      ddOf t_c (And (Or (Var p'2) (Var p'_2)) (Var p'2))
        @?= ddOf t_c (Var p'2)

  , testCase "(p'2 OR p'_2) AND p'_2 == p'_2" $
      ddOf t_c (And (Or (Var p'2) (Var p'_2)) (Var p'_2))
        @?= ddOf t_c (Var p'_2)

  , testCase "(p'2 AND p'_2) OR p'2 == p'2" $
      ddOf t_c (Or (And (Var p'2) (Var p'_2)) (Var p'2))
        @?= ddOf t_c (Var p'2)

  , testCase "(p'2 AND p'_2) AND p'_2 == p'2 AND p'_2" $
      ddOf t_c (And (And (Var p'2) (Var p'_2)) (Var p'_2))
        @?= ddOf t_c (And (Var p'2) (Var p'_2))

  , testCase "(p'2 OR p'_2) OR p'2 == p'2 OR p'_2" $
      ddOf t_c (Or (Or (Var p'2) (Var p'_2)) (Var p'2))
        @?= ddOf t_c (Or (Var p'2) (Var p'_2))
  ]

-- ============================================================
-- Multi-level: mixing Neg0 and Neg1 across levels
-- ============================================================

multiLevelMixed :: TestTree
multiLevelMixed = testGroup "Multi-level (Mixed contexts)"
  [ testCase "(n'_2 AND n__2) AND n_2 == Bot" $
      ddOf t_c (And (And (Var n'_2) (Var n__2)) (Var n_2))
        @?= ddOf t_c Bot

  , testCase "(n'_2 AND n__2) AND n'_2 == n'_2 AND n__2" $
      ddOf t_c (And (And (Var n'_2) (Var n__2)) (Var n'_2))
        @?= ddOf t_c (And (Var n'_2) (Var n__2))
  ]

-- ============================================================
-- 3 levels of class hierarchy
-- ============================================================

threeLevelOps :: TestTree
threeLevelOps = testGroup "Three-level hierarchy"
  [ testCase "Neg0: (n'_2 AND n'__2) OR n'_2 == n'_2" $
      ddOf t_c (Or (And (Var n'_2) (Var n'__2)) (Var n'_2))
        @?= ddOf t_c (Var n'_2)

  , testCase "Pos0: (p'_2 AND p'__2) OR p'_2 == p'_2" $
      ddOf t_c (Or (And (Var p'_2) (Var p'__2)) (Var p'_2))
        @?= ddOf t_c (Var p'_2)

  , testCase "Pos1: (p_2 AND p__2) OR p_2 == p_2" $
      ddOf t_c (Or (And (Var p_2) (Var p__2)) (Var p_2))
        @?= ddOf t_c (Var p_2)

  , testCase "Neg1: (n_2 AND n__2) OR n_2 == n_2" $
      ddOf t_c (Or (And (Var n_2) (Var n__2)) (Var n_2))
        @?= ddOf t_c (Var n_2)

  , testCase "Neg0: ((n'_2 AND n'__2) AND n'3) OR (n'__2 AND n'3) == n'__2 AND n'3" $
      ddOf t_c (Or (And (And (Var n'_2) (Var n'__2)) (Var n'3)) (And (Var n'__2) (Var n'3)))
        @?= ddOf t_c (And (Var n'__2) (Var n'3))

  , testCase "Pos0: ((p'_2 AND p'__2) AND p'3) OR (p'__2 AND p'3) == p'__2 AND p'3" $
      ddOf t_c (Or (And (And (Var p'_2) (Var p'__2)) (Var p'3)) (And (Var p'__2) (Var p'3)))
        @?= ddOf t_c (And (Var p'__2) (Var p'3))

  , testCase "Pos1: ((p_2 AND p__2) AND p3) OR (p__2 AND p3) == p__2 AND p3" $
      ddOf t_c (Or (And (And (Var p_2) (Var p__2)) (Var p3)) (And (Var p__2) (Var p3)))
        @?= ddOf t_c (And (Var p__2) (Var p3))

  , testCase "Neg1: ((n_2 AND n__2) AND n3) OR (n__2 AND n3) == n__2 AND n3" $
      ddOf t_c (Or (And (And (Var n_2) (Var n__2)) (Var n3)) (And (Var n__2) (Var n3)))
        @?= ddOf t_c (And (Var n__2) (Var n3))

  , testCase "Neg0: ((n'_2 OR n'__2) OR n'3) AND (n'__2 OR n'3) == n'__2 OR n'3" $
      ddOf t_c (And (Or (Or (Var n'_2) (Var n'__2)) (Var n'3)) (Or (Var n'__2) (Var n'3)))
        @?= ddOf t_c (Or (Var n'__2) (Var n'3))

  , testCase "Pos0: ((p'_2 OR p'__2) OR p'3) AND (p'__2 OR p'3) == p'__2 OR p'3" $
      ddOf t_c (And (Or (Or (Var p'_2) (Var p'__2)) (Var p'3)) (Or (Var p'__2) (Var p'3)))
        @?= ddOf t_c (Or (Var p'__2) (Var p'3))

  , testCase "Pos1: ((p_2 OR p__2) OR p3) AND (p__2 OR p3) == p__2 OR p3" $
      ddOf t_c (And (Or (Or (Var p_2) (Var p__2)) (Var p3)) (Or (Var p__2) (Var p3)))
        @?= ddOf t_c (Or (Var p__2) (Var p3))

  , testCase "Neg1: ((n_2 OR n__2) OR n3) AND (n__2 OR n3) == n__2 OR n3" $
      ddOf t_c (And (Or (Or (Var n_2) (Var n__2)) (Var n3)) (Or (Var n__2) (Var n3)))
        @?= ddOf t_c (Or (Var n__2) (Var n3))
  ]

-- ============================================================
-- 3 levels mixing all domain types
-- ============================================================

threeLevelMixed :: TestTree
threeLevelMixed = testGroup "Three-level (mixed domain types)"
  [ testCase "((n'_2 OR p'__2) OR p3) AND (p'__2 OR p3) == p'__2 OR p3" $
      ddOf t_c (And (Or (Or (Var n'_2) (Var p'__2)) (Var p3)) (Or (Var p'__2) (Var p3)))
        @?= ddOf t_c (Or (Var p'__2) (Var p3))

  , testCase "complex mixed expression 1" $
      ddOf t_c (Or (And (Var dc2) (And (Var dc3) (Var n3)))
                   (And (Or (And (Var n'_2) (Var p'__2)) (Var p3))
                        (Or (Var p'__2) (Var p3))))
        @?= ddOf t_c (Or (And (Var dc2) (And (Var dc3) (Var n3)))
                         (Or (And (Var n'_2) (Var p'__2)) (Var p3)))

  , testCase "complex mixed expression 2" $
      ddOf t_c (Or (And (Var n2) (And (Var p'3) (Var dc3)))
                   (And (Or (And (Var p__2) (Var p'__2)) (Var p3))
                        (Or (Var n__2) (Var p3))))
        @?= ddOf t_c (Or (And (Var n2) (And (Var p'3) (Var dc3)))
                         (Or (And (Var p__2) (Var n__2)) (Var p3)))
  ]

-- ============================================================
-- Context switching: same class under different inference contexts
-- ============================================================
--
-- This tests the "bounding" pattern from MDDmodelling.md §9:
-- A Dc1 content term specifies values for specific sub-classes,
-- while a Neg1 bounding term limits which sub-classes can exist.
-- AND'ing them should produce a bounded, content-filled result.

contextSwitchingTests :: TestTree
contextSwitchingTests = testGroup "Context Switching"
  [ testCase "Dc content AND Neg bound: content is preserved within bound" $
      let content = ddOf t_c (Var cs_dc_sub1)
          bound   = ddOf t_c (Var cs_neg_bound12)
          result  = content .*. bound
      in result /= bot @? "Dc content within Neg bound should not be bot"

  , testCase "Dc content AND Neg bound: result implies content (result -> content is tautology)" $
      let content = ddOf t_c (Var cs_dc_sub1)
          bound   = ddOf t_c (Var cs_neg_bound12)
          result  = content .*. bound
      in (result .->. content) @?= top

  , testCase "Dc content AND Neg bound: result is more restrictive than bound alone" $
      let content = ddOf t_c (Var cs_dc_sub1)
          bound   = ddOf t_c (Var cs_neg_bound12)
          result  = content .*. bound
      in (result .+. bound) @?= bound

  , testCase "Two Dc contents AND Neg bound: both contents preserved" $
      let c1     = ddOf t_c (Var cs_dc_sub1)
          c2     = ddOf t_c (Var cs_dc_sub2)
          bound  = ddOf t_c (Var cs_neg_bound12)
          result = (c1 .*. c2) .*. bound
      in result /= bot @? "two Dc contents within matching Neg bound should not be bot"

  , testCase "Dc content outside Neg bound gives bot" $
      let c3     = ddOf t_c (Var cs_dc_sub3)
          bound  = ddOf t_c (Var cs_neg_bound12)
          result = c3 .*. bound
      in result @?= bot

  , testCase "Dc content AND wider Neg bound: sub-class 3 accepted by bound123" $
      let c3     = ddOf t_c (Var cs_dc_sub3)
          bound  = ddOf t_c (Var cs_neg_bound123)
          result = c3 .*. bound
      in result /= bot @? "sub-class 3 should be accepted by bound123"

  , testCase "Commutativity: bound AND content == content AND bound" $
      let content = ddOf t_c (Var cs_dc_sub1)
          bound   = ddOf t_c (Var cs_neg_bound12)
      in (bound .*. content) @?= (content .*. bound)

  , testCase "Neg bound is idempotent: bound AND bound == bound" $
      let bound = ddOf t_c (Var cs_neg_bound12)
      in (bound .*. bound) @?= bound

  , testCase "Narrower bound is more restrictive: bound1 AND bound12 == bound1" $
      let bound1  = ddOf t_c (Var cs_neg_bound1)
          bound12 = ddOf t_c (Var cs_neg_bound12)
      in (bound1 .*. bound12) @?= bound1

  , testCase "Wider bound subsumes narrower under OR: bound1 OR bound12 == bound12" $
      let bound1  = ddOf t_c (Var cs_neg_bound1)
          bound12 = ddOf t_c (Var cs_neg_bound12)
      in (bound1 .+. bound12) @?= bound12

  , testCase "Dc content OR Neg bound: Dc subsumes" $
      let content = ddOf t_c (Var cs_dc_sub1)
          bound   = ddOf t_c (Var cs_neg_bound12)
      in (content .+. bound) /= bot @? "OR of content and bound should not be bot"

  , testCase "Full pattern: content1 AND content2 AND bound == bounded content" $
      let c1     = ddOf t_c (Var cs_dc_sub1)
          c2     = ddOf t_c (Var cs_dc_sub2)
          bound  = ddOf t_c (Var cs_neg_bound12)
          bounded_content = (c1 .*. c2) .*. bound
      in do
          bounded_content /= bot @? "bounded content should not be bot"
          bounded_content /= (c1 .*. c2) @? "bounded content should differ from unbounded"
          (bounded_content .+. bound) @?= bound

  , testCase "Associativity with context switch: (c1 AND bound) AND c2 == c1 AND (bound AND c2)" $
      let c1    = ddOf t_c (Var cs_dc_sub1)
          c2    = ddOf t_c (Var cs_dc_sub2)
          bound = ddOf t_c (Var cs_neg_bound12)
      in ((c1 .*. bound) .*. c2) @?= (c1 .*. (bound .*. c2))
  ]

-- ############################################################
-- Gap 3: Context-specific tautologies
-- ############################################################

-- ============================================================
-- Neg-specific tautologies
-- ============================================================

negSpecificTautologies :: TestTree
negSpecificTautologies = testGroup "Neg-specific tautologies"
  [
  -- Mutual exclusion: n_i AND n_j == Bot for i /= j in same class
    testGroup "Mutual exclusion (same-class Neg1)"
    [ testCase "n2 AND n3 == Bot" $
        ddOf t_c (And (Var n2) (Var n3)) @?= ddOf t_c Bot

    , testCase "n3 AND n2 == Bot (commutative)" $
        ddOf t_c (And (Var n3) (Var n2)) @?= ddOf t_c Bot

    , testCase "n2 AND n23 == Bot (single vs multi-item)" $
        ddOf t_c (And (Var n2) (Var n23)) @?= ddOf t_c Bot

    , testCase "n3 AND n23 == Bot (single vs multi-item)" $
        ddOf t_c (And (Var n3) (Var n23)) @?= ddOf t_c Bot
    ]

  -- Exhaustive complement: n'_i OR n'_j == Top
  , testGroup "Exhaustive complement (same-class Neg0)"
    [ testCase "n'2 OR n'3 == Top" $
        ddOf t_c (Or (Var n'2) (Var n'3)) @?= ddOf t_c Top

    , testCase "n'3 OR n'2 == Top (commutative)" $
        ddOf t_c (Or (Var n'3) (Var n'2)) @?= ddOf t_c Top
    ]

  -- 1/0 suffix complement: n_i AND n'_i == Bot, n_i OR n'_i == Top
  , testGroup "1/0 suffix complement (Neg1 vs Neg0)"
    [ testCase "n2 AND n'2 == Bot (opposite backgrounds)" $
        ddOf t_c (And (Var n2) (Var n'2)) @?= ddOf t_c Bot

    , testCase "n2 OR n'2 == Top (opposite backgrounds)" $
        ddOf t_c (Or (Var n2) (Var n'2)) @?= ddOf t_c Top

    , testCase "n3 AND n'3 == Bot" $
        ddOf t_c (And (Var n3) (Var n'3)) @?= ddOf t_c Bot

    , testCase "n3 OR n'3 == Top" $
        ddOf t_c (Or (Var n3) (Var n'3)) @?= ddOf t_c Top
    ]

  -- Cross-class independence: n_i (class 1) AND n_j (class 2) /= Bot
  , testGroup "Cross-class independence (Neg)"
    [ testCase "n2 AND n_2 /= Bot (different classes)" $
        ddOf t_c (And (Var n2) (Var n_2)) /= ddOf t_c Bot
          @? "Neg vars in different classes should be independent"

    , testCase "n2 AND n__2 /= Bot (different classes)" $
        ddOf t_c (And (Var n2) (Var n__2)) /= ddOf t_c Bot
          @? "Neg vars in different classes should be independent"

    , testCase "n_2 AND n__2 /= Bot (different classes)" $
        ddOf t_c (And (Var n_2) (Var n__2)) /= ddOf t_c Bot
          @? "Neg vars in different classes should be independent"

    , testCase "n__2 AND n__3 == Bot (same class 3)" $
        ddOf t_c (And (Var n__2) (Var n__3)) @?= ddOf t_c Bot
    ]
  ]

-- ============================================================
-- Pos-specific tautologies
-- ============================================================

posSpecificTautologies :: TestTree
posSpecificTautologies = testGroup "Pos-specific tautologies"
  [
  -- Mutual exclusion: p_i AND p_j == Bot for i /= j in same class
    testGroup "Mutual exclusion (same-class Pos1)"
    [ testCase "p2 AND p3 == Bot" $
        ddOf t_c (And (Var p2) (Var p3)) @?= ddOf t_c Bot

    , testCase "p3 AND p2 == Bot (commutative)" $
        ddOf t_c (And (Var p3) (Var p2)) @?= ddOf t_c Bot

    , testCase "p2 AND p23 == Bot (single vs multi-item)" $
        ddOf t_c (And (Var p2) (Var p23)) @?= ddOf t_c Bot

    , testCase "p3 AND p23 == Bot (single vs multi-item)" $
        ddOf t_c (And (Var p3) (Var p23)) @?= ddOf t_c Bot
    ]

  -- Exhaustive complement: p'_i OR p'_j == Top
  , testGroup "Exhaustive complement (same-class Pos0)"
    [ testCase "p'2 OR p'3 == Top" $
        ddOf t_c (Or (Var p'2) (Var p'3)) @?= ddOf t_c Top

    , testCase "p'3 OR p'2 == Top (commutative)" $
        ddOf t_c (Or (Var p'3) (Var p'2)) @?= ddOf t_c Top
    ]

  -- 1/0 suffix complement: p_i AND p'_i == Bot, p_i OR p'_i == Top
  , testGroup "1/0 suffix complement (Pos1 vs Pos0)"
    [ testCase "p2 AND p'2 == Bot (opposite backgrounds)" $
        ddOf t_c (And (Var p2) (Var p'2)) @?= ddOf t_c Bot

    , testCase "p2 OR p'2 == Top (opposite backgrounds)" $
        ddOf t_c (Or (Var p2) (Var p'2)) @?= ddOf t_c Top

    , testCase "p3 AND p'3 == Bot" $
        ddOf t_c (And (Var p3) (Var p'3)) @?= ddOf t_c Bot

    , testCase "p3 OR p'3 == Top" $
        ddOf t_c (Or (Var p3) (Var p'3)) @?= ddOf t_c Top
    ]

  -- Cross-class independence: p_i (class 1) AND p_j (class 2) /= Bot
  , testGroup "Cross-class independence (Pos)"
    [ testCase "p2 AND p_2 /= Bot (different classes)" $
        ddOf t_c (And (Var p2) (Var p_2)) /= ddOf t_c Bot
          @? "Pos vars in different classes should be independent"

    , testCase "p2 AND p__2 /= Bot (different classes)" $
        ddOf t_c (And (Var p2) (Var p__2)) /= ddOf t_c Bot
          @? "Pos vars in different classes should be independent"
    ]
  ]

-- ============================================================
-- Cross-context tautologies (Dc absorbs/subsumes Neg/Pos)
-- ============================================================

crossContextTautologies :: TestTree
crossContextTautologies = testGroup "Cross-context tautologies"
  [
  -- Dc absorbs Neg under AND: dc_i AND n_i == n_i
    testGroup "Dc absorbs Neg under AND"
    [ testCase "dc2 AND n2 == n2" $
        ddOf t_c (And (Var dc2) (Var n2)) @?= ddOf t_c (Var n2)

    , testCase "dc3 AND n3 == n3" $
        ddOf t_c (And (Var dc3) (Var n3)) @?= ddOf t_c (Var n3)

    , testCase "n2 AND dc2 == n2 (commutative)" $
        ddOf t_c (And (Var n2) (Var dc2)) @?= ddOf t_c (Var n2)
    ]

  -- Dc subsumes Neg under OR: dc_i OR n_i == dc_i
  , testGroup "Dc subsumes Neg under OR"
    [ testCase "dc2 OR n2 == dc2" $
        ddOf t_c (Or (Var dc2) (Var n2)) @?= ddOf t_c (Var dc2)

    , testCase "dc3 OR n3 == dc3" $
        ddOf t_c (Or (Var dc3) (Var n3)) @?= ddOf t_c (Var dc3)

    , testCase "n2 OR dc2 == dc2 (commutative)" $
        ddOf t_c (Or (Var n2) (Var dc2)) @?= ddOf t_c (Var dc2)
    ]

  -- Dc absorbs Pos under AND: dc'_i AND p_i == p_i
  , testGroup "Dc absorbs Pos under AND"
    [ testCase "dc'2 AND p2 == p2" $
        ddOf t_c (And (Var dc'2) (Var p2)) @?= ddOf t_c (Var p2)

    , testCase "p2 AND dc'2 == p2 (commutative)" $
        ddOf t_c (And (Var p2) (Var dc'2)) @?= ddOf t_c (Var p2)
    ]

  -- Dc subsumes Pos under OR: dc'_i OR p_i == dc'_i
  , testGroup "Dc subsumes Pos under OR"
    [ testCase "dc'2 OR p2 == dc'2" $
        ddOf t_c (Or (Var dc'2) (Var p2)) @?= ddOf t_c (Var dc'2)

    , testCase "p2 OR dc'2 == dc'2 (commutative)" $
        ddOf t_c (Or (Var p2) (Var dc'2)) @?= ddOf t_c (Var dc'2)
    ]

  -- Neg AND Pos in same class: usually Bot
  , testGroup "Neg AND Pos conflict (same class)"
    [ testCase "n2 AND p2 == Bot (conflicting defaults)" $
        ddOf t_c (And (Var n2) (Var p2)) @?= ddOf t_c Bot

    , testCase "n3 AND p3 == Bot (conflicting defaults)" $
        ddOf t_c (And (Var n3) (Var p3)) @?= ddOf t_c Bot
    ]
  ]
