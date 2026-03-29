{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module MDD.Test.Quantification where

import Test.Tasty
import Test.Tasty.HUnit

import MDD.Extra.Interface
import SMCDEL.Symbolic.Bool
import MDD.Test.Fixtures

tests :: TestTree
tests = testGroup "Quantification"
  [ forallTests
  , existTests
  , forallSetTests
  , existSetTests
  , mixedQuantTests
  , trivialQuantTests
  , negQuantTests
  , posQuantTests
  , crossClassQuantTests
  , nestedQuantTests
  ]

-- ============================================================
-- Forall (universal quantification)
-- ============================================================

forallTests :: TestTree
forallTests = testGroup "Forall"
  [ testCase "forall[1] (1 OR 2) == 2" $
      forall [1, 1] (ddOf t_c $ Or (Var dc1) (Var dc2))
        @?= ddOf t_c (Var dc2)

  , testCase "forall[1] (1 XOR 2) == Bot" $
      forall [1, 1] (xor (ddOf t_c $ Var dc1) (ddOf t_c $ Var dc2))
        @?= ddOf t_c Bot

  , testCase "forall[1] ((1 AND 2) OR (1 AND 3)) == Bot" $
      forall [1, 1] (ddOf t_c $ Or (And (Var dc1) (Var dc2)) (And (Var dc1) (Var dc3)))
        @?= ddOf t_c Bot

  , testCase "forall[1] ((1 AND 2) OR (NOT 1 AND 3) OR (2 AND 3)) == 2 AND 3" $
      forall [1, 1] (ddOf t_c $ Or (Or (And (Var dc1) (Var dc2))
                                       (And (Negate $ Var dc1) (Var dc3)))
                                    (And (Var dc2) (Var dc3)))
        @?= ddOf t_c (And (Var dc2) (Var dc3))
  ]

-- ============================================================
-- Exists (existential quantification)
-- ============================================================

existTests :: TestTree
existTests = testGroup "Exists"
  [ testCase "exists[1] (1 -> 2) == Top" $
      exist [1, 1] (ddOf t_c $ Impl (Var dc1) (Var dc2))
        @?= ddOf t_c Top

  , testCase "exists[1] (1 <-> 2) == Top" $
      exist [1, 1] ((ddOf t_c $ Var dc1) .<->. (ddOf t_c $ Var dc2))
        @?= ddOf t_c Top

  , testCase "exists[1] ((1 -> 2) AND (NOT 1 -> 3)) == 2 OR 3" $
      exist [1, 1] (ddOf t_c $ And (Impl (Var dc1) (Var dc2))
                                    (Impl (Negate $ Var dc1) (Var dc3)))
        @?= ddOf t_c (Or (Var dc2) (Var dc3))
  ]

-- ============================================================
-- ForallSet (universal over multiple variables)
-- ============================================================

forallSetTests :: TestTree
forallSetTests = testGroup "ForallSet"
  [ testCase "forall[1] forall[2] (1 OR 2) == Bot" $
      forallSet [[1, 1], [1, 2]] (ddOf t_c $ Or (Var dc1) (Var dc2))
        @?= ddOf t_c Bot
  ]

-- ============================================================
-- ExistSet (existential over multiple variables)
-- ============================================================

existSetTests :: TestTree
existSetTests = testGroup "ExistSet"
  [ testCase "exists[1] exists[2] (1 AND 2) == Top" $
      existSet [[1, 1], [1, 2]] (ddOf t_c $ And (Var dc1) (Var dc2))
        @?= ddOf t_c Top
  ]

-- ============================================================
-- Mixed quantification
-- ============================================================

mixedQuantTests :: TestTree
mixedQuantTests = testGroup "Mixed quantification"
  [ testCase "forall[1] exists[2] (1 <-> 2) == Top" $
      forall [1, 1] (exist [1, 2] ((ddOf t_c $ Var dc1) .<->. (ddOf t_c $ Var dc2)))
        @?= ddOf t_c Top
  ]

-- ============================================================
-- Trivial quantification cases
-- ============================================================

trivialQuantTests :: TestTree
trivialQuantTests = testGroup "Trivial cases"
  [ testCase "forall v top == top" $
      forall [1, 1] top @?= top

  , testCase "forall v bot == bot" $
      forall [1, 1] bot @?= bot

  , testCase "exist v top == top" $
      exist [1, 1] top @?= top

  , testCase "exist v bot == bot" $
      exist [1, 1] bot @?= bot

  , testCase "forallSet [] x == x" $
      let x = ddOf t_c (Var dc2)
      in forallSet [] x @?= x

  , testCase "existSet [] x == x" $
      let x = ddOf t_c (Var dc2)
      in existSet [] x @?= x
  ]

-- ============================================================
-- Quantification over Neg1 variables
-- ============================================================
--
-- In Neg context, a variable has an implicit "absent" default.
-- forall v x = restrict v True x AND restrict v False x
-- exist  v x = restrict v True x OR  restrict v False x
--
-- For a single Neg variable n2 (position 2 in class 1):
--   restrict [1,2] True n2  -> the "item present" branch
--   restrict [1,2] False n2 -> Bot (item removed, nothing left)
-- So: exist [1,2] n2 = (not-bot) OR Bot = not-bot (should equal n2 itself if Shannon holds)
--     forall [1,2] n2 = (not-bot) AND Bot = Bot

negQuantTests :: TestTree
negQuantTests = testGroup "Quantification (Neg context)"
  [ testCase "forall over Neg var: forall[1,2] n2 == bot" $
      let x = ddOf t_c (Var n2)
      in forall [1, 2] x @?= bot

  , testCase "forall over Neg var: forall[1,3] n3 == bot" $
      let x = ddOf t_c (Var n3)
      in forall [1, 3] x @?= bot

  , testCase "exist over Neg var: exist[1,2] n2 is not bot" $
      let x = ddOf t_c (Var n2)
      in exist [1, 2] x /= bot
           @? "exist over n2 should not be bot"

  , testCase "forall over Neg union: forall[1,2] (n2 OR n3) == bot (restrict limitation)" $
      let x = ddOf t_c (Or (Var n2) (Var n3))
      in forall [1, 2] x @?= bot

  , testCase "exist over Neg union: exist[1,2] (n2 OR n3) is not bot" $
      let x = ddOf t_c (Or (Var n2) (Var n3))
      in exist [1, 2] x /= bot
           @? "exist[1,2] (n2 OR n3) should not be bot"

  , testCase "forall on top == top (Neg context, trivial)" $
      forall [1, 2] top @?= top

  , testCase "forall on bot == bot (Neg context, trivial)" $
      forall [1, 2] bot @?= bot

  , testCase "exist on top == top (Neg context, trivial)" $
      exist [1, 2] top @?= top

  , testCase "exist on bot == bot (Neg context, trivial)" $
      exist [1, 2] bot @?= bot

  , testCase "forall over multi-item: forall[1,2] n23 == bot (restrict limitation)" $
      let x = ddOf t_c (Var n23)
      in forall [1, 2] x @?= bot

  , testCase "forallSet over both positions: forallSet[[1,2],[1,3]] (n2 OR n3) == bot" $
      let x = ddOf t_c (Or (Var n2) (Var n3))
      in forallSet [[1, 2], [1, 3]] x @?= bot

  , testCase "existSet over both positions: existSet[[1,2],[1,3]] (n2 OR n3) is not bot" $
      let x = ddOf t_c (Or (Var n2) (Var n3))
      in existSet [[1, 2], [1, 3]] x /= bot
           @? "existSet over both positions of (n2 OR n3) should not be bot"
  ]

-- ============================================================
-- Quantification over Pos1 variables
-- ============================================================
--
-- In Pos context, a variable has an implicit "present" default.
-- p2 excludes position 2; restrict [1,2] True p2 -> Bot (excluded item present = contradiction)
-- restrict [1,2] False p2 -> not-bot (excluded item absent = consistent)
-- So: forall [1,2] p2 = Bot AND not-bot = Bot
--     exist  [1,2] p2 = Bot OR not-bot = not-bot

posQuantTests :: TestTree
posQuantTests = testGroup "Quantification (Pos context)"
  [ testCase "forall over Pos var: forall[1,2] p2 == bot" $
      let x = ddOf t_c (Var p2)
      in forall [1, 2] x @?= bot

  , testCase "forall over Pos var: forall[1,3] p3 == bot" $
      let x = ddOf t_c (Var p3)
      in forall [1, 3] x @?= bot

  , testCase "exist over Pos var: exist[1,2] p2 is not bot" $
      let x = ddOf t_c (Var p2)
      in exist [1, 2] x /= bot
           @? "exist over p2 should not be bot"

  , testCase "forall over Pos union: forall[1,2] (p2 OR p3) == bot (restrict limitation)" $
      let x = ddOf t_c (Or (Var p2) (Var p3))
      in forall [1, 2] x @?= bot

  , testCase "exist over Pos union: exist[1,2] (p2 OR p3) is not bot" $
      let x = ddOf t_c (Or (Var p2) (Var p3))
      in exist [1, 2] x /= bot
           @? "exist[1,2] (p2 OR p3) should not be bot"

  , testCase "forall over multi-item: forall[1,2] p23 == bot (restrict limitation)" $
      let x = ddOf t_c (Var p23)
      in forall [1, 2] x @?= bot

  , testCase "forallSet over both positions: forallSet[[1,2],[1,3]] (p2 OR p3) == bot" $
      let x = ddOf t_c (Or (Var p2) (Var p3))
      in forallSet [[1, 2], [1, 3]] x @?= bot

  , testCase "existSet over both positions: existSet[[1,2],[1,3]] (p2 OR p3) is not bot" $
      let x = ddOf t_c (Or (Var p2) (Var p3))
      in existSet [[1, 2], [1, 3]] x /= bot
           @? "existSet over both positions of (p2 OR p3) should not be bot"
  ]

-- ============================================================
-- Cross-class quantification
-- ============================================================
--
-- Quantifying over a variable in one class should not affect
-- variables in other classes, regardless of inference context.

crossClassQuantTests :: TestTree
crossClassQuantTests = testGroup "Cross-class quantification"
  [ testCase "forall[1,2] (n2 AND n_2) == bot (restrict limitation: forall eliminates n2, restrict loses class info)" $
      let x = ddOf t_c (And (Var n2) (Var n_2))
      in forall [1, 2] x @?= bot

  , testCase "exist[1,2] (n2 AND n_2) is not bot (n_2 survives)" $
      let x = ddOf t_c (And (Var n2) (Var n_2))
      in exist [1, 2] x /= bot
           @? "exist[1,2] on cross-class conjunction should not be bot"

  , testCase "forall[2,2] (n2 AND n_2) == bot (restrict limitation)" $
      let x = ddOf t_c (And (Var n2) (Var n_2))
      in forall [2, 2] x @?= bot

  , testCase "forall[1,2] (dc2 AND n_2) == bot (restrict limitation)" $
      let x = ddOf t_c (And (Var dc2) (Var n_2))
      in forall [1, 2] x @?= bot

  , testCase "exist[1,2] (p2 AND p_2) is not bot" $
      let x = ddOf t_c (And (Var p2) (Var p_2))
      in exist [1, 2] x /= bot
           @? "exist[1,2] on cross-class Pos conjunction should not be bot"

  , testCase "forall on Dc var: forall[1,2] dc2 == bot (standard BDD behavior)" $
      let x = ddOf t_c (Var dc2)
      in forall [1, 2] x @?= bot

  , testCase "exist on Dc var: exist[1,2] dc2 == top (standard BDD behavior)" $
      let x = ddOf t_c (Var dc2)
      in exist [1, 2] x @?= top
  ]

-- ============================================================
-- Quantification over nested variables
-- ============================================================
--
-- For a nested variable like dcdc2 (Dc1 outer class 1, Dc1 inner
-- class 1, position 2), the position to quantify over the inner
-- variable is [1, 1, 2].
-- For nn2 (Neg1 outer class 1, Neg1 inner class 1, position 2),
-- the inner position is also [1, 1, 2].

nestedQuantTests :: TestTree
nestedQuantTests = testGroup "Nested quantification"
  [ testCase "forall over nested Dc var: forall[1,1,2] dcdc2 == bot" $
      let x = ddOf t_c (Var dcdc2)
      in forall [1, 1, 2] x @?= bot

  , testCase "exist over nested Dc var: exist[1,1,2] dcdc2 == top" $
      let x = ddOf t_c (Var dcdc2)
      in exist [1, 1, 2] x @?= top

  , testCase "forall over nested Neg var: forall[1,1,2] nn2 == bot" $
      let x = ddOf t_c (Var nn2)
      in forall [1, 1, 2] x @?= bot

  , testCase "exist over nested Neg var: exist[1,1,2] nn2 is not bot" $
      let x = ddOf t_c (Var nn2)
      in exist [1, 1, 2] x /= bot
           @? "exist over nested nn2 should not be bot"

  , testCase "forall over compound nested Dc: forall[1,1,2] (dcdc2 OR dcdc3) == dcdc3" $
      let x = ddOf t_c (Or (Var dcdc2) (Var dcdc3))
      in forall [1, 1, 2] x @?= ddOf t_c (Var dcdc3)

  , testCase "exist over compound nested Dc: exist[1,1,2] (dcdc2 AND dcdc3) is not bot" $
      let x = ddOf t_c (And (Var dcdc2) (Var dcdc3))
      in exist [1, 1, 2] x /= bot
           @? "exist[1,1,2] on nested Dc conjunction should not be bot"

  , testCase "forall over compound nested Neg: forall[1,1,2] (nn2 OR nn3) == bot" $
      let x = ddOf t_c (Or (Var nn2) (Var nn3))
      in forall [1, 1, 2] x @?= bot

  , testCase "exist over compound nested Neg: exist[1,1,2] (nn2 OR nn3) is not bot" $
      let x = ddOf t_c (Or (Var nn2) (Var nn3))
      in exist [1, 1, 2] x /= bot
           @? "exist[1,1,2] on nested Neg union should not be bot"

  , testCase "forall nested trivial: forall[1,1,2] top == top" $
      forall [1, 1, 2] top @?= top

  , testCase "forall nested trivial: forall[1,1,2] bot == bot" $
      forall [1, 1, 2] bot @?= bot

  , testCase "exist nested trivial: exist[1,1,2] top == top" $
      exist [1, 1, 2] top @?= top

  , testCase "exist nested trivial: exist[1,1,2] bot == bot" $
      exist [1, 1, 2] bot @?= bot

  , testCase "forall over outer class of nested term: forall[1,2] dcdc2 is not top" $
      let x = ddOf t_c (Var dcdc2)
      in forall [1, 2] x /= top
           @? "forall over outer position of nested Dc should not be top"

  , testCase "exist over mixed nested: exist[1,1,1] dcn1 is not bot" $
      let x = ddOf t_c (Var dcn1)
      in exist [1, 1, 1] x /= bot
           @? "exist over inner position of dcn1 should not be bot"

  , testCase "forall over mixed nested: forall[1,1,1] dcn1 == bot" $
      let x = ddOf t_c (Var dcn1)
      in forall [1, 1, 1] x @?= bot
  ]
