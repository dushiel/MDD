{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module MDD.Test.Relabeling where

import Test.Tasty
import Test.Tasty.HUnit

import MDD.Extra.Interface
import SMCDEL.Symbolic.Bool
import MDD.Test.Fixtures

tests :: TestTree
tests = testGroup "Relabeling"
  [ simpleRelabel
  , overlappingRelabel
  , crossDomainRelabel
  ]

-- ============================================================
-- Simple relabeling
-- ============================================================

simpleRelabel :: TestTree
simpleRelabel = testGroup "Simple relabeling"
  [ testCase "relabel [1,2] -> [1,3]: dc2 becomes dc3" $
      relabelWith [([1, 2], [1, 3])] dc2 @?= dc3

  , testCase "relabel [1,2] -> [2,2]: dc2 moves to class 2" $
      relabelWith [([1, 2], [2, 2])] dc2 @?= dc_2

  , testCase "relabel [1,2] -> [2,3]: dc2 becomes dc_3" $
      relabelWith [([1, 2], [2, 3])] dc2 @?= dc_3
  ]

-- ============================================================
-- Overlapping / simultaneous relabeling
-- ============================================================

overlappingRelabel :: TestTree
overlappingRelabel = testGroup "Overlapping relabeling"
  [ testCase "shift (2->3, 3->4) in (2 AND 3)" $
      relabelWith [([1, 2], [1, 3]), ([1, 3], [1, 4])] dc23 @?= node_and_34

  , testCase "shift (2->3, 3->4) in ((2 impl 1) AND 3)" $
      relabelWith [([1, 2], [1, 3]), ([1, 3], [1, 4])]
        (ddOf t_c_adv (And (Impl (Var dc2) (Var dc1)) (Var dc3)))
        @?= ddOf t_c_adv (And (Impl (Var dc3) (Var dc1)) (Var dc4))

  , testCase "swap (2<->3) in ((2 impl 1) AND 3)" $
      relabelWith [([1, 2], [1, 3]), ([1, 3], [1, 2])]
        (ddOf t_c_adv (And (Impl (Var dc2) (Var dc1)) (Var dc3)))
        @?= ddOf t_c_adv (And (Impl (Var dc3) (Var dc1)) (Var dc2))
  ]

-- ============================================================
-- Cross-domain relabeling
-- ============================================================

crossDomainRelabel :: TestTree
crossDomainRelabel = testGroup "Cross-domain relabeling"
  [ testCase "relabel from domain 2 to domain 1: ([2,2]->[1,3], [2,3]->[1,2]) in (dc_2 AND dc_3)" $
      relabelWith [([2, 2], [1, 3]), ([2, 3], [1, 2])]
        (ddOf t_c_adv (And (Var dc_2) (Var dc_3)))
        @?= dc23
  ]
