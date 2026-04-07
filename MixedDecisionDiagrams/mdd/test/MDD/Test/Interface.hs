{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module MDD.Test.Interface where

import Test.Tasty
import Test.Tasty.HUnit

import MDD.Extra.Interface
import SMCDEL.Symbolic.Bool
import MDD.Test.Fixtures

tests :: TestTree
tests = testGroup "Interface / Derived Operators"
  [ constantTests
  , iteTests
  , xorTests
  , implicationTests
  , biconditionalTests
  , setOperationTests
  ]

-- ============================================================
-- Constants
-- ============================================================

constantTests :: TestTree
constantTests = testGroup "Constants"
  [ testCase "top /= bot" $
      top /= bot @? "top and bot should differ"

  , testCase "top AND bot == bot" $
      top .*. bot @?= bot

  , testCase "top OR bot == top" $
      top .+. bot @?= top

  , testCase "top AND top == top" $
      top .*. top @?= top

  , testCase "bot OR bot == bot" $
      bot .+. bot @?= bot
  ]

-- ============================================================
-- If-then-else
-- ============================================================

iteTests :: TestTree
iteTests = testGroup "If-then-else"
  [ testCase "ite top a b == a" $
      let a = ddOf t_c (Var dc2)
          b = ddOf t_c (Var dc3)
      in ite top a b @?= a

  , testCase "ite bot a b == b" $
      let a = ddOf t_c (Var dc2)
          b = ddOf t_c (Var dc3)
      in ite bot a b @?= b

  , testCase "ite x top bot == x" $
      let x = ddOf t_c (Var dc2)
      in ite x top bot @?= x

  , testCase "ite x bot top == NOT x" $
      let x = ddOf t_c (Var dc2)
      in ite x bot top @?= (-.) x

  , testCase "ite x y y == y" $
      let x = ddOf t_c (Var dc2)
          y = ddOf t_c (Var dc3)
      in ite x y y @?= y
  ]

-- ============================================================
-- XOR
-- ============================================================

xorTests :: TestTree
xorTests = testGroup "XOR"
  [ testCase "x XOR x == bot (self-cancellation)" $
      let x = ddOf t_c (Var dc2)
      in xor x x @?= bot

  , testCase "x XOR bot == x" $
      let x = ddOf t_c (Var dc2)
      in xor x bot @?= x

  , testCase "x XOR top == NOT x" $
      let x = ddOf t_c (Var dc2)
      in xor x top @?= (-.) x

  , testCase "x XOR y == y XOR x (commutative)" $
      let x = ddOf t_c (Var dc2)
          y = ddOf t_c (Var dc3)
      in xor x y @?= xor y x

  , testCase "top XOR bot == top" $
      xor top bot @?= top
  ]

-- ============================================================
-- Implication
-- ============================================================

implicationTests :: TestTree
implicationTests = testGroup "Implication"
  [ testCase "x -> top == top" $
      let x = ddOf t_c (Var dc2)
      in (x .->. top) @?= top

  , testCase "bot -> x == top (ex falso)" $
      let x = ddOf t_c (Var dc2)
      in (bot .->. x) @?= top

  , testCase "top -> x == x" $
      let x = ddOf t_c (Var dc2)
      in (top .->. x) @?= x

  , testCase "x -> bot == NOT x" $
      let x = ddOf t_c (Var dc2)
      in (x .->. bot) @?= (-.) x

  , testCase "x -> x == top" $
      let x = ddOf t_c (Var dc2)
      in (x .->. x) @?= top
  ]

-- ============================================================
-- Biconditional
-- ============================================================

biconditionalTests :: TestTree
biconditionalTests = testGroup "Biconditional"
  [ testCase "x <-> x == top (reflexive)" $
      let x = ddOf t_c (Var dc2)
      in (x .<->. x) @?= top

  , testCase "x <-> y == y <-> x (commutative)" $
      let x = ddOf t_c (Var dc2)
          y = ddOf t_c (Var dc3)
      in (x .<->. y) @?= (y .<->. x)

  , testCase "top <-> x == x" $
      let x = ddOf t_c (Var dc2)
      in (top .<->. x) @?= x

  , testCase "bot <-> x == NOT x" $
      let x = ddOf t_c (Var dc2)
      in (bot .<->. x) @?= (-.) x
  ]

-- ============================================================
-- Set operations
-- ============================================================

setOperationTests :: TestTree
setOperationTests = testGroup "Set operations"
  [ testCase "conSet [] == top" $
      conSet [] @?= top

  , testCase "disSet [] == bot" $
      disSet [] @?= bot

  , testCase "conSet [a, b] == a AND b" $
      let a = ddOf t_c (Var dc2)
          b = ddOf t_c (Var dc3)
      in conSet [a, b] @?= (a .*. b)

  , testCase "disSet [a, b] == a OR b" $
      let a = ddOf t_c (Var dc2)
          b = ddOf t_c (Var dc3)
      in disSet [a, b] @?= (a .+. b)

  , testCase "conSet [a, b, c] == (a AND b) AND c" $
      let a = ddOf t_c (Var dc2)
          b = ddOf t_c (Var dc3)
          c = ddOf t_c (Var dc1)
      in conSet [a, b, c] @?= ((a .*. b) .*. c)

  , testCase "disSet [a, b, c] == (a OR b) OR c" $
      let a = ddOf t_c (Var dc2)
          b = ddOf t_c (Var dc3)
          c = ddOf t_c (Var dc1)
      in disSet [a, b, c] @?= ((a .+. b) .+. c)

  , testCase "conSet [top, x] == x" $
      let x = ddOf t_c (Var dc2)
      in conSet [top, x] @?= x

  , testCase "disSet [bot, x] == x" $
      let x = ddOf t_c (Var dc2)
      in disSet [bot, x] @?= x

  , testCase "conSet [bot, x] == bot" $
      let x = ddOf t_c (Var dc2)
      in conSet [bot, x] @?= bot

  , testCase "disSet [top, x] == top" $
      let x = ddOf t_c (Var dc2)
      in disSet [top, x] @?= top

  , testCase "xorSet [x] == x" $
      let x = ddOf t_c (Var dc2)
      in xorSet [x] @?= x

  , testCase "xorSet [x, x] == bot" $
      let x = ddOf t_c (Var dc2)
      in xorSet [x, x] @?= bot
  ]
