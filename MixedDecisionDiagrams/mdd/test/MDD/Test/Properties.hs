{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module MDD.Test.Properties where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.ExpectedFailure (expectFailBecause)

import MDD.Types
import MDD.Extra.Interface
import SMCDEL.Symbolic.Bool
import MDD.Test.Fixtures

-- QuickCheck property tests require an Arbitrary instance for MDD,
-- which is non-trivial to write correctly (need valid paths, shared context).
-- For now, we test algebraic laws exhaustively over the fixture variables.
-- A future improvement would add a proper Arbitrary MDD generator.

tests :: TestTree
tests = testGroup "Algebraic Properties"
  [ testGroup "Dc1 context"
    [ identityLaws
    , annihilationLaws
    , idempotenceLaws
    , complementLaws
    , commutativityLaws
    , associativityLaws
    , distributivityLaws
    , absorptionLaws
    , deMorganLaws
    , doubleNegationLaws
    ]
  , testGroup "Neg1 context"
    [ negIdentityLaws
    , negAnnihilationLaws
    , negIdempotenceLaws
    , negComplementLaws
    , negCommutativityLaws
    , negAssociativityLaws
    , negDistributivityLaws
    , negAbsorptionLaws
    , negDeMorganLaws
    , negDoubleNegationLaws
    ]
  , testGroup "Pos1 context"
    [ posIdentityLaws
    , posAnnihilationLaws
    , posIdempotenceLaws
    , posComplementLaws
    , posCommutativityLaws
    , posAssociativityLaws
    , posDistributivityLaws
    , posAbsorptionLaws
    , posDeMorganLaws
    , posDoubleNegationLaws
    ]
  , testGroup "Dc0 context"
    [ dc0IdentityLaws
    , dc0AnnihilationLaws
    , dc0IdempotenceLaws
    , dc0ComplementLaws
    , dc0CommutativityLaws
    , dc0AssociativityLaws
    , dc0DistributivityLaws
    , dc0AbsorptionLaws
    , dc0DeMorganLaws
    , dc0DoubleNegationLaws
    , dc0Dc1InteractionLaws
    ]
  , testGroup "Cross-context"
    [ crossCommutativityLaws
    , crossDistributivityLaws
    , crossAbsorptionLaws
    , crossDeMorganLaws
    ]
  ]

-- ============================================================
-- Dc1 helpers
-- ============================================================

v2, v3, v1 :: MDD
v2 = ddOf t_c (Var dc2)
v3 = ddOf t_c (Var dc3)
v1 = ddOf t_c (Var dc1)

-- ============================================================
-- Neg1 helpers (same-class variables for coupling tests,
-- cross-class variables for independence tests)
-- ============================================================

nv2, nv3, nv23 :: MDD
nv2  = ddOf t_c (Var n2)
nv3  = ddOf t_c (Var n3)
nv23 = ddOf t_c (Var n23)

nv_2, nv__2, nv__3 :: MDD
nv_2  = ddOf t_c (Var n_2)
nv__2 = ddOf t_c (Var n__2)
nv__3 = ddOf t_c (Var n__3)

-- ============================================================
-- Pos1 helpers
-- ============================================================

pv2, pv3, pv23 :: MDD
pv2  = ddOf t_c (Var p2)
pv3  = ddOf t_c (Var p3)
pv23 = ddOf t_c (Var p23)

pv_2, pv__2 :: MDD
pv_2  = ddOf t_c (Var p_2)
pv__2 = ddOf t_c (Var p__2)

-- ============================================================
-- Dc1: Identity laws
-- ============================================================

identityLaws :: TestTree
identityLaws = testGroup "Identity"
  [ testCase "x AND top == x" $ (v2 .*. top) @?= v2
  , testCase "top AND x == x" $ (top .*. v2) @?= v2
  , testCase "x OR bot == x"  $ (v2 .+. bot) @?= v2
  , testCase "bot OR x == x"  $ (bot .+. v2) @?= v2
  ]

-- ============================================================
-- Dc1: Annihilation laws
-- ============================================================

annihilationLaws :: TestTree
annihilationLaws = testGroup "Annihilation"
  [ testCase "x AND bot == bot" $ (v2 .*. bot) @?= bot
  , testCase "bot AND x == bot" $ (bot .*. v2) @?= bot
  , testCase "x OR top == top"  $ (v2 .+. top) @?= top
  , testCase "top OR x == top"  $ (top .+. v2) @?= top
  ]

-- ============================================================
-- Dc1: Idempotence laws
-- ============================================================

idempotenceLaws :: TestTree
idempotenceLaws = testGroup "Idempotence"
  [ testCase "x AND x == x" $ (v2 .*. v2) @?= v2
  , testCase "x OR x == x"  $ (v2 .+. v2) @?= v2
  ]

-- ============================================================
-- Dc1: Complement laws
-- ============================================================

complementLaws :: TestTree
complementLaws = testGroup "Complement"
  [ testCase "x AND (NOT x) == bot" $ (v2 .*. (-.) v2) @?= bot
  , testCase "x OR (NOT x) == top"  $ (v2 .+. (-.) v2) @?= top
  , testCase "(NOT x) AND x == bot" $ ((-.) v2 .*. v2) @?= bot
  , testCase "(NOT x) OR x == top"  $ ((-.) v2 .+. v2) @?= top
  ]

-- ============================================================
-- Dc1: Commutativity laws
-- ============================================================

commutativityLaws :: TestTree
commutativityLaws = testGroup "Commutativity"
  [ testCase "x AND y == y AND x" $ (v2 .*. v3) @?= (v3 .*. v2)
  , testCase "x OR y == y OR x"   $ (v2 .+. v3) @?= (v3 .+. v2)
  ]

-- ============================================================
-- Dc1: Associativity laws
-- ============================================================

associativityLaws :: TestTree
associativityLaws = testGroup "Associativity"
  [ testCase "(x AND y) AND z == x AND (y AND z)" $
      ((v1 .*. v2) .*. v3) @?= (v1 .*. (v2 .*. v3))

  , testCase "(x OR y) OR z == x OR (y OR z)" $
      ((v1 .+. v2) .+. v3) @?= (v1 .+. (v2 .+. v3))
  ]

-- ============================================================
-- Dc1: Distributivity laws
-- ============================================================

distributivityLaws :: TestTree
distributivityLaws = testGroup "Distributivity"
  [ testCase "x AND (y OR z) == (x AND y) OR (x AND z)" $
      (v1 .*. (v2 .+. v3)) @?= ((v1 .*. v2) .+. (v1 .*. v3))

  , testCase "x OR (y AND z) == (x OR y) AND (x OR z)" $
      (v1 .+. (v2 .*. v3)) @?= ((v1 .+. v2) .*. (v1 .+. v3))
  ]

-- ============================================================
-- Dc1: Absorption laws
-- ============================================================

absorptionLaws :: TestTree
absorptionLaws = testGroup "Absorption"
  [ testCase "x AND (x OR y) == x" $
      (v2 .*. (v2 .+. v3)) @?= v2

  , testCase "x OR (x AND y) == x" $
      (v2 .+. (v2 .*. v3)) @?= v2
  ]

-- ============================================================
-- Dc1: De Morgan's laws
-- ============================================================

deMorganLaws :: TestTree
deMorganLaws = testGroup "De Morgan"
  [ testCase "NOT (x AND y) == (NOT x) OR (NOT y)" $
      (-.) (v2 .*. v3) @?= ((-.) v2 .+. (-.) v3)

  , testCase "NOT (x OR y) == (NOT x) AND (NOT y)" $
      (-.) (v2 .+. v3) @?= ((-.) v2 .*. (-.) v3)
  ]

-- ============================================================
-- Dc1: Double negation
-- ============================================================

doubleNegationLaws :: TestTree
doubleNegationLaws = testGroup "Double Negation"
  [ testCase "NOT (NOT x) == x (var 1)" $ (-.) ((-.) v1) @?= v1
  , testCase "NOT (NOT x) == x (var 2)" $ (-.) ((-.) v2) @?= v2
  , testCase "NOT (NOT x) == x (var 3)" $ (-.) ((-.) v3) @?= v3
  ]

-- ############################################################
-- Neg1 context: algebraic properties
-- ############################################################
--
-- In Neg1 context, same-class variables are coupled (n_i AND n_j == Bot
-- for i /= j). Cross-class Neg1 variables remain independent.
-- All structural laws should still hold, but many reduce to trivial
-- equalities (Bot == Bot) for same-class operands.
-- We test both same-class (coupled) and cross-class (independent) cases.

-- ============================================================
-- Neg1: Identity laws
-- ============================================================

negIdentityLaws :: TestTree
negIdentityLaws = testGroup "Identity"
  [ testCase "n2 AND top == n2" $ (nv2 .*. top) @?= nv2
  , testCase "top AND n2 == n2" $ (top .*. nv2) @?= nv2
  , testCase "n2 OR bot == n2"  $ (nv2 .+. bot) @?= nv2
  , testCase "bot OR n2 == n2"  $ (bot .+. nv2) @?= nv2
  ]

-- ============================================================
-- Neg1: Annihilation laws
-- ============================================================

negAnnihilationLaws :: TestTree
negAnnihilationLaws = testGroup "Annihilation"
  [ testCase "n2 AND bot == bot" $ (nv2 .*. bot) @?= bot
  , testCase "bot AND n2 == bot" $ (bot .*. nv2) @?= bot
  , testCase "n2 OR top == top"  $ (nv2 .+. top) @?= top
  , testCase "top OR n2 == top"  $ (top .+. nv2) @?= top
  ]

-- ============================================================
-- Neg1: Idempotence laws
-- ============================================================

negIdempotenceLaws :: TestTree
negIdempotenceLaws = testGroup "Idempotence"
  [ testCase "n2 AND n2 == n2"   $ (nv2 .*. nv2) @?= nv2
  , testCase "n2 OR n2 == n2"    $ (nv2 .+. nv2) @?= nv2
  , testCase "n23 AND n23 == n23 (multi-item cube)" $ (nv23 .*. nv23) @?= nv23
  , testCase "n23 OR n23 == n23"  $ (nv23 .+. nv23) @?= nv23
  ]

-- ============================================================
-- Neg1: Complement laws
-- ============================================================

negComplementLaws :: TestTree
negComplementLaws = testGroup "Complement"
  [ testCase "n2 AND (NOT n2) == bot" $ (nv2 .*. (-.) nv2) @?= bot
  , testCase "n2 OR (NOT n2) == top"  $ (nv2 .+. (-.) nv2) @?= top
  , testCase "(NOT n2) AND n2 == bot" $ ((-.) nv2 .*. nv2) @?= bot
  , testCase "(NOT n2) OR n2 == top"  $ ((-.) nv2 .+. nv2) @?= top
  ]

-- ============================================================
-- Neg1: Commutativity laws
-- ============================================================

negCommutativityLaws :: TestTree
negCommutativityLaws = testGroup "Commutativity"
  [ testCase "n2 AND n3 == n3 AND n2 (same-class, both Bot)" $
      (nv2 .*. nv3) @?= (nv3 .*. nv2)
  , testCase "n2 OR n3 == n3 OR n2" $
      (nv2 .+. nv3) @?= (nv3 .+. nv2)
  , testCase "n2 AND n_2 == n_2 AND n2 (cross-class)" $
      (nv2 .*. nv_2) @?= (nv_2 .*. nv2)
  , testCase "n2 OR n_2 == n_2 OR n2 (cross-class)" $
      (nv2 .+. nv_2) @?= (nv_2 .+. nv2)
  ]

-- ============================================================
-- Neg1: Associativity laws (cross-class for non-trivial case)
-- ============================================================

negAssociativityLaws :: TestTree
negAssociativityLaws = testGroup "Associativity"
  [ testCase "(n2 AND n_2) AND n__2 == n2 AND (n_2 AND n__2) (cross-class)" $
      ((nv2 .*. nv_2) .*. nv__2) @?= (nv2 .*. (nv_2 .*. nv__2))

  , testCase "(n2 OR n_2) OR n__2 == n2 OR (n_2 OR n__2) (cross-class)" $
      ((nv2 .+. nv_2) .+. nv__2) @?= (nv2 .+. (nv_2 .+. nv__2))

  , testCase "(n2 AND n3) AND n23 == n2 AND (n3 AND n23) (same-class, trivial Bot)" $
      ((nv2 .*. nv3) .*. nv23) @?= (nv2 .*. (nv3 .*. nv23))

  , testCase "(n2 OR n3) OR n23 == n2 OR (n3 OR n23) (same-class)" $
      ((nv2 .+. nv3) .+. nv23) @?= (nv2 .+. (nv3 .+. nv23))
  ]

-- ============================================================
-- Neg1: Distributivity laws
-- ============================================================

negDistributivityLaws :: TestTree
negDistributivityLaws = testGroup "Distributivity"
  [ testCase "n2 AND (n3 OR n23) == (n2 AND n3) OR (n2 AND n23) (same-class)" $
      (nv2 .*. (nv3 .+. nv23)) @?= ((nv2 .*. nv3) .+. (nv2 .*. nv23))

  , testCase "n2 OR (n3 AND n23) == (n2 OR n3) AND (n2 OR n23) (same-class)" $
      (nv2 .+. (nv3 .*. nv23)) @?= ((nv2 .+. nv3) .*. (nv2 .+. nv23))

  , testCase "n2 AND (n_2 OR n__2) == (n2 AND n_2) OR (n2 AND n__2) (cross-class)" $
      (nv2 .*. (nv_2 .+. nv__2)) @?= ((nv2 .*. nv_2) .+. (nv2 .*. nv__2))

  , testCase "n2 OR (n_2 AND n__2) == (n2 OR n_2) AND (n2 OR n__2) (cross-class)" $
      (nv2 .+. (nv_2 .*. nv__2)) @?= ((nv2 .+. nv_2) .*. (nv2 .+. nv__2))
  ]

-- ============================================================
-- Neg1: Absorption laws
-- ============================================================

negAbsorptionLaws :: TestTree
negAbsorptionLaws = testGroup "Absorption"
  [ testCase "n2 AND (n2 OR n3) == n2 (same-class)" $
      (nv2 .*. (nv2 .+. nv3)) @?= nv2

  , testCase "n2 OR (n2 AND n3) == n2 (same-class, trivial since n2 AND n3 == Bot)" $
      (nv2 .+. (nv2 .*. nv3)) @?= nv2

  , testCase "n2 AND (n2 OR n_2) == n2 (cross-class)" $
      (nv2 .*. (nv2 .+. nv_2)) @?= nv2

  , testCase "n2 OR (n2 AND n_2) == n2 (cross-class)" $
      (nv2 .+. (nv2 .*. nv_2)) @?= nv2
  ]

-- ============================================================
-- Neg1: De Morgan's laws
-- ============================================================

negDeMorganLaws :: TestTree
negDeMorganLaws = testGroup "De Morgan"
  [ testCase "NOT (n2 AND n3) == (NOT n2) OR (NOT n3) (same-class)" $
      (-.) (nv2 .*. nv3) @?= ((-.) nv2 .+. (-.) nv3)

  , testCase "NOT (n2 OR n3) == (NOT n2) AND (NOT n3) (same-class)" $
      (-.) (nv2 .+. nv3) @?= ((-.) nv2 .*. (-.) nv3)

  , testCase "NOT (n2 AND n_2) == (NOT n2) OR (NOT n_2) (cross-class)" $
      (-.) (nv2 .*. nv_2) @?= ((-.) nv2 .+. (-.) nv_2)

  , testCase "NOT (n2 OR n_2) == (NOT n2) AND (NOT n_2) (cross-class)" $
      (-.) (nv2 .+. nv_2) @?= ((-.) nv2 .*. (-.) nv_2)
  ]

-- ============================================================
-- Neg1: Double negation
-- ============================================================

negDoubleNegationLaws :: TestTree
negDoubleNegationLaws = testGroup "Double Negation"
  [ testCase "NOT (NOT n2) == n2"   $ (-.) ((-.) nv2) @?= nv2
  , testCase "NOT (NOT n3) == n3"   $ (-.) ((-.) nv3) @?= nv3
  , testCase "NOT (NOT n23) == n23" $ (-.) ((-.) nv23) @?= nv23
  ]

-- ############################################################
-- Pos1 context: algebraic properties
-- ############################################################
--
-- Pos1 mirrors Neg1: same-class variables are coupled (p_i AND p_j == Bot
-- for i /= j, since different exclusion sets conflict).
-- Cross-class Pos1 variables are independent.

-- ============================================================
-- Pos1: Identity laws
-- ============================================================

posIdentityLaws :: TestTree
posIdentityLaws = testGroup "Identity"
  [ testCase "p2 AND top == p2" $ (pv2 .*. top) @?= pv2
  , testCase "top AND p2 == p2" $ (top .*. pv2) @?= pv2
  , testCase "p2 OR bot == p2"  $ (pv2 .+. bot) @?= pv2
  , testCase "bot OR p2 == p2"  $ (bot .+. pv2) @?= pv2
  ]

-- ============================================================
-- Pos1: Annihilation laws
-- ============================================================

posAnnihilationLaws :: TestTree
posAnnihilationLaws = testGroup "Annihilation"
  [ testCase "p2 AND bot == bot" $ (pv2 .*. bot) @?= bot
  , testCase "bot AND p2 == bot" $ (bot .*. pv2) @?= bot
  , testCase "p2 OR top == top"  $ (pv2 .+. top) @?= top
  , testCase "top OR p2 == top"  $ (top .+. pv2) @?= top
  ]

-- ============================================================
-- Pos1: Idempotence laws
-- ============================================================

posIdempotenceLaws :: TestTree
posIdempotenceLaws = testGroup "Idempotence"
  [ testCase "p2 AND p2 == p2"   $ (pv2 .*. pv2) @?= pv2
  , testCase "p2 OR p2 == p2"    $ (pv2 .+. pv2) @?= pv2
  , testCase "p23 AND p23 == p23 (multi-item)" $ (pv23 .*. pv23) @?= pv23
  , testCase "p23 OR p23 == p23"  $ (pv23 .+. pv23) @?= pv23
  ]

-- ============================================================
-- Pos1: Complement laws
-- ============================================================

posComplementLaws :: TestTree
posComplementLaws = testGroup "Complement"
  [ testCase "p2 AND (NOT p2) == bot" $ (pv2 .*. (-.) pv2) @?= bot
  , testCase "p2 OR (NOT p2) == top"  $ (pv2 .+. (-.) pv2) @?= top
  , testCase "(NOT p2) AND p2 == bot" $ ((-.) pv2 .*. pv2) @?= bot
  , testCase "(NOT p2) OR p2 == top"  $ ((-.) pv2 .+. pv2) @?= top
  ]

-- ============================================================
-- Pos1: Commutativity laws
-- ============================================================

posCommutativityLaws :: TestTree
posCommutativityLaws = testGroup "Commutativity"
  [ testCase "p2 AND p3 == p3 AND p2 (same-class, both Bot)" $
      (pv2 .*. pv3) @?= (pv3 .*. pv2)
  , testCase "p2 OR p3 == p3 OR p2" $
      (pv2 .+. pv3) @?= (pv3 .+. pv2)
  , testCase "p2 AND p_2 == p_2 AND p2 (cross-class)" $
      (pv2 .*. pv_2) @?= (pv_2 .*. pv2)
  , testCase "p2 OR p_2 == p_2 OR p2 (cross-class)" $
      (pv2 .+. pv_2) @?= (pv_2 .+. pv2)
  ]

-- ============================================================
-- Pos1: Associativity laws (cross-class for non-trivial case)
-- ============================================================

posAssociativityLaws :: TestTree
posAssociativityLaws = testGroup "Associativity"
  [ testCase "(p2 AND p_2) AND p__2 == p2 AND (p_2 AND p__2) (cross-class)" $
      ((pv2 .*. pv_2) .*. pv__2) @?= (pv2 .*. (pv_2 .*. pv__2))

  , testCase "(p2 OR p_2) OR p__2 == p2 OR (p_2 OR p__2) (cross-class)" $
      ((pv2 .+. pv_2) .+. pv__2) @?= (pv2 .+. (pv_2 .+. pv__2))

  , testCase "(p2 AND p3) AND p23 == p2 AND (p3 AND p23) (same-class, trivial Bot)" $
      ((pv2 .*. pv3) .*. pv23) @?= (pv2 .*. (pv3 .*. pv23))

  , testCase "(p2 OR p3) OR p23 == p2 OR (p3 OR p23) (same-class)" $
      ((pv2 .+. pv3) .+. pv23) @?= (pv2 .+. (pv3 .+. pv23))
  ]

-- ============================================================
-- Pos1: Distributivity laws
-- ============================================================

posDistributivityLaws :: TestTree
posDistributivityLaws = testGroup "Distributivity"
  [ testCase "p2 AND (p3 OR p23) == (p2 AND p3) OR (p2 AND p23) (same-class)" $
      (pv2 .*. (pv3 .+. pv23)) @?= ((pv2 .*. pv3) .+. (pv2 .*. pv23))

  , testCase "p2 OR (p3 AND p23) == (p2 OR p3) AND (p2 OR p23) (same-class)" $
      (pv2 .+. (pv3 .*. pv23)) @?= ((pv2 .+. pv3) .*. (pv2 .+. pv23))

  , testCase "p2 AND (p_2 OR p__2) == (p2 AND p_2) OR (p2 AND p__2) (cross-class)" $
      (pv2 .*. (pv_2 .+. pv__2)) @?= ((pv2 .*. pv_2) .+. (pv2 .*. pv__2))

  , testCase "p2 OR (p_2 AND p__2) == (p2 OR p_2) AND (p2 OR p__2) (cross-class)" $
      (pv2 .+. (pv_2 .*. pv__2)) @?= ((pv2 .+. pv_2) .*. (pv2 .+. pv__2))
  ]

-- ============================================================
-- Pos1: Absorption laws
-- ============================================================

posAbsorptionLaws :: TestTree
posAbsorptionLaws = testGroup "Absorption"
  [ testCase "p2 AND (p2 OR p3) == p2 (same-class)" $
      (pv2 .*. (pv2 .+. pv3)) @?= pv2

  , testCase "p2 OR (p2 AND p3) == p2 (same-class, trivial since p2 AND p3 == Bot)" $
      (pv2 .+. (pv2 .*. pv3)) @?= pv2

  , testCase "p2 AND (p2 OR p_2) == p2 (cross-class)" $
      (pv2 .*. (pv2 .+. pv_2)) @?= pv2

  , testCase "p2 OR (p2 AND p_2) == p2 (cross-class)" $
      (pv2 .+. (pv2 .*. pv_2)) @?= pv2
  ]

-- ============================================================
-- Pos1: De Morgan's laws
-- ============================================================

posDeMorganLaws :: TestTree
posDeMorganLaws = testGroup "De Morgan"
  [ testCase "NOT (p2 AND p3) == (NOT p2) OR (NOT p3) (same-class)" $
      (-.) (pv2 .*. pv3) @?= ((-.) pv2 .+. (-.) pv3)

  , testCase "NOT (p2 OR p3) == (NOT p2) AND (NOT p3) (same-class)" $
      (-.) (pv2 .+. pv3) @?= ((-.) pv2 .*. (-.) pv3)

  , testCase "NOT (p2 AND p_2) == (NOT p2) OR (NOT p_2) (cross-class)" $
      (-.) (pv2 .*. pv_2) @?= ((-.) pv2 .+. (-.) pv_2)

  , testCase "NOT (p2 OR p_2) == (NOT p2) AND (NOT p_2) (cross-class)" $
      (-.) (pv2 .+. pv_2) @?= ((-.) pv2 .*. (-.) pv_2)
  ]

-- ============================================================
-- Pos1: Double negation
-- ============================================================

posDoubleNegationLaws :: TestTree
posDoubleNegationLaws = testGroup "Double Negation"
  [ testCase "NOT (NOT p2) == p2"   $ (-.) ((-.) pv2) @?= pv2
  , testCase "NOT (NOT p3) == p3"   $ (-.) ((-.) pv3) @?= pv3
  , testCase "NOT (NOT p23) == p23" $ (-.) ((-.) pv23) @?= pv23
  ]

-- ############################################################
-- Dc0 context: algebraic properties
-- ############################################################
--
-- Dc0 should behave symmetrically to Dc1 with inverted background.
-- Variables are independent (like Dc1), but the default leaf is True
-- instead of False. All classical Boolean algebra laws should hold.

-- ============================================================
-- Dc0 helpers
-- ============================================================

d0v1, d0v2, d0v3 :: MDD
d0v1 = ddOf t_c (Var dc0_1)
d0v2 = ddOf t_c (Var dc0_2)
d0v3 = ddOf t_c (Var dc0_3)

-- ============================================================
-- Dc0: Identity laws
-- ============================================================

dc0IdentityLaws :: TestTree
dc0IdentityLaws = testGroup "Identity"
  [ testCase "x AND top == x" $ (d0v2 .*. top) @?= d0v2
  , testCase "top AND x == x" $ (top .*. d0v2) @?= d0v2
  , testCase "x OR bot == x"  $ (d0v2 .+. bot) @?= d0v2
  , testCase "bot OR x == x"  $ (bot .+. d0v2) @?= d0v2
  ]

-- ============================================================
-- Dc0: Annihilation laws
-- ============================================================

dc0AnnihilationLaws :: TestTree
dc0AnnihilationLaws = testGroup "Annihilation"
  [ testCase "x AND bot == bot" $ (d0v2 .*. bot) @?= bot
  , testCase "bot AND x == bot" $ (bot .*. d0v2) @?= bot
  , testCase "x OR top == top"  $ (d0v2 .+. top) @?= top
  , testCase "top OR x == top"  $ (top .+. d0v2) @?= top
  ]

-- ============================================================
-- Dc0: Idempotence laws
-- ============================================================

dc0IdempotenceLaws :: TestTree
dc0IdempotenceLaws = testGroup "Idempotence"
  [ testCase "x AND x == x" $ (d0v2 .*. d0v2) @?= d0v2
  , testCase "x OR x == x"  $ (d0v2 .+. d0v2) @?= d0v2
  ]

-- ============================================================
-- Dc0: Complement laws
-- ============================================================

dc0ComplementLaws :: TestTree
dc0ComplementLaws = testGroup "Complement"
  [ testCase "x AND (NOT x) == bot" $ (d0v2 .*. (-.) d0v2) @?= bot
  , testCase "x OR (NOT x) == top"  $ (d0v2 .+. (-.) d0v2) @?= top
  , testCase "(NOT x) AND x == bot" $ ((-.) d0v2 .*. d0v2) @?= bot
  , testCase "(NOT x) OR x == top"  $ ((-.) d0v2 .+. d0v2) @?= top
  ]

-- ============================================================
-- Dc0: Commutativity laws
-- ============================================================

dc0CommutativityLaws :: TestTree
dc0CommutativityLaws = testGroup "Commutativity"
  [ testCase "x AND y == y AND x" $ (d0v2 .*. d0v3) @?= (d0v3 .*. d0v2)
  , testCase "x OR y == y OR x"   $ (d0v2 .+. d0v3) @?= (d0v3 .+. d0v2)
  ]

-- ============================================================
-- Dc0: Associativity laws
-- ============================================================

dc0AssociativityLaws :: TestTree
dc0AssociativityLaws = testGroup "Associativity"
  [ testCase "(x AND y) AND z == x AND (y AND z)" $
      ((d0v1 .*. d0v2) .*. d0v3) @?= (d0v1 .*. (d0v2 .*. d0v3))

  , testCase "(x OR y) OR z == x OR (y OR z)" $
      ((d0v1 .+. d0v2) .+. d0v3) @?= (d0v1 .+. (d0v2 .+. d0v3))
  ]

-- ============================================================
-- Dc0: Distributivity laws
-- ============================================================

dc0DistributivityLaws :: TestTree
dc0DistributivityLaws = testGroup "Distributivity"
  [ testCase "x AND (y OR z) == (x AND y) OR (x AND z)" $
      (d0v1 .*. (d0v2 .+. d0v3)) @?= ((d0v1 .*. d0v2) .+. (d0v1 .*. d0v3))

  , testCase "x OR (y AND z) == (x OR y) AND (x OR z)" $
      (d0v1 .+. (d0v2 .*. d0v3)) @?= ((d0v1 .+. d0v2) .*. (d0v1 .+. d0v3))
  ]

-- ============================================================
-- Dc0: Absorption laws
-- ============================================================

dc0AbsorptionLaws :: TestTree
dc0AbsorptionLaws = testGroup "Absorption"
  [ testCase "x AND (x OR y) == x" $
      (d0v2 .*. (d0v2 .+. d0v3)) @?= d0v2

  , testCase "x OR (x AND y) == x" $
      (d0v2 .+. (d0v2 .*. d0v3)) @?= d0v2
  ]

-- ============================================================
-- Dc0: De Morgan's laws
-- ============================================================

dc0DeMorganLaws :: TestTree
dc0DeMorganLaws = testGroup "De Morgan"
  [ testCase "NOT (x AND y) == (NOT x) OR (NOT y)" $
      (-.) (d0v2 .*. d0v3) @?= ((-.) d0v2 .+. (-.) d0v3)

  , testCase "NOT (x OR y) == (NOT x) AND (NOT y)" $
      (-.) (d0v2 .+. d0v3) @?= ((-.) d0v2 .*. (-.) d0v3)
  ]

-- ============================================================
-- Dc0: Double negation
-- ============================================================

dc0DoubleNegationLaws :: TestTree
dc0DoubleNegationLaws = testGroup "Double Negation"
  [ testCase "NOT (NOT x) == x (var 1)" $ (-.) ((-.) d0v1) @?= d0v1
  , testCase "NOT (NOT x) == x (var 2)" $ (-.) ((-.) d0v2) @?= d0v2
  , testCase "NOT (NOT x) == x (var 3)" $ (-.) ((-.) d0v3) @?= d0v3
  ]

-- ============================================================
-- Dc0 vs Dc1 interaction: opposite backgrounds are complements
-- ============================================================

dc0Dc1InteractionLaws :: TestTree
dc0Dc1InteractionLaws = testGroup "Dc0 vs Dc1 interaction"
  [ testCase "dc0_2 AND dc2 == bot (same class, opposite backgrounds are complements)" $
      (d0v2 .*. v2) @?= bot

  , testCase "dc0_2 OR dc2 == top (same class, opposite backgrounds are complements)" $
      (d0v2 .+. v2) @?= top

  , testCase "dc0_2 AND dc0_3 is satisfiable (Dc0 vars are independent)" $
      (d0v2 .*. d0v3) /= bot @? "Dc0 vars should be independent"

  , testCase "dc0_2 cross-class: dc0_2 AND dc0__2 is satisfiable" $
      let d0v_2 = ddOf t_c (Var dc0__2)
      in (d0v2 .*. d0v_2) /= bot @? "Dc0 cross-class vars should be independent"
  ]

-- ############################################################
-- Cross-context: algebraic properties across inference contexts
-- ############################################################
--
-- These test algebraic laws where operands come from different
-- inference contexts (Dc1, Neg1, Pos1). This exercises the most
-- complex traversal paths where implicit backgrounds differ.

-- ============================================================
-- Cross-context: Commutativity
-- ============================================================

crossCommutativityLaws :: TestTree
crossCommutativityLaws = testGroup "Commutativity"
  [ testCase "dc2 AND n2 == n2 AND dc2 (Dc x Neg)" $
      (v2 .*. nv2) @?= (nv2 .*. v2)
  , testCase "dc2 OR n2 == n2 OR dc2 (Dc x Neg)" $
      (v2 .+. nv2) @?= (nv2 .+. v2)
  , testCase "dc2 AND p2 == p2 AND dc2 (Dc x Pos)" $
      (v2 .*. pv2) @?= (pv2 .*. v2)
  , testCase "dc2 OR p2 == p2 OR dc2 (Dc x Pos)" $
      (v2 .+. pv2) @?= (pv2 .+. v2)
  , testCase "n2 AND p2 == p2 AND n2 (Neg x Pos)" $
      (nv2 .*. pv2) @?= (pv2 .*. nv2)
  , testCase "n2 OR p2 == p2 OR n2 (Neg x Pos)" $
      (nv2 .+. pv2) @?= (pv2 .+. nv2)
  ]

-- ============================================================
-- Cross-context: Distributivity
-- ============================================================

crossDistributivityLaws :: TestTree
crossDistributivityLaws = testGroup "Distributivity"
  [ testCase "dc2 AND (n2 OR n3) == (dc2 AND n2) OR (dc2 AND n3) (Dc over Neg)" $
      (v2 .*. (nv2 .+. nv3)) @?= ((v2 .*. nv2) .+. (v2 .*. nv3))
  , testCase "dc2 OR (n2 AND n3) == (dc2 OR n2) AND (dc2 OR n3) (Dc over Neg)" $
      (v2 .+. (nv2 .*. nv3)) @?= ((v2 .+. nv2) .*. (v2 .+. nv3))
  , testCase "dc2 AND (p2 OR p3) == (dc2 AND p2) OR (dc2 AND p3) (Dc over Pos)" $
      (v2 .*. (pv2 .+. pv3)) @?= ((v2 .*. pv2) .+. (v2 .*. pv3))
  , testCase "dc2 OR (p2 AND p3) == (dc2 OR p2) AND (dc2 OR p3) (Dc over Pos)" $
      (v2 .+. (pv2 .*. pv3)) @?= ((v2 .+. pv2) .*. (v2 .+. pv3))
  , testCase "n2 AND (dc2 OR dc3) == (n2 AND dc2) OR (n2 AND dc3) (Neg over Dc)" $
      (nv2 .*. (v2 .+. v3)) @?= ((nv2 .*. v2) .+. (nv2 .*. v3))
  , testCase "n2 OR (dc2 AND dc3) == (n2 OR dc2) AND (n2 OR dc3) (Neg over Dc)" $
      (nv2 .+. (v2 .*. v3)) @?= ((nv2 .+. v2) .*. (nv2 .+. v3))
  , testCase "p2 AND (dc2 OR dc3) == (p2 AND dc2) OR (p2 AND dc3) (Pos over Dc)" $
      (pv2 .*. (v2 .+. v3)) @?= ((pv2 .*. v2) .+. (pv2 .*. v3))
  , expectFailBecause "library bug: Pos-edge not reduced in cross-context OR-over-AND" $
    testCase "p2 OR (dc2 AND dc3) == (p2 OR dc2) AND (p2 OR dc3) (Pos over Dc)" $
      (pv2 .+. (v2 .*. v3)) @?= ((pv2 .+. v2) .*. (pv2 .+. v3))
  ]

-- ============================================================
-- Cross-context: Absorption
-- ============================================================

crossAbsorptionLaws :: TestTree
crossAbsorptionLaws = testGroup "Absorption"
  [ testCase "dc2 AND (dc2 OR n2) == dc2 (Dc absorbs Dc+Neg)" $
      (v2 .*. (v2 .+. nv2)) @?= v2
  , testCase "dc2 OR (dc2 AND n2) == dc2 (Dc absorbs Dc*Neg)" $
      (v2 .+. (v2 .*. nv2)) @?= v2
  , testCase "dc2 AND (dc2 OR p2) == dc2 (Dc absorbs Dc+Pos)" $
      (v2 .*. (v2 .+. pv2)) @?= v2
  , testCase "dc2 OR (dc2 AND p2) == dc2 (Dc absorbs Dc*Pos)" $
      (v2 .+. (v2 .*. pv2)) @?= v2
  , testCase "n2 AND (n2 OR dc2) == n2 (Neg absorbs Neg+Dc)" $
      (nv2 .*. (nv2 .+. v2)) @?= nv2
  , testCase "n2 OR (n2 AND dc2) == n2 (Neg absorbs Neg*Dc)" $
      (nv2 .+. (nv2 .*. v2)) @?= nv2
  , testCase "p2 AND (p2 OR dc2) == p2 (Pos absorbs Pos+Dc)" $
      (pv2 .*. (pv2 .+. v2)) @?= pv2
  , testCase "p2 OR (p2 AND dc2) == p2 (Pos absorbs Pos*Dc)" $
      (pv2 .+. (pv2 .*. v2)) @?= pv2
  ]

-- ============================================================
-- Cross-context: De Morgan
-- ============================================================

crossDeMorganLaws :: TestTree
crossDeMorganLaws = testGroup "De Morgan"
  [ testCase "NOT (dc2 AND n2) == (NOT dc2) OR (NOT n2) (Dc x Neg)" $
      (-.) (v2 .*. nv2) @?= ((-.) v2 .+. (-.) nv2)
  , testCase "NOT (dc2 OR n2) == (NOT dc2) AND (NOT n2) (Dc x Neg)" $
      (-.) (v2 .+. nv2) @?= ((-.) v2 .*. (-.) nv2)
  , testCase "NOT (dc2 AND p2) == (NOT dc2) OR (NOT p2) (Dc x Pos)" $
      (-.) (v2 .*. pv2) @?= ((-.) v2 .+. (-.) pv2)
  , testCase "NOT (dc2 OR p2) == (NOT dc2) AND (NOT p2) (Dc x Pos)" $
      (-.) (v2 .+. pv2) @?= ((-.) v2 .*. (-.) pv2)
  , testCase "NOT (n2 AND p2) == (NOT n2) OR (NOT p2) (Neg x Pos)" $
      (-.) (nv2 .*. pv2) @?= ((-.) nv2 .+. (-.) pv2)
  , testCase "NOT (n2 OR p2) == (NOT n2) AND (NOT p2) (Neg x Pos)" $
      (-.) (nv2 .+. pv2) @?= ((-.) nv2 .*. (-.) pv2)
  ]
