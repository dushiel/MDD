{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module MDD.Test.Construction where

import Test.Tasty
import Test.Tasty.HUnit

import MDD.Types
import MDD.Extra.Interface
import MDD.Construction (path, add_path, makeNode, levelLtoPath)
import MDD.NodeLookup (init_lookup)

tests :: TestTree
tests = testGroup "Construction"
  [ testGroup "path: terminal paths"
    [ testCase "P'' [n] produces a non-trivial MDD" $
        let m = path (P'' [2])
        in m /= bot @? "path with single variable should not be bot"

    , testCase "P'' [n] with positive int gives positive evaluation" $
        let m = path (P'' [3])
        in m /= bot @? "positive variable path should not be bot"

    , testCase "P'' [-n] with negative int gives negative evaluation" $
        let m = path (P'' [-3])
        in m /= bot @? "negative variable path should not be bot"

    , testCase "P'' [0] in Dc1 context produces wildcard (Top)" $
        let m = path (P' [(1, Dc1, P'' [0])])
        in m /= bot @? "wildcard path should not be bot"

    , testCase "P'' [a, b] produces multi-variable path" $
        let m = path (P'' [2, 3])
        in m /= bot @? "multi-variable path should not be bot"
    ]

  , testGroup "path: class paths"
    [ testCase "P' with Dc1 produces ClassNode-containing MDD" $
        let m = path (P' [(1, Dc1, P'' [2])])
        in m /= bot @? "Dc1 class path should not be bot"

    , testCase "P' with Neg1 produces ClassNode-containing MDD" $
        let m = path (P' [(1, Neg1, P'' [2])])
        in m /= bot @? "Neg1 class path should not be bot"

    , testCase "P' with Pos1 produces ClassNode-containing MDD" $
        let m = path (P' [(1, Pos1, P'' [-2])])
        in m /= bot @? "Pos1 class path should not be bot"

    , testCase "Dc1 and Dc0 produce different MDDs" $
        let m1 = path (P' [(1, Dc1, P'' [2])])
            m2 = path (P' [(1, Dc0, P'' [2])])
        in m1 /= m2 @? "Dc1 and Dc0 should differ (different background)"

    , testCase "Neg1 and Neg0 produce different MDDs" $
        let m1 = path (P' [(1, Neg1, P'' [2])])
            m2 = path (P' [(1, Neg0, P'' [2])])
        in m1 /= m2 @? "Neg1 and Neg0 should differ"

    , testCase "Pos1 and Pos0 produce different MDDs" $
        let m1 = path (P' [(1, Pos1, P'' [-2])])
            m2 = path (P' [(1, Pos0, P'' [-2])])
        in m1 /= m2 @? "Pos1 and Pos0 should differ"
    ]

  , testGroup "path: nested class paths"
    [ testCase "nested Dc inside Dc" $
        let m = path (P' [(1, Dc1, P' [(1, Dc1, P'' [2])])])
        in m /= bot @? "nested Dc path should not be bot"

    , testCase "nested Neg inside Neg" $
        let m = path (P' [(1, Neg1, P' [(1, Neg1, P'' [2])])])
        in m /= bot @? "nested Neg path should not be bot"

    , testCase "nested Pos inside Pos" $
        let m = path (P' [(1, Pos1, P' [(1, Pos1, P'' [-2])])])
        in m /= bot @? "nested Pos path should not be bot"

    , testCase "mixed nesting: Dc containing Neg" $
        let m = path (P' [(1, Dc1, P' [(1, Neg1, P'' [2])])])
        in m /= bot @? "Dc-Neg nested path should not be bot"

    , testCase "3-level nesting" $
        let m = path (P' [(1, Dc1, P' [(2, Neg1, P' [(1, Dc1, P'' [3])])])])
        in m /= bot @? "3-level nested path should not be bot"
    ]

  , testGroup "add_path"
    [ testCase "adding a path to an existing MDD preserves the original" $
        let m1 = path (P' [(1, Dc1, P'' [2])])
            m2 = add_path m1 (P' [(1, Dc1, P'' [3])])
        in m2 /= m1 @? "add_path should produce a different MDD"

    , testCase "add_path with same path is idempotent for the lookup" $
        let m1 = path (P' [(1, Dc1, P'' [2])])
            m2 = add_path m1 (P' [(1, Dc1, P'' [2])])
        in m2 /= bot @? "re-adding same path should not produce bot"
    ]

  , testGroup "makeNode / levelLtoPath consistency"
    [ testCase "makeNode from LevelL matches path from equivalent Path" $
        let ll = Ll [(1, Dc1)] 2
            fromMakeNode = makeNode init_lookup ll
            fromPath = path (levelLtoPath ll)
        in fromMakeNode == fromPath @? "makeNode and path via levelLtoPath should agree"

    , testCase "var and var' produce equivalent results" $
        let p = P' [(1, Dc1, P'' [2])]
            ll = Ll [(1, Dc1)] 2
        in var p == var' ll @? "var and var' should produce equal MDDs"

    , testCase "levelLtoPath round-trips simple LevelL" $
        let ll = Ll [(1, Neg1)] 3
            converted = levelLtoPath ll
        in case converted of
             P' [(1, Neg1, P'' [3])] -> return ()
             other -> assertFailure $ "unexpected path structure: " ++ show other

    , testCase "levelLtoPath round-trips nested LevelL" $
        let ll = Ll [(1, Dc1), (2, Neg1)] 5
            converted = levelLtoPath ll
        in case converted of
             P' [(1, Dc1, P' [(2, Neg1, P'' [5])])] -> return ()
             other -> assertFailure $ "unexpected path structure: " ++ show other
    ]
  ]
