module Main (main) where

import Test.Tasty

import qualified MDD.Test.Construction as Construction
import qualified MDD.Test.BinaryOps as BinaryOps
import qualified MDD.Test.UnaryOps as UnaryOps
import qualified MDD.Test.Quantification as Quantification
import qualified MDD.Test.Relabeling as Relabeling
import qualified MDD.Test.Interface as Interface
import qualified MDD.Test.NestedDomains as NestedDomains
import qualified MDD.Test.Properties as Properties

main :: IO ()
main = defaultMain $ testGroup "MDD" 
  [ Construction.tests
  , BinaryOps.tests
  , NestedDomains.tests
  , UnaryOps.tests
  , Interface.tests
  , Quantification.tests
  , Relabeling.tests
  , Properties.tests
  ]
