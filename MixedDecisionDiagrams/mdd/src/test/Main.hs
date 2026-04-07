module Main (main) where

import Test.Tasty
import MDD.Extra.Draw (settings, debug_on)
import System.Environment (getArgs)

import qualified MDD.Test.Construction as Construction
import qualified MDD.Test.BinaryOps as BinaryOps
import qualified MDD.Test.UnaryOps as UnaryOps
import qualified MDD.Test.Quantification as Quantification
import qualified MDD.Test.Relabeling as Relabeling
import qualified MDD.Test.Interface as Interface
import qualified MDD.Test.NestedDomains as NestedDomains
import qualified MDD.Test.Properties as Properties

main :: IO ()
main = do
  args <- getArgs
  let isFullTestRun = null args || not (any (\arg -> arg == "-p" || arg == "--pattern") args)
  if debug_on settings && isFullTestRun
    then error "\n\n=========================================\nERROR: Cannot run full test suite with debug_on = True in src/MDD/Extra/Draw.hs.\nPlease set it to False before running cabal test.\n=========================================\n\n"
    else defaultMain $ testGroup "MDD" 
      [ Construction.tests
      , BinaryOps.tests
      , NestedDomains.tests
      , UnaryOps.tests
      , Interface.tests
      , Quantification.tests
      , Relabeling.tests
      , Properties.tests
      ]
