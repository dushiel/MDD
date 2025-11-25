module SMCDEL.Examples.MuddyChildren where

import Data.List
import Data.Map.Strict (fromList)

import SMCDEL.Internal.Help (seteq)
import Internal.Language
import SMCDEL.Symbolic.S5_MDD
-- import SMCDEL.Symbolic.K_MDD

mudScnInit :: Int -> Int -> KnowScene
mudScnInit n m = (KnS vocab law obs, actual) where
  vocab  = [P 1 .. P n]
  law    = boolMddOf Top
  obs    = [ (show i, delete (P i) vocab) | i <- [1..n] ]
  actual = [P 1 .. P m]


-- todo:
-- Int to path
-- init manager
-- update Language

myMudScnInit :: KnowScene
myMudScnInit = mudScnInit 3 3

knows :: Int -> Form
knows i = Kw (show i) (PrpF $ P i)

nobodyknows :: Int -> Form
nobodyknows n = Conj [ Neg $ knows i | i <- [1..n] ]

father :: Int -> Form
father n = Disj (map PrpF [P 1 .. P n])
mudScn0 :: KnowScene
mudScn0 = update myMudScnInit (father 3)

mudScn1 :: KnowScene
mudScn1 = update mudScn0 (nobodyknows 3)

mudScn2 :: KnowScene
mudKns2 :: KnowStruct
mudScn2@(mudKns2,_) = update mudScn1 (nobodyknows 3)

empty :: Int -> KnowScene
empty n = (KnS [] (boolMddOf Top) obs,[]) where
  obs    = [ (show i, []) | i <- [1..n] ]

-- buildMC :: Int -> Int -> Event
-- buildMC n m = (noChange KnTrf vocab Top obs, map P [1..m]) where
--   obs = [ (show i, delete (P i) vocab) | i <- [1..n] ]
--   vocab = map P [1..n]

-- buildResult :: KnowScene
-- buildResult = empty 3 `update` buildMC 3 3
