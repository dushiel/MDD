{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE TupleSections #-}
{-# HLINT ignore "Move brackets to avoid $" #-}
module Examples.Example where

import qualified Data.Map.Strict as Map
import MDD.Extra.Interface
import MDD.Types
import SMCDEL.Symbolic.Bool
import MDD.Extra.Draw (debug5)


-- signature = map from strings to MDD Positions / ordinals indicating the variable class

-- assocs :: [(Position, [Char])]
-- assocs = [([0, 2], "word"), ([0, 3], "shape"), ([0, 3, 5], "bear-like"), ([0,5], "feeling"), ([0,5,1], "danger")] ++ zip [[0, 2, i, j] | i <- [1..7], j <- [0..70]] (map (:[]) (cycle " abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890,.!?():-"))


-- -- Create the signature from the list of pairs
-- signature :: Map.Map Position String
-- signature = Map.fromList assocs


-- blob of experience
--

-- Implicit ordinals, responsibility of the use for correct formatting
symbols :: Map.Map Char Int
symbols = Map.fromList $ zip " abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890,.!?():-" [0..]

word :: [Char] -> Form
word sl = Var . var $ word_label $ P' [
        if s == '*' then (s_pos, Dc1, P'' [0])
        else (s_pos, Neg1, P'' [symbols Map.! s])
     | (s_pos, s) <- zip [1.. ] sl]

word_label :: Path -> Path
word_label c = P' [(2, Neg1, c)]

end_of_word :: Int -> Form
end_of_word i = Var . var $ P' [(2, Neg1, P' [(j, Dc1, P'' [0]) | j <- [1..i]])]

vocabulary :: Form
vocabulary = foldl1 Or (map word ["dani", "daniel", "run"]) --, "Malvin", "what?", "What a nice day!", ":)", ":-)","what else?", "what even.."])

shape_label :: Path -> Path
shape_label c = P' [(3, Dc1, c)]

shapes :: Map.Map String Int
shapes = Map.fromList $ zip ["rectangular", "round", "line", "face-like", "bear-like", "big", "small"] [1..]

shape :: [String] -> Form
shape sl = Var . var $ shape_label $ P'' [shapes Map.! s | s <- sl]


color_label :: Path -> Path
color_label c = P' [(4, Dc1, c)]

colors :: Map.Map String Int
-- dimensions would be the three cone value activations? cluster in which can define colors. once recognizable for the understanding they are given a label below.
colors = Map.fromList $ zip ["red", "orange", "yellow", "green", "blue", "purple", "white", "grey", "black"] [1..]

color :: [String] -> Form
color sl = Var . var $ color_label $ P'' [colors Map.! s | s <- sl]


feeling_label :: Path -> Path
feeling_label c = P' [(5, Dc1, c)]

feelings :: Map.Map String Int
-- dimensions here would be based on neuro science findings, what are core mechanisms that can influence us in such a way that we are open to conceptualizing them
feelings = Map.fromList $ zip ["danger", "safety", "interesse", "boredom", "friendship", "distance", "admiration", "disdain",  "love", "hate",  "in-control", "lost", "hot", "cold"] [1..]

feeling :: [String] -> Form
feeling sl = Var . var $ feeling_label $ P'' [feelings Map.! s | s <- sl]

bear_fear :: Form
bear_fear = Impl (shape ["bear-like"]) (And (feeling ["danger"]) (word "run")) --
-- generateAndShow_c


-- todo add sentences
-- senToDd = ezPath . sentenceToPath

-- sentenceToPath :: String -> EasyPath
-- -- e.g. (Dc, 3, [(Neg1, 1, [ (Neg1, [1,2, -3]) ]) ])
-- sentenceToPath s = InfP Neg1 [2] [InfP Neg1 [2,x] [NodeP Neg1 ([[2,x] ++ symbols Map.! y | ' ' /= y]) ] | (x, y) <- zip [1..] s ]

-- eFilter v = v .*. ezPath (InfP Dc [2] [InfP Neg1 [2,x] [NodeP Neg1 [[2,x] ++ symbols Map.! 'e']] | x <- [1 .. 50]])
-- eFilter2 v = v .*. ezPath (InfP Dc [2] [InfP Neg1 [2,2] [NodeP Neg1 [[2,2] ++ symbols Map.! 'e']]])


-- vocab_as_MDD = foldr ((.+.) . ezPath . sentenceToPath) bot vocabulary
