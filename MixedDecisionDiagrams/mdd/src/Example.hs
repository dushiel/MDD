{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE TupleSections #-}
{-# HLINT ignore "Move brackets to avoid $" #-}
module Example where

import qualified Data.Map.Strict as Map
import MDDi
import MDD
-- import Internal.Language
import DrawMDD
import qualified Data.HashMap.Lazy as HashMap



-- these will automatically be constrocted as Ordinals when transforming them to Dd's
-- labelClass = [2]
-- conceptLabels = Map.fromList $ zip [1 ..] (map (\x -> labelClass ++ [x]) [1..])


-- Implicit ordinals, responsibility of the use for correct formatting
symbols :: Map.Map Char Int
symbols = Map.fromList $ zip " abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890,.!?():-" [0..]

word :: [Char] -> Form
word sl = Var . path c $ word_label $ P' [
    if s == '*'
        then (s_pos, Dc1, P [symbols Map.! ' '])
        else (s_pos, Neg1, P [symbols Map.! s])
     | (s_pos, s) <- zip [1.. ] sl]

word_label :: Path -> Path
word_label c = P' [(2, Neg1, c)]

end_of_word :: Int -> Form
end_of_word i = Var . path c $ P' [(2, Neg1, P' [(j, Dc1, P [0]) | j <- [1..i]])]

vocabulary :: Form
vocabulary = foldl1 Or (map word ["dani", "daniel", "run"]) --, "Malvin", "what?", "What a nice day!", ":)", ":-)","what else?", "what even.."])

shape_label :: Path -> Path
shape_label c = P' [(3, Dc1, c)]

shapes :: Map.Map String Int
shapes = Map.fromList $ zip ["rectangular", "round", "line", "face-like", "bear-like", "big", "small"] [1..]

shape :: [String] -> Form
shape sl = Var . path c $ shape_label $ P [shapes Map.! s | s <- sl]


color_label :: Path -> Path
color_label c = P' [(4, Dc1, c)]

colors :: Map.Map String Int
-- dimensions would be the three cone value activations? cluster in which can define colors. once recognizable for the understanding they are given a label below.
colors = Map.fromList $ zip ["red", "orange", "yellow", "green", "blue", "purple", "white", "grey", "black"] [1..]

color :: [String] -> Form
color sl = Var . path c $ color_label $ P [colors Map.! s | s <- sl]


feeling_label :: Path -> Path
feeling_label c = P' [(5, Dc1, c)]

feelings :: Map.Map String Int
-- dimensions here would be based on neuro science findings, what are core mechanisms that can influence us in such a way that we are open to conceptualizing them
feelings = Map.fromList $ zip ["danger", "safety", "interesse", "boredom", "friendship", "distance", "admiration-love", "romantic-love", "in-control", "lost", "hot", "cold"] [1..]

feeling :: [String] -> Form
feeling sl = Var . path c $ feeling_label $ P [feelings Map.! s | s <- sl]

bear_fear :: Form
bear_fear = Impl (shape ["bear-like"]) (And (feeling ["danger"]) (word "run")) --
-- generateAndShow_c


-- senToDd = ezPath . sentenceToPath

-- sentenceToPath :: String -> EasyPath
-- -- e.g. (Dc, 3, [(Neg1, 1, [ (Neg1, [1,2, -3]) ]) ])
-- sentenceToPath s = InfP Neg1 [2] [InfP Neg1 [2,x] [NodeP Neg1 ([[2,x] ++ symbols Map.! y | ' ' /= y]) ] | (x, y) <- zip [1..] s ]

-- eFilter v = v .*. ezPath (InfP Dc [2] [InfP Neg1 [2,x] [NodeP Neg1 [[2,x] ++ symbols Map.! 'e']] | x <- [1 .. 50]])
-- eFilter2 v = v .*. ezPath (InfP Dc [2] [InfP Neg1 [2,2] [NodeP Neg1 [[2,2] ++ symbols Map.! 'e']]])


-- vocab_as_MDD = foldr ((.+.) . ezPath . sentenceToPath) bot vocabulary

-- -- [[y], x] -> [[y,x]]
-- -- todo use Data.Bimap
-- symbolsR :: [(Ordinal, String)]
-- symbolsR = zip (map (Order . (++) [2]) $ concatMap (\x -> map ((\z -> z ++ [x]) . (\y -> [y])) [1..50])  [0..])
--     (concatMap (replicate 50 . (\x -> [x])) "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890,.!?():-")

-- symbolPositionsLabelR :: [(Ordinal, String)]
-- symbolPositionsLabelR = zip (map (\x -> Order $ labelClass ++ [x]) [1..]) (map (\x -> "pos" ++ show x)  [1..50])


-- completeRmap :: Map.Map Ordinal String
-- completeRmap = Map.fromList $ symbolsR ++ symbolPositionsLabelR ++ [(Order labelClass, "Labels")]
{-}

-- experiences of concepts are a set of specified evaluations for properties in a Dc context
-- thus a single concept maps to a unique 1/0 set.
experienceClass :: Class
experienceClass = Order [1]

colors = Map.fromList [("green", Order [1,1,1]),("yellow", Order [1,1,2]),("blue", Order [1,1,3])]
shapes = Map.fromList [("round", Order [1,2,1]),("square", Order [1,2,2]),("big", Order [1,2,3])]
feeling = Map.fromList [("friendly", Order [1,3,1]),("dangerous", Order [1,3,2]),("interesting", Order [1,3,3])]

-- L concepts L color L red
-- L concepts L senses (1) / imagination (-1)
-- L concepts L time / timeless L future / present / past
-- L concepts L numbers
-- L concepts L physical (instance, somewhere a single path through a concept??) / conceptual ()


-- todo concept to path map
-- look up label in mapping, if nested look up net one
--

-- We can be aware of (have a focus on) a finite amount of concepts at once
-- the propositions are identities of unique concepts (by assumption that we can discern 1 concept from another)
-- the leaf nodes tell us whether they are in our focus or not

-- working memory
focusField = Map.fromList $ zip [1 ..] (map (\x -> Order $ [2,0] ++ [x]) [1..])
-- the powerset of the powerset of all properies maps to all concepts
-- (all possible sets of = the combination set of) (all states = the powerset of all properies :BDD)




-- The researchers can also label their concepts in order to communicate them. we asume they magically agree on what label belongs to what concept (by grounding process or whatever)
-- a 1 evaluation for a proposition represents a symbol present, a 0 represents an empty xzspace.
-- the 1 set represents a set of labels with different white space configuration.
labelClass :: Class
labelClass = Order [2]

symbols = Map.fromList $ zip ['a'..] (map (\x -> Order $ [2,0] ++ [x]) [1..])

conceptLabels = Map.fromList $ zip [1 ..] (map (\x -> Order $ [3,0] ++ [x]) [1..])

-- There are an infinite amount of symbols possible,
-- The 1 set describes all possible symbols per label symbolposition, thus it is possible to describe sets of labels with the two domains combined
-- The all negative evaluation corresponds to an empty space, and as such we have to add the rule that the empty spaces lead to Bot on all 1 positions
-- also add the "rule" that all 0 positions are Dc subdomains.

-- The label subdomain is needed as it also acts like a finite focus field/mask we apply, to ensure finite length tokens/sentences, just like the concept awareness mask.









--Order 0: world with agents (B + Z)
-- friends share information, distributed knowledge

type Class = Ordinal

agentClass :: Class
agentClass = Order [0]

agents = Map.fromList $ [("alice", Order [1]),("bob", Order [2])] ++ [("ag#" ++ show x, Order [x + 2]) | x <- [1..]]

knows :: String -> Form

-}

word_collection_label :: Path -> Path
word_collection_label c = P' [(2, Dc1, c)]

words_with_prefix :: [Char] -> Form
words_with_prefix sl = Var . path c $ word_label $ P' [(s_pos, Dc1, P [symbols Map.! s]) | (s_pos, s) <- zip [1.. ] sl]

test_word :: [Char] -> Form
test_word sl = (Var . path c $ word_label $ P' [(s_pos, Neg1, P [symbols Map.! s]) | (s_pos, s) <- zip [1.. ] sl]) `And` (end_of_word $ length sl)


test_example :: IO ()
test_example = do
    mapM_ print ([show $ snd x | x <- zip results [(0 :: Int) .. ], not $ fst x])
    where
        results = [
            -- (snd $ ddOf' (word "was")) == (snd $ ddOf' (test_word "was")) `debug5` "######## test nr 1"
            -- , (snd $ ddOf' (word "bit")) == (snd $ ddOf' (test_word "bit")) `debug5` "######## test nr 2"
            -- , (snd $ ddOf' ((word "abc" `Or` word "abd") `And` (word "ab" `Or` word "abd"))) == (snd $ ddOf' (word "abd"))`debug5` "######## test nr 3"
            (snd $ ddOf' ((words_with_prefix "abc" `Or` words_with_prefix "abd") `And` (words_with_prefix "ab" `Or` words_with_prefix "abd"))) == (snd $ ddOf' (words_with_prefix "abd")) `debug5` "######## test nr 4"
            ]





--Order 1: B properties
-- yellow
-- green
-- blue
-- brown

-- shape class of properties
-- round
-- square
-- big
-- small

-- emotional response class of properties
-- feels friendly!
-- feels like danger!
-- feels interesting!
-- feels dull!

--2: Z in a existence realm context (mass/essence)
-- that which is it, and that which is not it.
-- when structured/ordered:
-- 1 class for each spatial/time dimension
-- where each object has a volume in that dimension
-- when unordered we can only capture relative membership
-- e.g. we get a frame of the object and its parts and its surroundings, these weels are parts of this car

--3: Z word to refer to the properties or the referentials
-- 1 for each used symbol, unlimited length, 0 for each not-used symbol.
