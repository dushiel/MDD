{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE TupleSections #-}
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

y = ddOf' $ end_of_word 2
x = ddOf' $ word_to_symbols'' "he"

word_to_symbols :: [Char] -> Form
word_to_symbols sl = And (foldr1 And (map (Var . (uncurry $ path c )) (word_to_symbols' sl))) (end_of_word $ length sl)

word_to_symbols'' :: [Char] -> Form
word_to_symbols'' sl = (foldr1 And (map (Var . (uncurry $ path c )) (word_to_symbols' sl))) 

word_to_symbols' :: [Char] -> [([(Int, InfL)], [Int])] 
word_to_symbols' sl = [([(2 :: Int, Dc1), (s_pos :: Int, Neg1)], [symbols Map.! s]) | (s_pos, s) <- zip [1.. ] sl ]

end_of_word :: Int -> Form
end_of_word i = (Var . construct_path c) (end_of_word' i) `debug` (show $ end_of_word' i) 

end_of_word' :: Int -> Path 
end_of_word' i = P' [(2, Neg1, P' [(j, Dc1, P [0]) | j <- [1..i]])] 


vocabulary :: Form
vocabulary = foldl1 Or (map word_to_symbols ["h", "he"])--- my", "daniel"]) --, "Malvin", "what?", "What a nice day!", ":)", ":-)","what else?", "what even.."])

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
