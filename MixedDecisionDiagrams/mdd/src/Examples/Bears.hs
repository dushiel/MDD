{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE TupleSections #-}
{-# HLINT ignore "Move brackets to avoid $" #-}
module Examples.Bears where

import qualified Data.Map.Strict as Map
import MDD.Extra.Interface
import MDD.Types
import MDD.Extra.Dot (generateGraphImage, domainNaming, domainNamingC)
import System.Directory (createDirectoryIfMissing, setCurrentDirectory, getCurrentDirectory, renameFile)
import System.FilePath ((</>))




-- The common, albeit oversimplified, survival rhyme for bear encounters is:
-- "If it's brown, lay down; if it's black, fight back; if it's white, say goodnight"
-- take that saying as a toy model to play around with MDDs

-- a naive model, with some assumptions to make it "work":
-- it describes an agent.
-- It has a visual input, an action choice it can make, and determines this based on rules in written language,
-- input gets mapped onto words -> rules onto sentences -> resulting words get mapped onto actions.


-- input visuals (e.g. neural network classifier which decides the most important shape and corresponding color in the current input visual):
--      colors (brown, black, white, blue, red, yellow, green, purple, etc)
--      recognizable_shapes (human-like, tree-like, bear-like, etc)
-- rule based sentences (e.g. provided by humans):
--      sentences are build up from any number of words, which in turn are build up from any number of symbols
--      for this toy model, the rules that can trigger actions consist of 4 words (2 input, 1 connector, 1 action, see explanation below)
-- actions options:
--      once only one action of a predefined list is considered valid, it is chosen automatically
--      predfined list, e.g.: eat, lay-down, pray, fight, etc

-- scene 0 Alice sees no bear, but knows the saying
-- scene 1 Alice sees a black bear and runs.



-- ============================================================================
-- Class [1]: Visual Input (objects of interest, their shape and color)
-- ============================================================================

visual_label :: Path -> Path
visual_label c = P' [(1, Dc1, c)]

-- | Object at priority position i within visual input -> class [1,i]
object_label :: Int -> Path -> Path
object_label i c = visual_label $ P' [(i, Dc1, c)]

-- | Shape attribute of object at priority i -> class [1,i,1]
shape_of :: Int -> Path -> Path
shape_of i c = object_label i $ P' [(1, Neg1, c)]

-- | Color attribute of object at priority i -> class [1,i,2]
color_of :: Int -> Path -> Path
color_of i c = object_label i $ P' [(2, Neg1, c)]

shapes :: Map.Map String Int
shapes = Map.fromList $ zip ["rectangular", "round", "line", "face-like", "bear-like", "big", "small"] [1..]

shape :: Int -> [String] -> MDD
shape i sl = var $ shape_of i $ P'' [shapes !!! "shapes" $ s | s <- sl]

colors :: Map.Map String Int
colors = Map.fromList $ zip ["red", "orange", "yellow", "green", "blue", "purple", "brown", "white", "grey", "black"] [1..]

color :: Int -> [String] -> MDD
color i sl = var $ color_of i $ P'' [colors !!! "colors" $ s | s <- sl]


-- ============================================================================
-- Class [2]: Rules as given in Sentences / Words / Symbols
-- ============================================================================

sentence_label :: Path -> Path
sentence_label c = P' [(2, Dc1, c)]

-- | A word (string) placed at a specific position in a sentence.
-- The non-specified words are inferred to be dc (to be able to combine them with other word_at , as long as those are at different positions),
-- and non-specified symbol position within the word are inferred to be Neg (single determined choice).
word_at :: Int -> String -> MDD
word_at pos "*" = var $ sentence_label $ P' [(pos, Dc1, P'' [0])]  -- wildcard: any word at this position (don't-care)
word_at pos w   = var $ sentence_label $ P' [(pos, Dc1, wordPath w)]

wordPath :: String -> Path
wordPath w = P' [ symbolEntry j c | (j, c) <- zip [1..] w ]
  where
    symbolEntry j '*' = (j, Dc1, P'' [0])   -- wildcard: any symbol at this position (don't-care)
    symbolEntry j c   = (j, Neg1, P'' [symbols !!! ("symbols for word '" ++ w ++ "'") $ c])

-- | End-of-sentence: after n words, remaining word positions are inferred to be Neg empty (to make it a single specified sentence).
-- Marks that no more words follow after position n (in Neg1 context).
-- Until position n, match any (Dc1 Top) words
end_of_sentence :: Int -> MDD
end_of_sentence n = var $
    P' [(2, Neg1, P' [(j, Dc1, P'' [0]) | j <- [1..n]])]

-- Build a complete sentence as a conjunction of words at positions 1..n, and then limit such that no other words follow after n
sentence :: [String] -> MDD
sentence ws = conSet (wordMDDs ++ [endMarker])
  where
    wordMDDs  = [word_at pos w | (pos, w) <- zip [1..] ws]
    endMarker = end_of_sentence (length ws)

-- Possible infinte vocabulary of symbols for a word
symbols :: Map.Map Char Int
symbols = Map.fromList $ zip " abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890,.!?():-" [1..]

-- Wildcard support: "*" as a word in word_at means "any word" (Dc1 Top).
-- '*' as a character in wordPath means "any symbol at that position" (Dc1 Top).

-- ============================================================================
-- Class [3]: Actions, selected to be executed when only one is valid
-- ============================================================================

actions :: Map.Map String Int
actions = Map.fromList $ zip
  ["eat", "lay-down", "pray", "fight", "run"] [1..]

action_label :: Path -> Path
action_label c = P' [(3, Neg1, c)]

action :: String -> MDD
action a = var $ action_label $ P'' [actions !!! "actions" $ a]


-- ============================================================================
-- Bear rhyme: 3 rule-sentences
-- ============================================================================

-- Rule-sentence structure (4 word positions + end-of-sentence):
--   Position 1: Shape word   ("bear")
--   Position 2: Color word   ("brown" / "black" / "white")
--   Position 3: Connector    ("then")
--   Position 4: Action word  ("lay-down" / "fight" / "pray")
--   Position 5+: End-of-sentence (Neg1 empty)

-- "bear brown then lay-down"
rule1 :: MDD
rule1 = sentence ["bear", "brown", "then", "lay-down"]

-- "bear black then fight"
rule2 :: MDD
rule2 = sentence ["bear", "black", "then", "fight"]

-- "bear white then pray"
rule3 :: MDD
rule3 = sentence ["bear", "white", "then", "pray"]

-- All rules combined (disjunction: any of the 3 rules can be active)
rules :: MDD
rules = disSet [rule1, rule2, rule3]


-- ============================================================================
-- Scenes: visual input triggers rule -> action activation
-- ============================================================================

-- The shape+color at visual object position 1 maps to word positions 1+2
-- of the rule-sentence. Word position 4 then activates the corresponding action.

-- "seeing bear-like + brown" implies input words "bear" "brown"
scene_brown_bear :: MDD
scene_brown_bear = (shape 1 ["bear-like"] .*. color 1 ["brown"]) .->. sentence ["bear", "brown", "*", "*"]

-- "seeing bear-like + black" implies input words "bear" "black"
scene_black_bear :: MDD
scene_black_bear = (shape 1 ["bear-like"] .*. color 1 ["black"]) .->. sentence ["bear", "black", "*", "*"]

-- "seeing bear-like + white" implies input words "bear" "white"
scene_white_bear :: MDD
scene_white_bear = (shape 1 ["bear-like"] .*. color 1 ["white"]) .->. sentence ["bear", "white", "*", "*"]

-- Bridge rule: the 4th word of a sentence maps to the corresponding action.
-- For each known action word x: if word4 == x then action x is activated.
-- The action class uses Neg1 context, so if no single action word is determined,
-- the action set is empty (Neg1 [0]).
word4_to_action :: MDD
word4_to_action = conSet
  [ sentence ["*", "*", "*", x] .->. action x
  | x <- Map.keys actions
  ]

-- All scene implications combined (including the word-to-action bridge)
agent_specifics :: MDD
agent_specifics = conSet [scene_brown_bear, scene_black_bear, scene_white_bear, word4_to_action]

-- scene 0: Alice sees no bear, but knows the sayi  ng (rules are loaded)
scene0 :: MDD
scene0 = agent_specifics .*. rules

-- scene 1: Alice sees a black bear
scene1 :: MDD
scene1 = conSet [shape 1 ["bear-like"], color 1 ["black"]]

-- check whether fight is the only valid action
check :: Bool
check = var (P'' [0]) -- Top
        == (scene1 .->. action "fight")


-- ============================================================================
-- Visualization / Naming
-- ============================================================================

-- Class address mapping:
--   [1]       Visual Input
--   [1,i]     Object i
--   [1,i,1]   Shape
--   [1,i,2]   Color
--   [2]       Sentences
--   [2,i]     Word i
--   [2,i,j]   Symbol j
--   [3]       Actions

-- | English ordinal suffix for a number: 1 -> "1st", 2 -> "2nd", etc.
ordinal :: Int -> String
ordinal n
  | n `mod` 100 `elem` [11,12,13] = show n ++ "th"
  | n `mod` 10 == 1               = show n ++ "st"
  | n `mod` 10 == 2               = show n ++ "nd"
  | n `mod` 10 == 3               = show n ++ "rd"
  | otherwise                     = show n ++ "th"

-- Note: all position vectors are prefixed with 0 (the hidden root Dc context level).
namingMap :: Map.Map [Int] String
namingMap = Map.unions
  [ -- Class-level names
    Map.fromList
      [ ([0,1],       "Visual")
      , ([0,1,1],     "Obj_1")
      , ([0,1,1,1],   "Shape")
      , ([0,1,1,2],   "Color")
      , ([0,2],       "Sentences")
      , ([0,3],       "Actions")
      ]
    -- Word-position names: [0,2,w] -> "1st word", "2nd word", ...
  , Map.fromList [ ([0,2,w], ordinal w ++ " word") | w <- [1..4] ]
    -- Symbol-position names: [0,2,w,s] -> "1st symbol", "2nd symbol", ...
  , Map.fromList [ ([0,2,w,s], ordinal s ++ " symbol") | w <- [1..4], s <- [1..8] ]
    -- Leaf-level: shape values at [0,1,1,1]
  , domainNaming [0,1,1,1] shapes
    -- Leaf-level: color values at [0,1,1,2]
  , domainNaming [0,1,1,2] colors
    -- Leaf-level: symbol values at [0,2,w,s] for each word position w and symbol position s
  , Map.unions [ domainNamingC [0,2,w,s] symbols | w <- [1..4], s <- [1..8] ]
    -- Leaf-level: action values at [0,3]
  , domainNaming [0,3] actions
  ]

-- | Generate a named graph image in the current directory
generateNamed :: String -> MDD -> IO ()
generateNamed filename mdd = do
  (success, message, _) <- generateGraphImage mdd True True namingMap
  if success
    then do
      currentDir <- getCurrentDirectory
      let oldDot = currentDir </> "graph.dot"
          oldSvg = currentDir </> "graph.svg"
          newDot = currentDir </> (filename ++ ".dot")
          newSvg = currentDir </> (filename ++ ".svg")
      renameFile oldDot newDot
      renameFile oldSvg newSvg
      putStrLn $ "  Generated " ++ filename ++ ".svg"
    else putStrLn $ "  Error: " ++ message

run :: IO ()
run = do
  originalDir <- getCurrentDirectory
  createDirectoryIfMissing True ("output" </> "bears")
  setCurrentDirectory ("output" </> "bears")

  -- ── Rules ─────────────────────────────────────────────────────
  -- putStrLn "\n=== Rule 1: bear brown then lay-down ==="
  -- generateNamed "rule1_bear_brown_laydown" rule1

  -- putStrLn "\n=== Rule 2: bear black then fight ==="
  -- generateNamed "rule2_bear_black_fight" rule2

  -- putStrLn "\n=== Rule 3: bear white then pray ==="
  -- generateNamed "rule3_bear_white_pray" rule3

  -- putStrLn "\n=== All rules (disjunction) ==="
  -- generateNamed "rules_all" rules

  -- -- ── Word-to-Action bridge ─────────────────────────────────────
  -- putStrLn "\n=== Word4 to Action bridge ==="
  -- generateNamed "word4_to_action" word4_to_action

  -- ── Debug: individual scene implications ─────────────────────
  -- putStrLn "\n=== Debug: scene_brown_bear (visual -> sentence implication) ==="
  -- generateNamed "debug_scene_brown_bear" scene_brown_bear

  -- putStrLn "\n=== Debug: scene_black_bear (visual -> sentence implication) ==="
  -- generateNamed "debug_scene_black_bear" scene_black_bear

  -- putStrLn "\n=== Debug: scene_white_bear (visual -> sentence implication) ==="
  -- generateNamed "debug_scene_white_bear" scene_white_bear

  -- ── Debug: pairwise combinations inside agent_specifics ─────
  putStrLn "\n=== Debug: scene_brown .*. scene_black ==="
  let brown_and_black = scene_brown_bear .*. scene_black_bear
  generateNamed "debug_brown_and_black" brown_and_black

  putStrLn "\n=== Debug: (brown .*. black) .*. scene_white ==="
  let three_scenes = brown_and_black .*. scene_white_bear
  generateNamed "debug_three_scenes" three_scenes

  putStrLn "\n=== Debug: three_scenes .*. word4_to_action ==="
  let agent_specifics_built = three_scenes .*. word4_to_action
  generateNamed "debug_agent_specifics" agent_specifics_built

  -- ── Debug: agent_specifics .*. rules (this is scene0) ───────
  putStrLn "\n=== Scene 0: Alice knows the saying ==="
  let scene0_built = agent_specifics_built .*. rules
  generateNamed "scene0_rules" scene0_built

  -- ── Scene 1 ─────────────────────────────────────────────────
  putStrLn "\n=== Scene 1: Alice sees a black bear ==="
  generateNamed "scene1_black_bear" scene1

  setCurrentDirectory originalDir
  putStrLn "\nDone. Output in output/bears/"



-- | Safe map lookup with descriptive error
(!!!) :: (Ord k, Show k) => Map.Map k v -> String -> k -> v
(!!!) m name k = case Map.lookup k m of
  Just v  -> v
  Nothing -> error $ "Bears.hs: key " ++ show k ++ " not found in '" ++ name
                  ++ "'. Valid keys: " ++ show (Map.keys m)
