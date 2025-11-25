module SMCDEL.Examples.MuddyChildren where

import Data.List
import Data.Map.Strict (fromList)

import SMCDEL.Internal.Help (seteq)
import Internal.Language
import SMCDEL.Symbolic.S5_MDD

-- | Initialize a Muddy Children scene with n children, m of whom are muddy.
mudScnInit :: Int -> Int -> KnowScene
mudScnInit n m = (KnS vocab law obs, actual) where
  -- Use intToPrp with empty domain [] as established in Phase 2
  vocab  = [intToPrp [] i | i <- [1..n]]
  law    = boolMddOf Top
  -- Observables: Agent i sees all variables except intToPrp [] i
  obs    = [ (show i, delete (intToPrp [] i) vocab) | i <- [1..n] ]
  -- Actual world: The first m children are muddy
  actual = [intToPrp [] i | i <- [1..m]]


myMudScnInit :: KnowScene
myMudScnInit = mudScnInit 3 3

-- | Agent i knows whether they are muddy
knows :: Int -> Form
knows i = Kw (show i) (PrpF $ intToPrp [] i)

-- | "Nobody knows whether they are muddy"
nobodyknows :: Int -> Form
nobodyknows n = Conj [ Neg $ knows i | i <- [1..n] ]

-- | Father says: "At least one child is muddy"
father :: Int -> Form
father n = Disj [ PrpF (intToPrp [] i) | i <- [1..n] ]

-- | Example Scenes
mudScn0 :: KnowScene
mudScn0 = update myMudScnInit (father 3)

mudScn1 :: KnowScene
mudScn1 = update mudScn0 (nobodyknows 3)

mudScn2 :: KnowScene
mudScn2 = update mudScn1 (nobodyknows 3)

-- | Run the simulation in GHCi.
-- n: Total children
-- m: Muddy children
-- Example usage: runMuddy 10 5
runMuddy :: Int -> Int -> IO ()
runMuddy n m = do
  putStrLn $ "Initializing puzzle with " ++ show n ++ " children, " ++ show m ++ " muddy."

  -- 1. Initialize State
  let startState = mudScnInit n m

  -- 2. Father speaks ("At least one is muddy")
  let afterFather = update startState (father n)
  putStrLn "Round 0: Father announces 'At least one child is muddy'."

  -- 3. Loop rounds asking "Do you know?"
  loop 1 afterFather

  where
    loop :: Int -> KnowScene -> IO ()
    loop round currentScene = do
      -- Check if any child knows they are muddy in the current scene
      -- We check 'knows i' for every agent i
      let knowledgeCheck = [ (i, isTrue currentScene (knows i)) | i <- [1..n] ]
      let someoneKnows = any snd knowledgeCheck

      if someoneKnows
        then do
          putStrLn $ "SUCCESS: In Round " ++ show round ++ ", the following children know their status:"
          print [ i | (i, known) <- knowledgeCheck, known ]
        else do
          putStrLn $ "Round " ++ show round ++ ": Nobody knows. Announcing 'Nobody knows'..."
          -- Update the scene with the fact that nobody knew
          let nextScene = update currentScene (nobodyknows n)
          loop (round + 1) nextScene