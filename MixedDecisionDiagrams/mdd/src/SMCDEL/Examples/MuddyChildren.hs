module SMCDEL.Examples.MuddyChildren where

import Data.List
import Data.Map.Strict (fromList)
import qualified Data.Map.Strict as M

import SMCDEL.Internal.Help (seteq)
import SMCDEL.Internal.Language
import SMCDEL.Symbolic.S5_MDD
import qualified SMCDEL.Symbolic.K_MDD as K
import Data.Tagged (Tagged(..), untag)
import MDD.Types hiding (Neg)
import MDD.Extra.Interface
import MDD.Extra.Draw (settings, show_dd, drawTree3, debug)

-- | The default domain index for variables in this puzzle.
vocabAsPropsDomain :: [(Int, InfL)]
vocabAsPropsDomain = [(0, Dc1)]


-- | Initialize a Muddy Children scene with n children, m of whom are muddy.
mudScnInit :: Int -> Int -> KnowScene
mudScnInit n m = (KnS vocab law obs, actual) where
  vocab  = [intToPrp vocabAsPropsDomain i | i <- [1..n]]
  law    = boolMddOf Top
  obs    = [ (show i, delete (intToPrp vocabAsPropsDomain i) vocab) | i <- [1..n] ]
  actual = var (P' [(0, Neg1, P'' [1..m])])


myMudScnInit :: KnowScene
myMudScnInit = mudScnInit 3 3

-- | Agent i knows whether they are muddy
knows :: Int -> Form
knows i = Kw (show i) (PrpF $ intToPrp vocabAsPropsDomain i)

-- | "Nobody knows whether they are muddy"
nobodyknows :: Int -> Form
nobodyknows n = Conj [ Neg $ knows i | i <- [1..n] ]

-- | Father says: "At least one child is muddy"
father :: Int -> Form
father n = Disj [ PrpF (intToPrp vocabAsPropsDomain i) | i <- [1..n] ]

-- | Example Scenes
mudScn0 :: KnowScene
mudScn0 = update myMudScnInit (father 3)

mudScn1 :: KnowScene
mudScn1 = update mudScn0 (nobodyknows 3)

mudScn2 :: KnowScene
mudScn2 = update mudScn1 (nobodyknows 3)

runMuddy :: Int -> Int -> IO ()
runMuddy n m = do
  putStrLn $ "Initializing puzzle with " ++ show n ++ " children, " ++ show m ++ " muddy."

  let startState = mudScnInit n m

  let afterFather@(KnS _ law _, _) = update startState (father n)
  putStrLn "Round 0: Father announces 'At least one child is muddy'."

  loop 1 afterFather

  where
    loop :: Int -> KnowScene -> IO ()
    loop round currentScene = do
      let knowledgeCheck = [ (i, isTrue currentScene (knows i)) | i <- [1..n] ]
      let someoneKnows = any snd knowledgeCheck

      if someoneKnows
        then do
          putStrLn $ "SUCCESS: In Round " ++ show round ++ ", the following children know their status:"
          print [ i | (i, known) <- knowledgeCheck, known ]
        else do
          putStrLn $ "Round " ++ show round ++ ": Nobody knows. Announcing 'Nobody knows'..."
          let nextScene = update currentScene (nobodyknows n)
          loop (round + 1) nextScene

-- =============================================================================
-- * Phase 3: K-Logic Implementation
-- =============================================================================

-- | Helper to create an explicit equivalence relation MDD for K-logic.
makeEquivRel :: [Prp] -> [Prp] -> K.RelMDD
makeEquivRel vocab obsVars = Tagged final_mdd
  where
    -- Start with Top in the relational context
    topRel = top
    combine mdd_acc p =
        let
             mdd_std = boolMddOf (PrpF p)

             tagged_mv = K.mvMdd vocab mdd_std
             Tagged mdd_mv = tagged_mv

             tagged_cp = K.cpMdd vocab mdd_std
             Tagged mdd_cp = tagged_cp


             mdd_eq = mdd_mv .<->. mdd_cp
             mdd_res = mdd_acc .*. mdd_eq

        in mdd_res

    final_mdd = foldl combine topRel obsVars

-- | Initialize K-logic Muddy Children Scene
mudScnInitK :: Int -> Int -> K.BelScene
mudScnInitK n m = (K.BlS vocab law obs_pair, actual)
  where
    vocab  = [intToPrp vocabAsPropsDomain i | i <- [1..n]]
    law = top
    actual = var (P' [(0, Neg1, P'' [1..m])])
    buildObs i =
        let
            my_obs_vars = sort $ delete (intToPrp vocabAsPropsDomain i) vocab
            rel = makeEquivRel vocab my_obs_vars
            agentIndex = i - 1  -- Use 0-based indices: child 1 -> index 0, child 2 -> index 1, etc.
        in (show i, agentIndex, rel)
    obs_list = map buildObs [1..n]
    obs_pair = K.joinRelations obs_list


-- | Run the simulation in GHCi using K-Logic structures.
runMuddyK :: Int -> Int -> IO ()
runMuddyK n m = do
  putStrLn $ "Initializing K-puzzle with " ++ show n ++ " children, " ++ show m ++ " muddy."

  -- 1. Initialize K-State
  let startState = mudScnInitK n m

  -- 2. Father speaks
  let afterFather@(K.BlS _ statelaw obs_laws, _) = unsafeUpdate startState (father n)
  putStrLn "Round 0: Father announces 'At least one child is muddy'."

  putStrLn "State Law first one:"
  drawTree3 statelaw


  -- putStrLn "Observation Laws:"
  -- mapM_ (\(agent, rel) -> do
  --     putStrLn $ "Agent " ++ agent
  --     drawTree3 (untag rel)
  --   ) (M.toList obs_laws)
  putStrLn "==================================="

  -- 3. Loop
  loopK 1 afterFather

  where
    loopK :: Int -> K.BelScene -> IO ()
    loopK round currentScene = do
        let knowledgeCheck = [ (i, K.evalViaMdd currentScene (knows i)) | i <- [1..n] ]
        let someoneKnows = any snd knowledgeCheck

        if someoneKnows
            then do
                putStrLn $ "SUCCESS: In Round " ++ show round ++ ", the following children know their status:"
                print [ i | (i, known) <- knowledgeCheck, known ]
            else do
                putStrLn $ "Round " ++ show round ++ ": Nobody knows. Announcing 'Nobody knows'..."
                let nextScene@(K.BlS _ law obs_laws, _) = unsafeUpdate currentScene (nobodyknows n)

                putStrLn "State Law: ---------------- "
                drawTree3 law

                -- putStrLn "Observation Laws:"
                -- mapM_ (\(agent, rel) -> do
                --     putStrLn $ "Agent " ++ agent
                --     drawTree3 (untag rel)
                --   ) (M.toList obs_laws)

                -- error "stop"
                loopK (round + 1) nextScene