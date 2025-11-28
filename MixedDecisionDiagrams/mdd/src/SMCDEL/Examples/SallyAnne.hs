module SMCDEL.Examples.SallyAnne where

import Data.Map.Strict (fromList)
import qualified Data.Map.Strict as M

import Internal.Language
import SMCDEL.Symbolic.K_MDD -- Importing the MDD K implementation
import SMCDEL.Symbolic.S5_MDD (boolMddOf) -- Helper to make MDDs from formulas
import MDD
import MDDi (top, bot, var)
import Data.Tagged (Tagged(..))
import DrawMDD
import Debug.Trace (trace)

-- =============================================================================
-- * Setup: Vocabulary and Helpers
-- =============================================================================

-- We use a simpler domain setup for MDDs (Default Domain 0)
-- pp: Sally is Present
-- tt: Marble is in the Basket
domain :: [(Int, InfL)]
domain = [(0, Dc1)]

statedomain = [(0, Neg1)]

pp, tt :: Prp
pp = intToPrp domain 1 -- Variable 1
tt = intToPrp domain 2 -- Variable 2



-- Helper to create a total relation (Ignorance)
-- In K_MDD, a Total relation means the agent connects every world to every other world.
-- Since the Logic is S5-like for the start, we can just use Top (connect everything).
totalRelMdd :: [Prp] -> RelMDD
totalRelMdd vocab =
    -- We construct a relation that allows any transition between source (mv) and target (cp)
    -- This effectively is just "Top" in the relational domain.
    Tagged top

-- =============================================================================
-- * The Scenario
-- =============================================================================

-- 1. Initial State:
-- Law: Top (Anything is possible: Marble might be there or not)
-- Actual World: pp is True, tt is True (Sally present, Marble in Basket)
-- Knowledge: Both agents know nothing specific (Relations are Top)
sallyInitK :: BelScene
sallyInitK = (BlS vocab law obs, actual)
  where
    vocab  = [pp, tt]
    law    = boolMddOf Top
    -- Both agents consider all worlds possible (Ignorance about pp and tt)
    obs    = fromList [ ("Sally", totalRelMdd vocab), ("Anne", totalRelMdd vocab) ]
    -- In the actual world, both are True.
    s = var (P' [(0, Neg1, P'' [1, 2])])
    actual = trace ("statelaw: " ++ show_dd settings (fst s) (snd s)) s

-- 2. The Event: Anne Peeks
-- Anne privately learns that the marble is in the basket (tt).
-- This is a Private Announcement to Anne of formula "tt".
-- Note: 'Announce' in K_MDD takes [Agent], Formula, and the "Then" clause is handled by updates.
annePeeks :: BelScene
annePeeks =
    let (bls, s) = sallyInitK
        -- We update the Belief Structure with the private announcement
        -- The formula announced is (PrpF tt)
        -- The group receiving it is ["Anne"]
        newBls = announce bls ["Anne"] (PrpF tt)
    in (newBls, s)

-- =============================================================================
-- * Testing / Execution
-- =============================================================================

-- | Run this in GHCi to test the logic
runSallyMDD :: IO ()
runSallyMDD = do
    putStrLn "=== Sally-Anne MDD Test (The 'Peeking' Variant) ==="

    -- 1. Check Initial State
    putStrLn "\n[Step 1] Initial State: Marble is in basket (tt), but nobody knows it."
    let (initBls, initState) = sallyInitK

    -- Does Anne know tt?
    let anneKnowsInit = evalViaMdd sallyInitK (K "Anne" (PrpF tt))
    putStrLn $ "  Does Anne know tt? " ++ show anneKnowsInit

    -- Does Sally know tt?
    let sallyKnowsInit = evalViaMdd sallyInitK (K "Sally" (PrpF tt))
    putStrLn $ "  Does Sally know tt? " ++ show sallyKnowsInit

    -- 2. Perform Update
    putStrLn "\n[Step 2] Event: Anne privately peeks into the basket (Private Announcement of tt)."
    let finalScene = annePeeks

    -- 3. Check Final Knowledge
    putStrLn "\n[Step 3] Final State Checks:"

    -- Anne should now know tt
    let anneKnows = evalViaMdd finalScene (K "Anne" (PrpF tt))
    putStrLn $ "  Does Anne know tt? " ++ show anneKnows ++ " (Expected: True)"

    -- Sally should NOT know tt (she didn't see)
    let sallyKnows = evalViaMdd finalScene (K "Sally" (PrpF tt))
    putStrLn $ "  Does Sally know tt? " ++ show sallyKnows ++ " (Expected: False)"

    -- Does Sally know that Anne knows? (Should be False, it was private)
    let sallyKnowsAnneKnows = evalViaMdd finalScene (K "Sally" (K "Anne" (PrpF tt)))
    putStrLn $ "  Does Sally know that Anne knows? " ++ show sallyKnowsAnneKnows ++ " (Expected: False)"

    if anneKnows && not sallyKnows && not sallyKnowsAnneKnows
        then putStrLn "\n[SUCCESS] The Private Announcement logic is working correctly."
        else putStrLn "\n[FAILURE] The logic did not behave as expected."