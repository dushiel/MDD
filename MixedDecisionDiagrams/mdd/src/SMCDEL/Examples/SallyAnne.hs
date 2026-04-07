module SMCDEL.Examples.SallyAnne where

import Data.Map.Strict (fromList)
import qualified Data.Map.Strict as M
import Data.Tagged (Tagged(..), untag)

import Internal.Language
import SMCDEL.Symbolic.K_MDD
import SMCDEL.Symbolic.S5_MDD (boolMddOf)
import MDD.Types (InfL(..), Path(..), MDD)
import MDD.Interface
import MDD.Draw (settings, show_dd)
import MDD.Dot (generateGraphImage)
import System.Directory (createDirectoryIfMissing, setCurrentDirectory, getCurrentDirectory, renameFile)
import System.FilePath ((</>))
import Control.Monad (when)
import Debug.Trace (trace)

-- =============================================================================
-- * Setup
-- =============================================================================

-- Vocabulary
-- Using domains from K_MDD.hs: standardDomain for state law props, eventFactsDomain for events
pp, tt, qq :: Prp
pp = intToPrp standardDomain 1 -- Sally Present
tt = intToPrp standardDomain 2 -- Marble in Basket
qq = intToPrp eventFactsDomain 3 -- Event Variable (for Anne moves marble)

-- Helper for Total Relation (Ignorance)
totalRelMdd :: RelMDD
totalRelMdd = Tagged top

-- Helper for Identity Relation (Distinguishes p)
-- Relation: mv(p) <-> cp(p)
allsameMdd :: [Prp] -> RelMDD
allsameMdd ps =
    let
        mddList = map (\p ->
            let
                -- Create temporary BelStruct for single variable
                tempBls = BlS [p] top (M.empty, Tagged top)
                mv_node = mddOf tempBls (PrpF $ mvP p)
                cp_node = mddOf tempBls (PrpF $ cpP p)
            in mv_node .<->. cp_node
            ) ps
    in Tagged (conSet mddList)

-- Helper for Copy Relation (Copies p's value)
cpRelMdd :: Form -> RelMDD
cpRelMdd f =
    let
        -- Evaluate f in Target (cp)
        -- To do this cleanly without a BelStruct, we assume f is simple BDD
        -- But here we can just construct it.
        -- f is likely simple logic.
        -- If f is "Neg q", we want Rel = (-. cp_q)
        -- We construct a temporary structure to parse f
        tempStruct = BlS [pp,tt,qq] top (M.empty, Tagged top)
        node = mddOf tempStruct f
        -- This node is on standard vars. We need to shift to cp.
        -- K_MDD.cpMdd does this.
        rel = untag $ cpMdd [pp,tt,qq] node
    in Tagged rel

-- =============================================================================
-- * Initial State
-- =============================================================================

sallyInit :: BelScene
sallyInit = (BlS vocab law obs, actual)
  where
    vocab  = [pp, tt]
    -- Law: It is publicly known that Sally is present (pp) and Marble NOT in basket (She hasn't put it in yet).
    law    = boolMddOf (Conj [PrpF pp, Neg (PrpF tt)])
    -- Agent indices: "Anne" -> 0, "Sally" -> 1
    obs    = joinRelations [ ("Anne", 0, totalRelMdd), ("Sally", 1, totalRelMdd) ]
    -- Actual: pp, not tt (inferred in neg1, domain [0,0]), not any event (neg1 context in domain [0,1])
    actual = var (P' [(0, Neg1, P' [(0, Neg1, P'' [1]), (1, Neg1, P'' [0])])])

-- =============================================================================
-- * Actions
-- =============================================================================

-- 1. Sally puts marble in basket
-- Action: tt := Top. Both see it.
sallyPutsMarble :: Event
sallyPutsMarble =
    let
        trf = Trf
                [] -- No new event vars needed (public assignment)
                Top -- Law
                (fromList [(tt, Top)]) -- Assignment: tt becomes True
                (joinRelations [("Anne", 0, totalRelMdd), ("Sally", 1, totalRelMdd)]) -- Everyone sees everything (Identity on event)
                -- Note: totalRelMdd is just Top.
                -- Since there are no addprops, relations over empty set are just Top.
                -- Agent indices must match sallyInit: "Anne" -> 0, "Sally" -> 1
    in (trf, Top)

-- 2. Sally leaves
-- Action: pp := Bot. Both see it.
sallyLeaves :: Event
sallyLeaves =
    let
        trf = Trf
                []
                Top
                (fromList [(pp, Bot)]) -- Assignment: pp becomes False
                (joinRelations [("Anne", 0, totalRelMdd), ("Sally", 1, totalRelMdd)])
                -- Agent indices must match sallyInit: "Anne" -> 0, "Sally" -> 1
    in (trf, Top)

-- 3. Anne puts marble in box (Moves it)
-- This is the tricky one.
-- Event q: Marble moves (tt := False). Anne sees q. Sally sees "not q".
-- Event not q: Nothing happens.
-- We model this with 'qq'.
anneMovesMarble :: Event
anneMovesMarble =
    let
        -- Assignments depend on qq
        -- if qq then tt := Bot (Moved)
        -- if not qq then tt := tt (No change)
        -- Logic: tt <-> (not qq AND tt_old) OR (qq AND False)
        -- Simplified: tt := (not qq -> tt) & (qq -> Bot)  (From BDD version)
        assignTT = Conj [Impl (Neg (PrpF qq)) (PrpF tt), Impl (PrpF qq) Bot]

        trf = Trf
                [qq] -- New event var
                Top  -- Law
                (M.fromList [(tt, assignTT)])
                (joinRelations [
                    ("Anne", 0, allsameMdd [qq]), -- Anne distinguishes q (sees if it moved)
                    ("Sally", 1, cpRelMdd (Neg (PrpF qq))) -- Sally only considers worlds where q is False (didn't move)
                ])
                -- Agent indices must match sallyInit: "Anne" -> 0, "Sally" -> 1

        -- The actual event that happens is q (marble moved)
        facts = PrpF qq
    in (trf, facts)

-- 4. Sally comes back
-- Action: pp := Top. Both see it.
sallyReturns :: Event
sallyReturns =
    let
        trf = Trf
                []
                Top
                (fromList [(pp, Top)])
                (joinRelations [("Anne", 0, totalRelMdd), ("Sally", 1, totalRelMdd)])
                -- Agent indices must match sallyInit: "Anne" -> 0, "Sally" -> 1
    in (trf, Top)


-- =============================================================================
-- * Execution
-- =============================================================================

runSallyAnne :: IO ()
runSallyAnne = do
    putStrLn "=== Sally-Anne MDD Simulation ==="

    -- 0. Init
    let scene0 = sallyInit
    putStrLn "\n[0] Initial: Sally present, No marble."
    -- printStatus "scene0" scene0

    -- 1. Sally puts marble
    let scene1 = unsafeUpdate scene0 sallyPutsMarble
    putStrLn "\n[1] Action: Sally puts marble in basket."
    -- printStatus "scene1" scene1

    -- 2. Sally leaves
    let scene2 = unsafeUpdate scene1 sallyLeaves
    putStrLn "\n[2] Action: Sally leaves the room."
    -- printStatus "scene2" scene2

    -- 3. Anne moves marble
    let scene3 = unsafeUpdate scene2 anneMovesMarble
    putStrLn "\n[3] Action: Anne moves marble to box (Sally doesn't see)."
    printStatus "scene3" scene3

    -- error "stop"
    -- 4. Sally returns
    let scene4 = unsafeUpdate scene3 sallyReturns
    putStrLn "\n[4] Action: Sally returns."
    printStatus "scene4" scene4

    putStrLn "\n--- Final Belief Check ---"

    -- Does Anne know marble is NOT in basket? (True)
    let anneKnowsGone = evalViaMdd scene4 (K "Anne" (Neg (PrpF tt)))
    putStrLn $ "Does Anne know marble is gone? " ++ show anneKnowsGone ++ " (Expected: True)"

    -- Does Sally know marble is NOT in basket? (False - she thinks it's there)
    let sallyKnowsGone = evalViaMdd scene4 (K "Sally" (Neg (PrpF tt)))
    putStrLn $ "Does Sally know marble is gone? " ++ show sallyKnowsGone ++ " (Expected: False)"

    -- Does Sally believe marble IS in basket? (True)
    let sallyBelievesHere = evalViaMdd scene4 (K "Sally" (PrpF tt))
    putStrLn $ "Does Sally believe marble is still in basket? " ++ show sallyBelievesHere ++ " (Expected: True)"

-- | Helper function to generate a dot graph image with a custom filename
generateGraphImageNamed :: MDD -> String -> IO (Bool, String)
generateGraphImageNamed mdd filename = do
    (success, message, _) <- generateGraphImage mdd True False M.empty
    if success
        then do
            -- Rename the generated files to the custom filename
            currentDir <- getCurrentDirectory
            let oldDot = currentDir </> "graph.dot"
                oldSvg = currentDir </> "graph.svg"
                newDot = currentDir </> (filename ++ ".dot")
                newSvg = currentDir </> (filename ++ ".svg")
            renameFile oldDot newDot
            renameFile oldSvg newSvg
            return (True, "Generated " ++ filename ++ ".svg")
        else return (False, message)

printStatus :: String -> BelScene -> IO ()
printStatus folderName scn@(bls@(BlS _ law obs), actual) = do
    let p = evalViaMdd scn (PrpF pp)
    let t = evalViaMdd scn (PrpF tt)
    putStrLn $ "    Status: Sally Present=" ++ show p ++ ", Marble in Basket=" ++ show t

    -- Create folder and generate images
    originalDir <- getCurrentDirectory
    createDirectoryIfMissing True folderName
    setCurrentDirectory folderName

    -- Generate image for actual state
    (success1, msg1) <- generateGraphImageNamed actual "actual_state"
    when success1 $ putStrLn $ "    " ++ msg1

    -- Generate image for state law
    (success2, msg2) <- generateGraphImageNamed law "state_law"
    when success2 $ putStrLn $ "    " ++ msg2

    -- Generate images for all observable laws
    mapM_ (\(agent, i) -> do
        let relMdd = restrict (agentPos i) True (untag (snd obs))
            filename = "obs_law_" ++ agent
        (success, msg) <- generateGraphImageNamed relMdd filename
        when success $ putStrLn $ "    " ++ msg
        ) (M.toList (fst obs))

    -- Restore original directory
    setCurrentDirectory originalDir