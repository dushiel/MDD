module SMCDEL.Examples.SallyAnne where

import Data.Map.Strict (fromList)
import qualified Data.Map.Strict as M
import Data.Tagged (untag)

import SMCDEL.Internal.Language
import SMCDEL.Symbolic.K_MDD
import SMCDEL.Symbolic.S5_MDD (boolMddOf)
import MDD.Types (InfL(..), Path(..), MDD)
import MDD.Extra.Interface
import MDD.Extra.Dot (generateGraphImage)
import System.Directory (createDirectoryIfMissing, setCurrentDirectory, getCurrentDirectory, renameFile)
import System.FilePath ((</>))
import Control.Monad (when)


-- Vocabulary:
-- Using domains from K_MDD.hs: standardDomain for state law props, eventFactsDomain for events
pp, tt, qq :: Prp
pp = intToPrp standardDomain 1 -- Sally Present
tt = intToPrp standardDomain 2 -- Marble in Basket
qq = intToPrp eventFactsDomain 3 -- Event Variable (for Anne moves marble)

sallyInit :: BelScene
sallyInit = (BlS vocab law obs, actual)
  where
    vocab  = [pp, tt]
    -- Law: It is publicly known that Sally is present (pp) and Marble NOT in basket (She hasn't put it in yet) and that no special events have taken place.
    law    = boolMddOf (Conj [PrpF pp, Neg (PrpF tt)
        , PrpF $ intToPrp eventFactsDomainNeg 0
        ])
    -- Agent indices:
    obs    = joinRelations [ ("Anne", 2, totalRelMdd), ("Sally", 1, totalRelMdd) ]
    -- Actual: pp, not tt (inferred in neg1, domain [0,0]), not any event (neg1 context in domain [0,1])
    actual = var (P' [(0, Neg1, P' [(1, Neg1, P'' [1]), (0, Neg1, P'' [0])])])


-- 1. Sally puts marble in basket
-- Action: tt := Top. Both see it.
sallyPutsMarble :: Event
sallyPutsMarble =
    let
        trf = Trf
                [] -- No new event vars needed (public assignment)
                Top
                (fromList [(tt, Top)]) -- Assignment: tt becomes True
                (joinRelations [("Anne", 2, totalRelMdd), ("Sally", 1, totalRelMdd)]) -- Everyone sees everything (Identity on event)
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
                (joinRelations [("Anne", 2, totalRelMdd), ("Sally", 1, totalRelMdd)])
    in (trf, Top)

-- 3. Anne puts marble in box (Moves it)
-- Event q: Marble moves (tt := False). Anne sees q. Sally sees "not q".
-- Event not q: Nothing happens.
anneMovesMarble :: Event
anneMovesMarble =
    let
        assignTT = Conj [Impl (Neg (PrpF qq)) (PrpF tt), Impl (PrpF qq) Bot]

        trf = Trf
                [qq] -- New event var
                Top
                (M.fromList [(tt, assignTT)])
                (joinRelations [
                    ("Anne", 2, allsameMdd [qq]), -- Anne distinguishes q (sees if it moved)
                    ("Sally", 1, cpRelMdd [pp,tt,qq] (Neg (PrpF qq))) -- Sally only considers worlds where q is False (didn't move)
                ])

        -- The actual event that happens is q (marble moved)
        facts = PrpF qq
    in (trf, facts)

-- 4. Sally comes back
sallyReturns :: Event
sallyReturns =
    let
        trf = Trf
                []
                Top
                (fromList [(pp, Top)])
                (joinRelations [("Anne", 2, totalRelMdd), ("Sally", 1, totalRelMdd)])
    in (trf, Top)



runSallyAnne :: Bool -> IO ()
runSallyAnne generateOutput = do

    let scene0 = sallyInit
    putStrLn "\n[0] Initial: Sally present, No marble."
    when generateOutput $ printStatus "scene0" scene0

    let scene1 = unsafeUpdate scene0 sallyPutsMarble
    putStrLn "\n[1] Action: Sally puts marble in basket."
    when generateOutput $ printStatus "scene1" scene1

    let scene2 = unsafeUpdate scene1 sallyLeaves
    putStrLn "\n[2] Action: Sally leaves the room."
    when generateOutput $ printStatus "scene2" scene2

    let scene3 = unsafeUpdate scene2 anneMovesMarble
    putStrLn "\n[3] Action: Anne moves marble to box (Sally doesn't see)."
    when generateOutput $ printStatus "scene3" scene3

    let scene4 = unsafeUpdate scene3 sallyReturns
    putStrLn "\n[4] Action: Sally returns."
    when generateOutput $ printStatus "scene4" scene4

    putStrLn "\n--- Final Belief Check ---"

    let anneKnowsGone = evalViaMdd scene4 (K "Anne" (Neg (PrpF tt)))
    putStrLn $ "Does Anne know marble is gone? " ++ show anneKnowsGone ++ " (Expected: True)"

    let sallyKnowsGone = evalViaMdd scene4 (K "Sally" (Neg (PrpF tt)))
    putStrLn $ "Does Sally know marble is gone? " ++ show sallyKnowsGone ++ " (Expected: False)"

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

    -- Create output folder and scene folder, then generate images
    createDirectoryIfMissing True "output"
    createDirectoryIfMissing True ("output" </> folderName)
    setCurrentDirectory ("output" </> folderName)

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

    (success3, msg3) <- generateGraphImageNamed (untag (snd obs)) "obs_law_total"
    when success3 $ putStrLn $ "    " ++ msg3
