{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module DrawMDD where
import MDD
import System.IO
-- import Test.Hspec
import qualified Data.Map as Map
import GHC.IO (unsafePerformIO)
import Control.DeepSeq (deepseq)

import System.Console.ANSI
import qualified Data.HashMap.Lazy as HashMap
import Debug.Trace (trace)
import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode(..))
import System.FilePath ((</>))  -- Import for path manipulation
import System.Directory (getCurrentDirectory)
import Control.Monad (when)
import Data.List (intercalate, sortBy, groupBy, foldl')
import Data.Function (on)
import Data.Ord (comparing)
import Control.Monad.Cont (Cont)
import qualified Data.Set as Set

indentInit :: [String] -> [String]
indentInit [] = []
indentInit (s:ss) = (" ├─╴" ++ s) : map (" ¦  " ++) ss

indentInfInit :: [String] -> [String]
indentInfInit [] = []
indentInfInit (s:ss) = ("  ╠═╴" ++ s) : map ("  ║  " ++) ss

indentInfLast :: [String] -> [String]
indentInfLast [] = []
indentInfLast (s:ss) = ("  ╚═╴" ++ s) : map ("     " ++) ss

indentLast :: [String] -> [String]
indentLast [] = []
indentLast (s:ss) = (" └ ╴" ++ s) : map ("   " ++) ss


indentChildren :: [[String]] -> [[String]]
indentChildren [] = []
indentChildren ns = map indentInit (init ns) ++ [indentLast (last ns)]

indentInfChildren :: [[String]] -> [[String]]
indentInfChildren [] = []
indentInfChildren ns = map indentInfInit (init ns) ++ [indentInfLast (last ns)]

appLast :: [String] -> String -> [String]
appLast ss s = init ss ++ [last ss ++ s]


showTree'' :: Context -> (Int -> String) -> Node -> [String]
showTree'' a b c = snd $ showTree' a b c

showTree' :: Context -> (Int -> String) -> Node -> (Context, [String])
--showTree' (Node n ns) = n : concat (indentChildren (map showTree' ns))
showTree' c _ (_, Unknown) = (c, ["[.]"])
showTree' c _ (_, Leaf True) = (c, ["[1]"])
showTree' c _ (_, Leaf False) = (c, ["[0]"])
showTree' c f d@(id, Node a l r) = withCache' c'' d $
    ("("++ f a ++") " ++ col Dull Blue (show_id id)) :
    concat (indentChildren [s1, s2])
    where
        (c', s1) = showTree' c f (l, getDd c l)
        (c'', s2) = showTree' c' f (r, getDd c r)

showTree' c f d@(id, InfNodes a dc (0,0) (0,0)) = withCache' c' d $
    ("<"++ f a ++ "> dc " ++ col Dull Blue (show_id id)) : "  ║  " :
    concat (indentInfChildren [s1])
    where
        (c', s1) = showTree' c f (dc, getDd c dc)
showTree' c f d@(id, InfNodes a dc p (0, 0)) = withCache' c'' d $
    ("<"++ f a ++ "> dc, p " ++ col Dull Blue (show_id id)) : "  ║  " :
    concat (indentInfChildren [s1, s2])
    where
        (c', s1) = showTree' c f (dc, getDd c dc)
        (c'', s2) = showTree' c' f (p, getDd c p)

showTree' c f d@(id, InfNodes a dc (0, 0) n) = withCache' c'' d $
    ("<"++ f a ++ "> dc, n " ++ col Dull Blue (show_id id)) : "  ║  " :
    concat (indentInfChildren [s1, r_p1])
    where
        (c', s1) = showTree' c f (dc, getDd c dc)
        (c'', r_p1) = showTree' c' f (n, getDd c n)

showTree' c f d@(id, InfNodes a dc p n) = withCache' c''' d $
    ("<"++ f a ++ "> dc, p, n " ++ col Dull Blue (show_id id)) : "  ║  " :
    concat (indentInfChildren [s1, r_p, r_n])
    where
        (c', r_p) = showTree' c f (p, getDd c p)
        (c'', s1) = showTree' c' f (dc, getDd c dc)
        (c''', r_n) = showTree' c'' f (n, getDd c n)

showTree' c f d@(id, EndInfNode cons) =
        withCache' c' d $
            ("<> " ++ col Dull Blue (show_id id)) : "  ║  " :
            concat (indentInfChildren [s1])
        where
            (c', s1) = showTree' c f (cons, getDd c cons)

showTree :: Context -> Node -> String
showTree c d = "\n" ++ unlines (showTree'' c show d)
showTree2 :: Context -> Node -> String
showTree2 c = unlines . showTree'' c show


drawTree2 :: Context -> Node -> IO ()
drawTree2 c = putStrLn . showTree2 c

drawTree3 :: (Context, Node) -> IO ()
drawTree3 (c, x) = putStrLn . showTree c $ x



-- disp :: Map.Map Ordinal (Either (Map.Map Int String) String) -> Dd -> IO ()
-- disp m = putStrLn . unlines . showTree' (show . (\case
--    Left x -> if Map.member x m then m Map.! x else error $ "key: " ++ show x ++ " not in keys: " ++ show (Map.keys m)))


data Show_setting = ShowSetting {
  color :: Bool,
  display_node_id's :: Bool,
  draw_tree :: Bool,
  display_context :: Bool,
  display_leaf_cases :: Bool,
  display_end_infs :: Bool,
  display_dc_traversal :: Bool,
  debug_on :: Bool,
  save_logs :: Bool,
  debug_open :: Bool,
  debug_close :: Bool,
  debug_shorten_close :: Bool,
  debug_dc_stack :: Bool,
  display_level :: Bool,
  display_dcAs :: Bool,
  display_dcBs :: Bool,
  display_dcRs :: Bool
}


-- format :: String -> String
-- format s = format' $ words s

-- format' :: [String] -> String
-- format' [] = "" -- Base case: return an empty string for an empty list
-- format' (n : n2 : n3 : ns) =
--     colorize "red" n ++ colorize "green" n2 ++ colorize "" n3 ++ format' ns
-- format' (n : n2 : ns) =
--     colorize "red" n ++ colorize "green" n2 ++ format' ns
-- format' (n : ns) =
--     n ++ format' ns


show_dd :: Show_setting -> Context -> Node -> String
show_dd s@ShowSetting{display_context=True} c d = show c ++ show_dd s{display_context=False} c d
show_dd ShowSetting{draw_tree=True} c d = showTree c d
show_dd s _ (_, Unknown)
  | color s = "[" ++ colorize "purple" "." ++ "]"
  | otherwise = "[.]"
show_dd s _ (_, Leaf False)
  | color s = "[" ++ colorize "soft red" "0" ++ "]"
  | otherwise = "[0]"
show_dd s _ (_, Leaf True)
  | color s = "[" ++ colorize "soft green" "1" ++ "]"
  | otherwise = "[1]"
show_dd s c (d_id, d) = case d of
  Node i rC lC -> show_i i "orange" ++ " (" ++ show_dd s c (getNode c rC) ++ ") (" ++ show_dd s c (getNode c lC) ++ ")"
  InfNodes i dc p n -> show_i i "chill blue" ++ " <{dc: " ++ show_dd s c (getNode c dc) ++ "} {p: " ++ show_dd s c (getNode c p) ++ "} {n: " ++ show_dd s c (getNode c n) ++ "}"
  EndInfNode child -> (if color s then colorize "chill blue" "<>" else "<>") ++ show_dd s c (getNode c child)
  _ -> error "should not be possible"
  where
    show_i i c = (if display_node_id's s then (if color s then colorize "blue" ("#" ++ show d_id) else ("#" ++ show d_id)) ++ " " else "")
      ++ (if color s then colorize c (show i) else show i)

check_length :: Context -> Bool
check_length c@Context{dc_stack=(dcAs, dcBs, _), current_level=(lvAs, lvBs)}
    | length dcAs > length lvAs = False
    | length dcBs > length lvBs = False
    | otherwise = True

debug_manipulation :: (Context, Node) -> String -> String -> Context -> Node -> Node -> (Context, Node)
debug_manipulation f f_key f_name old_c@Context{cache = nc, dc_stack=dcs, current_level=lv} a@(a_id, a_d) b@(b_id, b_d)
    | getDd old_c a_id == a_d && getDd old_c b_id == b_d = if not $ save_logs settings then
    -- prepare message for before the calling of the function
    let
    leaf_msg = colorize "orange" (">> " ++ f_name ++ " : ") ++
                    "\n  ->   " ++ show_dd settings old_c a ++
                    "\n  ->   " ++ show_dd settings old_c b ++ "\n"
    (c,r) = if debug_open settings && check_skip_display a_id b_id
            then if debug_dc_stack settings
                then myTrace (leaf_msg ++ display_func_stack old_c) f
                else myTrace leaf_msg f
            else f
    in

    -- after calling the function
    if debug_close settings && check_skip_display a_id b_id
        then if a_id `elem` [(1,0), (2,0)] || b_id `elem` [(1,0), (2,0)]
            then if not $ display_leaf_cases settings
                then (c{dc_stack=dcs}, r)
                else --myTrace (display_func_stack old_c) $
                    myTrace (colorize "green" (f_name ++ " : ") ++
                    "\n  " ++ show_dd settings c a ++
                    " : " ++ show_dd settings c b ++
                    " = " ++ show_dd settings c r ++ " " ++ col Dull Blue (show_id' r) ++
                    "\n") (c, r)
            else
            --myTrace (display_func_stack old_c) $
            myTrace (
            case Map.lookup f_key nc of
                Just nc' -> case HashMap.lookup (a_id, b_id, dcs) nc' of
                    Just rt -> colorize "chill blue" "found cached result : " ++ col Dull Blue (show_id rt) ++ " for "
                        ++ colorize "green" (f_name ++ " : ") ++
                        (if not $ debug_shorten_close settings then
                            "\n  ->   " ++ show_dd settings c a ++
                            "\n  ->   " ++ show_dd settings c b
                        else "") ++
                        "\n  =>   " ++ show_dd settings c r ++
                        "\n"
                    Nothing ->
                        colorize "green" (f_name ++ " : ") ++
                        (if not $ debug_shorten_close settings then
                            "\n  ->   " ++ show_dd settings c a ++
                            "\n  ->   " ++ show_dd settings c b
                        else "") ++
                        "\n  =>   " ++ show_dd settings c r ++ " " ++ col Dull Blue (show_id' r) ++
                        "\n"
                Nothing -> error ("wrong function name in cache lookup: " ++ show f_key)
            ) (c{dc_stack=dcs}, r)
        else (c{dc_stack=dcs}, r)


    ---------------------------------------------------------
    else
    -- debug message for before the calling of the function
    let
    start_msg = ("\\n" ++ colorize "orange" "  ->   " ++ show_dd settings old_c a) ++
                ("\\n" ++ colorize "orange" "  ->   " ++ show_dd settings old_c b ++ "\\n")
    (c,r) = if check_skip_display a_id b_id
            then myDebugLog "\"inner\":[" f
            else f
    in
    -- debug for after calling the function

    if check_skip_display a_id b_id
        then myDebugLog ("{\"" ++ colorize "green" f_name ++"\": {" ++ "\"func_stack before\": [\"" ++ show_dc_stack old_c ++ "\"],\n\"input\": \"" ++ start_msg ++ "\",\n") $
            case Map.lookup f_key nc of
                Just nc' -> case HashMap.lookup (a_id, b_id, dcs) nc' of
                    Just rt -> myDebugLog ("],\n\"" ++ colorize "chill blue" "found cached result"++"\":\"" ++ col Vivid Blue (show_id rt) ++ " for " ++ "\\n" ++ colorize "green" "  =>   "
                        ++ show_dd settings c (rt, getDd c rt) ++ "\\n\"}},") (old_c, (rt, getDd c rt))
                    Nothing ->
                        myDebugLog ("],\n\"result\": \"\\n" ++ colorize "green" "  =>   " ++ show_dd settings c r ++ " " ++ col Vivid Blue (show_id' r)
                        ++ "\\n\"}},") (c{dc_stack=dcs}, r)
                Nothing -> error ("wrong function name in cache lookup: " ++ show f_key)
        else (c{dc_stack=dcs}, r)
    | otherwise = error ("id and dd are not equal, \n a_id: " ++ show (getDd old_c a_id) ++ "\n a: " ++ show a ++ "\n b_id: " ++ show (getDd old_c b_id) ++ " \n b: " ++ show b )

check_skip_display :: NodeId -> NodeId -> Bool
check_skip_display a_id b_id =
    debug_on settings &&
    not (a_id `elem` [(1,0), (2,0)] && b_id `elem` [(1,0), (2,0)]) && -- ez cases
    not (a_id == (0,0) && b_id == (0,0)) && -- always returns unkown
    not ((a_id `elem` [(1,0), (2,0)] || b_id `elem` [(1,0), (2,0)]) && not (display_leaf_cases settings))


debug_func :: String -> (Context, Node) -> (Context, Node)
debug_func f_name f = if save_logs settings
    then myDebugLog ("{\"" ++ colorize "orange" f_name ++ "\" : [") (myDebugLog ("\n{\""++ "context" ++ "\" : [\"" ++ show_context (fst f) ++ "\"]}\n]},") f)
    else if debug_on settings
        then myTrace ("{\"" ++ colorize "orange" f_name ++ "\" : [") (myTrace ("\n{\""++ "context" ++ "\" : [\"" ++ show_context (fst f) ++ "\"]}\n]},") f)
        else f
    -- where f' =  myTrace "\"inner\":{" f

debug_dc_traverse :: String -> Context -> NodeId -> NodeId -> Context -> Context
debug_dc_traverse s c a b f = if display_dc_traversal settings && debug_on settings
    then myTrace (colorize "purple" "dc_traverse" ++ ", for arguments: " ++ s ++ " a: " ++ show_dd settings c (getNode c a) ++ "  b: " ++ show_dd settings c (getNode c b))
        (myTrace (display_func_stack' c f ++ "\n\n") f)
    else f
    -- then myDebugLog ("{\"" ++ colorize "orange" "dc_traverse" ++ "\" : [") (myDebugLog ("\n{\""++ "context" ++ "\" : [\"" ++ show_context (f) ++ "\"]}\n]},") f)
    -- else if debug_on settings
    --     then myTrace ("{\"" ++ colorize "orange" "dc_traverse" ++ "\" : [") (myTrace ("\n{\""++ "context" ++ "\" : [\"" ++ show_context (f) ++ "\"]}\n]},") f)
    --     else f



display_func_stack' :: Context -> Context -> String
display_func_stack' old_c@Context{dc_stack = dcs} new_c@Context{dc_stack = new_dcs} = let
            (dcAs, dcBs, dcRs) = dcs
            (dcAs', dcBs', dcRs') = new_dcs
            old_dcAs = intercalate separator1 $ map (show_dd settings old_c) dcAs
            old_dcBs = intercalate separator1 $ map (show_dd settings old_c) dcBs
            old_dcRs = intercalate separator1 $ map (show_dd settings old_c) dcRs
            new_dcAs = intercalate separator1 $ map (show_dd settings new_c) dcAs'
            new_dcBs = intercalate separator1 $ map (show_dd settings new_c) dcBs'
            new_dcRs = intercalate separator1 $ map (show_dd settings new_c) dcRs'
            separator1 = " , \n  "
        in
            (if display_level settings then colorize "purple" "func stack : " ++ show (current_level old_c) ++ colorize "blue" "func stack : " ++ show (current_level new_c) else "") ++
            (if display_dcAs settings then colorize "orange" "\n- DcA old : \n  " ++ old_dcAs ++ colorize "green" "\n  DcA new : \n  " ++ new_dcAs else "") ++
            (if display_dcBs settings then colorize "orange" "\n- DcB old : \n  " ++ old_dcBs ++ colorize "green" "\n  DcB new : \n  " ++ new_dcBs else "") ++
            (if display_dcRs settings then colorize "orange" "\n- DcR old : \n  " ++ old_dcRs ++ colorize "green" "\n  DcR new : \n  " ++ new_dcRs else "")

display_func_stack :: Context -> String
display_func_stack c@Context{dc_stack = dcs} = let
            (dcAs, dcBs, dcRs) = dcs
            dcAs' = intercalate separator1 $ map (show_dd settings c) dcAs
            dcBs' = intercalate separator1 $ map (show_dd settings c) dcBs
            dcRs' = intercalate separator1 $ map (show_dd settings c) dcRs
            separator1 = " , \n"
        in
            (if display_level settings then colorize "purple" "func level : " ++ show (current_level c) else "") ++
            (if display_dcAs settings then colorize "blue" "\n DcA : \n" ++ dcAs' else "") ++
            (if display_dcBs settings then colorize "blue" "\n DcB : \n" ++ dcBs' else "") ++
            (if display_dcRs settings then colorize "blue" "\n DcR : \n" ++ dcRs' else "") ++ "\n"

jsonwrap :: String -> String -> String
jsonwrap k v = "{ \""++ k ++    "\": \"" ++ v ++ "\" }"

show_a_b :: Context -> Node -> Node -> String
show_a_b c a b = "\\n  ->   " ++ show_dd settings c a ++ "\\n  ->   " ++ show_dd settings c b

debug5 :: Node -> String -> Node
debug5 f s = if save_logs settings
    then myDebugLog ("{\"test_nr\" : \"" ++ colorize "red" s ++ "\", \n \"inner\": [")
            (myDebugLog ("], \"r\":\"" ++ colorize "dim red" (show $ fst f) ++ "\"\n},") (f) )
    else myTrace (colorize "red" (s ++ "\n\n")) f

myTrace :: String -> a -> a
myTrace msg x = unsafePerformIO $ do
    msg `deepseq` return (trace msg x)

myDebugLog :: String -> a -> a
myDebugLog msg x = unsafePerformIO $ do
    msg `deepseq` withFile "debug.log" AppendMode $ \h -> do
        hPutStrLn h msg
    return x

emptyFile :: IO ()
emptyFile = writeFile "debug.log" "["


settings :: Show_setting
settings = ShowSetting {
                color = True -- colorize
            ,   display_node_id's = False -- show node_id's
            ,   draw_tree = False
            ,   display_context = False
            ,   display_leaf_cases = True
            ,   display_end_infs = True
            ,   display_dc_traversal = False

            ,   debug_on = True
            ,   save_logs = False

            ,   debug_open = True
            ,   debug_close = True
            ,   debug_shorten_close = False

            ,   debug_dc_stack = True
            ,   display_level = True
            ,   display_dcAs = True
            ,   display_dcBs = True
            ,   display_dcRs = True
}



-- |====================================== Dot stuff


generateGraphImage :: Context -> Node -> Bool -> IO (Bool, String, FilePath)
generateGraphImage context rootNode color = do
    let dotFileName = "graph.dot"
    let pngFileName = "graph.png"
    let svgFileName = "graph.svg"
    currentDir <- getCurrentDirectory
    let dotFilePath = currentDir </> dotFileName
    let imageFilePath = currentDir </> pngFileName

    let dotGraphString = createDotGraph context rootNode color
    writeFile dotFilePath dotGraphString
    let dotExecutable = "C:\\Program Files\\Graphviz\\bin\\dot.exe"

    -- (exitCode, stdout, stderr) <- readProcessWithExitCode "dot" ["-Tpng", "-o", pngFileName, dotFileName] ""
    (exitCode, stdout, stderr) <- readProcessWithExitCode dotExecutable ["-Tsvg", "-o", svgFileName, dotFileName] ""

    case exitCode of
        ExitSuccess -> return (True, "Image generated successfully.", imageFilePath)
        ExitFailure _ -> return (False, "Error generating image: " ++ stderr, "")

-- | Generates a PNG image and prints the result. Convenient for GHCi.
generateAndShow :: (Context, Node) -> IO ()
generateAndShow (context, rootNode) = do
    (success, message, imageFilePath) <- generateGraphImage context rootNode False
    putStrLn message
    when success $ putStrLn $ "Image file: " ++ imageFilePath

generateAndShow_c :: (Context, Node) -> IO ()
generateAndShow_c (context, rootNode) = do
    (success, message, imageFilePath) <- generateGraphImage context rootNode True
    putStrLn message
    when success $ putStrLn $ "Image file: " ++ imageFilePath

-- Helper function to convert NodeId to DOT string format
nodeIdToDotId :: NodeId -> String
nodeIdToDotId (hash, idx) = "node" ++ show (abs hash) ++ "_" ++ show idx


-- Function to create the .dot graph (main traversal for nodes and edges)
createDotGraph' :: Context -> Node -> Map.Map NodeId String -> Bool -> ([String], [String], Map.Map NodeId String)
createDotGraph' context node@(nodeId, nodeData) visited colorized =
    case Map.lookup nodeId visited of
        Just _existingLabel -> ([], [], visited)
        Nothing ->
            let (nodeLabel, nodeShape, fontColor) = case nodeData of
                  Leaf True  -> ("1", "square", if colorized then "forestgreen" else "")
                  Leaf False -> ("0", "square", if colorized then "red" else "")
                  Unknown    -> ("?", "square", if colorized then "DarkOrange" else "")
                  Node position _ _ -> (show position, "circle", "")
                  InfNodes position _ _ _ -> ("{" ++ show position ++ "}", "trapezium", if colorized then "SteelBlue" else "")
                  EndInfNode _ -> ("", "diamond", "")

                nodeIdStr = nodeIdToDotId nodeId
                nodeAttributes = case nodeData of
                    EndInfNode _ -> " [label=\"" ++ nodeLabel ++ "\", shape=" ++ nodeShape ++ ", fontsize=8, margin=\"0.08,0.08\", width=0.3, height=0.3" ++ (if null fontColor then "" else ", fontcolor=" ++ fontColor) ++ "];"
                    _            -> " [label=\"" ++ nodeLabel ++ "\", shape=" ++ nodeShape ++ ", width=0.5, height=0.25, margin=\"0.025,0.001\"" ++ (if null fontColor then "" else ", fontcolor=" ++ fontColor) ++ "];"
                newNodeDefs = [nodeIdStr ++ nodeAttributes]
                updatedVisited = Map.insert nodeId nodeIdStr visited

                (childNodeDefs, childEdgeDefs, finalVisited) = case nodeData of
                    Node _ l r ->
                        let (lDefs, lEdges, v1) = createDotGraph' context (getNode context l) updatedVisited colorized
                            (rDefs, rEdges, v2) = createDotGraph' context (getNode context r) v1 colorized
                            edgeColorStart = if colorized then " [fontcolor=dimgray, " else " ["
                            edgeColorEnd = "]"
                            newEdges = [nodeIdStr ++ " -> " ++ (v2 Map.! l) ++ edgeColorStart ++ "style=\"solid\", arrowsize=0.75,  headlabel=\"\"" ++ edgeColorEnd,
                                         nodeIdStr ++ " -> " ++ (v2 Map.! r) ++ edgeColorStart ++ "style=\"dashed\", arrowsize=0.75, headlabel=\"\"" ++ edgeColorEnd]
                        in (lDefs ++ rDefs, lEdges ++ rEdges ++ newEdges, v2)

                    InfNodes _ dc n p ->
                        let vBase = updatedVisited
                            (dcDefs, dcEdges, v1) = if dc /= (0,0) then createDotGraph' context (getNode context dc) vBase colorized else ([], [], vBase)
                            (pDefs, pEdges, v2) = if p /= (0,0) then createDotGraph' context (getNode context p) v1 colorized else ([], [], v1)
                            (nDefs, nEdges, v3) = if n /= (0,0) then createDotGraph' context (getNode context n) v2 colorized else ([], [], v2)
                            edgeColorStart = if colorized then "[fontcolor=dimgray, " else "["
                            edgeColorEnd = "]"
                            newEdges = if dc /= (0,0) then
                                         [nodeIdStr ++ " -> " ++ (v3 Map.! dc) ++ " " ++ edgeColorStart ++ "style=\"dotted\", taillabel=\"Dc\", labeldistance=2, fontsize=12, arrowsize=0.75" ++ edgeColorEnd]
                                         else []
                            newEdges2 = if p /= (0,0)
                                        then [nodeIdStr ++ " -> " ++ (v3 Map.! p) ++ " " ++ edgeColorStart ++ "style=\"dotted\", taillabel=\"Pos\", labeldistance=2, fontsize=12, arrowsize=0.75" ++ edgeColorEnd]
                                        else []
                            newEdges3 =  if n /= (0,0)
                                         then [nodeIdStr ++ " -> " ++ (v3 Map.! n) ++ " " ++ edgeColorStart ++ "style=\"dotted\", /*taillabel=\"Neg\",*/ labeldistance=2, fontsize=12, arrowsize=0.75" ++ edgeColorEnd]
                                         else []
                        in (dcDefs ++ pDefs ++ nDefs, dcEdges ++ pEdges ++ nEdges ++ newEdges ++ newEdges2 ++newEdges3, v3)

                    EndInfNode cons ->
                        let (consDefs, consEdges, v1) = createDotGraph' context (getNode context cons) updatedVisited colorized
                            edgeColor = if colorized then "fontcolor=dimgray" else ""
                            newEdges = [nodeIdStr ++ " -> " ++ (v1 Map.! cons) ++ " [style=\"dotted\", arrowsize=0.75, " ++ edgeColor ++ ", headlabel=\"\"];"]
                        in (consDefs, consEdges ++ newEdges, v1)
                    _ -> ([], [], updatedVisited)
            in (newNodeDefs ++ childNodeDefs, childEdgeDefs, finalVisited)


-- Data structure to hold the hierarchy of InfNodes for subgraph generation
data InfNodeHierarchy = InfCluster {
    hNodeId :: NodeId,
    hPosition :: Int,
    hLevel :: Int,
    hDirectMemberNodeIds :: [NodeId],
    hNestedClusters :: [[InfNodeHierarchy]]
} deriving Show

-- Collects InfNode hierarchies
collectHierarchy :: Context -> Node -> Int -> Set.Set NodeId -> (Maybe InfNodeHierarchy, Set.Set NodeId)
collectHierarchy context (nodeId, nodeData) level visited =
    if Set.member nodeId visited then (Nothing, visited) else
    let visited' = Set.insert nodeId visited
    in case nodeData of
        InfNodes pos dc n p ->
            let childNodeIds = filter (/= (0,0)) [dc, n, p]
                (directMembers, nested, finalVisited) = processChildrenForHierarchy context childNodeIds (level + 1) visited'
                currentCluster = InfCluster nodeId pos level directMembers nested
            in (Just currentCluster, finalVisited)

        Node _ l r ->
            let (lRes, v1) = if l /= (0,0) then collectHierarchy context (getNode context l) level visited' else (Nothing, visited')
                (rRes, v2) = if r /= (0,0) then collectHierarchy context (getNode context r) level v1 else (Nothing, v1)
                finalRes = case lRes of
                               Just _  -> lRes
                               Nothing -> rRes
            in (finalRes, v2)

        EndInfNode cons ->
            if cons /= (0,0) then collectHierarchy context (getNode context cons) level visited' else (Nothing, visited')
        Leaf _          -> (Nothing, visited')
        Unknown         -> (Nothing, visited')

-- Processes children of an InfNode for hierarchy building
processChildrenForHierarchy :: Context -> [NodeId] -> Int -> Set.Set NodeId
                            -> ([NodeId], [[InfNodeHierarchy]], Set.Set NodeId)
processChildrenForHierarchy context childNodeIds childLevel initialVisited =
  let folder (directsAcc, nestsAcc, visitedAcc) childId =
        if Set.member childId visitedAcc then (directsAcc, nestsAcc, visitedAcc) else
        let childFullNode@(cNodeId, _cNodeData) = getNode context childId
            (mClusterStartedByChild, visitedAfterChildProcessing) =
                 collectHierarchy context childFullNode childLevel visitedAcc
        in case mClusterStartedByChild of
             Just foundCluster ->
                 (directsAcc, foundCluster : nestsAcc, visitedAfterChildProcessing)
             Nothing ->
                 (cNodeId : directsAcc, nestsAcc, visitedAfterChildProcessing)

      (directMemberIds_rev, nestedClusters_rev, finalVisited) =
          foldl' folder ([], [], initialVisited) childNodeIds

      groupedNested = if null nestedClusters_rev
                      then []
                      else groupBy ((==) `on` hPosition) $ sortBy (comparing hPosition) (reverse nestedClusters_rev)
  in (reverse directMemberIds_rev, groupedNested, finalVisited)


-- Serializes a group of InfNodeHierarchies (sharing position and level)
serializeNestedGroup :: [InfNodeHierarchy] -> String
serializeNestedGroup [] = ""
serializeNestedGroup infNodeGroup =
    "  {\n" ++
    "    rank=same; " ++ intercalate "; " (map (nodeIdToDotId . hNodeId) infNodeGroup) ++ ";\n" ++
    "  }\n" ++
    intercalate "\n" (map serializeHierarchyActualSubgraph infNodeGroup)

-- Serializes a single InfNodeHierarchy into its DOT subgraph cluster
serializeHierarchyActualSubgraph :: InfNodeHierarchy -> String
serializeHierarchyActualSubgraph cluster =
    let clusterDotId = "cluster_L" ++ show (hLevel cluster) ++ "_N" ++ show (abs (fst (hNodeId cluster))) ++ "_" ++ show (snd (hNodeId cluster))
        directMemberStrings = map nodeIdToDotId (hDirectMemberNodeIds cluster)
        memberNodesListing = if null directMemberStrings
                             then ""
                             else "  " ++ intercalate "; " directMemberStrings ++ ";\n"
    in
    "subgraph " ++ clusterDotId ++ " {\n" ++
    "  label=\"L:" ++ show (hLevel cluster) ++ " P:" ++ show (hPosition cluster) ++ "\";\n" ++
    memberNodesListing ++
    intercalate "\n" (map serializeNestedGroup (hNestedClusters cluster)) ++
    "}\n"

-- Finds all top-level InfNode hierarchies
findTopLevelHierarchies :: Context -> Node -> Set.Set NodeId -> ([InfNodeHierarchy], Set.Set NodeId)
findTopLevelHierarchies context (nodeId, nodeData) visited =
    if Set.member nodeId visited then ([], visited) else
    let visited' = Set.insert nodeId visited
    in case nodeData of
        InfNodes {} ->
            let (mCluster, finalV) = collectHierarchy context (nodeId, nodeData) 0 visited'
            in (maybe [] (:[]) mCluster, finalV)

        Node _ l r ->
            let (lH, v1) = if l /= (0,0) then findTopLevelHierarchies context (getNode context l) visited' else ([], visited')
                (rH, v2) = if r /= (0,0) then findTopLevelHierarchies context (getNode context r) v1 else ([], v1)
            in (lH ++ rH, v2)

        EndInfNode cons ->
            if cons /= (0,0) then findTopLevelHierarchies context (getNode context cons) visited' else ([], visited')
        Leaf _          -> ([], visited')
        Unknown         -> ([], visited')

-- MODIFIED Function to create subgraphs for InfNodes with nesting
createInfNodesSubgraphs :: Context -> Node -> String
createInfNodesSubgraphs context startNode =
    let (topLevelClusters, _) = findTopLevelHierarchies context startNode Set.empty
        groupedTopLevel = if null topLevelClusters
                          then []
                          else groupBy ((==) `on` hPosition) $ sortBy (comparing hPosition) topLevelClusters
    in intercalate "\n" (map serializeNestedGroup groupedTopLevel)


-- Helper function to collect leaf and unknown nodes
leafAndUnknownNodes :: Context -> Node -> [String]
leafAndUnknownNodes context startNode = fst (collectNodesRecursive startNode Set.empty)
  where
    collectNodesRecursive :: Node -> Set.Set NodeId -> ([String], Set.Set NodeId)
    collectNodesRecursive (nodeId, nodeData) visited =
      if Set.member nodeId visited then ([], visited) else
      let visitedAfterCurrent = Set.insert nodeId visited
          nodeStr = nodeIdToDotId nodeId
      in case nodeData of
        Leaf _  -> ([nodeStr], visitedAfterCurrent)
        Unknown -> ([nodeStr], visitedAfterCurrent)
        Node _ l r ->
            let (lStrs, vL) = if l /= (0,0) then collectNodesRecursive (getNode context l) visitedAfterCurrent else ([], visitedAfterCurrent)
                (rStrs, vR) = if r /= (0,0) then collectNodesRecursive (getNode context r) vL else ([], vL)
            in (lStrs ++ rStrs, vR)
        InfNodes _ dc n p ->
            let childrenInOrder = filter (/=(0,0)) [dc, p, n]
                foldFn (accStrs, currentVisited) childId =
                    let (childStrs, nextVisited) = collectNodesRecursive (getNode context childId) currentVisited
                    in (accStrs ++ childStrs, nextVisited)
            in foldl' foldFn ([], visitedAfterCurrent) childrenInOrder
        EndInfNode cons ->
            if cons /= (0,0) then collectNodesRecursive (getNode context cons) visitedAfterCurrent else ([], visitedAfterCurrent)


-- Top-level function to create the complete .dot graph string
createDotGraph :: Context -> Node -> Bool -> String
createDotGraph context startNode colorized =
  let collectedLUNodes = leafAndUnknownNodes context startNode
      -- Construct the sink block with an explicit rank=same for all leaf/unknown nodes
      sinkBlock = if null collectedLUNodes
                  then ""
                  else "{\n" ++
                       "    rank=same;\n" ++
                       "    {  rank=sink;" ++ intercalate "; " collectedLUNodes ++ "; }\n" ++
                       "  }\n"
      (nodeDefs, edgeDefs, _) = createDotGraph' context startNode Map.empty colorized
  in
  "digraph G {\n" ++
  "  node [shape=box];\n" ++
  (if colorized then "  graph [bgcolor=white];\n" else "") ++
  "  edge [style=\"mydotted\"];\n" ++
  "  \"mydotted\"[style=\"invis\", height=0.0,width=0.0, fixedsize=true, label=\"\", peripheries=0];\n" ++
  sinkBlock ++ "\n" ++ -- Add the sink block here
  createInfNodesSubgraphs context startNode ++ "\n" ++
  intercalate "\n" (nodeDefs ++ edgeDefs) ++ "\n}\n"
