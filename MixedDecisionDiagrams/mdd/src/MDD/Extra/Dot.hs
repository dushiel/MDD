{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module MDD.Extra.Dot where

import MDD.Types
import MDD.Traversal.Context
import MDD.Extra.Static
import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HashMap
import Data.List (intercalate, partition, sort, nub)
import Data.Maybe (fromMaybe, maybe)

import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode(..))
import System.FilePath ((</>))
import System.Directory (getCurrentDirectory)
import Control.Monad (when, guard)

-- | Helper function to get a NodeStatic from StaticNodeLookup
getNodeStatic :: StaticNodeLookup -> NodeId -> NodeStatic
getNodeStatic nm node_id =
    case HashMap.lookup (fst node_id) nm of
        Just result -> case Map.lookup (snd node_id) result of
            Just entry -> (node_id, ddStatic entry)
            Nothing -> error $ "Node address without Alternative in StaticNodeLookup: " ++ show node_id
        Nothing -> error $ "Node address not in StaticNodeLookup: " ++ show node_id

generatePositionMap :: [Position] -> ([Int] -> Int)
generatePositionMap xss =
  let positionMap = Map.fromList $ zip (nub (sort xss)) [1..]
  in (positionMap Map.!)

-- | Generates a graph image file.
--   Args:
--     mdd: The MDD to visualize.
--     color: Whether to use colored nodes.
--     hideUnknown: If true, hides the 'Unknown' leaf and its edges.
--     namingMap: A map from position vectors to custom string labels.
generateGraphImage :: MDD -> Bool -> Bool -> Map.Map [Int] String -> IO (Bool, String, FilePath)
generateGraphImage (MDD (nl, rootNode)) color hideUnknown namingMap = do
    let dotFileName = "graph.dot"
        svgFileName = "graph.svg"
    currentDir <- getCurrentDirectory
    let dotFilePath = currentDir </> dotFileName
        svgFilePath = currentDir </> svgFileName

    let ctx = init_unary_context nl
        (staticNodeLookup, staticGraph) = to_static_form ctx rootNode
    -- Pass all flags and the naming map down
    let dotGraphString = createDotGraph staticNodeLookup (fst staticGraph) color hideUnknown namingMap
    writeFile dotFilePath dotGraphString

    let dotExecutable = "dot"
    (exitCode, _, stderr) <- readProcessWithExitCode dotExecutable ["-Tsvg", "-o", svgFilePath, dotFilePath] ""

    case exitCode of
        ExitSuccess -> return (True, "Image generated successfully.", svgFilePath)
        ExitFailure _ -> return (False, "Error generating image: " ++ stderr, "")

-- Default: shows unknown nodes, no custom names
generateAndShow :: MDD -> IO ()
generateAndShow mdd = do
    (success, message, imageFilePath) <- generateGraphImage mdd False False Map.empty
    putStrLn message
    when success $ putStrLn $ "Image file: " ++ imageFilePath

-- Default colored: shows unknown nodes, no custom names
generateAndShow_c :: MDD -> IO ()
generateAndShow_c mdd = do
    (success, message, imageFilePath) <- generateGraphImage mdd True False Map.empty
    putStrLn message
    when success $ putStrLn $ "Image file: " ++ imageFilePath

-- Hides unknown nodes, no custom names
generateAndShow_h :: MDD -> IO ()
generateAndShow_h mdd = do
    (success, message, imageFilePath) <- generateGraphImage mdd False True Map.empty
    putStrLn message
    when success $ putStrLn $ "Image file: " ++ imageFilePath

-- Hides unknown nodes, colored, no custom names
generateAndShow_ch :: MDD -> IO ()
generateAndShow_ch mdd = do
    (success, message, imageFilePath) <- generateGraphImage mdd True True Map.empty
    putStrLn message
    when success $ putStrLn $ "Image file: " ++ imageFilePath

-- | Shows unknown nodes, colored, with custom names.
generateAndShow_cn :: Map.Map [Int] String -> MDD -> IO ()
generateAndShow_cn namingMap mdd = do
    (success, message, imageFilePath) <- generateGraphImage mdd True False namingMap
    putStrLn message
    when success $ putStrLn $ "Image file: " ++ imageFilePath

-- | Helper to check if a node is the Unknown' type.
isUnknownNode :: DdStatic -> Bool
isUnknownNode Unknown' = True
isUnknownNode _        = False

-- | Traverses the graph to collect node and edge definitions.
createDotGraph' :: StaticNodeLookup -> NodeId -> Map.Map NodeId String -> Bool -> Bool -> Map.Map [Int] String -> ([(NodeId, String, [Int])], [String], Map.Map NodeId String)
createDotGraph' staticNodeLookup startNodeId visited colorized hideUnknown namingMap =
  case Map.lookup startNodeId visited of
    Just _ -> ([], [], visited) -- Node already visited
    Nothing ->
      let
        (_nodeId, nodeData) = getNodeStatic staticNodeLookup startNodeId
      in
      if hideUnknown && isUnknownNode nodeData
      then ([], [], visited)
      else
        let
          safeLast xs = if null xs then 0 else last xs
          (nodeLabel, nodeShape, fontColor, position) = case nodeData of
            Leaf' True        -> ("1", "square",   if colorized then "forestgreen" else "", [-1])
            Leaf' False       -> ("0", "square",   if colorized then "red" else "",         [-1])
            Unknown'          -> ("?", "square",   if colorized then "DarkOrange" else "",  [-1])
            -- ✅ Use the naming map or default to the last integer of the position vector.
            Node' p _ _       -> (fromMaybe (show (safeLast p)) (Map.lookup p namingMap), "circle", "", p)
            InfNodes' p _ _ _ -> ("{" ++ fromMaybe (show (safeLast p)) (Map.lookup p namingMap) ++ "}", "trapezium", if colorized then "SteelBlue" else "", p)
            EndInfNode' _     -> ("", "diamond",  "", [-2])

          nodeIdStr = "node" ++ show (abs (fst startNodeId)) ++ "_" ++ show (snd startNodeId)
          commonAttrs = " [label=\"" ++ nodeLabel ++ "\", shape=" ++ nodeShape
          specificAttrs = case nodeData of
              EndInfNode' _ -> ", fontsize=8, margin=\"0.08,0.08\", width=0.3, height=0.3"
              _             -> ", width=0.5, height=0.25, margin=\"0.025,0.001\""
          colorAttr = if null fontColor then "" else ", fontcolor=" ++ fontColor
          nodeDefString = nodeIdStr ++ commonAttrs ++ specificAttrs ++ colorAttr ++ "];"
          newNodeDef = (startNodeId, nodeDefString, position)
          updatedVisited = Map.insert startNodeId nodeIdStr visited

          -- Recursive traversal for child nodes and edges
          (childNodeDefs, childEdgeDefs, finalVisited) = case nodeData of
            Node' _ l r ->
              let (lDefs, lEdges, v1) = createDotGraph' staticNodeLookup l updatedVisited colorized hideUnknown namingMap
                  (rDefs, rEdges, v2) = createDotGraph' staticNodeLookup r v1 colorized hideUnknown namingMap
                  edgeColorStart = if colorized then " [fontcolor=dimgray, " else " ["
                  lEdge = maybe [] (\target -> [nodeIdStr ++ " -> " ++ target ++ edgeColorStart ++ "style=\"solid\", arrowsize=0.75]"]) (Map.lookup l v2)
                  rEdge = maybe [] (\target -> [nodeIdStr ++ " -> " ++ target ++ edgeColorStart ++ "style=\"dashed\", arrowsize=0.75]"]) (Map.lookup r v2)
                  newEdges = lEdge ++ rEdge
              in (lDefs ++ rDefs, lEdges ++ rEdges ++ newEdges, v2)

            InfNodes' _ dc p n ->
              let (dcDefs, dcEdges, v1) = createDotGraph' staticNodeLookup dc updatedVisited colorized hideUnknown namingMap
                  (pDefs, pEdges, v2) = if p /= (0,0) then createDotGraph' staticNodeLookup p v1 colorized hideUnknown namingMap else ([], [], v1)
                  (nDefs, nEdges, v3) = if n /= (0,0) then createDotGraph' staticNodeLookup n v2 colorized hideUnknown namingMap else ([], [], v2)
                  edgeColorStart = if colorized then "[fontcolor=dimgray, " else "["
                  dcEdge = guard (dc /= (0,0)) >> maybe [] (\t -> [nodeIdStr ++ " -> " ++ t ++ " " ++ edgeColorStart ++ "style=\"dotted\", taillabel=\"Dc\", fontsize=10]"]) (Map.lookup dc v3)
                  pEdge  = guard (p  /= (0,0)) >> maybe [] (\t -> [nodeIdStr ++ " -> " ++ t ++ " " ++ edgeColorStart ++ "style=\"dotted\", taillabel=\"Pos\", fontsize=10]"]) (Map.lookup p v3)
                  nEdge  = guard (n  /= (0,0)) >> maybe [] (\t -> [nodeIdStr ++ " -> " ++ t ++ " " ++ edgeColorStart ++ "style=\"dotted\", taillabel=\"Neg\", fontsize=10]"]) (Map.lookup n v3)
                  newEdges = dcEdge ++ pEdge ++ nEdge
              in (dcDefs ++ pDefs ++ nDefs, dcEdges ++ pEdges ++ nEdges ++ newEdges, v3)

            EndInfNode' cons ->
              let (consDefs, consEdges, v1) = createDotGraph' staticNodeLookup cons updatedVisited colorized hideUnknown namingMap
                  edgeColor = if colorized then "fontcolor=dimgray" else ""
                  newEdges = maybe [] (\target -> [nodeIdStr ++ " -> " ++ target ++ " [style=\"dotted\", arrowsize=0.75, " ++ edgeColor ++ "];"]) (Map.lookup cons v1)
              in (consDefs, consEdges ++ newEdges, v1)

            _ -> ([], [], updatedVisited)
        in (newNodeDef : childNodeDefs, childEdgeDefs, finalVisited)

-- | Main function to generate the final .dot graph string using ranks.
createDotGraph :: StaticNodeLookup -> NodeId -> Bool -> Bool -> Map.Map [Int] String -> String
createDotGraph staticNodeLookup startNode colorized hideUnknown namingMap =
  let
    -- Pass all arguments down to the recursive traversal
    (allNodes, allEdges, _) = createDotGraph' staticNodeLookup startNode Map.empty colorized hideUnknown namingMap

    (leafAndUnknownNodes, rest1) = partition (\(_, _, pos) -> pos == [-1]) allNodes
    (endInfNodes, regularNodes)  = partition (\(_, _, pos) -> pos == [-2]) rest1

    regularPositions = map (\(_, _, pos) -> pos) regularNodes
    posMap = generatePositionMap regularPositions

    nodesByRank :: Map.Map Int [String]
    nodesByRank = Map.fromListWith (++) $ do
        (_, nodeDef, pos) <- regularNodes
        let rank = posMap pos
        return (rank, [nodeDef])

    rankBlocks = unlines $ Map.elems $ Map.mapWithKey (\_rank defs ->
        "  { rank=same;\n" ++
        unlines (map ("    " ++) defs) ++
        "  }") nodesByRank

    endInfNodeDefs = unlines $ map (("  " ++) . (\(_, def, _) -> def)) endInfNodes

    leafDefs = map (\(_, def, _) -> def) leafAndUnknownNodes
    leafBlock = if null leafDefs then "" else
        "  { rank=sink;\n" ++
        unlines (map ("    " ++) leafDefs) ++
        "  }\n"

  in
  "digraph G {\n" ++
  "  node [fontsize=12];\n" ++
  (if colorized then "  graph [bgcolor=white];\n" else "") ++
  "  edge [fontsize=10];\n\n" ++
  rankBlocks ++ "\n" ++
  endInfNodeDefs ++ "\n" ++
  leafBlock ++ "\n" ++
  unlines (map ("  "++) allEdges) ++
  "}\n"
