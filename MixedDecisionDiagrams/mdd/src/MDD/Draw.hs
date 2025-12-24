{-# LANGUAGE FlexibleContexts #-}

module MDD.Draw where

import MDD.Types
import MDD.Context
import MDD.Manager
import MDD.Construction
import System.Console.ANSI
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.Map as Map
import Data.List (intercalate)
import Debug.Trace (trace)
import GHC.IO (unsafePerformIO)
import Control.DeepSeq (deepseq)
import System.IO

-- ==========================================================================================================
-- * Drawing Configuration
-- ==========================================================================================================

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

settings :: Show_setting
settings = ShowSetting {
                color = True
            ,   draw_tree = False
            ,   display_node_id's = False
            ,   display_context = False
            ,   display_leaf_cases = False
            ,   display_end_infs = True
            ,   display_dc_traversal = False
            ,   debug_on = False
            ,   save_logs = False
            ,   debug_open = True
            ,   debug_close = True
            ,   debug_shorten_close = True
            ,   debug_dc_stack = False
            ,   display_level = False
            ,   display_dcAs = False
            ,   display_dcBs = False
            ,   display_dcRs = False
}

-- ==========================================================================================================
-- * ANSI Formatting Helpers
-- ==========================================================================================================

col :: ColorIntensity -> Color -> String -> String
col i c s = setSGRCode [SetColor Foreground i c] ++ s ++ setSGRCode [Reset]

colorize :: String -> String -> String
colorize c s
    | c == "red" = setColor24bit 255 100 100  ++ s ++ resetColor
    | c == "soft red" = setColor24bit 255 130 130  ++ s ++ resetColor
    | c == "green" = setColor24bit 100 200 100  ++ s ++ resetColor
    | c == "soft green" = setColor24bit 150 255 150  ++ s ++ resetColor
    | c == "blue" = "\ESC[2m" ++ setColor24bit 1 100 999  ++ s ++ resetColor
    | c == "chill blue" = setColor24bit 150 200 255  ++ s ++ resetColor
    | c == "orange" = setColor24bit 255 215 50  ++ s ++ resetColor
    | c == "purple" = setColor24bit 153 0 135  ++ s ++ resetColor
    | c == "dark" = setSGRCode [SetColor Foreground Dull White] ++ s ++ setSGRCode [Reset]
    | otherwise = setSGRCode [SetColor Foreground Vivid Blue] ++ s ++ setSGRCode [Reset]

setColor24bit :: Int -> Int -> Int -> String
setColor24bit r g b = "\ESC[38;2;" ++ show r ++ ";" ++ show g ++ ";" ++ show b ++ "m"

resetColor :: String
resetColor = "\ESC[0m"

-- ==========================================================================================================
-- * Tree Visualization Logic
-- ==========================================================================================================

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

showTree' :: DrawOperatorContext -> (Int -> String) -> Node -> (DrawOperatorContext, [String])
showTree' c _ (_, Unknown) = (c, ["[.]"])
showTree' c _ (_, Leaf True) = (c, ["[1]"])
showTree' c _ (_, Leaf False) = (c, ["[0]"])
showTree' c f d@(id, Node a l r) =
    let (c', s1) = showTree' c f (getNode c l)
        (c'', s2) = showTree' c' f (getNode c' r)
    in (c'', ("("++ f a ++") " ++ col Dull Blue (show_id id)) : concat (indentChildren [s1, s2]))
showTree' c f d@(id, InfNodes a dc p n) =
    let (c1, s1) = showTree' c f (getNode c dc)
        (c2, s2) = if p == l_u then (c1, []) else showTree' c1 f (getNode c1 p)
        (c3, s3) = if n == l_u then (c2, []) else showTree' c2 f (getNode c2 n)
        header = ("<"++ f a ++ "> " ++ col Dull Blue (show_id id)) : ["  ║  "]
    in (c3, header ++ concat (indentInfChildren (filter (not . null) [s1, s2, s3])))
showTree' c f (id, EndInfNode child) =
    let (c', s1) = showTree' c f (getNode c child)
    in (c', ("<> " ++ col Dull Blue (show_id id)) : ["  ║  "] ++ concat (indentInfChildren [s1]))

show_id :: NodeId -> String
show_id (k, alt) = "#" ++ show k ++ ":" ++ show alt

show_dd :: (HasNodeLookup c) => Show_setting -> c -> Node -> String
show_dd s c (d_id, d) = case d of
  Leaf True  -> if color s then colorize "soft green" "1" else "1"
  Leaf False -> if color s then colorize "soft red" "0" else "0"
  Unknown    -> if color s then colorize "purple" "." else "."
  Node i rC lC -> colorize "orange" (show i) ++ " (" ++ show_dd s c (getNode c rC) ++ ") (" ++ show_dd s c (getNode c lC) ++ ")"
  InfNodes i dc p n -> colorize "chill blue" (show i) ++ " <" ++ show_dd s c (getNode c dc) ++ "," ++ show_dd s c (getNode c p) ++ "," ++ show_dd s c (getNode c n) ++ ">"
  EndInfNode child -> "<>" ++ show_dd s c (getNode c child)

-- ==========================================================================================================
-- * Debugging Trace
-- ==========================================================================================================

myTrace :: String -> a -> a
myTrace msg x = unsafePerformIO $ do
    msg `deepseq` return (trace msg x)