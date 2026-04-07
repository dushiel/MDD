{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module MDD.Extra.Draw where

import MDD.Types
import MDD.Traversal.Context
import MDD.NodeLookup
import MDD.Construction
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashMap.Strict as HashMapStrict
import qualified Data.Map as Map
import Data.List (intercalate)
import System.Console.ANSI
import Debug.Trace (trace)
import GHC.IO (unsafePerformIO)
import Control.DeepSeq (deepseq)


-- | Module for drawing and debugging Mixed Decision Diagrams (MDDs).
-- Provides tree visualization, string representation, and debug output utilities.

-- * Debugging and Drawing Configuration
-- * refactored with AI

data Show_setting = ShowSetting {
  color :: Bool,
  display_node_id's :: Bool,
  draw_tree :: Bool,
  display_context :: Bool,
  display_leaf_cases :: Bool,
  display_end_infs :: Bool,
  display_dc_traversal :: Bool,
  debug_on :: Bool,
  debug_open :: Bool,
  debug_close :: Bool,
  debug_shorten_close :: Bool,
  debug_dc_stack :: Bool,
  display_level :: Bool,
  display_dcAs :: Bool,
  display_dcBs :: Bool,
  display_dcRs :: Bool
}


-- | Global settings for display and debugging behavior
settings :: Show_setting
settings = ShowSetting {
                color = False -- colorize
            ,   draw_tree = False
            ,   display_node_id's = False
            ,   display_context = False
            ,   display_leaf_cases = True
            ,   display_end_infs = True
            ,   display_dc_traversal = False

            ,   debug_on = False

            ,   debug_open = True
            ,   debug_close = True
            ,   debug_shorten_close = False

            ,   debug_dc_stack = False
            ,   display_level = False
            ,   display_dcAs = False
            ,   display_dcBs = False
            ,   display_dcRs = False
}

-- * Color Utilities

-- | Apply ANSI color with specified intensity to a string
col :: ColorIntensity -> Color -> String -> String
col i c s = setSGRCode [SetColor Foreground i c] ++ s ++ setSGRCode [Reset]

-- | Apply a named color to a string using 24-bit color codes
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

-- | Generate 24-bit ANSI color escape sequence
setColor24bit :: Int -> Int -> Int -> String
setColor24bit r g b = "\ESC[38;2;" ++ show r ++ ";" ++ show g ++ ";" ++ show b ++ "m"

-- | ANSI reset color escape sequence
resetColor :: String
resetColor = "\ESC[0m"

-- * Tree Visualization

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

-- | Internal helper to handle the draw cache during tree traversal
withCache' :: DrawOperatorContext -> Node -> [String] -> (DrawOperatorContext, [String])
withCache' c (nid, _) res = (c { draw_cache = HashMap.insert nid res (draw_cache c) }, res)

showTree'' :: DrawOperatorContext -> (Int -> String) -> Node -> [String]
showTree'' a b c = snd $ showTree' a b c

showTree' :: DrawOperatorContext -> (Int -> String) -> Node -> (DrawOperatorContext, [String])
showTree' c _ (_, Unknown) = (c, ["[.]"])
showTree' c _ (_, Leaf True) = (c, ["[1]"])
showTree' c _ (_, Leaf False) = (c, ["[0]"])
showTree' c f d@(nid, Node a l r) =
    let (c', s1) = showTree' c f (getNode c l)
        (c'', s2) = showTree' c' f (getNode c' r)
        res = ("("++ f a ++") " ++ col Dull Blue (show_id nid)) : concat (indentChildren [s1, s2])
    in withCache' c'' d res

showTree' c f d@(nid, ClassNode a dc (0,0) (0,0)) = withCache' c' d $
    ("<"++ f a ++ "> dc " ++ col Dull Blue (show_id nid)) : "  ║  " :
    concat (indentInfChildren [s1])
    where
        (c', s1) = showTree' c f (getNode c dc)
showTree' c f d@(nid, ClassNode a dc p (0, 0)) = withCache' c'' d $
    ("<"++ f a ++ "> dc, p " ++ col Dull Blue (show_id nid)) : "  ║  " :
    concat (indentInfChildren [s1, s2])
    where
        (c', s1) = showTree' c f (getNode c dc)
        (c'', s2) = showTree' c' f (getNode c' p)
showTree' c f d@(nid, ClassNode a dc (0, 0) n) = withCache' c'' d $
    ("<"++ f a ++ "> dc, n " ++ col Dull Blue (show_id nid)) : "  ║  " :
    concat (indentInfChildren [s1, r_p1])
    where
        (c', s1) = showTree' c f (getNode c dc)
        (c'', r_p1) = showTree' c' f (getNode c' n)
showTree' c f d@(nid, ClassNode a dc p n) = withCache' c''' d $
    ("<"++ f a ++ "> dc, p, n " ++ col Dull Blue (show_id nid)) : "  ║  " :
    concat (indentInfChildren [s1, r_p, r_n])
    where
        (c', r_p) = showTree' c f (getNode c p)
        (c'', s1) = showTree' c' f (getNode c' dc)
        (c''', r_n) = showTree' c'' f (getNode c'' n)

showTree' c f d@(nid, EndClassNode cons) =
    let (c', s1) = showTree' c f (getNode c cons)
        res = ("<> " ++ col Dull Blue (show_id nid)) : "  ║  " : concat (indentInfChildren [s1])
    in withCache' c' d res

showTree :: MDD -> String
showTree (MDD (nl, node)) = "\n" ++ unlines (showTree'' (init_draw_context nl) show node)

-- | Print an MDD tree structure to stdout
drawTree3 :: MDD -> IO ()
drawTree3 mdd = putStrLn (showTree mdd)

-- * String Representation

show_id :: NodeId -> String
show_id (k, alt) = "#" ++ show k ++ ":" ++ show alt

show_id' :: Node -> String
show_id' (nid, _) = show_id nid

show_context :: (HasNodeLookup c) => c -> String
show_context c = show (getLookup c)

show_dd :: (HasNodeLookup c) => Show_setting -> c -> Node -> String
show_dd s@ShowSetting{display_context=True} c d = show_context c ++ show_dd s{display_context=False} c d
show_dd ShowSetting{draw_tree=True} _ _ = "Tree drawing requested but logic not linked here."
show_dd s _ (_, Unknown) = ""
--   | color s = "[" ++ colorize "purple" "." ++ "]"
--   | otherwise = "[.]"
show_dd s _ (_, Leaf False)
  | color s = "[" ++ colorize "soft red" "0" ++ "]"
  | otherwise = "[0]"
show_dd s _ (_, Leaf True)
  | color s = "[" ++ colorize "soft green" "1" ++ "]"
  | otherwise = "[1]"
show_dd s c (d_id, d) = case d of
  Node i rC lC -> show_i i "orange" ++ " (" ++ show_dd s c (getNode c rC) ++ ") (" ++ show_dd s c (getNode c lC) ++ ")"
  ClassNode i dc p n -> show_i i "chill blue" ++ " <{dc: " ++ show_dd s c (getNode c dc) ++ "} {p: " ++ show_dd s c (getNode c p) ++ "} {n: " ++ show_dd s c (getNode c n) ++ "}"
  EndClassNode child -> (if color s then colorize "chill blue" "<>" else "<>") ++ show_dd s c (getNode c child)
  _ -> error "should not be possible"
  where
    show_i i clr = (if display_node_id's s then (if color s then colorize "blue" ("#" ++ show d_id) else ("#" ++ show d_id)) ++ " " else "")
      ++ (if color s then colorize clr (show i) else show i)

-- * Debugging

-- ** Debug Message Formatting Helpers

-- | Helper to format opening debug message for binary operations
format_debug_open_binary :: String -> String -> BiOpContext -> Node -> Node -> String
format_debug_open_binary f_name suffix old_c a b =
    colorize "orange" (">> " ++ f_name ++ suffix ++ " : ") ++
    "\n  ->   " ++ show_dd settings old_c a ++
    "\n  ->   " ++ show_dd settings old_c b ++ "\n"

-- | Helper to format opening debug message for unary operations
format_debug_open_unary :: String -> UnOpContext -> Node -> [Position] -> Bool -> String
format_debug_open_unary f_name old_c a nas b_val =
    colorize "orange" (">> " ++ f_name ++ " : ") ++
    "\n  ->   " ++ show_dd settings old_c a ++
    "\n  ->   restrict: " ++ show nas ++ " to " ++ show b_val ++ "\n"

-- | Helper to format closing debug message for binary operations
format_debug_close_binary :: String -> String -> BiOpContext -> Node -> Node -> Node -> String
format_debug_close_binary f_name suffix c a b r =
    colorize "green" (f_name ++ suffix ++ " : ") ++
    "\n  " ++ show_dd settings c a ++
    " : " ++ show_dd settings c b ++
    " = " ++ show_dd settings c r ++ " " ++ col Dull Blue (show_id' r) ++
    "\n"

-- | Helper to format closing debug message for unary operations
format_debug_close_unary :: String -> UnOpContext -> Node -> [Position] -> Bool -> Node -> String
format_debug_close_unary f_name c a nas b_val r =
    colorize "green" (f_name ++ " : ") ++
    "\n  " ++ show_dd settings c a ++
    " (restrict: " ++ show nas ++ " to " ++ show b_val ++ ")" ++
    " = " ++ show_dd settings c r ++ " " ++ col Dull Blue (show_id' r) ++
    "\n"

-- | Helper to format cache lookup result message for binary operations
format_cache_result_binary :: String -> String -> BiOpContext -> Node -> Node -> Node -> Maybe NodeId -> String
format_cache_result_binary f_name suffix c a b r mCached =
    case mCached of
        Just rt -> colorize "chill blue" "found cached result : " ++ col Dull Blue (show_id rt) ++ " for "
            ++ colorize "green" (f_name ++ suffix ++ " : ") ++
            (if not $ debug_shorten_close settings then
                "\n  ->   " ++ show_dd settings c a ++
                "\n  ->   " ++ show_dd settings c b
            else "") ++
            "\n  =>   " ++ show_dd settings c r ++
            "\n"
        Nothing -> colorize "green" (f_name ++ suffix ++ " : ") ++
            (if not $ debug_shorten_close settings then
                "\n  ->   " ++ show_dd settings c a ++
                "\n  ->   " ++ show_dd settings c b
            else "") ++
            "\n  =>   " ++ show_dd settings c r ++ " " ++ col Dull Blue (show_id' r) ++
            "\n"

-- | Helper to format cache lookup result message for unary operations
format_cache_result_unary :: String -> UnOpContext -> Node -> [Position] -> Bool -> Node -> Maybe NodeId -> String
format_cache_result_unary f_name c a nas b_val r mCached =
    case mCached of
        Just rt -> colorize "chill blue" "found cached result : " ++ col Dull Blue (show_id rt) ++ " for "
            ++ colorize "green" (f_name ++ " : ") ++
            (if not $ debug_shorten_close settings then
                "\n  ->   " ++ show_dd settings c a ++
                "\n  ->   restrict: " ++ show nas ++ " to " ++ show b_val
            else "") ++
            "\n  =>   " ++ show_dd settings c r ++
            "\n"
        Nothing -> colorize "green" (f_name ++ " : ") ++
            (if not $ debug_shorten_close settings then
                "\n  ->   " ++ show_dd settings c a ++
                "\n  ->   restrict: " ++ show nas ++ " to " ++ show b_val
            else "") ++
            "\n  =>   " ++ show_dd settings c r ++ " " ++ col Dull Blue (show_id' r) ++
            "\n"

-- ** Debug Manipulation Functions

-- | Debug wrapper for binary operations on decision diagrams
debug_manipulation :: (BiOpContext, Node) -> String -> String -> BiOpContext -> Node -> Node -> (BiOpContext, Node)
debug_manipulation result_pair f_key f_name old_c@BCxt{bin_cache = nc, bin_dc_stack=dcs} a@(a_id, a_d) b@(b_id, b_d)
    | getDd old_c a_id == a_d && getDd old_c b_id == b_d =
    let
        leaf_msg = format_debug_open_binary f_name "" old_c a b
        (c,r) = if debug_on settings && debug_open settings && check_skip_display a_id b_id
                then if debug_dc_stack settings
                    then myTrace (leaf_msg ++ display_func_stack old_c) result_pair
                    else myTrace leaf_msg result_pair
                else result_pair
        should_skip = a_id `elem` [l_1, l_0] || b_id `elem` [l_1, l_0]
        mCached = Map.lookup f_key nc >>= \nc' -> HashMapStrict.lookup (a_id, b_id, dcs) nc'
    in
    if debug_on settings && debug_close settings && check_skip_display a_id b_id
        then if should_skip
            then if not $ display_leaf_cases settings
                then (c{bin_dc_stack=dcs}, r)
                else myTrace (format_debug_close_binary f_name "" c a b r) (c, r)
            else myTrace (format_cache_result_binary f_name "" c a b r mCached) (c{bin_dc_stack=dcs}, r)
        else (c{bin_dc_stack=dcs}, r)
    | otherwise = error ("id and dd are not equal, \n a_id: " ++ show (getDd old_c a_id) ++ "\n a: " ++ show a ++ "\n b_id: " ++ show (getDd old_c b_id) ++ " \n b: " ++ show b )

debug_manipulation_inf :: (BiOpContext, Node) -> String -> String -> BiOpContext -> Node -> Node -> (BiOpContext, Node)
debug_manipulation_inf result_pair f_key f_name old_c@BCxt{bin_cache = nc, bin_dc_stack=dcs} a@(a_id, a_d) b@(b_id, b_d)
    | getDd old_c a_id == a_d && getDd old_c b_id == b_d =
    let
        leaf_msg = format_debug_open_binary f_name " (INF)" old_c a b
        (c,r) = if debug_on settings && debug_open settings && check_skip_display a_id b_id
                then if debug_dc_stack settings
                    then myTrace (leaf_msg ++ display_func_stack old_c) result_pair
                    else myTrace leaf_msg result_pair
                else result_pair
        should_skip = a_id `elem` [l_1, l_0] || b_id `elem` [l_1, l_0]
        mCached = Map.lookup f_key nc >>= \nc' -> HashMapStrict.lookup (a_id, b_id, dcs) nc'
    in
    if debug_on settings && debug_close settings && check_skip_display a_id b_id
        then if should_skip
            then if not $ display_leaf_cases settings
                then (c{bin_dc_stack=dcs}, r)
                else myTrace (format_debug_close_binary f_name " (INF)" c a b r) (c, r)
            else myTrace (format_cache_result_binary f_name " (INF)" c a b r mCached) (c{bin_dc_stack=dcs}, r)
        else (c{bin_dc_stack=dcs}, r)
    | otherwise = error ("id and dd are not equal, \n a_id: " ++ show (getDd old_c a_id) ++ "\n a: " ++ show a ++ "\n b_id: " ++ show (getDd old_c b_id) ++ " \n b: " ++ show b )

-- ** Debug Display Control

check_skip_display :: NodeId -> NodeId -> Bool
check_skip_display a_id b_id =
    debug_on settings &&
    not (a_id `elem` [l_1, l_0] && b_id `elem` [l_1, l_0]) &&
    not (a_id == l_u && b_id == l_u) &&
    not ((a_id `elem` [l_1, l_0] || b_id `elem` [l_1, l_0]) && not (display_leaf_cases settings))

check_skip_display_unary :: NodeId -> Bool
check_skip_display_unary a_id =
    debug_on settings &&
    not (a_id `elem` [l_1, l_0]) &&
    not (a_id == l_u) &&
    not (a_id `elem` [l_1, l_0] && not (display_leaf_cases settings))


debug_manipulation_unary :: (UnOpContext, Node) -> String -> String -> UnOpContext -> Node -> [Position] -> Bool -> (UnOpContext, Node)
debug_manipulation_unary result_pair f_key f_name old_c@UCxt{un_cache = nc, un_dc_stack=dcs} a@(a_id, a_d) nas b_val
    | getDd old_c a_id == a_d =
    let
        leaf_msg = format_debug_open_unary f_name old_c a nas b_val
        (c,r) = if debug_on settings && debug_open settings && check_skip_display_unary a_id
                then if debug_dc_stack settings
                    then myTrace (leaf_msg ++ display_func_stack_unary old_c) result_pair
                    else myTrace leaf_msg result_pair
                else result_pair
        should_skip = a_id `elem` [l_1, l_0]
        mCached = HashMap.lookup a_id nc
    in
    if debug_on settings && debug_close settings && check_skip_display_unary a_id
        then if should_skip
            then if not $ display_leaf_cases settings
                then (c{un_dc_stack=dcs}, r)
                else myTrace (format_debug_close_unary f_name c a nas b_val r) (c, r)
            else myTrace (format_cache_result_unary f_name c a nas b_val r mCached) (c{un_dc_stack=dcs}, r)
        else (c{un_dc_stack=dcs}, r)
    | otherwise = error ("id and dd are not equal, \n a_id: " ++ show (getDd old_c a_id) ++ "\n a: " ++ show a)

-- ** Function Stack Display

display_func_stack_unary :: UnOpContext -> String
display_func_stack_unary c@UCxt{un_dc_stack = dcs} = let
            dcRs' = intercalate separator1 $ map (show_dd settings c) dcs
            separator1 = " , \n"
        in
            (if display_level settings then colorize "purple" "func level : " ++ show (un_current_level c) else "") ++
            (if display_dcRs settings then colorize "blue" "\n DcR : \n" ++ dcRs' else "") ++ "\n"

-- | Debug wrapper for function entry/exit
debug_func :: String -> (BiOpContext, Node) -> (BiOpContext, Node)
debug_func f_name f = if debug_on settings
    then myTrace ("{\"" ++ colorize "orange" f_name ++ "\" : [") (myTrace ("\n{\""++ "context" ++ "\" : [\"" ++ show_context (fst f) ++ "\"]}\n]},") f)
    else f

debug_dc_traverse :: String -> BiOpContext -> NodeId -> NodeId -> BiOpContext -> BiOpContext
debug_dc_traverse s c a b f = if display_dc_traversal settings && debug_on settings
    then myTrace (colorize "purple" "dc_traverse" ++ ", for arguments: " ++ s ++ " a: " ++ show_dd settings c (getNode c a) ++ "  b: " ++ show_dd settings c (getNode c b))
        (myTrace (display_func_stack' c f ++ "\n\n") f)
    else f

display_func_stack' :: BiOpContext -> BiOpContext -> String
display_func_stack' old_c@BCxt{bin_dc_stack = dcs} new_c@BCxt{bin_dc_stack = new_dcs} = let
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
            (if display_level settings then colorize "purple" "func stack : " ++ show (bin_current_level old_c) ++ colorize "blue" "func stack : " ++ show (bin_current_level new_c) else "") ++
            (if display_dcAs settings then colorize "orange" "\n- DcA old : \n  " ++ old_dcAs ++ colorize "green" "\n  DcA new : \n  " ++ new_dcAs else "") ++
            (if display_dcBs settings then colorize "orange" "\n- DcB old : \n  " ++ old_dcBs ++ colorize "green" "\n  DcB new : \n  " ++ new_dcBs else "") ++
            (if display_dcRs settings then colorize "orange" "\n- DcR old : \n  " ++ old_dcRs ++ colorize "green" "\n  DcR new : \n  " ++ new_dcRs else "")

display_func_stack :: BiOpContext -> String
display_func_stack c@BCxt{bin_dc_stack = dcs} = let
            (dcAs, dcBs, dcRs) = dcs
            dcAs' = intercalate separator1 $ map (show_dd settings c) dcAs
            dcBs' = intercalate separator1 $ map (show_dd settings c) dcBs
            dcRs' = intercalate separator1 $ map (show_dd settings c) dcRs
            separator1 = " , \n"
        in
            (if display_level settings then colorize "purple" "func level : " ++ show (bin_current_level c) else "") ++
            (if display_dcAs settings then colorize "blue" "\n DcA : \n" ++ dcAs' else "") ++
            (if display_dcBs settings then colorize "blue" "\n DcB : \n" ++ dcBs' else "") ++
            (if display_dcRs settings then colorize "blue" "\n DcR : \n" ++ dcRs' else "") ++ "\n"

-- * Utility Functions

-- | Trace function that ensures message is evaluated
myTrace :: String -> a -> a
myTrace msg x = unsafePerformIO $ do
    msg `deepseq` return (trace msg x)

debug5 :: Bool -> String -> Bool
debug5 b s = trace (colorize "red" (s ++ "\n\n")) b

debug :: a -> String -> a
debug f s = trace (colorize "green" (s ++ "\n\n")) f

show_node :: (HasNodeLookup c) => c -> Node -> String
show_node c n = show_dd settings c n

show_mdd :: MDD -> String
show_mdd mdd = let
    (c, n) = unMDD mdd
    in show_dd settings c n