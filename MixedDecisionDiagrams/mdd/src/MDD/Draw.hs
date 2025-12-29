{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module MDD.Draw where

import MDD.Types
import MDD.Context
import MDD.Manager
import MDD.Construction
import qualified Data.HashMap.Strict as HashMapStrict

import System.IO
import System.Console.ANSI
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashMap.Strict as HashMapStrict
import qualified Data.Map as Map
import Data.List (intercalate, sortBy, groupBy, foldl')
import Data.Function (on)
import Data.Ord (comparing)
import Debug.Trace (trace)
import GHC.IO (unsafePerformIO)
import Control.DeepSeq (deepseq)
import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode(..))
import System.FilePath ((</>))
import System.Directory (getCurrentDirectory)
import Control.Monad (when)
import Control.Monad.Cont (Cont)
import qualified Data.Set as Set
import Data.Graph hiding (Node)
import Data.Maybe

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
                color = True -- colorize
            ,   draw_tree = False
            ,   display_node_id's = False -- show node_id's
            ,   display_context = False
            ,   display_leaf_cases = False
            ,   display_end_infs = True
            ,   display_dc_traversal = False

            ,   debug_on = True
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

appLast :: [String] -> String -> [String]
appLast ss s = init ss ++ [last ss ++ s]

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

showTree' c f d@(nid, InfNodes a dc (0,0) (0,0)) = withCache' c' d $
    ("<"++ f a ++ "> dc " ++ col Dull Blue (show_id nid)) : "  ║  " :
    concat (indentInfChildren [s1])
    where
        (c', s1) = showTree' c f (getNode c dc)
showTree' c f d@(nid, InfNodes a dc p (0, 0)) = withCache' c'' d $
    ("<"++ f a ++ "> dc, p " ++ col Dull Blue (show_id nid)) : "  ║  " :
    concat (indentInfChildren [s1, s2])
    where
        (c', s1) = showTree' c f (getNode c dc)
        (c'', s2) = showTree' c' f (getNode c' p)
showTree' c f d@(nid, InfNodes a dc (0, 0) n) = withCache' c'' d $
    ("<"++ f a ++ "> dc, n " ++ col Dull Blue (show_id nid)) : "  ║  " :
    concat (indentInfChildren [s1, r_p1])
    where
        (c', s1) = showTree' c f (getNode c dc)
        (c'', r_p1) = showTree' c' f (getNode c' n)
showTree' c f d@(nid, InfNodes a dc p n) = withCache' c''' d $
    ("<"++ f a ++ "> dc, p, n " ++ col Dull Blue (show_id nid)) : "  ║  " :
    concat (indentInfChildren [s1, r_p, r_n])
    where
        (c', r_p) = showTree' c f (getNode c p)
        (c'', s1) = showTree' c' f (getNode c' dc)
        (c''', r_n) = showTree' c'' f (getNode c'' n)

showTree' c f d@(nid, EndInfNode cons) =
    let (c', s1) = showTree' c f (getNode c cons)
        res = ("<> " ++ col Dull Blue (show_id nid)) : "  ║  " : concat (indentInfChildren [s1])
    in withCache' c' d res

showTree :: MDD -> String
showTree (MDD (nl, node)) = "\n" ++ unlines (showTree'' (init_draw_context nl) show node)

showTree2 :: MDD -> String
showTree2 (MDD (nl, node)) = unlines (showTree'' (init_draw_context nl) show node)

showTree3 :: MDD -> String
showTree3 (MDD (nl, node)) = unlines (showTree'' (init_draw_context nl) show node)

drawTree2 :: MDD -> IO ()
drawTree2 mdd = putStrLn (showTree2 mdd)

drawTree3 :: MDD -> IO ()
drawTree3 mdd = putStrLn (showTree mdd)

-- ==========================================================================================================
-- * String Representation
-- ==========================================================================================================

show_id :: NodeId -> String
show_id (k, alt) = "#" ++ show k ++ ":" ++ show alt

show_id' :: Node -> String
show_id' (nid, _) = show_id nid

show_context :: (HasNodeLookup c) => c -> String
show_context c = show (getLookup c)

show_dd :: (HasNodeLookup c) => Show_setting -> c -> Node -> String
show_dd s@ShowSetting{display_context=True} c d = show_context c ++ show_dd s{display_context=False} c d
show_dd ShowSetting{draw_tree=True} _ _ = "Tree drawing requested but logic not linked here."
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
    show_i i clr = (if display_node_id's s then (if color s then colorize "blue" ("#" ++ show d_id) else ("#" ++ show d_id)) ++ " " else "")
      ++ (if color s then colorize clr (show i) else show i)

-- ==========================================================================================================
-- * Debugging Logic
-- ==========================================================================================================

check_length :: BinaryOperatorContext -> Bool
check_length ctx@BinaryOperatorContext{bin_dc_stack=(dcAs, dcBs, _), bin_current_level=(lvAs, lvBs)}
    | length dcAs > length lvAs = False
    | length dcBs > length lvBs = False
    | otherwise = True

debug_manipulation :: (BinaryOperatorContext, Node) -> String -> String -> BinaryOperatorContext -> Node -> Node -> (BinaryOperatorContext, Node)
debug_manipulation result_pair f_key f_name old_c@BinaryOperatorContext{bin_cache = nc, bin_dc_stack=dcs} a@(a_id, a_d) b@(b_id, b_d)
    | getDd old_c a_id == a_d && getDd old_c b_id == b_d = if not $ save_logs settings then
    let
    leaf_msg = colorize "orange" (">> " ++ f_name ++ " : ") ++
                    "\n  ->   " ++ show_dd settings old_c a ++
                    "\n  ->   " ++ show_dd settings old_c b ++ "\n"
    (c,r) = if debug_on settings && debug_open settings && check_skip_display a_id b_id
            then if debug_dc_stack settings
                then myTrace (leaf_msg ++ display_func_stack old_c) result_pair
                else myTrace leaf_msg result_pair
            else result_pair
    in
    if debug_on settings && debug_close settings && check_skip_display a_id b_id
        then if a_id `elem` [l_1, l_0] || b_id `elem` [l_1, l_0]
            then if not $ display_leaf_cases settings
                then (c{bin_dc_stack=dcs}, r)
                else myTrace (colorize "green" (f_name ++ " : ") ++
                    "\n  " ++ show_dd settings c a ++
                    " : " ++ show_dd settings c b ++
                    " = " ++ show_dd settings c r ++ " " ++ col Dull Blue (show_id' r) ++
                    "\n") (c, r)
            else
            myTrace (
            case Map.lookup f_key nc of
                Just nc' -> case HashMapStrict.lookup (a_id, b_id, dcs) nc' of
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
            ) (c{bin_dc_stack=dcs}, r)
        else (c{bin_dc_stack=dcs}, r)
    else
    let
    start_msg = ("\\n" ++ colorize "orange" "  ->   " ++ show_dd settings old_c a) ++
                ("\\n" ++ colorize "orange" "  ->   " ++ show_dd settings old_c b ++ "\\n")
    (c,r) = if check_skip_display a_id b_id
            then myDebugLog "\"inner\":[" result_pair
            else result_pair
    in
    if check_skip_display a_id b_id
        then myDebugLog ("{\"" ++ colorize "green" f_name ++"\": {" ++ "\"func_stack before\": [\"" ++ show_dc_stack_str old_c ++ "\"],\n\"input\": \"" ++ start_msg ++ "\",\n") $
            case Map.lookup f_key nc of
                Just nc' -> case HashMapStrict.lookup (a_id, b_id, dcs) nc' of
                    Just rt -> myDebugLog ("],\n\"" ++ colorize "chill blue" "found cached result"++"\":\"" ++ col Vivid Blue (show_id rt) ++ " for " ++ "\\n" ++ colorize "green" "  =>   "
                        ++ show_dd settings c (getNode c rt) ++ "\\n\"}},") (old_c, (getNode old_c rt))
                    Nothing ->
                        myDebugLog ("],\n\"result\": \"\\n" ++ colorize "green" "  =>   " ++ show_dd settings c r ++ " " ++ col Vivid Blue (show_id' r)
                        ++ "\\n\"}},") (c{bin_dc_stack=dcs}, r)
                Nothing -> error ("wrong function name in cache lookup: " ++ show f_key)
        else (c{bin_dc_stack=dcs}, r)
    | otherwise = error ("id and dd are not equal, \n a_id: " ++ show (getDd old_c a_id) ++ "\n a: " ++ show a ++ "\n b_id: " ++ show (getDd old_c b_id) ++ " \n b: " ++ show b )

show_dc_stack_str :: BinaryOperatorContext -> String
show_dc_stack_str ctx = show (bin_dc_stack ctx)

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

-- | Debug wrapper for unary operations (similar to debug_manipulation for binary operations).
-- | Provides debugging output for restrict_node_set and other unary operations.
debug_manipulation_unary :: (UnaryOperatorContext, Node) -> String -> String -> UnaryOperatorContext -> Node -> [Position] -> Bool -> (UnaryOperatorContext, Node)
debug_manipulation_unary result_pair f_key f_name old_c@UnaryOperatorContext{un_cache = nc, un_dc_stack=dcs} a@(a_id, a_d) nas b_val
    | getDd old_c a_id == a_d = if not $ save_logs settings then
    let
    leaf_msg = colorize "orange" (">> " ++ f_name ++ " : ") ++
                    "\n  ->   " ++ show_dd settings old_c a ++
                    "\n  ->   restrict: " ++ show nas ++ " to " ++ show b_val ++ "\n"
    (c,r) = if debug_on settings && debug_open settings && check_skip_display_unary a_id
            then if debug_dc_stack settings
                then myTrace (leaf_msg ++ display_func_stack_unary old_c) result_pair
                else myTrace leaf_msg result_pair
            else result_pair
    in
    if debug_on settings && debug_close settings && check_skip_display_unary a_id
        then if a_id `elem` [l_1, l_0]
            then if not $ display_leaf_cases settings
                then (c{un_dc_stack=dcs}, r)
                else myTrace (colorize "green" (f_name ++ " : ") ++
                    "\n  " ++ show_dd settings c a ++
                    " (restrict: " ++ show nas ++ " to " ++ show b_val ++ ")" ++
                    " = " ++ show_dd settings c r ++ " " ++ col Dull Blue (show_id' r) ++
                    "\n") (c, r)
            else
            myTrace (
            case HashMap.lookup a_id nc of
                Just rt -> colorize "chill blue" "found cached result : " ++ col Dull Blue (show_id rt) ++ " for "
                    ++ colorize "green" (f_name ++ " : ") ++
                    (if not $ debug_shorten_close settings then
                        "\n  ->   " ++ show_dd settings c a ++
                        "\n  ->   restrict: " ++ show nas ++ " to " ++ show b_val
                    else "") ++
                    "\n  =>   " ++ show_dd settings c r ++
                    "\n"
                Nothing ->
                    colorize "green" (f_name ++ " : ") ++
                    (if not $ debug_shorten_close settings then
                        "\n  ->   " ++ show_dd settings c a ++
                        "\n  ->   restrict: " ++ show nas ++ " to " ++ show b_val
                    else "") ++
                    "\n  =>   " ++ show_dd settings c r ++ " " ++ col Dull Blue (show_id' r) ++
                    "\n"
            ) (c{un_dc_stack=dcs}, r)
        else (c{un_dc_stack=dcs}, r)
    else
    let
    start_msg = ("\\n" ++ colorize "orange" "  ->   " ++ show_dd settings old_c a) ++
                ("\\n" ++ colorize "orange" "  ->   restrict: " ++ show nas ++ " to " ++ show b_val ++ "\\n")
    (c,r) = if check_skip_display_unary a_id
            then myDebugLog "\"inner\":[" result_pair
            else result_pair
    in
    if check_skip_display_unary a_id
        then myDebugLog ("{\"" ++ colorize "green" f_name ++"\": {" ++ "\"func_stack before\": [\"" ++ show_dc_stack_str_unary old_c ++ "\"],\n\"input\": \"" ++ start_msg ++ "\",\n") $
            case HashMap.lookup a_id nc of
                Just rt -> myDebugLog ("],\n\"" ++ colorize "chill blue" "found cached result"++"\":\"" ++ col Vivid Blue (show_id rt) ++ " for " ++ "\\n" ++ colorize "green" "  =>   "
                    ++ show_dd settings c (getNode c rt) ++ "\\n\"}},") (old_c, (getNode old_c rt))
                Nothing ->
                    myDebugLog ("],\n\"result\": \"\\n" ++ colorize "green" "  =>   " ++ show_dd settings c r ++ " " ++ col Vivid Blue (show_id' r)
                    ++ "\\n\"}},") (c{un_dc_stack=dcs}, r)
        else (c{un_dc_stack=dcs}, r)
    | otherwise = error ("id and dd are not equal, \n a_id: " ++ show (getDd old_c a_id) ++ "\n a: " ++ show a)

show_dc_stack_str_unary :: UnaryOperatorContext -> String
show_dc_stack_str_unary ctx = show (un_dc_stack ctx)

display_func_stack_unary :: UnaryOperatorContext -> String
display_func_stack_unary c@UnaryOperatorContext{un_dc_stack = dcs} = let
            dcRs' = intercalate separator1 $ map (show_dd settings c) dcs
            separator1 = " , \n"
        in
            (if display_level settings then colorize "purple" "func level : " ++ show (un_current_level c) else "") ++
            (if display_dcRs settings then colorize "blue" "\n DcR : \n" ++ dcRs' else "") ++ "\n"

debug_func :: String -> (BinaryOperatorContext, Node) -> (BinaryOperatorContext, Node)
debug_func f_name f = if save_logs settings
    then myDebugLog ("{\"" ++ colorize "orange" f_name ++ "\" : [") (myDebugLog ("\n{\""++ "context" ++ "\" : [\"" ++ show_context (fst f) ++ "\"]}\n]},") f)
    else if debug_on settings
        then myTrace ("{\"" ++ colorize "orange" f_name ++ "\" : [") (myTrace ("\n{\""++ "context" ++ "\" : [\"" ++ show_context (fst f) ++ "\"]}\n]},") f)
        else f

debug_dc_traverse :: String -> BinaryOperatorContext -> NodeId -> NodeId -> BinaryOperatorContext -> BinaryOperatorContext
debug_dc_traverse s c a b f = if display_dc_traversal settings && debug_on settings
    then myTrace (colorize "purple" "dc_traverse" ++ ", for arguments: " ++ s ++ " a: " ++ show_dd settings c (getNode c a) ++ "  b: " ++ show_dd settings c (getNode c b))
        (myTrace (display_func_stack' c f ++ "\n\n") f)
    else f

display_func_stack' :: BinaryOperatorContext -> BinaryOperatorContext -> String
display_func_stack' old_c@BinaryOperatorContext{bin_dc_stack = dcs} new_c@BinaryOperatorContext{bin_dc_stack = new_dcs} = let
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

display_func_stack :: BinaryOperatorContext -> String
display_func_stack c@BinaryOperatorContext{bin_dc_stack = dcs} = let
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

jsonwrap :: String -> String -> String
jsonwrap k v = "{ \""++ k ++    "\": \"" ++ v ++ "\" }"

show_a_b :: (HasNodeLookup c) => c -> Node -> Node -> String
show_a_b c a b = "\\n  ->   " ++ show_dd settings c a ++ "\\n  ->   " ++ show_dd settings c b


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

debug5 :: Bool -> String -> Bool
debug5 b s = trace (colorize "red" (s ++ "\n\n")) b

debug :: a -> String -> a
debug f s = trace (colorize "green" (s ++ "\n\n")) f