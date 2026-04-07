{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module DrawMDD where
import MDD
import System.IO
-- import Test.Hspec
import qualified Data.Map as Map
import Data.Hashable
import GHC.IO (unsafePerformIO)
import GHC.IO.Encoding (TextEncoding(textEncodingName))
import Data.Char (GeneralCategory(EnclosingMark))
import System.IO (appendFile, hFlush, stdout, withFile, IOMode (AppendMode), hPutStrLn)
import Control.DeepSeq (deepseq)
import System.Console.ANSI
    ( setSGRCode,
      Color(Blue, Red, Green),
      ColorIntensity(Vivid, Dull),
      ConsoleLayer(Foreground),
      SGR(Reset, SetColor) )

import System.Console.ANSI
import qualified Data.HashMap.Lazy as HashMap
import Debug.Trace (trace)

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

showTree0' :: Context -> (Int -> String) -> Dd -> (Context, [String])
showTree0' c _ (Leaf True) = (c, ["   "])
showTree0' c _ (Leaf False) = (c, ["[0]"])
showTree0' c f d@(Node a l r) = withCache' c'' (snd $ insert c d) $ (("("++ f a ++")") ++ col Dull Blue (show_id (snd $ insert c d))) : concat (indentChildren [s1, s2])
    where
    (c', s1) = showTree0' c f (getDd c l)
    (c'',s2) = showTree0' c' f (getDd c r)
showTree0' c f x = showTree' c f x

showTree1' :: Context -> (Int -> String) -> Dd -> (Context, [String])
showTree1' c _ (Leaf True) = (c, ["[1]"])
showTree1' c _ (Leaf False) = (c, ["   "])
showTree1' c f d@(Node a l r) = withCache' c'' (snd $ insert c d) $ (("("++ f a ++")") ++ col Dull Blue (show_id (snd $ insert c d))) : concat (indentChildren [s1, s2])
    where
    (c', s1) = showTree1' c f (getDd c l)
    (c'',s2) = showTree1' c' f (getDd c r)
showTree1' c f x = showTree' c f x


-- take_c_show :: (Context, [String]) -> (Context -> NodeId -> (Context, [String])) -> (Context, NodeId) -> (Context, [String])
-- take_c_show (c, _) f (_,a) = f c a
showTree'' :: Context -> (Int -> String) -> Dd -> [String]
showTree'' a b c = snd $ showTree' a b c

showTree' :: Context -> (Int -> String) -> Dd -> (Context, [String])
--showTree' (Node n ns) = n : concat (indentChildren (map showTree' ns))

showTree' c _ (Leaf True) = (c, ["[1]"])
showTree' c _ (Leaf False) = (c, ["[0]"])
showTree' c f d@(Node a l r) = withCache' c'' (snd $ insert c d) $
    ("("++ f a ++") " ++ col Dull Blue (show_id (snd $ insert c d))) :
    concat (indentChildren [s1, s2])
    where
        (c', s1) = showTree' c f (getDd c l)
        (c'', s2) = showTree' c' f (getDd c r)

showTree' c f d@(InfNodes a dc (0, 0) (1,0) (0, 0) (1,0)) = withCache' c' (snd $ insert c d) $
    ("<"++ f a ++ "> dc " ++ col Dull Blue (show_id (snd $ insert c d))) : "  ║  " :
    concat (indentInfChildren [s1])
    where
        (c', s1) = showTree' c f (getDd c dc)
showTree' c f d@(InfNodes a dc (0, 0) (1,0) (0, 0) p0) = withCache' c'' (snd $ insert c d) $
    ("<"++ f a ++ "> dc, p0 " ++ col Dull Blue (show_id (snd $ insert c d))) : "  ║  " :
    concat (indentInfChildren [s1, s2])
    where
        (c', s1) = showTree' c f (getDd c dc)
        (c'', s2) = showTree0' c' f (getDd c p0)

showTree' c f d@(InfNodes a dc (0, 0) (1,0) p1 (1,0)) = withCache' c'' (snd $ insert c d) $
    ("<"++ f a ++ "> dc, p1 " ++ col Dull Blue (show_id (snd $ insert c d))) : "  ║  " :
    concat (indentInfChildren [s1, r_p1])
    where
        (c', s1) = showTree' c f (getDd c dc)
        (c'', r_p1) = showTree1' c' f (getDd c p1)

showTree' c f d@(InfNodes a dc (0, 0) n0 (0, 0) (1,0)) = withCache' c'' (snd $ insert c d) $
    ("<"++ f a ++ "> dc, n0 " ++ col Dull Blue (show_id (snd $ insert c d))) : "  ║  " :
    concat (indentInfChildren [s1, r_n0])
    where
        (c', s1) = showTree' c f (getDd c dc)
        (c'', r_n0) = showTree0' c' f (getDd c n0)

showTree' c f d@(InfNodes a dc n1 (1,0) (0, 0) (1,0)) = withCache' c'' (snd $ insert c d) $
    ("<"++ f a ++ "> dc, n1 " ++ col Dull Blue (show_id (snd $ insert c d))) : "  ║  " :
    concat (indentInfChildren [s1, r_n1])
    where
        (c', r_n1) = showTree1' c f (getDd c n1)
        (c'', s1) = showTree' c' f (getDd c dc)

showTree' c f d@(InfNodes a dc (0, 0) (1,0) p1 p0) = withCache' c''' (snd $ insert c d) $
    ("<"++ f a ++ "> dc, p1, p0 " ++ col Dull Blue (show_id (snd $ insert c d))) : "  ║  " :
    concat (indentInfChildren [s1, r_p1, r_p0])
    where
        (c', r_p0) = showTree0' c f (getDd c p0)
        (c'', s1) = showTree' c' f (getDd c dc)
        (c''', r_p1) = showTree1' c'' f (getDd c p1)

showTree' c f d@(InfNodes a dc (0, 0) n0 (0, 0) p0) = withCache' c''' (snd $ insert c d) $
    ("<"++ f a ++ "> dc, n0, p0 " ++ col Dull Blue (show_id (snd $ insert c d))) : "  ║  " :
    concat (indentInfChildren [s1, r_n0, r_p0])
    where
        (c', r_p0) = showTree0' c f (getDd c p0)
        (c'', r_n0) = showTree0' c' f (getDd c n0)
        (c''', s1) = showTree' c'' f (getDd c dc)

showTree' c f d@(InfNodes a dc (0, 0) n0 p1 (1,0)) = withCache' c''' (snd $ insert c d) $
    ("<"++ f a ++ "> dc, n0, p1 " ++ col Dull Blue (show_id (snd $ insert c d))) : "  ║  " :
    concat (indentInfChildren [s1, r_n0, r_p1])
    where
        (c', r_n0) = showTree0' c f (getDd c n0)
        (c'', s1) = showTree' c' f (getDd c dc)
        (c''', r_p1) = showTree1' c'' f (getDd c p1)

showTree' c f d@(InfNodes a dc n1 (1,0) (0, 0) p0) = withCache' c''' (snd $ insert c d) $
    ("<"++ f a ++ "> dc, n1, p0 " ++ col Dull Blue (show_id (snd $ insert c d))) : "  ║  " :
    concat (indentInfChildren [s1, r_n1, r_p0])
    where
        (c', r_p0) = showTree0' c f (getDd c p0)
        (c'', r_n1) = showTree1' c' f (getDd c n1)
        (c''', s1) = showTree' c'' f (getDd c dc)

showTree' c f d@(InfNodes a dc n1 (1,0) p1 (1,0)) = withCache' c''' (snd $ insert c d) $
    ("<"++ f a ++ "> dc, n1, p1 " ++ col Dull Blue (show_id (snd $ insert c d))) : "  ║  " :
    concat (indentInfChildren [s1, r_n1, r_p1])
    where
        (c', r_n1) = showTree1' c f (getDd c n1)
        (c'', s1) = showTree' c' f (getDd c dc)
        (c''', r_p1) = showTree1' c'' f (getDd c p1)

showTree' c f d@(InfNodes a dc n1 n0 (0, 0) (1,0)) = withCache' c''' (snd $ insert c d) $
    ("<"++ f a ++ "> dc, n1, n0 " ++ col Dull Blue (show_id (snd $ insert c d))) : "  ║  " :
    concat (indentInfChildren [s1, r_n1, r_n0])
    where
        (c', r_n1) = showTree1' c f (getDd c n1)
        (c'', r_n0) = showTree0' c' f (getDd c n0)
        (c''', s1) = showTree' c'' f (getDd c dc)

showTree' c f d@(InfNodes a dc (0, 0) n0 p1 p0) = withCache' c'''' (snd $ insert c d) $
    ("<"++ f a ++ "> dc, n0, p1, p0 " ++ col Dull Blue (show_id (snd $ insert c d))) : "  ║  " :
    concat (indentInfChildren [s1, r_n0, r_p1, r_p0])
    where
        (c', r_p0) = showTree0' c f (getDd c p0)
        (c'', r_n0) = showTree0' c' f (getDd c n0)
        (c''', s1) = showTree' c'' f (getDd c dc)
        (c'''', r_p1) = showTree1' c''' f (getDd c p1)

showTree' c f d@(InfNodes a dc n1 (1,0) p1 p0) = withCache' c'''' (snd $ insert c d) $
    ("<"++ f a ++ "> dc, n1, p1, p0 " ++ col Dull Blue (show_id (snd $ insert c d))) : "  ║  " :
    concat (indentInfChildren [s1, r_n1, r_p1, r_p0])
    where
        (c', r_p0) = showTree0' c f (getDd c p0)
        (c'', r_n1) = showTree1' c' f (getDd c n1)
        (c''', s1) = showTree' c'' f (getDd c dc)
        (c'''', r_p1) = showTree1' c''' f (getDd c p1)
showTree' c f d@(InfNodes a dc n1 n0 (0, 0) p0) = withCache' c'''' (snd $ insert c d) $
    ("<"++ f a ++ "> dc, n1, n0, p0 " ++ col Dull Blue (show_id (snd $ insert c d))) : "  ║  " :
    concat (indentInfChildren [s1, r_n1, r_n0, r_p0])
    where
        (c', r_p0) = showTree0' c f (getDd c p0)
        (c'', r_n1) = showTree1' c' f (getDd c n1)
        (c''', r_n0) = showTree0' c'' f (getDd c n0)
        (c'''', s1) = showTree' c''' f (getDd c dc)
showTree' c f d@(InfNodes a dc n1 n0 p1 (0, 0)) = withCache' c'''' (snd $ insert c d) $
    ("<"++ f a ++ "> dc, n1, n0, p1 " ++ col Dull Blue (show_id (snd $ insert c d))) : "  ║  " :
    concat (indentInfChildren [s1, r_n1, r_n0, r_p1]) `debug` (" draw: " ++  show n0 ++ show n1 ++ show p1)
    where
        (c', r_n1) = showTree1' c f (getDd c n1)
        (c'', r_n0) = showTree0' c' f (getDd c n0)
        (c''', s1) = showTree' c'' f (getDd c dc)
        (c'''', r_p1) = showTree1' c''' f (getDd c p1)


showTree' c f d@(InfNodes a dc n1 n0 p1 p0) = withCache' c''''' (snd $ insert c d) $
    ("<"++ f a ++ "> dc, n1, n0, p1, p0 " ++ col Dull Blue (show_id (snd $ insert c d))) : "  ║  " :
    concat (indentInfChildren [s1, r_n1, r_n0, r_p1, r_p0])
    where
        (c', r_p0) = showTree0' c f (getDd c p0)
        (c'', r_n1) = showTree1' c' f (getDd c n1)
        (c''', r_n0) = showTree0' c'' f (getDd c n0)
        (c'''', s1) = showTree' c''' f (getDd c dc)
        (c''''', r_p1) = showTree1' c'''' f (getDd c p1)

showTree' c f d@(EndInfNode cons) =
        withCache' c' (snd $ insert c d) $
            ("<> " ++ col Dull Blue (show_id (snd $ insert c d))) : "  ║  " :
            concat (indentInfChildren [s1])
        where
            (c', s1) = showTree' c f (getDd c cons)

showTree :: Context -> Dd -> String
showTree c d = "\n" ++ unlines (showTree'' c show d)
showTree2 :: Context -> Dd -> String
showTree2 c = unlines . showTree'' c show

drawTree :: Context -> NodeId -> IO ()
drawTree c x = putStrLn . showTree c $ getDd c x

drawTree2 :: Context -> Dd -> IO ()
drawTree2 c = putStrLn . showTree2 c

drawTree3 :: (Context, NodeId) -> IO ()
drawTree3 (c, x) = putStrLn . showTree c $ getDd c x



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
  debug_on :: Bool,
  save_logs :: Bool,
  debug_open :: Bool,
  debug_close :: Bool,
  debug_shorten_close :: Bool,
  debug_func_stack :: Bool
}


format :: String -> String
format s = format' $ words s

format' :: [String] -> String
format' [] = "" -- Base case: return an empty string for an empty list
format' (n : n2 : n3 : ns) =
    colorize "red" n ++ colorize "green" n2 ++ colorize "" n3 ++ format' ns
format' (n : n2 : ns) =
    colorize "red" n ++ colorize "green" n2 ++ format' ns
format' (n : ns) =
    n ++ format' ns


show_dd :: Show_setting -> Context -> NodeId -> String
show_dd s@ShowSetting{display_context=True} c d = show c ++ show_dd s{display_context=False} c d
show_dd ShowSetting{draw_tree=True} c d = showTree c (getDd c d)
show_dd s _ (0,0)
  | color s = "[" ++ colorize "soft red" "0" ++ "]"
  | otherwise = "[0]"
show_dd s _ (1,0)
  | color s = "[" ++ colorize "soft green" "1" ++ "]"
  | otherwise = "[1]"
show_dd s c d = case getDd c d of
  Node i rC lC -> show_i i "orange" ++ " (" ++ show_dd s c rC ++ ") (" ++ show_dd s c lC ++ ")"
  InfNodes i dc n1 n0 p1 p0 -> show_i i "chill blue" ++ " <{dc: " ++ show_dd s c dc ++ "} {n1: " ++ show_dd s c n1 ++ "} {n0: " ++ show_dd s c n0 ++ "} {p1: " ++ show_dd s c p1 ++ "} {p0: " ++ show_dd s c p0 ++ "}>"
  EndInfNode child -> (if color s then colorize "chill blue" "<>" else "<>") ++ show_dd s c child
  _ -> error "should not be possible"
  where
    show_i i c = (if display_node_id's s then (if color s then colorize "blue" ("#" ++ show d) else ("#" ++ show d)) ++ " " else "")
      ++ (if color s then colorize c (show i) else show i)


debug_manipulation :: (Context, NodeId) -> String -> String -> Context -> NodeId -> NodeId -> (Context, NodeId)
debug_manipulation f f_key f_name old_c@Context{cache = nc, func_stack=fs} a_id b_id = if not $ save_logs settings then
    -- prepare message for before the calling of the function
    let
    leaf_msg = colorize "orange" (">> " ++ f_name ++ " : ") ++
                    "\n  ->   " ++ show_dd settings old_c a_id ++
                    "\n  ->   " ++ show_dd settings old_c b_id ++ "\n"
    (c,r) = if debug_on settings && debug_open settings &&
                not ((a_id `elem` [(0,0), (1,0)] || b_id `elem` [(0,0), (1,0)]) && (not $ display_leaf_cases settings))
                && not (a_id `elem` [(0,0), (1,0)] && b_id `elem` [(0,0), (1,0)])
            then if debug_func_stack settings
                then myTrace (show_func_stack old_c) (myTrace leaf_msg f)
                else myTrace leaf_msg f
            else f
    in

    -- after calling the function
    if debug_on settings && debug_close settings && not (a_id `elem` [(0,0), (1,0)] && b_id `elem` [(0,0), (1,0)]) then
        if a_id `elem` [(0,0), (1,0)] || b_id `elem` [(0,0), (1,0)]
        then if not $ display_leaf_cases settings
            then (c{func_stack=fs}, r)
            else myTrace (show_func_stack old_c) $ myTrace (colorize "green" (f_name ++ " : ") ++
                "\n  " ++ show_dd settings c a_id ++
                " : " ++ show_dd settings c b_id ++
                " = " ++ show_dd settings c r ++ " " ++ col Dull Blue (show_id r) ++
                "\n") (c, r)
        else
        myTrace (show_func_stack old_c) $ myTrace (
        case Map.lookup f_key nc of
            Just nc' -> case HashMap.lookup (a_id, b_id) nc' of
                Just rt -> colorize "chill blue" "found cached result : " ++ col Dull Blue (show_id rt) ++ " for "
                    ++ colorize "green" (f_name ++ " : ") ++
                    (if not $ debug_shorten_close settings then
                        "\n  ->   " ++ show_dd settings c a_id ++
                        "\n  ->   " ++ show_dd settings c b_id
                     else "") ++
                    "\n  =>   " ++ show_dd settings c r ++
                    "\n"
                Nothing ->
                    colorize "green" (f_name ++ " : ") ++
                    (if not $ debug_shorten_close settings then
                        "\n  ->   " ++ show_dd settings c a_id ++
                        "\n  ->   " ++ show_dd settings c b_id
                    else "") ++
                    "\n  =>   " ++ show_dd settings c r ++ " " ++ col Dull Blue (show_id r) ++
                    "\n"
            Nothing -> error ("wrong function name in cache lookup: " ++ show f_key)
        ) (c{func_stack=fs}, r)
    else (c{func_stack=fs}, r)


    ---------------------------------------------------------
    else
    -- debug message for before the calling of the function
    let
    start_msg = ("\\n" ++ colorize "orange" "  ->   " ++ show_dd settings old_c a_id) ++
                ("\\n" ++ colorize "orange" "  ->   " ++ show_dd settings old_c b_id ++ "\\n")
    (c,r) = if not (a_id `elem` [(0,0), (1,0)] && b_id `elem` [(0,0), (1,0)])
            then myDebugLog "\"inner\":[" f
            else f
    in
    -- debug for after calling the function

    if not (a_id `elem` [(0,0), (1,0)] && b_id `elem` [(0,0), (1,0)])
        then myDebugLog ("{\"" ++ colorize "green" f_name ++"\": {" ++ "\"func_stack before\": [\"" ++ show_func_stack old_c ++ "\"],\n\"input\": \"" ++ start_msg ++ "\",\n") $
            case Map.lookup f_key nc of
                Just nc' -> case HashMap.lookup (a_id, b_id) nc' of
                    Just rt -> myDebugLog ("],\n\"" ++ colorize "chill blue" "found cached result"++"\":\"" ++ col Vivid Blue (show_id rt) ++ " for " ++ "\\n" ++ colorize "green" "  =>   "
                        ++ show_dd settings c rt ++ "\\n\"}},") (old_c, rt)
                    Nothing ->
                        myDebugLog ("],\n\"result\": \"\\n" ++ colorize "green" "  =>   " ++ show_dd settings c r ++ " " ++ col Vivid Blue (show_id r)
                        ++ "\\n\"}},") (c{func_stack=fs}, r)
                Nothing -> error ("wrong function name in cache lookup: " ++ show f_key)
        else (c{func_stack=fs}, r)

debug_func :: String -> (Context, NodeId) -> (Context, NodeId)
debug_func f_name f = if save_logs settings
    then myDebugLog ("{\"" ++ colorize "orange" f_name ++ "\" : [") (myDebugLog ("\n{\""++ "context" ++ "\" : [\"" ++ show_context (fst f) ++ "\"]}\n]},") f)
    else if debug_on settings
        then myTrace ("{\"" ++ colorize "orange" f_name ++ "\" : [") (myTrace ("\n{\""++ "context" ++ "\" : [\"" ++ show_context (fst f) ++ "\"]}\n]},") f)
        else f
    -- where f' =  myTrace "\"inner\":{" f

jsonwrap :: String -> String -> String
jsonwrap k v = "{ \""++ k ++    "\": \"" ++ v ++ "\" }"

show_a_b :: Context -> NodeId -> NodeId -> String
show_a_b c a_id b_id = "\\n  ->   " ++ show_dd settings c a_id ++ "\\n  ->   " ++ show_dd settings c b_id

debug5 :: NodeId -> String -> NodeId
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
            ,   display_leaf_cases = False
            ,   display_end_infs = True

            ,   debug_on = True
            ,   save_logs = False

            ,   debug_open = True
            ,   debug_close = True
            ,   debug_shorten_close = True
            ,   debug_func_stack = False
}
