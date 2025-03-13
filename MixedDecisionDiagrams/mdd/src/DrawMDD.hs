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

-- showTree0' :: Context -> (Int -> String) -> Node -> (Context, [String])
-- showTree0' c _ (_, Leaf True) = (c, ["   "])
-- showTree0' c _ (_, Leaf False) = (c, ["[0]"])
-- showTree0' c f d@(id, Node a l r) = withCache' c'' d $ (("("++ f a ++")") ++ col Dull Blue (show_id id)) : concat (indentChildren [s1, s2])
--     where
--     (c', s1) = showTree0' c f (l, getDd c l)
--     (c'',s2) = showTree0' c' f (r, getDd c r)
-- showTree0' c f x = showTree' c f x

-- showTree1' :: Context -> (Int -> String) -> Node -> (Context, [String])
-- showTree1' c _ (_, Leaf True) = (c, ["[1]"])
-- showTree1' c _ (_, Leaf False) = (c, ["   "])
-- showTree1' c f d@(id, Node a l r) = withCache' c'' d $ (("("++ f a ++")") ++ col Dull Blue (show_id id)) : concat (indentChildren [s1, s2])
--     where
--     (c', s1) = showTree1' c f (l, getDd c l)
--     (c'',s2) = showTree1' c' f (r, getDd c r)
-- showTree1' c f x = showTree' c f x


-- take_c_show :: (Context, [String]) -> (Context -> NodeId -> (Context, [String])) -> (Context, NodeId) -> (Context, [String])
-- take_c_show (c, _) f (_,a) = f c a
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


debug_manipulation :: (Context, Node) -> String -> String -> Context -> Node -> Node -> (Context, Node)
debug_manipulation f f_key f_name old_c@Context{cache = nc, func_stack=fs} a@(a_id, a_d) b@(b_id, b_d)
    | getDd old_c a_id == a_d && getDd old_c b_id == b_d = if not $ save_logs settings then
    -- prepare message for before the calling of the function
    let
    leaf_msg = colorize "orange" (">> " ++ f_name ++ " : ") ++
                    "\n  ->   " ++ show_dd settings old_c a ++
                    "\n  ->   " ++ show_dd settings old_c b ++ "\n"
    (c,r) = if debug_on settings && debug_open settings &&
                not ((a_id `elem` [(1,0), (2,0)] || b_id `elem` [(1,0), (2,0)]) && (not $ display_leaf_cases settings))
                 -- leaf vs leaf, always skip printing
            then if debug_func_stack settings
                then myTrace (show_func_stack old_c) (myTrace leaf_msg f)
                else myTrace leaf_msg f
            else f
    in

    -- after calling the function
    if debug_on settings && debug_close settings then
        if a_id `elem` [(1,0), (2,0)] || b_id `elem` [(1,0), (2,0)]
        then if not $ display_leaf_cases settings
            then (c{func_stack=fs}, r)
            else myTrace (show_func_stack old_c) $ myTrace (colorize "green" (f_name ++ " : ") ++
                "\n  " ++ show_dd settings c a ++
                " : " ++ show_dd settings c b ++
                " = " ++ show_dd settings c r ++ " " ++ col Dull Blue (show_id' r) ++
                "\n") (c, r)
        else
        myTrace (show_func_stack old_c) $ myTrace (
        case Map.lookup f_key nc of
            Just nc' -> case HashMap.lookup (a_id, b_id) nc' of
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
        ) (c{func_stack=fs}, r)
    else (c{func_stack=fs}, r)


    ---------------------------------------------------------
    else
    -- debug message for before the calling of the function
    let
    start_msg = ("\\n" ++ colorize "orange" "  ->   " ++ show_dd settings old_c a) ++
                ("\\n" ++ colorize "orange" "  ->   " ++ show_dd settings old_c b ++ "\\n")
    (c,r) = if not (a_id `elem` [(1,0), (2,0)] && b_id `elem` [(1,0), (2,0)])
            then myDebugLog "\"inner\":[" f
            else f
    in
    -- debug for after calling the function

    if not (a_id `elem` [(1,0), (2,0)] && b_id `elem` [(1,0), (2,0)])
        then myDebugLog ("{\"" ++ colorize "green" f_name ++"\": {" ++ "\"func_stack before\": [\"" ++ show_func_stack old_c ++ "\"],\n\"input\": \"" ++ start_msg ++ "\",\n") $
            case Map.lookup f_key nc of
                Just nc' -> case HashMap.lookup (a_id, b_id) nc' of
                    Just rt -> myDebugLog ("],\n\"" ++ colorize "chill blue" "found cached result"++"\":\"" ++ col Vivid Blue (show_id rt) ++ " for " ++ "\\n" ++ colorize "green" "  =>   "
                        ++ show_dd settings c (rt, getDd c rt) ++ "\\n\"}},") (old_c, (rt, getDd c rt))
                    Nothing ->
                        myDebugLog ("],\n\"result\": \"\\n" ++ colorize "green" "  =>   " ++ show_dd settings c r ++ " " ++ col Vivid Blue (show_id' r)
                        ++ "\\n\"}},") (c{func_stack=fs}, r)
                Nothing -> error ("wrong function name in cache lookup: " ++ show f_key)
        else (c{func_stack=fs}, r)
    | otherwise = error ("id and dd are not equal, \n a_id: " ++ show (getDd old_c a_id) ++ "\n a: " ++ show a ++ "\n b_id: " ++ show (getDd old_c b_id) ++ " \n b: " ++ show b )

debug_func :: String -> (Context, Node) -> (Context, Node)
debug_func f_name f = if save_logs settings
    then myDebugLog ("{\"" ++ colorize "orange" f_name ++ "\" : [") (myDebugLog ("\n{\""++ "context" ++ "\" : [\"" ++ show_context (fst f) ++ "\"]}\n]},") f)
    else if debug_on settings
        then myTrace ("{\"" ++ colorize "orange" f_name ++ "\" : [") (myTrace ("\n{\""++ "context" ++ "\" : [\"" ++ show_context (fst f) ++ "\"]}\n]},") f)
        else f
    -- where f' =  myTrace "\"inner\":{" f

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

            ,   debug_on = False
            ,   save_logs = False

            ,   debug_open = True
            ,   debug_close = True
            ,   debug_shorten_close = False
            ,   debug_func_stack = False
}
