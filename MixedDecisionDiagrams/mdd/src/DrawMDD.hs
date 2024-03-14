{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module DrawMDD where
import MDD
import System.IO
-- import Test.Hspec
import qualified Data.Map as Map
import Data.Hashable
import System.Console.ANSI

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
showTree0' c f d@(Node a l r) = withCache' c'' (hash d) $ ("("++ f a ++")") : concat (indentChildren [s1, s2])
    where
    (c', s1) = showTree0' c f (getDd c l)
    (c'',s2) = showTree0' c' f (getDd c r)
showTree0' c f x = showTree' c f x

showTree1' :: Context -> (Int -> String) -> Dd -> (Context, [String])
showTree1' c _ (Leaf True) = (c, ["[1]"])
showTree1' c _ (Leaf False) = (c, ["   "])
showTree1' c f d@(Node a l r) = withCache' c'' (hash d) $ ("("++ f a ++")") : concat (indentChildren [s1, s2])
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
showTree' c f d@(Node a l r) = withCache' c'' (hash d) $
    ("("++ f a ++") " ++ col Dull Blue ("#" ++ show (hash d))) :
    concat (indentChildren [s1, s2])
    where
        (c', s1) = showTree' c f (getDd c l)
        (c'', s2) = showTree' c' f (getDd c r)

showTree' c f d@(InfNodes a dc (0, 0) (1,0) (0, 0) (1,0)) = withCache' c' (hash d) $
    ("<"++ f a ++ "> dc " ++ col Dull Blue ("#" ++ show (hash d))) : "  ║  " :
    concat (indentInfChildren [s1])
    where
        (c', s1) = showTree' c f (getDd c dc)
showTree' c f d@(InfNodes a dc (0, 0) (1,0) (0, 0) p0) = withCache' c'' (hash d) $
    ("<"++ f a ++ "> dc, p0 " ++ col Dull Blue ("#" ++ show (hash d))) : "  ║  " :
    concat (indentInfChildren [s1, s2])
    where
        (c', s1) = showTree' c f (getDd c dc)
        (c'', s2) = showTree0' c' f (getDd c p0)

showTree' c f d@(InfNodes a dc (0, 0) (1,0) p1 (1,0)) = withCache' c'' (hash d) $
    ("<"++ f a ++ "> dc, p1 " ++ col Dull Blue ("#" ++ show (hash d))) : "  ║  " :
    concat (indentInfChildren [s1, r_p1])
    where
        (c', s1) = showTree' c f (getDd c dc)
        (c'', r_p1) = showTree1' c' f (getDd c p1)

showTree' c f d@(InfNodes a dc (0, 0) n0 (0, 0) (1,0)) = withCache' c'' (hash d) $
    ("<"++ f a ++ "> dc, n0 " ++ col Dull Blue ("#" ++ show (hash d))) : "  ║  " :
    concat (indentInfChildren [s1, r_n0])
    where
        (c', s1) = showTree' c f (getDd c dc)
        (c'', r_n0) = showTree0' c' f (getDd c n0)

showTree' c f d@(InfNodes a dc n1 (1,0) (0, 0) (1,0)) = withCache' c'' (hash d) $
    ("<"++ f a ++ "> dc, n1 " ++ col Dull Blue ("#" ++ show (hash d))) : "  ║  " :
    concat (indentInfChildren [s1, r_n1])
    where
        (c', r_n1) = showTree1' c f (getDd c n1)
        (c'', s1) = showTree' c' f (getDd c dc)

showTree' c f d@(InfNodes a dc (0, 0) (1,0) p1 p0) = withCache' c''' (hash d) $
    ("<"++ f a ++ "> dc, p1, p0 " ++ col Dull Blue ("#" ++ show (hash d))) : "  ║  " :
    concat (indentInfChildren [s1, r_p1, r_p0])
    where
        (c', r_p0) = showTree0' c f (getDd c p0)
        (c'', s1) = showTree' c' f (getDd c dc)
        (c''', r_p1) = showTree1' c'' f (getDd c p1)

showTree' c f d@(InfNodes a dc (0, 0) n0 (0, 0) p0) = withCache' c''' (hash d) $
    ("<"++ f a ++ "> dc, n0, p0 " ++ col Dull Blue ("#" ++ show (hash d))) : "  ║  " :
    concat (indentInfChildren [s1, r_n0, r_p0])
    where
        (c', r_p0) = showTree0' c f (getDd c p0)
        (c'', r_n0) = showTree0' c' f (getDd c n0)
        (c''', s1) = showTree' c'' f (getDd c dc)

showTree' c f d@(InfNodes a dc (0, 0) n0 p1 (1,0)) = withCache' c''' (hash d) $
    ("<"++ f a ++ "> dc, n0, p1 " ++ col Dull Blue ("#" ++ show (hash d))) : "  ║  " :
    concat (indentInfChildren [s1, r_n0, r_p1])
    where
        (c', r_n0) = showTree0' c f (getDd c n0)
        (c'', s1) = showTree' c' f (getDd c dc)
        (c''', r_p1) = showTree1' c'' f (getDd c p1)

showTree' c f d@(InfNodes a dc n1 (1,0) (0, 0) p0) = withCache' c''' (hash d) $
    ("<"++ f a ++ "> dc, n1, p0 " ++ col Dull Blue ("#" ++ show (hash d))) : "  ║  " :
    concat (indentInfChildren [s1, r_n1, r_p0])
    where
        (c', r_p0) = showTree0' c f (getDd c p0)
        (c'', r_n1) = showTree1' c' f (getDd c n1)
        (c''', s1) = showTree' c'' f (getDd c dc)

showTree' c f d@(InfNodes a dc n1 (1,0) p1 (1,0)) = withCache' c''' (hash d) $
    ("<"++ f a ++ "> dc, n1, p1 " ++ col Dull Blue ("#" ++ show (hash d))) : "  ║  " :
    concat (indentInfChildren [s1, r_n1, r_p1])
    where
        (c', r_n1) = showTree1' c f (getDd c n1)
        (c'', s1) = showTree' c' f (getDd c dc)
        (c''', r_p1) = showTree1' c'' f (getDd c p1)

showTree' c f d@(InfNodes a dc n1 n0 (0, 0) (1,0)) = withCache' c''' (hash d) $
    ("<"++ f a ++ "> dc, n1, n0 " ++ col Dull Blue ("#" ++ show (hash d))) : "  ║  " :
    concat (indentInfChildren [s1, r_n1, r_n0])
    where
        (c', r_n1) = showTree1' c f (getDd c n1)
        (c'', r_n0) = showTree0' c' f (getDd c n0)
        (c''', s1) = showTree' c'' f (getDd c dc)

showTree' c f d@(InfNodes a dc (0, 0) n0 p1 p0) = withCache' c'''' (hash d) $
    ("<"++ f a ++ "> dc, n0, p1, p0 " ++ col Dull Blue ("#" ++ show (hash d))) : "  ║  " :
    concat (indentInfChildren [s1, r_n0, r_p1, r_p0])
    where
        (c', r_p0) = showTree0' c f (getDd c p0)
        (c'', r_n0) = showTree0' c' f (getDd c n0)
        (c''', s1) = showTree' c'' f (getDd c dc)
        (c'''', r_p1) = showTree1' c''' f (getDd c p1)

showTree' c f d@(InfNodes a dc n1 (1,0) p1 p0) = withCache' c'''' (hash d) $
    ("<"++ f a ++ "> dc, n1, p1, p0 " ++ col Dull Blue ("#" ++ show (hash d))) : "  ║  " :
    concat (indentInfChildren [s1, r_n1, r_p1, r_p0])
    where
        (c', r_p0) = showTree0' c f (getDd c p0)
        (c'', r_n1) = showTree1' c' f (getDd c n1)
        (c''', s1) = showTree' c'' f (getDd c dc)
        (c'''', r_p1) = showTree1' c''' f (getDd c p1)
showTree' c f d@(InfNodes a dc n1 n0 (0, 0) p0) = withCache' c'''' (hash d) $
    ("<"++ f a ++ "> dc, n1, n0, p0 " ++ col Dull Blue ("#" ++ show (hash d))) : "  ║  " :
    concat (indentInfChildren [s1, r_n1, r_n0, r_p0])
    where
        (c', r_p0) = showTree0' c f (getDd c p0)
        (c'', r_n1) = showTree1' c' f (getDd c n1)
        (c''', r_n0) = showTree0' c'' f (getDd c n0)
        (c'''', s1) = showTree' c''' f (getDd c dc)
showTree' c f d@(InfNodes a dc n1 n0 p1 (0, 0)) = withCache' c'''' (hash d) $
    ("<"++ f a ++ "> dc, n1, n0, p1 " ++ col Dull Blue ("#" ++ show (hash d))) : "  ║  " :
    concat (indentInfChildren [s1, r_n1, r_n0, r_p1]) `debug` (" draw: " ++  show n0 ++ show n1 ++ show p1)
    where
        (c', r_n1) = showTree1' c f (getDd c n1)
        (c'', r_n0) = showTree0' c' f (getDd c n0)
        (c''', s1) = showTree' c'' f (getDd c dc)
        (c'''', r_p1) = showTree1' c''' f (getDd c p1)


showTree' c f d@(InfNodes a dc n1 n0 p1 p0) = withCache' c''''' (hash d) $
    ("<"++ f a ++ "> dc, n1, n0, p1, p0 " ++ col Dull Blue ("#" ++ show (hash d))) : "  ║  " :
    concat (indentInfChildren [s1, r_n1, r_n0, r_p1, r_p0])
    where
        (c', r_p0) = showTree0' c f (getDd c p0)
        (c'', r_n1) = showTree1' c' f (getDd c n1)
        (c''', r_n0) = showTree0' c'' f (getDd c n0)
        (c'''', s1) = showTree' c''' f (getDd c dc)
        (c''''', r_p1) = showTree1' c'''' f (getDd c p1)

showTree' c f d@(EndInfNode cons) = withCache' c' (hash d) $
    ("<> " ++ col Dull Blue ("#" ++ show (hash d))) : "  ║  " :
    concat (indentInfChildren [s1])
    where
        (c', s1) = showTree' c f (getDd c cons)

showTree :: Context -> Dd -> String
showTree c = unlines . showTree'' c show

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
