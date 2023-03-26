{-# LANGUAGE LambdaCase #-}
module DrawMDD where
import MDD
import System.IO
-- import Test.Hspec
import qualified Data.Map as Map

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

showTree0' :: (Either Ordinal Int -> String) -> Dd -> [String]
showTree0' f (Leaf True) = ["   "]
showTree0' f (Leaf False) = ["[0]"]
showTree0' f (Node a l r) = ("("++ f (Right a) ++")") : concat (indentChildren (map (showTree0' f) [l, r]))
showTree0' f x = showTree' f x

showTree1' :: (Either Ordinal Int -> String) -> Dd -> [String]
showTree1' f (Leaf True) = ["[1]"]
showTree1' f (Leaf False) = ["   "]
showTree1' f (Node a l r) = ("("++ f (Right a) ++")") : concat (indentChildren (map (showTree1' f) [l, r]))
showTree1' f x = showTree' f x

showTree' :: (Either Ordinal Int -> String) -> Dd -> [String]
--showTree' (Node n ns) = n : concat (indentChildren (map showTree' ns))

showTree' f (Leaf True) = ["[1]"]
showTree' f (Leaf False) = ["[0]"]
showTree' f (Node a l r) = ("("++ f (Right a) ++")") : concat (indentChildren (map (showTree' f) [l, r]))
showTree' f (InfNodes a dc (Leaf False) (Leaf True) (Leaf False) (Leaf True)) = ("<"++ f (Left a) ++ "> dc") : "  ║  " : concat (indentInfChildren [showTree' f dc])

showTree' f (InfNodes a dc (Leaf False) (Leaf True) (Leaf False) p0) =("<"++ f (Left a) ++ "> dc, p0") : "  ║  " : concat (indentInfChildren [showTree' f dc, showTree0' f p0])
showTree' f (InfNodes a dc (Leaf False) (Leaf True) p1 (Leaf True)) =("<"++ f (Left a) ++ "> dc, p1") : "  ║  " : concat (indentInfChildren [showTree' f dc, showTree1' f p1])
showTree' f (InfNodes a dc (Leaf False) n0 (Leaf False) (Leaf True)) =("<"++ f (Left a) ++ "> dc, n0") : "  ║  " : concat (indentInfChildren [showTree' f dc, showTree0' f n0])
showTree' f (InfNodes a dc n1 (Leaf True) (Leaf False) (Leaf True)) =("<"++ f (Left a) ++ "> dc, n1") : "  ║  " : concat (indentInfChildren [showTree' f dc, showTree1' f n1])

showTree' f (InfNodes a dc (Leaf False) (Leaf True) p1 p0) = ("<"++ f (Left a) ++ "> dc, p1, p0)") : "  ║  " : concat (indentInfChildren [showTree' f dc, showTree1' f p1, showTree0' f p0])
showTree' f (InfNodes a dc (Leaf False) n0 (Leaf False) p0) = ("<"++ f (Left a) ++ "> dc, n0, p0)") : "  ║  " : concat (indentInfChildren [showTree' f dc, showTree0' f n0, showTree0' f p0])
showTree' f (InfNodes a dc (Leaf False) n0 p1 (Leaf True)) = ("<"++ f (Left a) ++ "> dc, n0, p1)") : "  ║  " : concat (indentInfChildren [showTree' f dc, showTree0' f n0, showTree1' f p1])
showTree' f (InfNodes a dc n1 (Leaf True) (Leaf False) p0) = ("<"++ f (Left a) ++ "> dc, n1, p0)") : "  ║  " : concat (indentInfChildren [showTree' f dc, showTree1' f n1, showTree0' f p0])
showTree' f (InfNodes a dc n1 (Leaf True) p1 (Leaf True)) = ("<"++ f (Left a) ++ "> dc, n1, p1)") : "  ║  " : concat (indentInfChildren [showTree' f dc, showTree1' f n1, showTree1' f p1])
showTree' f (InfNodes a dc n1 n0 (Leaf False) (Leaf True)) = ("<"++ f (Left a) ++ "> dc, n1, n0)") : "  ║  " : concat (indentInfChildren [showTree' f dc, showTree1' f n1, showTree0' f n0])

showTree' f (InfNodes a dc (Leaf False) n0 p1 p0) = ("<"++ f (Left a) ++ "> dc, n0, p1, p0)") : "  ║  " : concat (indentInfChildren [showTree' f dc, showTree0' f n0, showTree1' f p1, showTree0' f p0])
showTree' f (InfNodes a dc n1 (Leaf True) p1 p0) = ("<"++ f (Left a) ++ "> dc, n1, p1, p0)") : "  ║  " : concat (indentInfChildren [showTree' f dc, showTree1' f n1, showTree1' f p1, showTree0' f p0])
showTree' f (InfNodes a dc n1 n0 (Leaf False) p0) = ("<"++ f (Left a) ++ "> dc, n0, p1, p0)") : "  ║  " : concat (indentInfChildren [showTree' f dc, showTree1' f n1, showTree0' f n0, showTree0' f p0])
showTree' f (InfNodes a dc n1 n0 p1 (Leaf False)) = ("<"++ f (Left a) ++ "> dc, n0, p1, p0)") : "  ║  " : concat (indentInfChildren [showTree' f dc, showTree1' f n1, showTree0' f n0, showTree1' f p1])

showTree' f (InfNodes a dc n1 n0 p1 p0) =("<"++ f (Left a) ++ "> dc, n1, n0, p1, p0") : "  ║  " : concat (indentInfChildren [showTree' f dc, showTree1' f n1, showTree0' f  n0, showTree1' f p1, showTree0' f p0])
showTree' f (EndInfNode a cons) = showTree' f cons

showTree :: Dd -> String
showTree = unlines . showTree' show

showTree2 :: Dd -> String
showTree2 = unlines . showTree' (\case
    Left (Order x) -> show (last x)
    Right x -> show x
    )

drawTree :: Dd -> IO ()
drawTree = putStrLn . showTree

drawTree2 :: Dd -> IO ()
drawTree2 = putStrLn . showTree2

-- disp :: Map.Map Ordinal (Either (Map.Map Int String) String) -> Dd -> IO ()
-- disp m = putStrLn . unlines . showTree' (show . (\case
--    Left x -> if Map.member x m then m Map.! x else error $ "key: " ++ show x ++ " not in keys: " ++ show (Map.keys m)))





