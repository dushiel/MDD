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

showTree0' :: NodeLookup -> (Int -> String) -> Dd -> [String]
showTree0' _ _ (Leaf True) = ["   "]
showTree0' _ _ (Leaf False) = ["[0]"]
showTree0' nm f (Node a l r) = ("("++ f a ++")") : concat (indentChildren (map (showTree0' nm f) [getDd_ l nm, getDd_ r nm]))
showTree0' nm f x = showTree'' nm f x

showTree1' :: NodeLookup -> (Int -> String) -> Dd -> [String]
showTree1' _ _ (Leaf True) = ["[1]"]
showTree1' _ _ (Leaf False) = ["   "]
showTree1' nm f (Node a l r) = ("("++ f a ++")") : concat (indentChildren (map (showTree1' nm f) [getDd_ l nm, getDd_ r nm]))
showTree1' nm f x = showTree'' nm f x

showTree'' :: NodeLookup -> (Int -> String) -> Dd -> [String]
--showTree' (Node n ns) = n : concat (indentChildren (map showTree' ns))
showTree'' nm =  showTree'
    where
        showTree' _ (Leaf False) = ["[1]"]
        showTree' _ (Leaf True) = ["[0]"]
        showTree' f (Node a l r) = ("("++ f a ++")") : concat (indentChildren (map (showTree' f) [getDd_ l nm, getDd_ r nm]))
        showTree' f (InfNodes a dc 0 1 0 1) = ("<"++ f a ++ "> dc") : "  ║  " : concat (indentInfChildren [showTree' f (getDd_ dc nm)])
        showTree' f (InfNodes a dc 0 1 0 p0) =("<"++ f a ++ "> dc, p0") : "  ║  " : concat (indentInfChildren [showTree' f (getDd_ dc nm), showTree0' nm f (getDd_ p0 nm)])
        showTree' f (InfNodes a dc 0 1 p1 1) =("<"++ f a ++ "> dc, p1") : "  ║  " : concat (indentInfChildren [showTree' f (getDd_ dc nm), showTree1' nm f (getDd_ p1 nm)])
        showTree' f (InfNodes a dc 0 n0 0 1) =("<"++ f a ++ "> dc, n0") : "  ║  " : concat (indentInfChildren [showTree' f (getDd_ dc nm), showTree0' nm f (getDd_ n0 nm)])
        showTree' f (InfNodes a dc n1 1 0 1) =("<"++ f a ++ "> dc, n1") : "  ║  " : concat (indentInfChildren [showTree' f (getDd_ dc nm), showTree1' nm f (getDd_ n1 nm)])
        showTree' f (InfNodes a dc 0 1 p1 p0) = ("<"++ f a ++ "> dc, p1, p0)") : "  ║  " : concat (indentInfChildren [showTree' f (getDd_ dc nm), showTree1' nm f (getDd_ p1 nm), showTree0' nm f (getDd_ p0 nm)])
        showTree' f (InfNodes a dc 0 n0 0 p0) = ("<"++ f a ++ "> dc, n0, p0)") : "  ║  " : concat (indentInfChildren [showTree' f (getDd_ dc nm), showTree0' nm f (getDd_ n0 nm), showTree0' nm f (getDd_ p0 nm)])
        showTree' f (InfNodes a dc 0 n0 p1 1) = ("<"++ f a ++ "> dc, n0, p1)") : "  ║  " : concat (indentInfChildren [showTree' f (getDd_ dc nm), showTree0' nm f (getDd_ n0 nm), showTree1' nm f (getDd_ p1 nm)])
        showTree' f (InfNodes a dc n1 1 0 p0) = ("<"++ f a ++ "> dc, n1, p0)") : "  ║  " : concat (indentInfChildren [showTree' f (getDd_ dc nm), showTree1' nm f (getDd_ n1 nm), showTree0' nm f (getDd_ p0 nm)])
        showTree' f (InfNodes a dc n1 1 p1 1) = ("<"++ f a ++ "> dc, n1, p1)") : "  ║  " : concat (indentInfChildren [showTree' f (getDd_ dc nm), showTree1' nm f (getDd_ n1 nm), showTree1' nm f (getDd_ p1 nm)])
        showTree' f (InfNodes a dc n1 n0 0 1) = ("<"++ f a ++ "> dc, n1, n0)") : "  ║  " : concat (indentInfChildren [showTree' f (getDd_ dc nm), showTree1' nm f (getDd_ n1 nm), showTree0' nm f (getDd_ n0 nm)])
        showTree' f (InfNodes a dc 0 n0 p1 p0) = ("<"++ f a ++ "> dc, n0, p1, p0)") : "  ║  " : concat (indentInfChildren [showTree' f (getDd_ dc nm), showTree0' nm f (getDd_ n0 nm), showTree1' nm f (getDd_ p1 nm), showTree0' nm f (getDd_ p0 nm)])
        showTree' f (InfNodes a dc n1 1 p1 p0) = ("<"++ f a ++ "> dc, n1, p1, p0)") : "  ║  " : concat (indentInfChildren [showTree' f (getDd_ dc nm), showTree1' nm f (getDd_ n1 nm), showTree1' nm f (getDd_ p1 nm), showTree0' nm f (getDd_ p0 nm)])
        showTree' f (InfNodes a dc n1 n0 0 p0) = ("<"++ f a ++ "> dc, n0, p1, p0)") : "  ║  " : concat (indentInfChildren [showTree' f (getDd_ dc nm), showTree1' nm f (getDd_ n1 nm), showTree0' nm f (getDd_ n0 nm), showTree0' nm f (getDd_ p0 nm)])
        showTree' f (InfNodes a dc n1 n0 p1 0) = ("<"++ f a ++ "> dc, n0, p1, p0)") : "  ║  " : concat (indentInfChildren [showTree' f (getDd_ dc nm), showTree1' nm f (getDd_ n1 nm), showTree0' nm f (getDd_ n0 nm), showTree1' nm f (getDd_ p1 nm)])
        showTree' f (InfNodes a dc n1 n0 p1 p0) =("<"++ f a ++ "> dc, n1, n0, p1, p0") : "  ║  " : concat (indentInfChildren [showTree' f (getDd_ dc nm), showTree1' nm f (getDd_ n1 nm), showTree0' nm f (getDd_ n0 nm), showTree1' nm f (getDd_ p1 nm), showTree0' nm f (getDd_ p0 nm)])
        showTree' f (EndInfNode cons) = "<>" : "  ║  " : concat (indentInfChildren [showTree' f (getDd_ cons nm)])

showTree :: NodeLookup -> Dd -> String
showTree nm = unlines . showTree'' nm show

showTree2 :: NodeLookup -> Dd -> String
showTree2 nm = unlines . showTree'' nm show

drawTree :: NodeLookup -> NodeId -> IO ()
drawTree nm = putStrLn . showTree nm . (\x -> getDd_ x nm)

drawTree2 :: NodeLookup -> Dd -> IO ()
drawTree2 nm = putStrLn . showTree2 nm

-- disp :: Map.Map Ordinal (Either (Map.Map Int String) String) -> Dd -> IO ()
-- disp m = putStrLn . unlines . showTree' (show . (\case
--    Left x -> if Map.member x m then m Map.! x else error $ "key: " ++ show x ++ " not in keys: " ++ show (Map.keys m)))
