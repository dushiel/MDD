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

showTree0' :: Context -> (Int -> String) -> Dd -> [String]
showTree0' _ _ (Leaf True) = ["   "]
showTree0' _ _ (Leaf False) = ["[0]"]
showTree0' c f (Node a l r) = ("("++ f a ++")") : concat (indentChildren (map (showTree0' c f) [getDd c l, getDd c r]))
showTree0' c f x = showTree'' c f x

showTree1' :: Context -> (Int -> String) -> Dd -> [String]
showTree1' _ _ (Leaf True) = ["[1]"]
showTree1' _ _ (Leaf False) = ["   "]
showTree1' c f (Node a l r) = ("("++ f a ++")") : concat (indentChildren (map (showTree1' c f) [getDd c l, getDd c r]))
showTree1' c f x = showTree'' c f x

showTree'' :: Context -> (Int -> String) -> Dd -> [String]
--showTree' (Node n ns) = n : concat (indentChildren (map showTree' ns))
showTree'' c =  showTree'
    where
        showTree' _ (Leaf False) = ["[1]"]
        showTree' _ (Leaf True) = ["[0]"]
        showTree' f (Node a l r) = ("("++ f a ++")") : concat (indentChildren (map (showTree' f) [getDd c l, getDd c r]))
        showTree' f (InfNodes a dc (0, 0) (1,0) (0, 0) (1,0)) = ("<"++ f a ++ "> dc") : "  ║  " : concat (indentInfChildren [showTree' f (getDd c dc)])
        showTree' f (InfNodes a dc (0, 0) (1,0) (0, 0) p0) =("<"++ f a ++ "> dc, p0") : "  ║  " : concat (indentInfChildren [showTree' f (getDd c dc), showTree0' c f (getDd c p0)])
        showTree' f (InfNodes a dc (0, 0) (1,0) p1 (1,0)) =("<"++ f a ++ "> dc, p1") : "  ║  " : concat (indentInfChildren [showTree' f (getDd c dc), showTree1' c f (getDd c p1)])
        showTree' f (InfNodes a dc (0, 0) n0 (0, 0) (1,0)) =("<"++ f a ++ "> dc, n0") : "  ║  " : concat (indentInfChildren [showTree' f (getDd c dc), showTree0' c f (getDd c n0)])
        showTree' f (InfNodes a dc n1 (1,0) (0, 0) (1,0)) =("<"++ f a ++ "> dc, n1") : "  ║  " : concat (indentInfChildren [showTree' f (getDd c dc), showTree1' c f (getDd c n1)])
        showTree' f (InfNodes a dc (0, 0) (1,0) p1 p0) = ("<"++ f a ++ "> dc, p1, p0") : "  ║  " : concat (indentInfChildren [showTree' f (getDd c dc), showTree1' c f (getDd c p1), showTree0' c f (getDd c p0)])
        showTree' f (InfNodes a dc (0, 0) n0 (0, 0) p0) = ("<"++ f a ++ "> dc, n0, p0") : "  ║  " : concat (indentInfChildren [showTree' f (getDd c dc), showTree0' c f (getDd c n0), showTree0' c f (getDd c p0)])
        showTree' f (InfNodes a dc (0, 0) n0 p1 (1,0)) = ("<"++ f a ++ "> dc, n0, p1") : "  ║  " : concat (indentInfChildren [showTree' f (getDd c dc), showTree0' c f (getDd c n0), showTree1' c f (getDd c p1)])
        showTree' f (InfNodes a dc n1 (1,0) (0, 0) p0) = ("<"++ f a ++ "> dc, n1, p0") : "  ║  " : concat (indentInfChildren [showTree' f (getDd c dc), showTree1' c f (getDd c n1), showTree0' c f (getDd c p0)])
        showTree' f (InfNodes a dc n1 (1,0) p1 (1,0)) = ("<"++ f a ++ "> dc, n1, p1") : "  ║  " : concat (indentInfChildren [showTree' f (getDd c dc), showTree1' c f (getDd c n1), showTree1' c f (getDd c p1)])
        showTree' f (InfNodes a dc n1 n0 (0, 0) (1,0)) = ("<"++ f a ++ "> dc, n1, n0") : "  ║  " : concat (indentInfChildren [showTree' f (getDd c dc), showTree1' c f (getDd c n1), showTree0' c f (getDd c n0)])
        showTree' f (InfNodes a dc (0, 0) n0 p1 p0) = ("<"++ f a ++ "> dc, n0, p1, p0") : "  ║  " : concat (indentInfChildren [showTree' f (getDd c dc), showTree0' c f (getDd c n0), showTree1' c f (getDd c p1), showTree0' c f (getDd c p0)])
        showTree' f (InfNodes a dc n1 (1,0) p1 p0) = ("<"++ f a ++ "> dc, n1, p1, p0") : "  ║  " : concat (indentInfChildren [showTree' f (getDd c dc), showTree1' c f (getDd c n1), showTree1' c f (getDd c p1), showTree0' c f (getDd c p0)])
        showTree' f (InfNodes a dc n1 n0 (0, 0) p0) = ("<"++ f a ++ "> dc, n1, n0, p0") : "  ║  " : concat (indentInfChildren [showTree' f (getDd c dc), showTree1' c f (getDd c n1), showTree0' c f (getDd c n0), showTree0' c f (getDd c p0)])
        showTree' f (InfNodes a dc n1 n0 p1 (0, 0)) = ("<"++ f a ++ "> dc, n1, n0, p1") : "  ║  " : concat (indentInfChildren [showTree' f (getDd c dc), showTree1' c f (getDd c n1), showTree0' c f (getDd c n0), showTree1' c f (getDd c p1)]) `debug` (" draw: " ++  show n0 ++ show n1 ++ show p1)
        showTree' f (InfNodes a dc n1 n0 p1 p0) =("<"++ f a ++ "> dc, n1, n0, p1, p0") : "  ║  " : concat (indentInfChildren [showTree' f (getDd c dc), showTree1' c f (getDd c n1), showTree0' c f (getDd c n0), showTree1' c f (getDd c p1), showTree0' c f (getDd c p0)])
        showTree' f (EndInfNode cons) = "<>" : "  ║  " : concat (indentInfChildren [showTree' f (getDd c cons)])

showTree :: Context -> Dd -> String
showTree c = unlines . showTree'' c show

showTree2 :: Context -> Dd -> String
showTree2 c = unlines . showTree'' c show

drawTree :: Context -> NodeId -> IO ()
drawTree c x = putStrLn . showTree c $ getDd c x

drawTree2 :: Context -> Dd -> IO ()
drawTree2 c = putStrLn . showTree2 c

-- disp :: Map.Map Ordinal (Either (Map.Map Int String) String) -> Dd -> IO ()
-- disp m = putStrLn . unlines . showTree' (show . (\case
--    Left x -> if Map.member x m then m Map.! x else error $ "key: " ++ show x ++ " not in keys: " ++ show (Map.keys m)))
