module MixedDecisionDiagrams.Src.DrawMDD
    ( showTree
    , drawTree
    ) where
import MixedDecisionDiagrams.Src.MDD
import System.IO



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

showTree0' :: Dd Ordinal -> [String]
showTree0' (Leaf True) = ["   "]
showTree0' (Leaf False) = ["[0]"]
showTree0' (Node (Order a) l r) = ("("++show ( a)++")") : concat (indentChildren (map showTree0' [l, r]))
showTree0' x = showTree' x

showTree1' :: Dd Ordinal -> [String]
showTree1' (Leaf True) = ["[1]"]
showTree1' (Leaf False) = ["   "]
showTree1' (Node (Order a) l r) = ("("++show ( a)++")") : concat (indentChildren (map showTree1' [l, r]))
showTree1' x = showTree' x

showTree' :: Dd Ordinal -> [String]
--showTree' (Node n ns) = n : concat (indentChildren (map showTree' ns))

showTree' (Leaf True) = ["[1]"]
showTree' (Leaf False) = ["[0]"]
showTree' (Node (Order a) l r) = ("("++show ( a)++")") : concat (indentChildren (map showTree' [l, r]))
showTree' (InfNodes a dc (Leaf False) (Leaf True) (Leaf False) (Leaf True)) = ("<"++ show a ++ "> dc") : "  ║  " : concat (indentInfChildren [showTree' dc])

showTree' (InfNodes a dc (Leaf False) (Leaf True) (Leaf False) p0) =("<"++ show a ++ "> dc, p0") : "  ║  " : concat (indentInfChildren [showTree' dc, showTree0' p0])
showTree' (InfNodes a dc (Leaf False) (Leaf True) p1 (Leaf True)) =("<"++ show a ++ "> dc, p1") : "  ║  " : concat (indentInfChildren [showTree' dc, showTree1' p1])
showTree' (InfNodes a dc (Leaf False) n0 (Leaf False) (Leaf True)) =("<"++ show a ++ "> dc, n0") : "  ║  " : concat (indentInfChildren [showTree' dc, showTree0' n0])
showTree' (InfNodes a dc n1 (Leaf True) (Leaf False) (Leaf True)) =("<"++ show a ++ "> dc, n1") : "  ║  " : concat (indentInfChildren [showTree' dc, showTree1' n1])

showTree' (InfNodes a dc (Leaf False) (Leaf True) p1 p0) = ("<"++ show a ++ "> dc, p1, p0)") : "  ║  " : concat (indentInfChildren [showTree' dc, showTree1' p1, showTree0' p0])
showTree' (InfNodes a dc (Leaf False) n0 (Leaf False) p0) = ("<"++ show a ++ "> dc, n0, p0)") : "  ║  " : concat (indentInfChildren [showTree' dc, showTree0' n0, showTree0' p0])
showTree' (InfNodes a dc (Leaf False) n0 p1 (Leaf True)) = ("<"++ show a ++ "> dc, n0, p1)") : "  ║  " : concat (indentInfChildren [showTree' dc, showTree0' n0, showTree1' p1])
showTree' (InfNodes a dc n1 (Leaf True) (Leaf False) p0) = ("<"++ show a ++ "> dc, n1, p0)") : "  ║  " : concat (indentInfChildren [showTree' dc, showTree1' n1, showTree0' p0])
showTree' (InfNodes a dc n1 (Leaf True) p1 (Leaf True)) = ("<"++ show a ++ "> dc, n1, p1)") : "  ║  " : concat (indentInfChildren [showTree' dc, showTree1' n1, showTree1' p1])
showTree' (InfNodes a dc n1 n0 (Leaf False) (Leaf True)) = ("<"++ show a ++ "> dc, n1, n0)") : "  ║  " : concat (indentInfChildren [showTree' dc, showTree1' n1, showTree0' n0])

showTree' (InfNodes a dc (Leaf False) n0 p1 p0) = ("<"++ show a ++ "> dc, n0, p1, p0)") : "  ║  " : concat (indentInfChildren [showTree' dc, showTree0' n0, showTree1' p1, showTree0' p0])
showTree' (InfNodes a dc n1 (Leaf True) p1 p0) = ("<"++ show a ++ "> dc, n1, p1, p0)") : "  ║  " : concat (indentInfChildren [showTree' dc, showTree1' n1, showTree1' p1, showTree0' p0])
showTree' (InfNodes a dc n1 n0 (Leaf False) p0) = ("<"++ show a ++ "> dc, n0, p1, p0)") : "  ║  " : concat (indentInfChildren [showTree' dc, showTree1' n1, showTree0' n0, showTree0' p0])
showTree' (InfNodes a dc n1 n0 p1 (Leaf False)) = ("<"++ show a ++ "> dc, n0, p1, p0)") : "  ║  " : concat (indentInfChildren [showTree' dc, showTree1' n1, showTree0' n0, showTree1' p1])

showTree' (InfNodes a dc n1 n0 p1 p0) =("<"++ show a ++ "> dc, n1, n0, p1, p0") : "  ║  " : concat (indentInfChildren [showTree' dc, showTree1' n1, showTree0'  n0, showTree1' p1, showTree0' p0])


showTree :: Dd Ordinal -> String
showTree = unlines . showTree'

drawTree :: Dd Ordinal -> IO ()
drawTree = putStrLn . showTree


