{-# LANGUAGE LambdaCase #-}
module DrawMDD where
import MDD
import System.IO
-- import Test.Hspec
import qualified Data.Map as Map
import Control.Monad.State

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

-- showTree0' :: Context -> (Int -> String) -> Dd -> [String]
-- showTree0' c _ (Leaf True) = ["   "]
-- showTree0' c _ (Leaf False) = ["[0]"]
-- showTree0' c f (Node a l r) = ("("++ f a ++")") : concat (indentChildren (map (showTree0' c f) [getDd c l, getDd c r]))
-- showTree0' c f x = showTree' c f x

showTree0' :: (NodeId -> String) -> Dd -> State Context [String]
showTree0' _ (Leaf True) = return ["   "]
showTree0' _ (Leaf False) = return ["[0]"]
showTree0' f (Node a l r) = do
  leftDd <- getDd l
  rightDd <- getDd r
  leftStr <- showTree0' f leftDd
  rightStr <- showTree0' f rightDd
  return $ ("(" ++ f a ++ ")") : concat (indentChildren [leftStr, rightStr])
showTree0' f x = showTree' f x  -- Assuming showTree' is similarly refactored

showTree1' :: (NodeId -> String) -> Dd -> State Context [String]
showTree1' _ (Leaf True) = return ["[1]"]
showTree1' _ (Leaf False) = return ["   "]
showTree1' f (Node a l r) = do
  leftDd <- getDd l
  rightDd <- getDd r
  leftStr <- showTree1' f leftDd
  rightStr <- showTree1' f rightDd
  return $ ("(" ++ f a ++ ")") : concat (indentChildren [leftStr, rightStr])
showTree1' f x = showTree' f x  -- Assuming showTree' is similarly refactored

showTree' :: (Int -> String) -> Dd -> State Context [String]
showTree' _ (Leaf False) = return ["[1]"]
showTree' _ (Leaf True) = return ["[0]"]
showTree' f (Node a l r) = do
  leftDd <- getDd l
  rightDd <- getDd r
  leftStr <- showTree' f leftDd
  rightStr <- showTree' f rightDd
  return $ ("(" ++ f a ++ ")") : concat (indentChildren [leftStr, rightStr])
showTree' f (InfNodes a dc 0 1 0 1) = do
  dcDd <- getDd dc
  dcStr <- showTree' f dcDd
  return $ ("<" ++ f a ++ "> dc") : "  ║  " : concat (indentInfChildren [dcStr])

-- Adapt similarly for other InfNodes patterns
showTree' f (InfNodes a dc 0 1 0 p0) = do
  dcDd <- getDd dc
  p0Dd <- getDd p0
  dcStr <- showTree' f dcDd
  p0Str <- showTree0' f p0Dd
  return $ ("<" ++ f a ++ "> dc, p0") : "  ║  " : concat (indentInfChildren [dcStr, p0Str])
showTree' f (InfNodes a dc 0 1 p1 1) = do
  dcDd <- getDd dc
  p0Dd <- getDd p1
  dcStr <- showTree' f dcDd
  p0Str <- showTree0' f p0Dd
  return $ ("<" ++ f a ++ "> dc, p0") : "  ║  " : concat (indentInfChildren [dcStr, p0Str])
showTree' f (InfNodes a dc 0 n0 0 1) = do
  dcDd <- getDd dc
  p0Dd <- getDd n0
  dcStr <- showTree' f dcDd
  p0Str <- showTree0' f p0Dd -- Note: showTree0' needs to be adapted to State Context as well
  return $ ("<" ++ f a ++ "> dc, p0") : "  ║  " : concat (indentInfChildren [dcStr, p0Str])
showTree' f (InfNodes a dc n1 1 0 1) = do
  dcDd <- getDd dc
  p0Dd <- getDd n1
  dcStr <- showTree' f dcDd
  p0Str <- showTree0' f p0Dd -- Note: showTree0' needs to be adapted to State Context as well
  return $ ("<" ++ f a ++ "> dc, p0") : "  ║  " : concat (indentInfChildren [dcStr, p0Str])

showTree' f (InfNodes a dc 0 1 p1 p0) = do
  dcStrings <- getDd dc >>= showTree' f
  p1Strings <- getDd p1 >>= showTree1' f
  p0Strings <- getDd p0 >>= showTree0' f
  return $ ("<" ++ f a ++ "> dc, p1, p0)") : "  ║  " : concat (indentInfChildren [dcStrings, p1Strings, p0Strings])
showTree' f (InfNodes a dc 0 n0 0 p0) = do
  dcStrings <- getDd dc >>= showTree' f
  n0Strings <- getDd n0 >>= showTree0' f
  p0Strings <- getDd p0 >>= showTree0' f
  return $ ("<" ++ f a ++ "> dc, n0, p0)") : "  ║  " : concat (indentInfChildren [dcStrings, n0Strings, p0Strings])
showTree' f (InfNodes a dc 0 n0 p1 1) = do
  dcStrings <- getDd dc >>= showTree' f
  n0Strings <- getDd n0 >>= showTree0' f
  p1Strings <- getDd p1 >>= showTree1' f
  return $ ("<" ++ f a ++ "> dc, n0, p1)") : "  ║  " : concat (indentInfChildren [dcStrings, n0Strings, p1Strings])
showTree' f (InfNodes a dc n1 1 0 p0) = do
  dcStrings <- getDd dc >>= showTree' f
  n1Strings <- getDd n1 >>= showTree1' f
  p0Strings <- getDd p0 >>= showTree0' f
  return $ ("<" ++ f a ++ "> dc, n1, p0)") : "  ║  " : concat (indentInfChildren [dcStrings, n1Strings, p0Strings])
showTree' f (InfNodes a dc n1 1 p1 1) = do
  dcStrings <- getDd dc >>= showTree' f
  n1Strings <- getDd n1 >>= showTree1' f
  p1Strings <- getDd p1 >>= showTree1' f
  return $ ("<" ++ f a ++ "> dc, n1, p1)") : "  ║  " : concat (indentInfChildren [dcStrings, n1Strings, p1Strings])
showTree' f (InfNodes a dc n1 n0 0 1) = do
  dcStrings <- getDd dc >>= showTree' f
  n1Strings <- getDd n1 >>= showTree1' f
  n0Strings <- getDd n0 >>= showTree0' f
  return $ ("<" ++ f a ++ "> dc, n1, n0)") : "  ║  " : concat (indentInfChildren [dcStrings, n1Strings, n0Strings])

showTree' f (InfNodes a dc 0 n0 p1 p0) = do
  dcStrings <- getDd dc >>= showTree' f
  n0Strings <- getDd n0 >>= showTree0' f
  p1Strings <- getDd p1 >>= showTree1' f
  p0Strings <- getDd p0 >>= showTree0' f
  return $ ("<" ++ f a ++ "> dc, n0, p1, p0)") : "  ║  " : concat (indentInfChildren [dcStrings, n0Strings, p1Strings, p0Strings])

showTree' f (InfNodes a dc n1 1 p1 p0) = do
  dcStrings <- getDd dc >>= showTree' f
  n1Strings <- getDd n1 >>= showTree1' f
  p1Strings <- getDd p1 >>= showTree1' f
  p0Strings <- getDd p0 >>= showTree0' f
  return $ ("<" ++ f a ++ "> dc, n1, p1, p0)") : "  ║  " : concat (indentInfChildren [dcStrings, n1Strings, p1Strings, p0Strings])

showTree' f (InfNodes a dc n1 n0 0 p0) = do
  dcStrings <- getDd dc >>= showTree' f
  n1Strings <- getDd n1 >>= showTree1' f
  n0Strings <- getDd n0 >>= showTree0' f
  p0Strings <- getDd p0 >>= showTree0' f
  return $ ("<" ++ f a ++ "> dc, n1, n0, p0)") : "  ║  " : concat (indentInfChildren [dcStrings, n1Strings, n0Strings, p0Strings])

showTree' f (InfNodes a dc n1 n0 p1 0) = do
  dcStrings <- getDd dc >>= showTree' f
  n1Strings <- getDd n1 >>= showTree1' f
  n0Strings <- getDd n0 >>= showTree0' f
  p1Strings <- getDd p1 >>= showTree1' f
  return $ ("<" ++ f a ++ "> dc, n1, n0, p1)") : "  ║  " : concat (indentInfChildren [dcStrings, n1Strings, n0Strings, p1Strings])


showTree' f (InfNodes a dc n1 n0 p1 p0) = do
  -- Fetch Dd instances for each nodeId
  dcDd <- getDd dc
  n1Dd <- getDd n1
  n0Dd <- getDd n0
  p1Dd <- getDd p1
  p0Dd <- getDd p0
  -- Generate string representations for each Dd
  dcStr <- showTree' f dcDd
  n1Str <- showTree1' f n1Dd
  n0Str <- showTree0' f n0Dd
  p1Str <- showTree1' f p1Dd
  p0Str <- showTree0' f p0Dd
  return $ ("<" ++ f a ++ "> dc, n1, n0, p1, p0") : "  ║  " : concat (indentInfChildren [dcStr, n1Str, n0Str, p1Str, p0Str])

showTree' f (EndInfNode cons) = do
  consDd <- getDd cons
  consStr <- showTree' f consDd
  return $ "<>" : "  ║  " : concat (indentInfChildren [consStr])
--showTree' (Node n ns) = n : concat (indentChildren (map showTree' ns))

-- showTree' c _ (Leaf False) = ["[1]"]
-- showTree' c _ (Leaf True) = ["[0]"]
-- showTree' c f (Node a l r) = ("("++ f a ++")") : concat (indentChildren (map (showTree' c f) [getDd c l, getDd c r]))
-- showTree' c f (InfNodes a dc 0 1 0 1) = ("<"++ f a ++ "> dc") : "  ║  " : concat (indentInfChildren [showTree' c f (getDd c dc)])

-- showTree' c f (InfNodes a dc 0 1 0 p0) =("<"++ f a ++ "> dc, p0") : "  ║  " : concat (indentInfChildren [showTree' c f (getDd c dc), showTree0' c f (getDd c p0)])
-- showTree' c f (InfNodes a dc 0 1 p1 1) =("<"++ f a ++ "> dc, p1") : "  ║  " : concat (indentInfChildren [showTree' c f (getDd c dc), showTree1' c f (getDd c p1)])
-- showTree' c f (InfNodes a dc 0 n0 0 1) =("<"++ f a ++ "> dc, n0") : "  ║  " : concat (indentInfChildren [showTree' c f (getDd c dc), showTree0' c f (getDd c n0)])
-- showTree' c f (InfNodes a dc n1 1 0 1) =("<"++ f a ++ "> dc, n1") : "  ║  " : concat (indentInfChildren [showTree' c f (getDd c dc), showTree1' c f (getDd c n1)])

-- showTree' c f (InfNodes a dc 0 1 p1 p0) = ("<"++ f a ++ "> dc, p1, p0)") : "  ║  " : concat (indentInfChildren [showTree' c f (getDd c dc), showTree1' c f (getDd c p1), showTree0' c f (getDd c p0)])
-- showTree' c f (InfNodes a dc 0 n0 0 p0) = ("<"++ f a ++ "> dc, n0, p0)") : "  ║  " : concat (indentInfChildren [showTree' c f (getDd c dc), showTree0' c f (getDd c n0), showTree0' c f (getDd c p0)])
-- showTree' c f (InfNodes a dc 0 n0 p1 1) = ("<"++ f a ++ "> dc, n0, p1)") : "  ║  " : concat (indentInfChildren [showTree' c f (getDd c dc), showTree0' c f (getDd c n0), showTree1' c f (getDd c p1)])
-- showTree' c f (InfNodes a dc n1 1 0 p0) = ("<"++ f a ++ "> dc, n1, p0)") : "  ║  " : concat (indentInfChildren [showTree' c f (getDd c dc), showTree1' c f (getDd c n1), showTree0' c f (getDd c p0)])
-- showTree' c f (InfNodes a dc n1 1 p1 1) = ("<"++ f a ++ "> dc, n1, p1)") : "  ║  " : concat (indentInfChildren [showTree' c f (getDd c dc), showTree1' c f (getDd c n1), showTree1' c f (getDd c p1)])
-- showTree' c f (InfNodes a dc n1 n0 0 1) = ("<"++ f a ++ "> dc, n1, n0)") : "  ║  " : concat (indentInfChildren [showTree' c f (getDd c dc), showTree1' c f (getDd c n1), showTree0' c f (getDd c n0)])

-- showTree' c f (InfNodes a dc 0 n0 p1 p0) = ("<"++ f a ++ "> dc, n0, p1, p0)") : "  ║  " : concat (indentInfChildren [showTree' c f (getDd c dc), showTree0' c f (getDd c n0), showTree1' c f (getDd c p1), showTree0' c f (getDd c p0)])
-- showTree' c f (InfNodes a dc n1 1 p1 p0) = ("<"++ f a ++ "> dc, n1, p1, p0)") : "  ║  " : concat (indentInfChildren [showTree' c f (getDd c dc), showTree1' c f (getDd c n1), showTree1' c f (getDd c p1), showTree0' c f (getDd c p0)])
-- showTree' c f (InfNodes a dc n1 n0 0 p0) = ("<"++ f a ++ "> dc, n0, p1, p0)") : "  ║  " : concat (indentInfChildren [showTree' c f (getDd c dc), showTree1' c f (getDd c n1), showTree0' c f (getDd c n0), showTree0' c f (getDd c p0)])
-- showTree' c f (InfNodes a dc n1 n0 p1 0) = ("<"++ f a ++ "> dc, n0, p1, p0)") : "  ║  " : concat (indentInfChildren [showTree' c f (getDd c dc), showTree1' c f (getDd c n1), showTree0' c f (getDd c n0), showTree1' c f (getDd c p1)])

-- showTree' c f (InfNodes a dc n1 n0 p1 p0) =("<"++ f a ++ "> dc, n1, n0, p1, p0") : "  ║  " : concat (indentInfChildren [showTree' c f (getDd c dc), showTree1' c f (getDd c n1), showTree0' c f (getDd c n0), showTree1' c f (getDd c p1), showTree0' c f (getDd c p0)])
-- showTree' c f (EndInfNode cons) = "<>" : "  ║  " : concat (indentInfChildren [showTree' c f (getDd c cons)])

showTree :: Context -> Dd -> String
showTree c dd = unlines . evalState (showTree' show dd) $ c

showTree2 :: Context -> Dd -> String
showTree2 c dd = unlines . evalState (showTree' show dd) $ c


drawTree :: Context -> NodeId -> IO ()
drawTree c nodeId = do
    let ddAction = getDd nodeId >>= showTree' show
    let output = unlines . evalState ddAction $ c
    putStrLn output


drawTree2 :: Context -> Dd -> IO ()
drawTree2 c = putStrLn . showTree2 c

-- disp :: Map.Map Ordinal (Either (Map.Map Int String) String) -> Dd -> IO ()
-- disp m = putStrLn . unlines . showTree' (show . (\case
--    Left x -> if Map.member x m then m Map.! x else error $ "key: " ++ show x ++ " not in keys: " ++ show (Map.keys m)))
