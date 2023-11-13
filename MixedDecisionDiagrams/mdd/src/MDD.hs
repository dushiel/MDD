{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module MDD where

import Debug.Trace ( trace )

-- proof of concept GenDDs where no merging of isomorphic nodes happen and no cashing / moization of results during traversal.
-- GenDDs can model check second order logic formulas containing variables in multiple (disjointed and/or nested) infinite domains.


-- |======================================== Data Types + Explanation ==============================================


data Dd =  Node Int Dd Dd               -- left = pos, right = neg
                | InfNodes Int Dd Dd Dd Dd Dd    -- sets the inference type when traversing through the tree depending which literal type is inf. We place them at the top (of each sub path of infinite domain). We can have multiple branches due to the multiple possible contexts.
                | EndInfNode Dd
                | Leaf Bool
    deriving (Eq)

data Inf = Dc | Neg1 | Neg0 | Pos1 | Pos0
    deriving (Eq, Show)

-- as we traverse through the graph, we can get nested inference contexts:
type Context = [Inf]


top :: Dd
top = Leaf True

bot :: Dd
bot = Leaf False


-- With makeNode we can never produce a ZDD with 2 specified nodes. See makePath for the more generalised construction of a (single) path in MDDs.
-- Set the node to pos, except for the positiove inference - there it sets it to neg --todo make this clearer?
makeNode :: Int -> Inf -> Dd
makeNode i c
    | c == Dc = InfNodes i (Node i (Leaf True) (Leaf False)) (Leaf False) (Leaf True) (Leaf False) (Leaf True)
    | c == Neg1 = InfNodes i (Leaf False) (Node i (Leaf True) (Leaf False)) (Leaf True) (Leaf False) (Leaf True)
    | c == Neg0 = InfNodes i (Leaf True) (Leaf False) (Node i (Leaf False) (Leaf True)) (Leaf False) (Leaf True)
    | c == Pos1 = InfNodes i (Leaf False) (Leaf False) (Leaf True) (Node i (Leaf False) (Leaf True)) (Leaf True)
    | c == Pos0 = InfNodes i (Leaf True) (Leaf False) (Leaf True) (Leaf False) (Node i (Leaf True) (Leaf False))
    | otherwise = error "empty ordinal for makeNode"


-- At the variable class given represented by the ordinal, create a path containing the specified nodes from the list with the given inference rule.
-- We assume fixed variable classes, it is the responsibility of the user to give the correct ordinal
-- give empty list to create empty ZDD, e.g. : makePath (Order [1,2]) [] Neg1

-- For making paths that take multiple Infnodes through finite types.
-- used for e.g. [2::Neg1, 1::Neg1, 3::Neg1]
-- possible to give an empty list for the nodes to be set to positive
-- place a minus sign before a node nr to set it to negative.

data Transfinite_adress = T [(Int, Inf)] [Int]

path :: [(Int, Inf)] -> [Int] -> Dd
path = makeLocalPath

makeLocalPath :: [(Int, Inf)] -> [Int] -> Dd
makeLocalPath a b = makeLocalPath' a b 1

unpackEndInf :: Dd -> Dd
unpackEndInf (EndInfNode d) = d
unpackEndInf _ = error "not possible"


-- < 0:dc > 3' 4' <2: n1>

makeLocalPath' :: [(Int, Inf)] -> [Int] -> Int -> Dd
makeLocalPath' [] _ _ = error "empty context"

makeLocalPath' [(i, inf)] nodeList l
    | inf == Dc = InfNodes i (loopDc nodeList False) (Leaf False) (Leaf True) (Leaf False) (Leaf True)
    | inf == Neg1 = InfNodes i ( Leaf False) (loopNeg nodeList False ) (Leaf True) (Leaf False) (Leaf True)
    | inf == Neg0 = InfNodes i ( Leaf True) (Leaf False) (loopNeg nodeList True) (Leaf False) (Leaf True)
    | inf == Pos1 = InfNodes i ( Leaf False) (Leaf False) (Leaf True) (loopPos nodeList False) (Leaf True)
    | inf == Pos0 = InfNodes i ( Leaf True) (Leaf False) (Leaf True) (Leaf False) (loopPos nodeList True)
    where
        loopDc (n:ns) end = if n <=0 then Node (abs n) ((Leaf True)) (loopNeg ns end) else Node n (loopNeg ns end) ((Leaf False))
        loopNeg [] end = (Leaf $ not end)
        loopNeg (n:ns) end = if n <=0 then Node (abs n) (Leaf end) (loopNeg ns end) else Node n (loopNeg ns end) (Leaf end)
        loopPos [] end = (Leaf $ not end)
        loopPos (n:ns) end = if n <=0 then Node (abs n) (loopNeg ns end) (Leaf end) else Node n (Leaf end) (loopPos ns end)
        close = (!! l) . iterate EndInfNode

makeLocalPath' ((i, inf):cs) nodeList l
    | inf == Dc = InfNodes i (makeLocalPath' cs nodeList (l+1)) (Leaf False) (Leaf True) (Leaf False) (Leaf True)
    | inf == Neg1 = InfNodes i ( Leaf False) (makeLocalPath' cs nodeList (l+1) ) (Leaf True) (Leaf False) (Leaf True)
    | inf == Neg0 = InfNodes i ( Leaf True) (Leaf False) (makeLocalPath' cs nodeList (l+1)) (Leaf False) (Leaf True)
    | inf == Pos1 = InfNodes i ( Leaf False) (Leaf False) (Leaf True) (makeLocalPath' cs nodeList (l+1)) (Leaf True)
    | inf == Pos0 = InfNodes i ( Leaf True) (Leaf False) (Leaf True) (Leaf False) (makeLocalPath' cs nodeList (l+1))
    where
        close = (!! l) . iterate EndInfNode




instance Show Dd where
    show (Leaf True) = "1"
    show (Leaf False) = "0"
    show (EndInfNode d) = " <> " ++ show d
    show (Node a l r) = " " ++ show a ++ " (" ++ show l ++ ") (" ++ show r ++ ")"
    show (InfNodes a dc (Leaf False) (Leaf True) (Leaf False) (Leaf True)) = " " ++ show a ++ " ( dc: " ++ show dc ++ " )"

    show (InfNodes a dc (Leaf False) (Leaf True) (Leaf False) p0) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( p0: " ++ show p0 ++ " )"
    show (InfNodes a dc (Leaf False) (Leaf True) p1 (Leaf True)) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( p1: " ++ show p1 ++ " )"
    show (InfNodes a dc (Leaf False) n0 (Leaf False) (Leaf True)) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n0: " ++ show n0 ++ " )"
    show (InfNodes a dc n1 (Leaf True) (Leaf False) (Leaf True)) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n1: " ++ show n1 ++ " )"

    show (InfNodes a dc (Leaf False) (Leaf True) p1 p0) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( p1: " ++ show p1 ++ " ) ( p0: " ++ show p0 ++ " )"
    show (InfNodes a dc (Leaf False) n0 (Leaf False) p0) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n0: " ++ show n0 ++ " ) ( p0: " ++ show p0 ++ " )"
    show (InfNodes a dc (Leaf False) n0 p1 (Leaf True)) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n0: " ++ show n0 ++ " ) ( p1: " ++ show p1 ++ " )"
    show (InfNodes a dc n1 (Leaf True) (Leaf False) p0) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n1: " ++ show n1 ++ " ) ( p0: " ++ show p0 ++ " )"
    show (InfNodes a dc n1 (Leaf True) p1 (Leaf True)) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n1: " ++ show n1 ++ " ) ( p1: " ++ show p1 ++ " )"
    show (InfNodes a dc n1 n0 (Leaf False) (Leaf True)) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n1: " ++ show n1 ++ " ) ( n0: " ++ show n0 ++ " )"

    show (InfNodes a dc (Leaf False) n0 p1 p0) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n0: " ++ show n0 ++ " ) ( p1: " ++ show p1 ++ " ) ( p0: " ++ show p0 ++ " )"
    show (InfNodes a dc n1 (Leaf True) p1 p0) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n1: " ++ show n1 ++ " ) ( p1: " ++ show p1 ++ " ) ( p0: " ++ show p0 ++ " )"
    show (InfNodes a dc n1 n0 (Leaf False) p0) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n1: " ++ show n1 ++ " ) ( n0: " ++ show n0 ++ " ) ( p0: " ++ show p0 ++ " )"
    show (InfNodes a dc n1 n0 p1 (Leaf False)) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n1: " ++ show n1 ++ " ) ( n0: " ++ show n0 ++ " ) ( p1: " ++ show p1 ++ " )"

    show (InfNodes a dc n1 n0 p1 p0) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n1: " ++ show n1 ++ " ) ( n0: " ++ show n0 ++ " ) ( p1: " ++ show p1 ++ " ) ( p0: " ++ show p0 ++ " )"
