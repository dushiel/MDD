{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module MixedDecisionDiagrams.Src.MDD where

import Debug.Trace ( trace )
import Distribution.PackageDescription.Configuration (freeVars)
import Data.List (sort)
-- proof of concept GenDDs where no merging of isomorphic nodes happen and no cashing / moization of results during traversal.
-- GenDDs can model check second order logic formulas containing variables in multiple (disjointed and/or nested) infinite domains.

-- todo do you repeat the dc information for finite set of paths ?
-- todo add InfNode reduction

-- |======================================== Data Types + Explanation ==============================================


data Dd a =  Node !a !(Dd a) !(Dd a)               -- left = pos, right = neg
                | InfNodes !a !(Dd a) !(Dd a) !(Dd a) !(Dd a) !(Dd a)    -- sets the inference type when traversing through the tree depending which literal type is inf. We place them at the top (of each sub path of infinite domain). We can have multiple branches due to the multiple possible contexts.
                | Leaf !Bool
    deriving (Eq)

-- Decision Diagram model checking uses simultanious traversal, which requires all nodes to be identified by their position in a order
newtype Ordinal = Order [Int]

instance Show Ordinal where
    show (Order i) = show i

-- Where [a0, a1, a2, .. ] stands for a0 + a1 / W + a2 / W2 + ...
instance Ord Ordinal where
    compare (Order xl) (Order yl) = go xl yl EQ
        where
            go [] [] acc = acc
            go [] ys acc = go [0] ys acc
            go xs [] acc = go xs [0] acc
            go (x:xs) (y:ys) acc
                | x == y = go xs ys acc
                | otherwise = compare x y

instance Eq Ordinal where
  x == y = compare x y == EQ

data Inf = Dc | Neg1 | Neg0 | Pos1 | Pos0
    deriving (Eq, Show)


top :: Dd Ordinal
top = Leaf True

bot :: Dd Ordinal
bot = Leaf False

path :: Ordinal -> [Int] -> Inf -> Dd Ordinal
path i il = makePath i (sort il)

-- With makeNode we can never produce a ZDD with 2 specified nodes. See makePath for the more generalised construction of a (single) path in MDDs.
-- Set the node to pos, except for the positiove inference - there it sets it to neg --todo make this clearer?
makeNode :: Ordinal -> Inf -> Dd Ordinal
makeNode (Order i) c
    | c == Dc = InfNodes (Order $ init i) (Node (Order i) (Leaf True) (Leaf False)) (Leaf False) (Leaf True) (Leaf False) (Leaf True)
    | c == Neg1 = InfNodes (Order $ init i) (Leaf False) (Node (Order i) (Leaf True) (Leaf False)) (Leaf True) (Leaf False) (Leaf True)
    | c == Neg0 = InfNodes (Order $ init i) (Leaf True) (Leaf False) (Node (Order i) (Leaf False) (Leaf True)) (Leaf False) (Leaf True)
    | c == Pos1 = InfNodes (Order $ init i) (Leaf False) (Leaf False) (Leaf True) (Node (Order i) (Leaf False) (Leaf True)) (Leaf True)
    | c == Pos0 = InfNodes (Order $ init i) (Leaf True) (Leaf False) (Leaf True) (Leaf False) (Node (Order i) (Leaf True) (Leaf False))
    | otherwise = error "empty ordinal for makeNode"



-- At the variable class given represented by the ordinal, create a path containing the specified nodes from the list with the given inference rule.
-- We assume fixed variable classes, it is the responsibility of the user to give the correct ordinal
makePath :: Ordinal -> [Int] -> Inf -> Dd Ordinal
makePath (Order varClass) nodeList c
    | c == Dc = InfNodes (Order varClass) (loopNeg nodeList False) (Leaf False) (Leaf True) (Leaf False) (Leaf True)
    | c == Neg1 = InfNodes (Order varClass) (Leaf False) (loopNeg nodeList False ) (Leaf True) (Leaf False) (Leaf True)
    | c == Neg0 = InfNodes (Order varClass) (Leaf True) (Leaf False) (loopNeg nodeList True) (Leaf False) (Leaf True)
    | c == Pos1 = InfNodes (Order varClass) (Leaf False) (Leaf False) (Leaf True) (loopPos nodeList False) (Leaf True)
    | c == Pos0 = InfNodes (Order varClass) (Leaf True) (Leaf False) (Leaf True) (Leaf False) (loopPos nodeList True)
    | otherwise = error "empty ordinal or node list for makeNode"
    where
        loopNeg [] end = Leaf $ not end
        loopNeg (n:ns) end = Node (Order $ varClass ++ [n]) (loopNeg ns end) (Leaf end)
        loopPos [] end = Leaf $ not end
        loopPos (n:ns) end = Node (Order $ varClass ++ [n]) (Leaf end) (loopPos ns end)


instance Show a => Show (Dd a) where
    show (Leaf True) = "1"
    show (Leaf False) = "0"
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
