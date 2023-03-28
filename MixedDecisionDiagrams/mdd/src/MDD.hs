{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module MDD where

import Debug.Trace ( trace )
import Data.List (sort, dropWhileEnd)
import Data.Type.Ord (OrderingI)
-- proof of concept GenDDs where no merging of isomorphic nodes happen and no cashing / moization of results during traversal.
-- GenDDs can model check second order logic formulas containing variables in multiple (disjointed and/or nested) infinite domains.


-- |======================================== Data Types + Explanation ==============================================


data Dd =  Node Int Dd Dd               -- left = pos, right = neg
                | InfNodes Int Dd Dd Dd Dd Dd    -- sets the inference type when traversing through the tree depending which literal type is inf. We place them at the top (of each sub path of infinite domain). We can have multiple branches due to the multiple possible contexts.
                | EndInfNode Dd
                | Leaf Bool
    deriving (Eq)

-- Decision Diagram model checking uses simultanious traversal, which requires all nodes to be identified by their position in a order
newtype Ordinal = Order [Int]

safeOrd :: [Int] -> Ordinal
safeOrd = Order . dropWhileEnd (== 0)

instance Show Ordinal where
    show (Order i) = show i

-- todo add double Ordinal with point in the middle
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

-- as we traverse through the graph, we can get nested inference contexts:
type Context = [Inf]


top :: Dd
top = Leaf True

bot :: Dd
bot = Leaf False

path :: Ordinal -> [Int] -> Inf -> Dd
path i il = makePath i (sort il)

-- With makeNode we can never produce a ZDD with 2 specified nodes. See makePath for the more generalised construction of a (single) path in MDDs.
-- Set the node to pos, except for the positiove inference - there it sets it to neg --todo make this clearer?
makeNode :: Ordinal -> Inf -> Dd
makeNode (Order i) c
    | c == Dc = InfNodes (Order $ init i) (Node (last i) (Leaf True) (Leaf False)) (Leaf False) (Leaf True) (Leaf False) (Leaf True)
    | c == Neg1 = InfNodes (Order $ init i) (Leaf False) (Node (last i) (Leaf True) (Leaf False)) (Leaf True) (Leaf False) (Leaf True)
    | c == Neg0 = InfNodes (Order $ init i) (Leaf True) (Leaf False) (Node (last i) (Leaf False) (Leaf True)) (Leaf False) (Leaf True)
    | c == Pos1 = InfNodes (Order $ init i) (Leaf False) (Leaf False) (Leaf True) (Node (last i) (Leaf False) (Leaf True)) (Leaf True)
    | c == Pos0 = InfNodes (Order $ init i) (Leaf True) (Leaf False) (Leaf True) (Leaf False) (Node (last i) (Leaf True) (Leaf False))
    | otherwise = error "empty ordinal for makeNode"


-- At the variable class given represented by the ordinal, create a path containing the specified nodes from the list with the given inference rule.
-- We assume fixed variable classes, it is the responsibility of the user to give the correct ordinal
-- give empty list to create empty ZDD, e.g. : makePath (Order [1,2]) [] Neg1
makePath :: Ordinal -> [Int] -> Inf -> Dd
makePath (Order varClass) nodeList c
    | c == Dc = InfNodes (Order varClass) (loopNeg nodeList False) (Leaf False) (Leaf True) (Leaf False) (Leaf True)
    | c == Neg1 = InfNodes (Order varClass) (Leaf False) (loopNeg nodeList False ) (Leaf True) (Leaf False) (Leaf True)
    | c == Neg0 = InfNodes (Order varClass) (Leaf True) (Leaf False) (loopNeg nodeList True) (Leaf False) (Leaf True)
    | c == Pos1 = InfNodes (Order varClass) (Leaf False) (Leaf False) (Leaf True) (loopPos nodeList False) (Leaf True)
    | c == Pos0 = InfNodes (Order varClass) (Leaf True) (Leaf False) (Leaf True) (Leaf False) (loopPos nodeList True)
    | otherwise = error "empty ordinal or node list for makeNode"
    where
        loopNeg [] end = EndInfNode (Leaf $ not end)
        loopNeg (n:ns) end = Node n (loopNeg ns end) (Leaf end)
        loopPos [] end = EndInfNode (Leaf $ not end)
        loopPos (n:ns) end = Node n (Leaf end) (loopPos ns end)

-- For making paths that take multiple Infnodes through finite types.
-- used for e.g. [2::Neg1, 1::Neg1, 3::Neg1]
-- possible to give an empty list for the nodes to be set to positive
-- place a minus sign before a node nr to set it to negative.
makePathWithContext :: Ordinal -> Context -> [Int] -> Inf -> Dd
makePathWithContext (Order varClass) varCxt nodeList c = loop [] varClass varCxt
    where
        loop _ [vCl] [vCxt] = makePath (Order varClass) nodeList c
        loop prefix (vCl : xs) (vCxt : ys)
            | vCxt == Dc = loop (prefix ++ [vCl]) xs ys -- todo not only for bdd
            | vCxt == Neg1 = InfNodes vCl (((!! length prefix) . iterate EndInfNode) (Leaf False)) (loop (prefix ++ [vCl]) xs ys ) (Leaf True) (Leaf False) (Leaf True)
            | vCxt == Neg0 = InfNodes vCl (((!! length prefix) . iterate EndInfNode) (Leaf True)) (Leaf False) (loop (prefix ++ [vCl]) xs ys) (Leaf False) (Leaf True)
            | vCxt == Pos1 = InfNodes vCl (((!! length prefix) . iterate EndInfNode) (Leaf False)) (Leaf False) (Leaf True) (loop (prefix ++ [vCl]) xs ys) (Leaf True)
            | vCxt == Pos0 = InfNodes vCl (((!! length prefix) . iterate EndInfNode) (Leaf True)) (Leaf False) (Leaf True) (Leaf False) (loop (prefix ++ [vCl]) xs ys)
        loop _ _ _ = error "Context and Ordinal have unequal length."

{-}
ezPath :: EasyPath -> Dd
ezPath p = loop p [] [0] where
    loop (InfP inf ord (c : cs)) other max
        | inf == Dc && max<ord = InfNodes ord (loop c (cs++other) ord) (Leaf False) (Leaf True) (Leaf False) (Leaf True)
        | inf == Neg1 && max<ord = InfNodes ord (Leaf False) (loop c (cs++other) ord) (Leaf True) (Leaf False) (Leaf True)
        | inf == Neg0 && max<ord = InfNodes ord (Leaf True) (Leaf False) (loop c (cs++other) ord) (Leaf False) (Leaf True)
        | inf == Pos1 && max<ord = InfNodes ord (Leaf False) (Leaf False) (Leaf True) (loop c (cs++other) ord) (Leaf True)
        | inf == Pos0 && max<ord = InfNodes ord (Leaf True) (Leaf False) (Leaf True) (Leaf False) (loop c (cs++other) ord)
    loop (InfP _ ord (c : cs)) _ max = error $ "Encountered ordinal (ord=" ++ show ord ++ ") smaller or equal than earlier (max=" ++ show max ++ ") in the path, please check the supplied EasyPath."
    loop (InfP _ _ []) _ _ = error "Cannot end on InfNode / InfP, it should have at least one NodeP as child. Please check the supplied EasyPath."

    loop (NodeP inf children) other max
        | inf == Dc = loopNeg children False other max
        | inf == Neg1 = loopNeg children False other max
        | inf == Neg0 = loopNeg children True other max
        | inf == Pos1 = loopPos children False other max
        | inf == Pos0 = loopPos children True other max

    loopNeg [] end [] _ = Leaf $ not end
    loopNeg [] end (next: other) max = loop next other max
    loopNeg (n:ns) end other max = if (Order $ map abs n) > (Order max)
        then if last n <= 0 then Node (last n) (Leaf end) (loopNeg ns end other n) else Node (last n) (loopNeg ns end other n) (Leaf end)
        else error $ "Encountered ordinal (n=" ++ show n ++ ") smaller or equal than earlier (max=" ++ show max ++ ") in the path, please check the supplied EasyPath."
    loopPos [] end [] _ = Leaf $ not end
    loopPos [] end (next: other) max = loop next other max
    loopPos (n:ns) end other max = if (Order $ map abs n) > (Order max)
        then if last n <= 0 then Node (last n) (loopPos ns end other n) (Leaf end) else Node (last n) (Leaf end) (loopPos ns end other n)
        else error $ "Encountered ordinal (n=" ++ show n ++ ") smaller or equal than earlier (max=" ++ show max ++ ") in the path, please check the supplied EasyPath."


data EasyPath = InfP Inf [Int] [EasyPath ] | NodeP Inf [ [Int] ]
    deriving Show
-}

instance Show Dd where
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
