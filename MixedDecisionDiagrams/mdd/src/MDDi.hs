
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Move brackets to avoid $" #-}
{-# LANGUAGE TupleSections #-}
module MDDi where
import MDD
import SODDmanipulation hiding (Neg, Or, And)
import DrawMDD
import qualified Data.HashMap.Lazy as HashMap
import Data.GraphViz.Attributes.Complete (OutputMode(NodesFirst))
import Data.Foldable (foldl', Foldable (fold))
import qualified Data.Map as Map


-- todo sophisticated test suite,
-- have arbitrary formulas, then
-- restrict should be equal replacing with Top / Bot (for Dc at least or any local type)
-- negate formula and read all n1 as n0 and p1 as p0 to check symmetries
--

-- |======================================== Dd Manipulation operators ==============================================

infixl 4 -.
(-.) :: Context -> Node -> (Context, Node)
(-.) c a = negation c{func_stack = []} a
-- i dont think negation needs to keep track of context, right?

-- infix 2 .*.   -- F1 Conjunction / product | F0 Disjunction / sum
(.*.) :: Context -> Node -> Node -> (Context, Node)
(.*.) c a b =
    let (c', (_, r)) = debug_func "INTER" $ intersection' @Dc c{func_stack = []} a b
    in applyElimRule @Dc c' r
    -- `MDDmanipulation.debug` "===========" ++

-- infixl 3 .+.
-- (.+.) :: Context -> NodeId -> NodeId -> (Context, NodeId)
-- (.+.) c a b =
--     let r = debug_func "UNION" $ unionLocal @Dc c{func_stack = []} a b (getDd c a) (getDd c b)
--     in applyInfElimRule2 @Dc (fst r) (getDd (fst r) $ snd r)

-- ite :: Context -> NodeId -> NodeId -> NodeId -> (Context, NodeId)
-- ite c x y z = (x .+. y) .*. ((-.) x .+. z)


-- infixl 1 .->.
-- (.->.) :: Context -> NodeId -> NodeId -> (Context, NodeId)
-- (.->.) c a b = (-.) a .+. b

-- infixl 1 .<-.
-- (.<-.) :: Context -> NodeId -> NodeId -> (Context, NodeId)
-- (.<-.) c a b = a .+. (-.) b

-- infixl 1 .<->.
-- (.<->.) :: Context -> NodeId -> NodeId -> (Context, NodeId)
-- (.<->.) c a b = (a .*. b) .+. ((-.) a .*. (-.) b)

------------------------------------ Test
c = Context{
    nodelookup = defaultNodeMap,
    cache = Map.fromList (map (, HashMap.empty :: HashMap.HashMap (NodeId, NodeId) NodeId) ["union", "intersection", "inter", "absorb", "traverse_and_return", "remove_outercomplement"]) :: Map.Map String (HashMap.HashMap (NodeId, NodeId) NodeId),
    cache_ = HashMap.empty :: HashMap.HashMap NodeId NodeId,
    func_stack = [],
    current_level = L [] 0,
    cache' = HashMap.empty
    }




take_c :: (Context, Node) -> (Context -> Node -> Node -> (Context, Node)) -> (Context, Node) -> (Context, Node) -> (Context, Node)
take_c (c, _) f (_,a) (_,b) = f c a b
take_c_ :: (Context, Node) -> (Context -> Node -> (Context, Node)) -> (Context, Node) -> (Context, Node)
take_c_ (c, _) f (_,a) = f c a
take_c__ :: (Context, Node) -> (Context -> LevelL -> (Context, Node)) -> LevelL -> (Context, Node)
take_c__ (c, _) f = f c


-- write a parser :: String -> Form
-- "[dc:5, n1:3, 4]" -> Pr L [(5, Dc), (3, Neg1)] 4
-- "([dc:1, 2] + [p0:2, 1]) * Top" ->  And (Or (Pr L [(1, Dc) 2) (Pr L [(2, Pos0)] 1)) Top
-- which we can then use with ddOf

data Form
    = Top
    | Bot
    | Negate Form
    | And Form Form
    | Or Form Form
    | PrpF LevelL
    | Var (Context, Node)
    | Impl Form Form
    | ImplR Form Form
    | F Form

ddOf :: Context -> Form -> (Context, Node)
ddOf c Top = (c, ((1,0), Leaf True))
ddOf c Bot = (c, ((2,0), Leaf False))
ddOf c (Negate a) =
                let
                    (c1, r1) = ddOf c a
                in (-.) c1 r1
ddOf c (And a b) =
                let
                    (c1, r1) = ddOf c a
                    (c2, r2) = ddOf c1 b
                in (.*.) c2 r1 r2
-- ddOf c (Or a b) =
--                 let
--                     (c1, r1) = ddOf c a
--                     (c2, r2) = ddOf c1 b
--                 in (.+.) c2 r1 r2
ddOf c (Impl a b) = ddOf c $ Or (Negate a) b
ddOf c (ImplR a b) = ddOf c $ Or a (Negate b)
ddOf c (PrpF l) = makeNode c l
ddOf c (Var (_, d)) = (c, d)




-- data Level = L [(Int, Inf)] Int deriving (Eq, Show)
-- data Inf = Dc | Neg1 | Neg0 | Pos1 | Pos0
--     deriving (Eq, Show)


x =                     makeNode c (Ll [(0, Dc1)] 2)
xx = take_c__ x         makeNode (Ll [(0, Dc1)] (-2))
x' = take_c_ xx         (-.) x
h = take_c__ x'         makeNode (Ll [(0, Dc1)] 3)
j = take_c__ h          makeNode (Ll [(0, Dc1)] (-1))
jj = take_c__ j         makeNode (Ll [(0, Dc1)] (1))
-- 1    , neg1
-- neg2 , 2
-- 3

m = ddOf (fst jj) $ And (Var h) (Var x)
mm = ddOf (fst m) $ And (Var h) (Var xx)

n = ddOf (fst mm) $ And (Var j) (Var m)
nn = ddOf (fst n) $ And (Var jj) (Var mm)

-- ok = ddOf (fst nn) $ Or (Var n) (Var nn)

dc2 = path (c)         [(0, Dc1)] [2]
dc3 = path (fst dc2)        [(0, Dc1)] [3]
dc_2 = path (fst dc3)       [(1, Dc1)] [2]
dc__2 = path (fst dc_2)     [(2,Dc1)] [2]
dc = ddOf (fst dc__2) $     And (Var dc2) (Var dc3)
n2 = path (fst dc)          [(0, Neg1)] [2]
n3 = path (fst n2)          [(0, Neg1)] [3]
n23 = path (fst n3)         [(0, Neg1)] [2,3]
n_2 = path (fst n23)        [(1, Neg1)] [2]
n__2 = path (fst n_2)       [(3, Neg1)] [2]
-- b = ddOf (fst n__2) $       Or (Var n2) (Var n3)
p'2 = path (fst n__2)          [(0, Pos0)] [2]
p'3 = path (fst p'2)        [(0, Pos0)] [3]
p'_2 = path (fst p'3)       [(1, Pos0)] [2]
p'__2 = path (fst p'_2)     [(3, Pos0)] [2]
_c = ddOf (fst p'__2) $     And (Var p'2) (Var p'3)
p2 = path (fst _c)          [(0, Pos1)] [2]
p3 = path (fst p2)          [(0, Pos1)] [3]
p_2 = path (fst p3)         [(1,Pos1)] [2]
p__2 = path (fst p_2)       [(3, Pos1)] [2]

n'2 = path (fst p__2)       [(0, Neg0)] [2]
n'3 = path (fst n'2)        [(0, Neg0)] [3]
n'_2 = path (fst n'3)       [(1,Neg0)] [2]
n'__2 = path (fst n'_2)     [(3, Neg0)] [2]

dcn1 = path (fst n'__2)     [(0, Dc1), (0, Neg1)] [1]
dcn'1 = path (fst dcn1)     [(0, Dc1), (0, Neg0)] [1]

nn1 = path (fst dcn'1)      [(0, Neg1), (0, Neg1)] [1]
nn2 = path (fst nn1)        [(0, Neg1), (0, Neg1)] [2]
n_n1 = path (fst nn2)       [(0, Neg1), (1, Neg1)] [1]
n_n2 = path (fst n_n1)      [(0, Neg1), (1, Neg1)] [2]
n'n'1 = path (fst n_n2)     [(0, Neg0), (0, Neg0)] [1]
n'n1 = path (fst n'n'1)     [(0, Neg0), (0, Neg1)] [1]
n'n2 = path (fst n'n1)      [(0, Neg0), (0, Neg1)] [2]
n'_n1 = path (fst n'n2)     [(0, Neg0), (1, Neg1)] [1]
n'_n2 = path (fst n'_n1)    [(0, Neg0), (1, Neg1)] [2]

nn'1 = path (fst n'_n2)      [(0, Neg1), (0, Neg0)] [1]
(t_c, _) = nn'1
-- -- <[0,0]> -> ([0,1]) -> <[0,2,0]> -> ([0,2,1]) -> [1]
-- --dcZ =  (path (Order [0]) [1] Dc .->. path (Order [0,2]) [1] Dc) .*. path (Order [0]) [1] Dc
-- --neg1Z =  (path (Order [0]) [1] Neg1 .*. path (Order [0,2]) [1] Neg1) .*. path (Order [0]) [3] Neg1




test :: IO ()
test = do
    emptyFile
    mapM_ print ([show $ snd x | x <- zip results [(0 :: Int) .. ], not $ fst x])
    where
        results =
            [ (snd $ ddOf t_c $ And (Var p'2) (Var p2)) == (snd $ ddOf t_c Bot) `debug5` ("############# Test nr: 0 ")
--             , (snd $ ddOf t_c $ Or (Var p'2) (Var p2)) == (snd $ ddOf t_c Top)  `debug5` ("############# Test nr: 1 ")
--             , (snd $ ddOf t_c $ Or (Var dc) (Neg $ Var dc)) == (snd $ ddOf t_c Top)  `debug5` ("############# Test nr: 2 ")
            , (snd $ ddOf t_c $ And (Var dc) (Negate $ Var dc)) == (snd $ ddOf t_c Bot)  `debug5` ("############# Test nr: 3 ")

--             , (snd $ ddOf t_c $ And (Or (Var n2) (Var n3)) (Var n3)) == (snd $ ddOf t_c $ Var n3)  `debug5` ("############# Test nr: 4 ")
--             , (snd $ ddOf t_c $ And (Or (Var n2) (Var n3)) (Var n2)) == (snd $ ddOf t_c $ Var n2)  `debug5` ("############# Test nr: 5 ")

--             -- double domain (6)
--             , (snd $ ddOf t_c $ And (Or (Var dc2) (Var dc_2)) dc(Var dc_2)) == (snd $ ddOf t_c $ Var dc_2)  `debug5` ("############# Test nr: 6 ")
--             , (snd $ ddOf t_c $ And (Or (Var dc2) (Var dc_2)) (Var dc2)) == (snd $ ddOf t_c $ Var dc2)  `debug5` ("############# Test nr: 7 ")

--             -- inclusive finite subset dominance and submission (8)
--             , (snd $ ddOf t_c $ And (Var dc2) (Or (Var n2) (Var n23))) == (snd $ ddOf t_c $ Or (Var n2) (Var n23))  `debug5` ("############# Test nr: 8 ")
--             , (snd $ ddOf t_c $ Or (Var dc2) (Or (Var n2) (Var n23))) == (snd $ ddOf t_c $ Var dc2)  `debug5` ("############# Test nr: 9 ")
--             -- exclusive
--             , (snd $ ddOf t_c $ Or (And (Var dc2) (Var n'2)) (Var n'2)) == (snd $ ddOf t_c $ Var n'2)  `debug5` ("############# Test nr: 10 ")
--             , (snd $ ddOf t_c $ Or (And (Var dc2) (Var n'2)) (Var dc2)) == (snd $ ddOf t_c $ Var dc2)  `debug5` ("############# Test nr: 11 ")

--             --double domain inclusive (12)
--             , (snd $ ddOf t_c $ Or (And (Var n2) (Var n_2)) (Var n2)) == (snd $ ddOf t_c $ Var n2)  `debug5` ("############# Test nr: 12 ")
--             , (snd $ ddOf t_c $ Or (And (Var n2) (Var n_2)) (Var n_2)) == (snd $ ddOf t_c $ Var n_2)  `debug5` ("############# Test nr: 13 ")
--             , (snd $ ddOf t_c $ And (Or (Var n2) (Var n_2)) (Var n2)) == (snd $ ddOf t_c $ Var n2)  `debug5` ("############# Test nr: 14 ")
--             , (snd $ ddOf t_c $ Or (Or (Var n2) (Var n_2)) (Var n_2)) == (snd $ ddOf t_c $ Or (Var n2) (Var n_2))  `debug5` ("############# Test nr: 15 ")
            , (snd $ ddOf t_c $ And (And (Var n2) (Var n_2)) (Var n2)) == (snd $ ddOf t_c $ And (Var n2) (Var n_2))  `debug5` ("############# Test nr: 16 ")
--             , (snd $ ddOf t_c $ Or (And (Var n2) (Var n_2)) (Var n_2)) == (snd $ ddOf t_c $ Var  n_2)  `debug5` ("############# Test nr: 17 ")

--             --double domain exclusive (18)
--             , (snd $ ddOf t_c $ And (Or (Var p'2) (Var p'_2) ) (Var p'2)) == (snd $ ddOf t_c $ ( Var p'2 )) `debug5` ("############# Test nr: 18 ")
--             , (snd $ ddOf t_c $ And (Or (Var p'2) (Var p'_2) ) (Var p'_2)) == (snd $ ddOf t_c $ ( Var p'_2 )) `debug5` ("############# Test nr: 19 ")
--             , (snd $ ddOf t_c $ Or (And (Var p'2) (Var p'_2)) (Var p'2)) == (snd $ ddOf t_c $ ( Var p'2 )) `debug5` ("############# Test nr: 20 ")
            , (snd $ ddOf t_c $ And (And (Var p'2) (Var p'_2)) (Var p'_2)) == (snd $ ddOf t_c $ And ( Var p'2) (Var p'_2) ) `debug5` ("############# Test nr: 21 ")
--             , (snd $ ddOf t_c $ Or (Or (Var p'2) (Var p'_2)) (Var p'2)) == (snd $ ddOf t_c $ Or (Var p'2) (Var p'_2))  `debug5` ("############# Test nr: 22 ")

--             --double domain inclusive s0 (23)
--             , (snd $ ddOf t_c $ Or (And (Var p2) (Var p_2)) (Var p2)) == (snd $ ddOf t_c $ ( Var p2 ) )`debug5` ("############# Test nr: 23 ")
--             , (snd $ ddOf t_c $ Or (And (Var p2) (Var p_2)) (Var p_2)) == (snd $ ddOf t_c $ ( Var p_2 )) `debug5` ("############# Test nr: 24 ")
--             , (snd $ ddOf t_c $ And (Or (Var p2) (Var p_2)) (Var p2)) == (snd $ ddOf t_c $ ( Var p2 )) `debug5` ("############# Test nr: 25 ")
--             , (snd $ ddOf t_c $ Or (Or (Var p2) (Var p_2)) (Var p_2)) == (snd $ ddOf t_c $ Or ( Var p2) (Var p_2))  `debug5` ("############# Test nr: 26 ")
            , (snd $ ddOf t_c $ And (And (Var p2) (Var p_2)) (Var p2)) == (snd $ ddOf t_c $ And ( Var p2) (Var p_2))  `debug5` ("############# Test nr: 27 ")
--             , (snd $ ddOf t_c $ Or (And (Var p2) (Var p_2)) (Var p_2)) == (snd $ ddOf t_c $ ( Var p_2 )) `debug5` ("############# Test nr: 28 ")

--             --double domain exclusive s0 (29)
--             , (snd $ ddOf t_c $ Or (And (Var n'2) (Var n'_2)) (Var n'2)) == (snd $ ddOf t_c $ ( Var n'2 )) `debug5` ("############# Test nr: 29 ")
--             , (snd $ ddOf t_c $ Or (And (Var n'2) (Var n'_2)) (Var n'_2)) == (snd $ ddOf t_c $ ( Var n'_2 )) `debug5` ("############# Test nr: 30 ")
--             , (snd $ ddOf t_c $ And (Or (Var n'2) (Var n'_2)) (Var n'2)) == (snd $ ddOf t_c $ ( Var n'2 )) `debug5` ("############# Test nr: 31 ")
--             , (snd $ ddOf t_c $ Or (Or (Var n'2) (Var n'_2)) (Var n'_2)) == (snd $ ddOf t_c $ Or ( Var n'2) (Var n'_2))  `debug5` ("############# Test nr: 32 ")
            , (snd $ ddOf t_c $ And (And (Var n'2) (Var n'_2)) (Var n'2)) == (snd $ ddOf t_c $ And ( Var n'2) (Var n'_2))  `debug5` ("############# Test nr: 33 ")
--             , (snd $ ddOf t_c $ Or (And (Var n'2) (Var n'_2)) (Var n'_2)) == (snd $ ddOf t_c $ ( Var n'_2 )) `debug5` ("############# Test nr: 34 ")

-- --             -- some triple domain cases (35)
--             , (snd $ ddOf t_c $ Or (And (Var n'_2) (Var n'__2)) (Var n'_2)) == (snd $ ddOf t_c $  Var n'_2)  `debug5` ("############# Test nr: 35 ")
--             , (snd $ ddOf t_c $ Or (And (Var p'_2) (Var p'__2)) (Var p'_2)) == (snd $ ddOf t_c $  Var p'_2)  `debug5` ("############# Test nr: 36 ")
--             , (snd $ ddOf t_c $ Or (And (Var p_2) (Var p__2)) (Var p_2)) == (snd $ ddOf t_c $ Var p_2 ) `debug5` ("############# Test nr: 37 ")
--             , (snd $ ddOf t_c $ Or (And (Var n_2) (Var n__2)) (Var n_2)) == (snd $ ddOf t_c $ Var n_2)  `debug5` ("############# Test nr: 38 ")
--             , (snd $ ddOf t_c $ Or (And (And (Var n'_2) (Var n'__2)) (Var n'3)) (And (Var n'__2) (Var n'3))) == (snd $ ddOf t_c $ And (Var n'__2)  (Var n'3))  `debug5` ("############# Test nr: 39 ")
--             , (snd $ ddOf t_c $ Or (And (And (Var p'_2) (Var p'__2)) (Var p'3)) (And (Var p'__2) (Var p'3))) == (snd $ ddOf t_c $ And (Var p'__2)  (Var p'3))  `debug5` ("############# Test nr: 40 ")
--             , (snd $ ddOf t_c $ Or (And (And (Var p_2) (Var p__2)) (Var p3)) (And (Var p__2)  (Var p3))) == (snd $ ddOf t_c $ And ( Var p__2) (Var p3))  `debug5` ("############# Test nr: 41 ")
--             , (snd $ ddOf t_c $ Or (And (And (Var n_2) (Var n__2)) (Var n3)) (And (Var n__2)  (Var n3))) == (snd $ ddOf t_c $ And ( Var n__2) (Var n3))  `debug5` ("############# Test nr: 42 ")

--             , (snd $ ddOf t_c $ And (Or (Or (Var n'_2) (Var n'__2)) (Var n'3)) (Or (Var n'__2) (Var n'3))) == (snd $ ddOf t_c $ Or (Var n'__2) (Var n'3))  `debug5` ("############# Test nr: 43 ")
--             , (snd $ ddOf t_c $ And (Or (Or (Var p'_2) (Var p'__2)) (Var p'3)) (Or (Var p'__2) (Var p'3))) == (snd $ ddOf t_c $ Or (Var p'__2) (Var p'3))  `debug5` ("############# Test nr: 44 ")
--             , (snd $ ddOf t_c $ And (Or (Or (Var p_2) (Var p__2)) (Var p3)) (Or (Var p__2) (Var p3))) == (snd $ ddOf t_c $ Or (Var p__2) (Var p3))  `debug5` ("############# Test nr: 45 ")
--             , (snd $ ddOf t_c $ And (Or (Or (Var n_2) (Var n__2)) (Var n3)) (Or (Var n__2) (Var n3))) == (snd $ ddOf t_c $ Or (Var n__2) (Var n3))  `debug5` ("############# Test nr: 46 ")

--             -- mixing all domains (48)
--             , (snd $ ddOf t_c $ And (Or (Or (Var n'_2) (Var p'__2)) (Var p3)) (Or (Var p'__2) (Var p3))) == (snd $ ddOf t_c $ Or (Var p'__2) (Var p3))  `debug5` ("############# Test nr: 47 ")
--             , (snd $ ddOf t_c $ Or (And (Var dc2) (And (Var dc3) (Var n3))) (And (Or (And (Var n'_2) (Var p'__2)) (Var p3)) (Or (Var p'__2) (Var p3)))) == (snd $ ddOf t_c $ Or (And (Var dc2) (And (Var dc3) (Var n3))) (Or (And (Var n'_2) (Var p'__2)) (Var p3)))  `debug5` ("############# Test nr: 48 ")
--             , (snd $ ddOf t_c $ Or (And (Var n2) (And (Var p'3) (Var dc3))) (And (Or (And (Var p__2) (Var p'__2)) (Var p3)) (Or (Var n__2) (Var p3)))) == (snd $ ddOf t_c $ Or (And (Var n2) (And (Var p'3) (Var dc3))) (Or (And (Var p__2) (Var n__2)) (Var p3)))  `debug5` ("############# Test nr: 49 ")

--             -- recursive
--             , (snd $ ddOf t_c $ Or (Impl (Var dcn1) (Var nn1)) (Var n'n1)) == (snd $ ddOf t_c Top) `debug5` ("############# Test nr: 50 \n\n")
--             , (snd $ ddOf t_c $ (ImplR (Var dcn1) (Var nn1))) == (snd $ ddOf t_c Bot) `debug5` ("############# Test nr: 51 \n\n")
--             , (snd $ ddOf t_c $ (ImplR (Var dcn1) (Var n'n1))) == (snd $ ddOf t_c Top) `debug5` ("############# Test nr: 52 \n\n")
--             , (snd $ ddOf t_c $ (Impl (Var dcn1) (Var n'n1))) == (snd $ ddOf t_c Bot) `debug5` ("############# Test nr: 53 \n\n")
--             , (snd $ ddOf t_c $ (And (Var nn1) (Var n'n1))) == (snd $ ddOf t_c Bot) `debug4` ("############# Test nr: 54 \n\n")
--             , ((snd $ ddOf t_c $ (Or (Var nn1) (Var n'n1))) == (snd $ ddOf t_c Top) `debug4` ("############# Test nr: 55 \n\n"))

            -- n1/no/p1/p0/dc outer shell and inner shell

            -- tripple time
            ]

-- {-}
-- dc = (path (Order [0]) [2] Dc) .*. (path (Order [1]) [2] Dc)
-- b = path (Order [1]) [2] Neg1

-- (dc .*. a) .+. dc == dc
-- (dc .+. a) .*. dc == dc

-- (dc .*. a) .+. a == a
-- (dc .+. a) .*. a == a
-- -}

-- test2 :: IO ()
-- test2 = do
--     mapM_ print ([show $ snd x | x <- zip results2 [(0 :: Int) .. ], not $ fst x])
--     where
--         results2 =
--             [
--                 snd $ ddOf t_c $ (n'2 .*. n2) == snd $ ddOf t_c Bot `debug` ("############# Test nr: 2.0 \n\n")
--             ,   snd $ ddOf t_c $ ((Var n3) .*. n2) == snd $ ddOf t_c Bot `debug` ("############# Test nr: 2.0 \n\n")
--             ,   snd $ ddOf t_c $ (n'3 .+. n'2) == snd $ ddOf t_c Top `debug` ("############# Test nr: 2.0 \n\n")
--             ,   snd $ ddOf t_c $ (p3 .*. p2) == snd $ ddOf t_c Bot `debug` ("############# Test nr: 2.0 \n\n")
--             ,   snd $ ddOf t_c $ (p'3 .+. p'2) == snd $ ddOf t_c Top `debug` ("############# Test nr: 2.0 \n\n")

--             , snd $ ddOf t_c $ ((n2 .*. (Var n3)) .+. (Var n3)) == snd $ ddOf t_c $ Var (Var n3)  `debug` ("############# Test nr: 4 \n\n")
--             , snd $ ddOf t_c $ ((n2 .*. (Var n3)) .+. n2) == snd $ ddOf t_c $ Var n2  `debug` ("############# Test nr: 5 \n\n")
--             , snd $ ddOf t_c $ (((Var dc2) .*. dc3) .+. dc3) == snd $ ddOf t_c $ Var dc3  `debug` ("############# Test nr: 4 \n\n")
--             , snd $ ddOf t_c $ (((Var dc2) .*. dc3) .+. (Var dc2)) == snd $ ddOf t_c $ Var (Var dc2)  `debug` ("############# Test nr: 5 \n\n")
--             , snd $ ddOf t_c $ (((Var dc2) .+. dc3) .*. dc3) == snd $ ddOf t_c $ Var dc3  `debug` ("############# Test nr: 4 \n\n")
--             , snd $ ddOf t_c $ (((Var dc2) .+. dc3) .*. (Var dc2)) == snd $ ddOf t_c $ Var (Var dc2)  `debug` ("############# Test nr: 5 \n\n")]