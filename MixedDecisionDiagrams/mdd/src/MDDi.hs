
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Move brackets to avoid $" #-}
{-# LANGUAGE TupleSections #-}
{-# HLINT ignore "Eta reduce" #-}
module MDDi where
import MDD
import SODDmanipulation 
import DrawMDD
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.Map as Map



-- |======================================== Dd Manipulation operators ==============================================

infixl 4 -.
(-.) :: Context -> Node -> (Context, Node)
(-.) c a = negation c{func_stack = top_level_func_stack} a

-- infix 2 .*.   -- F1 Conjunction / product | F0 Disjunction / sum
(.*.) :: Context -> Node -> Node -> (Context, Node)
(.*.) c a b =
    let (c', (_, r)) = debug_func "INTER" $ apply' @Dc c{func_stack = top_level_func_stack} "inter" a b
    in applyElimRule @Dc c' r

-- infixl 3 .+.
(.+.) :: Context -> Node -> Node -> (Context, Node)
(.+.) c a b =
    let (c', (_, r)) = debug_func "UNION" $ apply' @Dc c{func_stack = top_level_func_stack} "union" a b 
    in applyElimRule @Dc c' r

-- ite :: Context -> Node -> Node -> Node -> (Context, Node)
-- ite c x y z = (x .+. y) .*. ((-.) x .+. z)


-- infixl 1 .->.
-- (.->.) :: Context -> Node -> Node -> (Context, Node)
-- (.->.) c a b = (-.) a .+. b

-- infixl 1 .<-.
-- (.<-.) :: Context -> Node -> Node -> (Context, Node)
-- (.<-.) c a b = a .+. (-.) b

-- infixl 1 .<->.
-- (.<->.) :: Context -> Node -> Node -> (Context, Node)
-- (.<->.) c a b = (a .*. b) .+. ((-.) a .*. (-.) b)

-- todo future:  write a parser :: String -> Form
-- "[dc:5, n1:3, 4]" -> Pr L [(5, Dc), (3, Neg1)] 4
-- "([dc:1, 2] + [p0:2, 1]) * Top" ->  And (Or (Pr L [(1, Dc) 2) (Pr L [(2, Pos0)] 1)) Top

-- {-}
-- dc = (path (Order [0]) [2] Dc) .*. (path (Order [1]) [2] Dc)
-- b = path (Order [1]) [2] Neg1

-- (dc .*. a) .+. dc == dc
-- (dc .+. a) .*. dc == dc

-- (dc .*. a) .+. a == a
-- (dc .+. a) .*. a == a
-- -}


-- |======================================== Setup for constructing DD's from a given input ==============================================

-- base context
c = Context{
    nodelookup = defaultNodeMap,
    cache = Map.fromList (map (, HashMap.empty :: HashMap.HashMap (NodeId, NodeId, [(Inf, (Node, Node, Node))]) NodeId) ["union", "intersection", "inter", "interDc", "unionDc", "absorb", "traverse_and_return", "remove_outercomplement"]) :: Map.Map String (HashMap.HashMap (NodeId, NodeId, [(Inf, (Node, Node, Node))]) NodeId),
    cache_ = HashMap.empty :: HashMap.HashMap NodeId NodeId,
    func_stack = [],
    current_level = L [] 0,
    cache' = HashMap.empty
    }

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
    -- | F Form

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
ddOf c (Or a b) =
                let
                    (c1, r1) = ddOf c a
                    (c2, r2) = ddOf c1 b
                in (.+.) c2 r1 r2
ddOf c (Impl a b) = ddOf c $ Or (Negate a) b
ddOf c (ImplR a b) = ddOf c $ Or a (Negate b)
ddOf c (PrpF l) = makeNode c l
ddOf c (Var (_, d)) = (c, d)



-- |======================================== Constructing base test DD's ==============================================

-- Construct DD's containing a single path for testing
-- place them in the context ( t_c ) for availability during test cases
-- well-defined w.r.t. to logic statements

-- the reason why i do this here and not during the test cases is baisically as a refactor:
-- the variables themselves are shorter than writing out the entire expression and thus are easier to read

-- the numbers are for the node positions 
-- the underscores indicate at what infnode domain the nodes reside
-- the ' indicates a 0 suffix to the domain type

-- the types Dc1, Dc0, Neg1, Neg0, Pos1, Pos0 are for contrustion
-- the paths in the DD's only have the types Dc, Pos, Neg (without the 1/0 suffix) 
  
-- currently i expand the list of variables whenever i need it for a new test case
-- it would be nice to not have to 

dc2 = path (c)              [(0, Dc1)] [2]
dc'2 = path (fst dc2)       [(0, Dc1)] [-2]
dc3 = path (fst dc'2)       [(0, Dc1)] [3]
dc_2 = path (fst dc3)       [(1, Dc1)] [2]
dc__2 = path (fst dc_2)     [(2, Dc1)] [2]

n2 = path (fst dc__2)       [(0, Neg1)] [2]
n3 = path (fst n2)          [(0, Neg1)] [3]
n23 = path (fst n3)         [(0, Neg1)] [2,3]
n_2 = path (fst n23)        [(1, Neg1)] [2]
n__2 = path (fst n_2)       [(2, Neg1)] [2]
n__3 = path (fst n__2)       [(2, Neg1)] [3]

n'2 = path (fst n__3)       [(0, Neg0)] [2]
n'3 = path (fst n'2)        [(0, Neg0)] [3]
n'23 = path (fst n'3)       [(0, Neg0)] [2,3]
n'_2 = path (fst n'23)      [(1, Neg0)] [2]
n'_3 = path (fst n'_2)      [(1, Neg0)] [3]
n'__2 = path (fst n'_3)     [(2, Neg0)] [2]
n'__3 = path (fst n'__2)     [(2, Neg0)] [3]

-- | ALL POS NODES HAVE THEIR NEGATIVE CHILD LEAD TO LEAF, AND POS TO UNKNOWN. OTHERWISE THEY GET ELIMINATED
p2 = path (fst n'__3)       [(0, Pos1)] [-2]
p3 = path (fst p2)          [(0, Pos1)] [-3]
p23 = path (fst p3)         [(0, Pos1)] [-2,-3]
p_2 = path (fst p23)         [(1, Pos1)] [-2]
p__2 = path (fst p_2)       [(2, Pos1)] [-2]

p'2 = path (fst p__2)       [(0, Pos0)] [-2]
p'3 = path (fst p'2)        [(0, Pos0)] [-3]
p'_2 = path (fst p'3)       [(1, Pos0)] [-2]
p'__2 = path (fst p'_2)     [(2, Pos0)] [-2]

-- nested domains dc
dcdc2 = path (fst p'__2)     [(0, Dc1), (0, Dc1)] [2]
dcdc3 = path (fst dcdc2)     [(0, Dc1), (0, Dc1)] [3]
dcdc'2 = path (fst dcdc3)     [(0, Dc1), (0, Dc1)] [-2]
dcdc'3 = path (fst dcdc'2)     [(0, Dc1), (0, Dc1)] [-3]

-- nested domains pos
pp2 = path (fst dcdc'3)     [(0, Pos1), (0, Pos1)] [-2]
pp3 = path (fst pp2)     [(0, Pos1), (0, Pos1)] [-3]
pp'2 = path (fst pp3)     [(0, Pos0), (0, Pos0)] [-2]
pp'3 = path (fst pp'2)     [(0, Pos0), (0, Pos0)] [-3]

-- nested domains neg
nn2 = path (fst pp'3)     [(0, Neg1), (0, Neg1)] [2]
nn3 = path (fst nn2)     [(0, Neg1), (0, Neg1)] [3]
nn'2 = path (fst nn3)     [(0, Neg0), (0, Neg0)] [2]
nn'3 = path (fst nn'2)     [(0, Neg0), (0, Neg0)] [3]

-- mixing different types of domains in the same path (nested domains)
dcn1 = path (fst p'__2)     [(0, Dc1), (0, Neg1)] [-1]
dcn'1 = path (fst dcn1)     [(0, Dc1), (0, Neg0)] [1]

nn1 = path (fst dcn'1)      [(0, Neg1), (0, Neg1)] [1]
-- nn2 = path (fst nn1)        [(0, Neg1), (0, Neg1)] [2]
n_n1 = path (fst nn2)       [(0, Neg1), (1, Neg1)] [1]
n_n2 = path (fst n_n1)      [(0, Neg1), (1, Neg1)] [2]
n'n'1 = path (fst n_n2)     [(0, Neg0), (0, Neg0)] [1]
n'n1 = path (fst n'n'1)     [(0, Neg0), (0, Neg1)] [1]
n'n2 = path (fst n'n1)      [(0, Neg0), (0, Neg1)] [2]
n'_n1 = path (fst n'n2)     [(0, Neg0), (1, Neg1)] [1]
n'_n2 = path (fst n'_n1)    [(0, Neg0), (1, Neg1)] [2]
nn'1 = path (fst n'_n2)      [(0, Neg1), (0, Neg0)] [1]

-- the actual test context, containing all the DD's of the above declarations 
(t_c, _) = nn'1



-- |======================================== Actual test cases ==============================================

-- negation is very simple to implement and does not need its own test category
-- some categories do not yet have test cases, as i add them as i develop

-- goals: 
-- 1) i would like to have a monad for passing the context around
-- 2) improve struturing of tests further, such that the categories are more consistent and complete 
-- in such a way that it is easy to add / remove / adjust tests in each category 
-- 3) if there is someway to automate some of the test writing, that would be very nice (some tests contain symmetries)

test :: IO ()
test = do
    emptyFile
    mapM_ print ([show $ snd x | x <- zip results [(0 :: Int) .. ], not $ fst x])
    where
        results = [ 
            
-- combining simple boolean DD's

    -- intersection dc
                (snd $ ddOf t_c $ And (Var dc2) (Negate $ Var dc2)) == (snd $ ddOf t_c Bot)  `debug5` "######## test nr 0"
            ,   (snd $ ddOf t_c $ And (Var dc3) (Var dc3)) == (snd $ ddOf t_c (Var dc3)) `debug5` "######## test nr 1"
            ,   (snd $ ddOf t_c $ And (Var dc2) (Negate $ Var dc2)) == (snd $ ddOf t_c Bot)  `debug5` "######## test nr 2"
            ,   (snd $ ddOf t_c $ And (Var dc2) (Var dc3)) == (snd $ ddOf t_c $ And (Var dc3) (Var dc2))  `debug5` "######## test nr 3"
    
    -- intersection neg
            ,   (snd $ ddOf t_c (And (Var n'2) (Var n2))) == (snd $ ddOf t_c Bot) `debug5` "######## test nr 4"
            ,   (snd $ ddOf t_c (And (Var n3) (Var n2))) == (snd $ ddOf t_c Bot) `debug5` "######## test nr 5"
            ,   (snd $ ddOf t_c (And (Var n2) (Var n3))) == (snd $ ddOf t_c Bot) `debug5` "######## test nr 6"
            -- IVALID TEST -- ,   (snd $ ddOf t_c (And (Var n'2) (Var n'3))) == (snd $ ddOf t_c (Var n'23)) `debug5` "######## test nr 7"

    -- intersection pos
            ,   (snd $ ddOf t_c (And (Var p3) (Var p2))) == (snd $ ddOf t_c Bot) `debug5` "######## test nr 8"
            ,   (snd $ ddOf t_c (And (Var p3) (Var p3))) == (snd $ ddOf t_c (Var p3)) `debug5` "######## test nr 9"
            ,   (snd $ ddOf t_c (And (Var p'3) (Var p3))) == (snd $ ddOf t_c Bot) `debug5` "######## test nr 10"
            ,   (snd $ ddOf t_c $ And (Var p'2) (Var p2)) == (snd $ ddOf t_c Bot)`debug5` "######## test nr 11"

    -- intersection mixed 
            -- Dc with neg
            , (snd $ ddOf t_c $ And (Var dc2) (Or (Var n2) (Var n23))) == (snd $ ddOf t_c $ Or (Var n2) (Var n23))  `debug5` "######## test nr 12"
            , (snd $ ddOf t_c $ And (Var dc'2) (Or (Var p2) (Var p23))) == (snd $ ddOf t_c $ Or (Var p2) (Var p23))  `debug5` "######## test nr 13" 
            , (snd $ ddOf t_c $ Or (Var dc2) (Or (Var n2) (Var n23))) == (snd $ ddOf t_c $ Var dc2)  `debug5` "######## test nr 14"
            , (snd $ ddOf t_c $ Or (Var dc'2) (Or (Var p2) (Var p23))) == (snd $ ddOf t_c $ Var dc'2)  `debug5` "######## test nr 15"
            -- Dc with neg
            , (snd $ ddOf t_c $ Or (And (Var dc2) (Var n'2)) (Var n'2)) == (snd $ ddOf t_c $ Var n'2)  `debug5` "######## test nr 16"
            ,  (snd $ ddOf t_c $ Or (And (Var dc2) (Var p'2)) (Var p'2)) == (snd $ ddOf t_c $ Var p'2)  `debug5` "######## test nr 17"
            , (snd $ ddOf t_c $ Or (And (Var dc2) (Var n'2)) (Var dc2)) == (snd $ ddOf t_c $ Var dc2)  `debug5` "######## test nr 18"
    --         -- etc


    -- -- union dc
            ,   (snd $ ddOf t_c $ Or (Var dc2) (Negate $ Var dc2)) == (snd $ ddOf t_c Top)  `debug5` "######## test nr 19 union base"
    -- union neg
            ,   (snd $ ddOf t_c (Or (Var n'3) (Var n'2))) == (snd $ ddOf t_c Top) `debug5` "######## test nr 20 union base"
    -- union pos
            ,   (snd $ ddOf t_c (Or (Var p'3) (Var p'2))) == (snd $ ddOf t_c Top) `debug5` "######## test nr 21 union base"
            ,   (snd $ ddOf t_c $ Or (Var p'2) (Var p2)) == (snd $ ddOf t_c Top)  `debug5` "######## test nr 22 union base"
--     -- union mixed 


    -- union and intersection dc
            ,   (snd $ ddOf t_c (Or (And (Var dc2) (Var dc3)) (Var dc3))) == (snd $ ddOf t_c $ Var dc3)  `debug5` "######## test nr 23 union containing"
            ,   (snd $ ddOf t_c (Or (And (Var dc2) (Var dc3)) (Var dc2))) == (snd $ ddOf t_c $ Var dc2)  `debug5` "######## test nr 24 union containing"
            ,   (snd $ ddOf t_c (And (Or (Var dc2) (Var dc3))  (Var dc3))) == (snd $ ddOf t_c $ Var dc3)  `debug5` "######## test nr 25 union containing"
            ,   (snd $ ddOf t_c (And (Or (Var dc2) (Var dc3))  (Var dc2))) == (snd $ ddOf t_c $ Var dc2)  `debug5` "######## test nr 26 union containing"
    -- union and intersection neg
            ,   (snd $ ddOf t_c $ And (Or (Var n2) (Var n3)) (Var n3)) == (snd $ ddOf t_c $ Var n3)  `debug5` "######## test nr 27 union containing"
            ,   (snd $ ddOf t_c $ And (Or (Var n2) (Var n3)) (Var n2)) == (snd $ ddOf t_c $ Var n2)`debug5` "######## test nr 28 union containing"
            ,   (snd $ ddOf t_c (Or (And (Var n2) (Var n3)) (Var n3))) == (snd $ ddOf t_c (Var n3))  `debug5` "######## test nr 29 union containing"
            ,   (snd $ ddOf t_c (Or (And (Var n2) (Var n3)) (Var n2))) == (snd $ ddOf t_c $ Var n2)   `debug5` "######## test nr 30 union containing" 
    -- union and intersection pos
    -- union and intersection mixed


-- -- combining DD's spread over 2 levels of inf domains

--     -- Dc only
            ,   (snd $ ddOf t_c $ And (Or (Var dc2) (Var dc_2)) (Var dc_2)) == (snd $ ddOf t_c $ Var dc_2)  `debug5` "######## test nr 31 union containing"
            ,   (snd $ ddOf t_c $ And (Or (Var dc2) (Var dc_2)) (Var dc2)) == (snd $ ddOf t_c $ Var dc2)  `debug5` "######## test nr 32 union containing"
            ,   (snd $ ddOf t_c $ And (And (Var dc_2) (Var dc__2)) (Var dc_2)) == (snd $ ddOf t_c $ And (Var dc_2) (Var dc__2)) `debug5` "#### test 33 "
            ,   (snd $ ddOf t_c $ And (And (Var dc_2) (Var dc__2)) (Var dc_2)) == (snd $ ddOf t_c $ And (Var dc_2) (Var dc__2)) `debug5` "#### test 34"

    -- neg1 only
            ,   (snd $ ddOf t_c $ Or (And (Var n2) (Var n_2)) (Var n2)) == (snd $ ddOf t_c $ Var n2)  `debug5` "######## test nr 35 union containing"
            ,   (snd $ ddOf t_c $ Or (And (Var n2) (Var n_2)) (Var n_2)) == (snd $ ddOf t_c $ Var n_2)  `debug5` "######## test nr 36 union containing"
            ,   (snd $ ddOf t_c $ And (Or (Var n2) (Var n_2)) (Var n2)) == (snd $ ddOf t_c $ Var n2)  `debug5` "######## test nr union containing"
            ,   (snd $ ddOf t_c $ Or (Or (Var n2) (Var n_2)) (Var n_2)) == (snd $ ddOf t_c $ Or (Var n2) (Var n_2))  `debug5` "######## test nr union containing"
            ,   (snd $ ddOf t_c $ And (And (Var n2) (Var n_2)) (Var n2)) == (snd $ ddOf t_c $ And (Var n2) (Var n_2))  `debug5` "#### test -"
            ,   (snd $ ddOf t_c $ Or (And (Var n2) (Var n_2)) (Var n_2)) == (snd $ ddOf t_c $ Var  n_2)  `debug5` "######## test nr union containing"
            ,   (snd $ ddOf t_c $ And (And (Var n_2) (Var n__2)) (Var n_2)) == (snd $ ddOf t_c $ And (Var n_2) (Var n__2)) `debug5` "#### test --"
            ,   (snd $ ddOf t_c $ And (Var n_2) (And (Var n_2) (Var n__2))) == (snd $ ddOf t_c $ And (Var n_2) (Var n__2)) `debug5` "#### test ---"

--     -- neg0 only
            ,   (snd $ ddOf t_c $ Or (And (Var n'2) (Var n'_2)) (Var n'2)) == (snd $ ddOf t_c $ ( Var n'2 )) `debug5` "######## test nr union containing"
            ,   (snd $ ddOf t_c $ Or (And (Var n'2) (Var n'_2)) (Var n'_2)) == (snd $ ddOf t_c $ ( Var n'_2 )) `debug5` "######## test nr union containing"
            ,   (snd $ ddOf t_c $ And (Or (Var n'2) (Var n'_2)) (Var n'2)) == (snd $ ddOf t_c $ ( Var n'2 )) `debug5` "######## test nr union containing"
            ,   (snd $ ddOf t_c $ Or (Or (Var n'2) (Var n'_2)) (Var n'_2)) == (snd $ ddOf t_c $ Or ( Var n'2) (Var n'_2)) `debug5` "######## test nr union containing" 
            ,   (snd $ ddOf t_c $ And (And (Var n'2) (Var n'_2)) (Var n'2)) == (snd $ ddOf t_c $ And ( Var n'2) (Var n'_2))  `debug5` "#### test ----"
            ,   (snd $ ddOf t_c $ Or (And (Var n'2) (Var n'_2)) (Var n'_2)) == (snd $ ddOf t_c $ ( Var n'_2 )) `debug5` "######## test nr union containing"


--     -- pos1 only
            ,   (snd $ ddOf t_c $ And (And (Var p_2) (Var p__2)) (Var p_2)) == (snd $ ddOf t_c $ And (Var p_2) (Var p__2)) `debug5` "#### test -----"
            ,   (snd $ ddOf t_c $ And (Var p_2) (And (Var p__2) (Var p_2))) == (snd $ ddOf t_c $ And (Var p_2) (Var p__2)) `debug5` "#### test ----= 50"
            ,   (snd $ ddOf t_c $ Or (And (Var p2) (Var p_2)) (Var p2)) == (snd $ ddOf t_c $ ( Var p2 ) )`debug5` "######## test nr union containing"
            ,   (snd $ ddOf t_c $ Or (And (Var p2) (Var p_2)) (Var p_2)) == (snd $ ddOf t_c $ ( Var p_2 )) `debug5` "######## test nr union containing"
            ,   (snd $ ddOf t_c $ And (Or (Var p2) (Var p_2)) (Var p2)) == (snd $ ddOf t_c $ ( Var p2 )) `debug5` "######## test nr union containing"
            ,   (snd $ ddOf t_c $ Or (Or (Var p2) (Var p_2)) (Var p_2)) == (snd $ ddOf t_c $ Or ( Var p2) (Var p_2))  `debug5` "######## test nr union containing"
            ,   (snd $ ddOf t_c $ And (And (Var p2) (Var p_2)) (Var p2)) == (snd $ ddOf t_c $ And ( Var p2) (Var p_2)) `debug5` "#### test =" 
            ,   (snd $ ddOf t_c $ Or (And (Var p2) (Var p_2)) (Var p_2)) == (snd $ ddOf t_c $ ( Var p_2 )) `debug5` "######## test nr union containing"


--     -- pos0 only
            ,   (snd $ ddOf t_c $ And (Or (Var p'2) (Var p'_2) ) (Var p'2)) == (snd $ ddOf t_c $ ( Var p'2 )) `debug5` "######## test nr union containing"
            ,   (snd $ ddOf t_c $ And (Or (Var p'2) (Var p'_2) ) (Var p'_2)) == (snd $ ddOf t_c $ ( Var p'_2 )) `debug5` "######## test nr union containing"
            ,   (snd $ ddOf t_c $ Or (And (Var p'2) (Var p'_2)) (Var p'2)) == (snd $ ddOf t_c $ ( Var p'2 )) `debug5` "######## test nr union containing"
            ,   (snd $ ddOf t_c $ And (And (Var p'2) (Var p'_2)) (Var p'_2)) == (snd $ ddOf t_c $ And ( Var p'2) (Var p'_2) ) `debug5` "#### test =="
            ,   (snd $ ddOf t_c $ Or (Or (Var p'2) (Var p'_2)) (Var p'2)) == (snd $ ddOf t_c $ Or (Var p'2) (Var p'_2))  `debug5` "######## test nr union containing"

--     -- mixing all cases?
            ,   (snd $ ddOf t_c $ And (And (Var n'_2) (Var n__2)) (Var n_2)) == (snd $ ddOf t_c $ Bot) `debug5` "######## test nr union containing"
            ,   (snd $ ddOf t_c $ And (And (Var n'_2) (Var n__2)) (Var n'_2)) == (snd $ ddOf t_c $ And (Var n'_2) (Var n__2)) `debug5` "#### test ==="
            



-- -- combining DD's spread over 3 levels of inf domains
            ,   (snd $ ddOf t_c $ Or (And (Var n'_2) (Var n'__2)) (Var n'_2)) == (snd $ ddOf t_c $  Var n'_2)  `debug5` "#### test 3 levels of inf domains"
            ,   (snd $ ddOf t_c $ Or (And (Var p'_2) (Var p'__2)) (Var p'_2)) == (snd $ ddOf t_c $  Var p'_2)  `debug5` "#### test 3 levels of inf domains"
            ,   (snd $ ddOf t_c $ Or (And (Var p_2) (Var p__2)) (Var p_2)) == (snd $ ddOf t_c $ Var p_2 ) `debug5` "#### test 3 levels of inf domains"
            ,   (snd $ ddOf t_c $ Or (And (Var n_2) (Var n__2)) (Var n_2)) == (snd $ ddOf t_c $ Var n_2)  `debug5` "#### test 3 levels of inf domains"
            ,   (snd $ ddOf t_c $ Or (And (And (Var n'_2) (Var n'__2)) (Var n'3)) (And (Var n'__2) (Var n'3))) == (snd $ ddOf t_c $ And (Var n'__2)  (Var n'3))  `debug5` "#### test 3 levels of inf domains"
            ,   (snd $ ddOf t_c $ Or (And (And (Var p'_2) (Var p'__2)) (Var p'3)) (And (Var p'__2) (Var p'3))) == (snd $ ddOf t_c $ And (Var p'__2)  (Var p'3))  `debug5` "#### test 3 levels of inf domains"
            ,   (snd $ ddOf t_c $ Or (And (And (Var p_2) (Var p__2)) (Var p3)) (And (Var p__2)  (Var p3))) == (snd $ ddOf t_c $ And ( Var p__2) (Var p3))  `debug5` "#### test 3 levels of inf domains"
            ,   (snd $ ddOf t_c $ Or (And (And (Var n_2) (Var n__2)) (Var n3)) (And (Var n__2)  (Var n3))) == (snd $ ddOf t_c $ And ( Var n__2) (Var n3))  `debug5` "#### test 3 levels of inf domains"

            ,   (snd $ ddOf t_c $ And (Or (Or (Var n'_2) (Var n'__2)) (Var n'3)) (Or (Var n'__2) (Var n'3))) == (snd $ ddOf t_c $ Or (Var n'__2) (Var n'3))  `debug5` "#### test 3 levels of inf domains"
            ,   (snd $ ddOf t_c $ And (Or (Or (Var p'_2) (Var p'__2)) (Var p'3)) (Or (Var p'__2) (Var p'3))) == (snd $ ddOf t_c $ Or (Var p'__2) (Var p'3))  `debug5` "#### test 3 levels of inf domains"
            ,   (snd $ ddOf t_c $ And (Or (Or (Var p_2) (Var p__2)) (Var p3)) (Or (Var p__2) (Var p3))) == (snd $ ddOf t_c $ Or (Var p__2) (Var p3))  `debug5` "#### test 3 levels of inf domains"
            ,   (snd $ ddOf t_c $ And (Or (Or (Var n_2) (Var n__2)) (Var n3)) (Or (Var n__2) (Var n3))) == (snd $ ddOf t_c $ Or (Var n__2) (Var n3))  `debug5` "#### test 3 levels of inf domains"
    
    -- mixing all domains types
            ,   (snd $ ddOf t_c $ And (Or (Or (Var n'_2) (Var p'__2)) (Var p3)) (Or (Var p'__2) (Var p3))) == (snd $ ddOf t_c $ Or (Var p'__2) (Var p3))  `debug5` "#### test 3 levels of inf domains"
            ,   (snd $ ddOf t_c $ Or (And (Var dc2) (And (Var dc3) (Var n3))) (And (Or (And (Var n'_2) (Var p'__2)) (Var p3)) (Or (Var p'__2) (Var p3)))) == (snd $ ddOf t_c $ Or (And (Var dc2) (And (Var dc3) (Var n3))) (Or (And (Var n'_2) (Var p'__2)) (Var p3)))  `debug5` "#### test 3 levels of inf domains"
            ,   (snd $ ddOf t_c $ Or (And (Var n2) (And (Var p'3) (Var dc3))) (And (Or (And (Var p__2) (Var p'__2)) (Var p3)) (Or (Var n__2) (Var p3)))) == (snd $ ddOf t_c $ Or (And (Var n2) (And (Var p'3) (Var dc3))) (Or (And (Var p__2) (Var n__2)) (Var p3)))  `debug5` "#### test 3 levels of inf domains"


-- combining DD's with nested / recursive inf domains
        -- dc simple
            -- (snd $ ddOf t_c $ (And (Var dcdc2) (Var dcdc3))) == (snd $ ddOf t_c Top)

            -- ,   (snd $ ddOf t_c $ Or (Impl (Var dcn1) (Var nn1)) (Var n'n1)) == (snd $ ddOf t_c Top) 
            -- ,   (snd $ ddOf t_c $ (ImplR (Var dcn1) (Var nn1))) == (snd $ ddOf t_c Bot) 
            -- ,   (snd $ ddOf t_c $ (ImplR (Var dcn1) (Var n'n1))) == (snd $ ddOf t_c Top) 
            -- ,   (snd $ ddOf t_c $ (Impl (Var dcn1) (Var n'n1))) == (snd $ ddOf t_c Bot) 
            -- ,   (snd $ ddOf t_c $ (And (Var nn1) (Var n'n1))) == (snd $ ddOf t_c Bot) 
            -- ,   (snd $ ddOf t_c $ (Or (Var nn1) (Var n'n1))) == (snd $ ddOf t_c Top) 

            ]







