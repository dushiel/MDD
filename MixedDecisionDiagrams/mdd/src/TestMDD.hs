{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Move brackets to avoid $" #-}
{-# HLINT ignore "Eta reduce" #-}
module TestMDD where
import MDD
import MDDi
import Bool_MDD
import SODDmanipulation
import DrawMDD
import SupportMDD
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.Map as Map
import Text.ParserCombinators.ReadPrec (reset)




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


dc = path (c)               (P' [(1, Dc1, P'' [0])])
dc' = path (fst dc)         (P' [(1, Dc0, P'' [0])])
n = path (fst dc')          (P' [(1, Neg1, P'' [0])])
n' = path (fst n)           (P' [(1, Neg0, P'' [0])])
p = path (fst n')           (P' [(1, Pos1, P'' [0])])
p' = path (fst p)           (P' [(1, Pos0, P'' [0])])

dc1 = path (fst p')         (P' [(1, Dc1, P'' [1])])
dc2 = path (fst dc1)        (P' [(1, Dc1, P'' [2])])
dc23 = path (fst dc2)       (P' [(1, Dc1, P'' [2, 3])])
dc'2 = path (fst dc23)      (P' [(1, Dc1, P'' [-2])])
dc3 = path (fst dc'2)       (P' [(1, Dc1, P'' [3])])
dc4 = path (fst dc3)        (P' [(1, Dc1, P'' [4])])
dc_2 = path (fst dc4)       (P' [(2, Dc1, P'' [2])])
dc_3 = path (fst dc_2)      (P' [(2, Dc1, P'' [3])])
dc__2 = path (fst dc_3)     (P' [(3, Dc1, P'' [2])])

n2 = path (fst dc__2)       (P' [(1, Neg1, P'' [2])])
n3 = path (fst n2)          (P' [(1, Neg1, P'' [3])])
n23 = path (fst n3)         (P' [(1, Neg1, P'' [2,3])])
n_2 = path (fst n23)        (P' [(2, Neg1, P'' [2])])
n__2 = path (fst n_2)       (P' [(3, Neg1, P'' [2])])
n__3 = path (fst n__2)      (P' [(3, Neg1, P'' [3])])

n'2 = path (fst n__3)       (P' [(1, Neg0, P'' [2])])
n'3 = path (fst n'2)        (P' [(1, Neg0, P'' [3])])
n'23 = path (fst n'3)       (P' [(1, Neg0, P'' [2,3])])
n'_2 = path (fst n'23)      (P' [(2, Neg0, P'' [2])])
n'_3 = path (fst n'_2)      (P' [(2, Neg0, P'' [3])])
n'__2 = path (fst n'_3)     (P' [(3, Neg0, P'' [2])])
n'__3 = path (fst n'__2)    (P' [(3, Neg0, P'' [3])])

-- | ALL POS NODES HAVE THEIR NEGATIVE CHILD LEAD TO LEAF, AND POS TO UNKNOWN. OTHERWISE THEY GET ELIMINATED
p2 = path (fst n'__3)       (P' [(1, Pos1, P'' [-2])])
p3 = path (fst p2)          (P' [(1, Pos1, P'' [-3])])
p23 = path (fst p3)         (P' [(1, Pos1, P'' [-2,-3])])
p_2 = path (fst p23)        (P' [(2, Pos1, P'' [-2])])
p__2 = path (fst p_2)       (P' [(3, Pos1, P'' [-2])])

p'2 = path (fst p__2)       (P' [(1, Pos0, P'' [-2])])
p'3 = path (fst p'2)        (P' [(1, Pos0, P'' [-3])])
p'_2 = path (fst p'3)       (P' [(2, Pos0, P'' [-2])])
p'__2 = path (fst p'_2)     (P' [(3, Pos0, P'' [-2])])

-- nested domains dc
dcdc2 = path (fst p'__2)        (P' [(1, Dc1, P' [(1, Dc1, P'' [2])])])
dcdc3 = path (fst dcdc2)        (P' [(1, Dc1, P' [(1, Dc1, P'' [3])])])
dcdc'2 = path (fst dcdc3)       (P' [(1, Dc1, P' [(1, Dc1, P'' [-2])])])
dcdc'3 = path (fst dcdc'2)      (P' [(1, Dc1, P' [(1, Dc1, P'' [-3])])])

-- nested domains pos
pp2 = path (fst dcdc'3)         (P' [(1, Pos1, P' [(1, Pos1, P'' [-2])])])

pp3 = path (fst pp2)            (P' [(1, Pos1, P' [(1, Pos1, P'' [-3])])])
pp'2 = path (fst pp3)           (P' [(1, Pos1, P' [(1, Pos0, P'' [-2])])])
pp'3 = path (fst pp'2)          (P' [(1, Pos1, P' [(1, Pos0, P'' [-3])])])

-- nested domains neg
nn2 = path (fst pp'3)           (P' [(1, Neg1, P' [(1, Neg1, P'' [2])])])
nn3 = path (fst nn2)            (P' [(1, Neg1, P' [(1, Neg1, P'' [3])])])
nn'2 = path (fst nn3)           (P' [(1, Neg1, P' [(1, Neg0, P'' [2])])])
nn'3 = path (fst nn'2)          (P' [(1, Neg1, P' [(1, Neg0, P'' [3])])])

-- mixing different types of domains in the same path (nested domains)
dcn1 = path (fst nn'3)          (P' [(1, Dc1, P' [(1, Neg1, P'' [1])])])
dcn'1 = path (fst dcn1)         (P' [(1, Dc1, P' [(1, Neg0, P'' [1])])])
dcn23 = path (fst dcn'1)        (P' [(1, Dc1, P' [(1, Neg1, P'' [2,3])])])
dcn'23 = path (fst dcn23)       (P' [(1, Dc1, P' [(1, Neg0, P'' [2,3])])])

nn1 = path (fst dcn'23)         (P' [(1, Neg1, P' [(1, Neg1, P'' [1])])])
n_n1 = path (fst nn1)           (P' [(1, Neg1, P' [(2, Neg1, P'' [1])])])
n_n2 = path (fst n_n1)          (P' [(1, Neg1, P' [(2, Neg1, P'' [2])])])
n'n'1 = path (fst n_n2)         (P' [(1, Neg0, P' [(1, Neg0, P'' [1])])])
n'n1 = path (fst n'n'1)         (P' [(1, Neg0, P' [(1, Neg1, P'' [1])])])
n'n2 = path (fst n'n1)          (P' [(1, Neg0, P' [(1, Neg1, P'' [2])])])
n'_n1 = path (fst n'n2)         (P' [(1, Neg0, P' [(2, Neg1, P'' [1])])])
n'_n2 = path (fst n'_n1)        (P' [(1, Neg0, P' [(2, Neg1, P'' [2])])])
nn'1 = path (fst n'_n2)         (P' [(1, Neg1, P' [(1, Neg0, P'' [1])])])
nn = path (fst dc')             (P' [(1, Neg1, P' [(1, Neg1, P'' [0])])])
n'n = path (fst n)              (P' [(1, Neg0, P' [(1, Neg1, P'' [0])])])
nn' = path (fst n)              (P' [(1, Neg1, P' [(1, Neg0, P'' [0])])])

pp1 = path (fst nn'1)           (P' [(1, Pos1, P' [(1, Pos1, P'' [-1])])])
p_p1 = path (fst pp1)           (P' [(1, Pos1, P' [(2, Pos1, P'' [-1])])])
p_p2 = path (fst p_p1)          (P' [(1, Pos1, P' [(2, Pos1, P'' [-2])])])
p'p'1 = path (fst p_p2)         (P' [(1, Pos0, P' [(1, Pos0, P'' [-1])])])
p'p'2 = path (fst p'p'1)        (P' [(1, Pos0, P' [(1, Pos0, P'' [-2])])])
p'p1 = path (fst p'p'2)         (P' [(1, Pos0, P' [(1, Pos1, P'' [-1])])])
p'p2 = path (fst p'p1)          (P' [(1, Pos0, P' [(1, Pos1, P'' [-2])])])
p'_p1 = path (fst p'p2)         (P' [(1, Pos0, P' [(2, Pos1, P'' [-1])])])
p'_p2 = path (fst p'_p1)        (P' [(1, Pos0, P' [(2, Pos1, P'' [-2])])])
pp'1 = path (fst p'_p2)         (P' [(1, Pos1, P' [(1, Pos0, P'' [-1])])])
p'p'12 = path (fst p'_p2)       (P' [(1, Pos1, P' [(1, Pos0, P'' [-1, -2])])])

ndc = path (fst p'p'12)         (P' [(1, Neg1, P' [(1, Dc1, P'' [0])])])
n'dc' = path (fst p'p'12)       (P' [(1, Neg0, P' [(1, Dc0, P'' [0])])])

-- | The actual test context (NodeLookup)
(t_c, _) = p'p'12


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


-- ============================================================
-- * combining DD's with nested / recursive inf domains
-- ============================================================

        -- dc simple
            -- (snd $ ddOf t_c $ (And (Var dcdc2) (Var dcdc3))) == (snd $ ddOf t_c Top)

            -- intersection dc
            ,    (snd $ ddOf t_c $ And (Var dcdc2) (Negate $ Var dcdc2)) == (snd $ ddOf t_c Bot)  `debug5` "######## test nr 0"
            ,   (snd $ ddOf t_c $ And (Var dcdc3) (Var dcdc3)) == (snd $ ddOf t_c (Var dcdc3)) `debug5` "######## test nr 1"
            ,   (snd $ ddOf t_c $ Or (Var dcdc2) (Negate $ Var dcdc2)) == (snd $ ddOf t_c Top)  `debug5` "######## test nr 2"
            ,   (snd $ ddOf t_c $ Or (Var dcdc2) (Var dcdc3)) == (snd $ ddOf t_c $ Or (Var dcdc3) (Var dcdc2))  `debug5` "######## test nr 3"

    -- intersection neg
            ,   (snd $ ddOf t_c (And (Var nn'2) (Var nn2))) == (snd $ ddOf t_c Bot) `debug5` "######## test nr 4"
            ,   (snd $ ddOf t_c (And (Var nn3) (Var nn2))) == (snd $ ddOf t_c Bot) `debug5` "######## test nr 5"
            ,   (snd $ ddOf t_c (And (Var nn2) (Var nn3))) == (snd $ ddOf t_c Bot) `debug5` "######## test nr 6"
            ,   (snd $ ddOf t_c (Or (Var nn'2) (Var nn'3))) == (snd $ ddOf t_c (Var ndc)) `debug5` "######## test nr 7"
            ,   (snd $ ddOf t_c (And (Var n'n2) (Var n'n1))) == (snd $ ddOf t_c (Var n'dc')) `debug5` "######## test nr 7.5"

    -- intersection pos
            ,   (snd $ ddOf t_c (Or (Var pp'3) (Var p'p'1))) == (snd $ ddOf t_c Top) `debug5` "######## test nr 8"
            ,   (snd $ ddOf t_c (And (Var pp3) (Var pp3))) == (snd $ ddOf t_c (Var pp3)) `debug5` "######## test nr 9"
            ,   (snd $ ddOf t_c (And (Var p'p2) (Var pp2))) == (snd $ ddOf t_c (Var pp2)) `debug5` "######## test nr 10"
            ,   (snd $ ddOf t_c $ (And (Var p'p'1) (Var p'p'2))) == (snd $ ddOf t_c (Impl (Or (Var pp1) (Var pp2)) (Bot))) `debug5` "######## test nr 11"
            ,   (snd $ ddOf t_c (And (Var pp1) (Var pp2))) == (snd $ ddOf t_c Bot) `debug5` "######## test nr 10"

--     -- intersection mixed
            -- Dc with neg
            , (snd $ ddOf t_c $ And (Var dcdc2) (Or (Var dcn1) (Var dcn23))) == (snd $ ddOf t_c $ And (Var dcn23) (Var dcdc2))  `debug5` "######## test nr 12"
            , (snd $ ddOf t_c $ And (Var dc'2) (Or (Var p2) (Var p23))) == (snd $ ddOf t_c $ Or (Var p2) (Var p23))  `debug5` "######## test nr 13"
            , (snd $ ddOf t_c $ Or (Var dc2) (Or (Var n2) (Var n23))) == (snd $ ddOf t_c $ Var dc2)  `debug5` "######## test nr 14"
            , (snd $ ddOf t_c $ Or (Var dc'2) (Or (Var p2) (Var p23))) == (snd $ ddOf t_c $ Var dc'2)  `debug5` "######## test nr 15"
            -- Dc with neg
            , (snd $ ddOf t_c $ Or (And (Var dc2) (Var n'2)) (Var n'2)) == (snd $ ddOf t_c $ Var n'2)  `debug5` "######## test nr 16"
            ,  (snd $ ddOf t_c $ Or (And (Var dc2) (Var p'2)) (Var p'2)) == (snd $ ddOf t_c $ Var p'2)  `debug5` "######## test nr 17"
            , (snd $ ddOf t_c $ Or (And (Var dc2) (Var n'2)) (Var dc2)) == (snd $ ddOf t_c $ Var dc2)  `debug5` "######## test nr 18"
    --         -- etc


--     -- -- union dc
--             ,   (snd $ ddOf t_c $ Or (Var dc2) (Negate $ Var dc2)) == (snd $ ddOf t_c Top)  `debug5` "######## test nr 19 union base"
--     -- union neg
--             ,   (snd $ ddOf t_c (Or (Var n'3) (Var n'2))) == (snd $ ddOf t_c Top) `debug5` "######## test nr 20 union base"
--     -- union pos
--             ,   (snd $ ddOf t_c (Or (Var p'3) (Var p'2))) == (snd $ ddOf t_c Top) `debug5` "######## test nr 21 union base"
--             ,   (snd $ ddOf t_c $ Or (Var p'2) (Var p2)) == (snd $ ddOf t_c Top)  `debug5` "######## test nr 22 union base"
-- --     -- union mixed


--     -- union and intersection dc
--             ,   (snd $ ddOf t_c (Or (And (Var dc2) (Var dc3)) (Var dc3))) == (snd $ ddOf t_c $ Var dc3)  `debug5` "######## test nr 23 union containing"
--             ,   (snd $ ddOf t_c (Or (And (Var dc2) (Var dc3)) (Var dc2))) == (snd $ ddOf t_c $ Var dc2)  `debug5` "######## test nr 24 union containing"
--             ,   (snd $ ddOf t_c (And (Or (Var dc2) (Var dc3))  (Var dc3))) == (snd $ ddOf t_c $ Var dc3)  `debug5` "######## test nr 25 union containing"
--             ,   (snd $ ddOf t_c (And (Or (Var dc2) (Var dc3))  (Var dc2))) == (snd $ ddOf t_c $ Var dc2)  `debug5` "######## test nr 26 union containing"
--     -- union and intersection neg
--             ,   (snd $ ddOf t_c $ And (Or (Var n2) (Var n3)) (Var n3)) == (snd $ ddOf t_c $ Var n3)  `debug5` "######## test nr 27 union containing"
--             ,   (snd $ ddOf t_c $ And (Or (Var n2) (Var n3)) (Var n2)) == (snd $ ddOf t_c $ Var n2)`debug5` "######## test nr 28 union containing"
--             ,   (snd $ ddOf t_c (Or (And (Var n2) (Var n3)) (Var n3))) == (snd $ ddOf t_c (Var n3))  `debug5` "######## test nr 29 union containing"
--             ,   (snd $ ddOf t_c (Or (And (Var n2) (Var n3)) (Var n2))) == (snd $ ddOf t_c $ Var n2)   `debug5` "######## test nr 30 union containing"

            -- ,   (snd $ ddOf t_c $ Or (Impl (Var dcn1) (Var nn1)) (Var n'n1)) == (snd $ ddOf t_c Top)
            -- ,   (snd $ ddOf t_c $ (ImplR (Var dcn1) (Var nn1))) == (snd $ ddOf t_c Bot)
            -- ,   (snd $ ddOf t_c $ (ImplR (Var dcn1) (Var n'n1))) == (snd $ ddOf t_c Top)
            -- ,   (snd $ ddOf t_c $ (Impl (Var dcn1) (Var n'n1))) == (snd $ ddOf t_c Bot)
            -- ,   (snd $ ddOf t_c $ (And (Var nn1) (Var n'n1))) == (snd $ ddOf t_c Bot)
            -- ,   (snd $ ddOf t_c $ (Or (Var nn1) (Var n'n1))) == (snd $ ddOf t_c Top)

            ]


-- |======================================== Advanced operations tests ==============================================


-- Compound MDDs for testing
(c_or , dc_or_23)  = (t_c, snd dc2) .+. (t_c, snd dc3) -- (2 OR 3)
(c_34    , node_and_34) = (c_or, snd dc3) .*. (path c_or (P' [(1, Dc1, P'' [4])])) -- (3 AND 4) using a fresh var 4

t_c_adv = c_34

testAdvancedOps :: IO ()
testAdvancedOps = do
    putStrLn "Running Advanced Operations Tests..."
    mapM_ print ([show $ snd x | x <- zip results [(0 :: Int) .. ], not $ fst x])
    where


        results = [

        -- Relabeling (uses/tests ddswapvars)
            -- Simple relabeling
              (snd $ relabelWith [([1, 2], [1,3])] (t_c_adv, snd dc2)) == (snd dc3) `debug5` "relabelWith 2->3"
            , (snd $ relabelWith [([1, 2], [2,2])] (t_c_adv, snd dc2)) == (snd dc_2) `debug5` "relabelWith from domain 1 to 2"
            , (snd $ relabelWith [([1, 2], [2,3])] (t_c_adv, snd dc2)) == (snd dc_3) `debug5` "relabelWith from [1, 2] -> [2,3]"

        --     Overlapping list Relabeling
            , (snd $ relabelWith [([1, 2], [1,3]), ([1,3], [1,4])] (t_c_adv, snd dc23)) == node_and_34 `debug5` "relabelWith Shift (2->3, 3->4) in (2 AND 3)"
            , (snd $ relabelWith [([1, 2], [1,3]), ([1,3], [1,4])] $
                        ddOf t_c_adv (And (Impl (Var dc2) (Var dc1)) (Var dc3)))
                        == (snd $ ddOf t_c_adv (And (Impl (Var dc3) (Var dc1)) (Var dc4)))
                        `debug5` "relabelWith Shift (2->3, 3->4) in ((2 impl 1) AND 3)"

            , (snd $ relabelWith [([1, 2], [1,3]), ([1,3], [1,2])] $
                        ddOf t_c_adv (And (Impl (Var dc2) (Var dc1)) (Var dc3)))
                        == (snd $ ddOf t_c_adv (And (Impl (Var dc3) (Var dc1)) (Var dc2)))
                        `debug5` "relabelWith Shift (2->3, 3->2) in ((2 impl 1) AND 3)"

            , (snd $ relabelWith [([2, 2], [1,3]), ([2,3], [1,2])] $
                        ddOf t_c_adv (And (Var dc_2) (Var dc_3)))
                        == (snd dc23)
                        `debug5` "relabelWith domain change ([2, 2] -> [1,3]), ([2,3] -> [1,2]) in (2 AND 3)"

            , (snd $ relabelWith [([1,1],[0,1]),([1,2],[0,2]),([2,1],[0,1]),([2,2],[0,2])] $
                        ddOf t_c_adv (Var dc_2))
                        == (snd dc2)
                        `debug5` "relabel with large list between domains, testing unmvd for beliefstructures"


        -- Substitutions
            -- Simple Substitutions, dc
        --     ,  (snd $ substitSimul [([1, 2], snd dc3)] (t_c_adv, snd dc2)) == (snd dc3) `debug5` "substitSimul 2->3"
        --     , (snd $ substitSimul [([1, 2], top')] (t_c_adv, snd dc2)) == (snd $ ddOf t_c_adv Top) `debug5` "substitSimul 2->Top"

            -- neg1, neg0, pos1, pos0 separatly
            -- ....

            -- all dc, neg1, neg0, pos1, pos0 mixed
            -- ....

            -- Simultaneous Substitution, dc
        --     , (snd $ substitSimul [([1, 2], snd dc3), ([1,3], snd dc2)] (t_c_adv, snd dc23)) == (snd dc23) `debug5` "substitSimul Swap (2<->3) in (2 AND 3)"
        --     , (snd $ substitSimul [([1, 2], snd dc3), ([1,3], snd dc2)] (t_c_adv, snd dc2)) == (snd dc3) `debug5` "substitSimul Swap (2<->3) in (2)"

            -- neg1, neg0, pos1, pos0 separatly
            -- ....

            -- all dc, neg1, neg0, pos1, pos0 mixed
            -- ....

            -- Simple substitution over multiple domains, dc (e.g. [1,2] -> [3,1])
            -- ....



            -- 5. RestrictLaw
            -- Identity: Restricting with Top
        --     , (snd $ restrictLaw [[1, 2]] (t_c_adv, snd dc2) (t_c_adv, top')) == (snd dc2) `debug5` "restrictLaw Top"

        --     -- Vacuous: Restricting with Bot -> Top
        --     , (snd $ restrictLaw [[1, 2]] (t_c_adv, snd dc2) (t_c_adv, bot')) == (snd $ ddOf t_c_adv Top) `debug5` "restrictLaw Bot"

        --     -- Implication: Restrict (2 AND 3) with Law (2=True). Result should be (3).
        --     , (snd $ restrictLaw [[1, 2]] (c_23, node_and_23) (t_c_adv, snd dc2)) == (snd dc3) `debug5` "restrictLaw (2 AND 3) | 2=True -> 3"

        --     -- Implication: Restrict (2 OR 3) with Law (2=True). Result should be (True).
        --     , (snd $ restrictLaw [[1, 2]] (c_or, node_or_23) (t_c_adv, snd dc2)) == (snd $ ddOf t_c_adv Top) `debug5` "restrictLaw (2 OR 3) | 2=True -> True"

        --     -- Implication: Restrict (2 OR 3) with Law (2=False). Result should be (3).
        --     -- We assume restrictLaw handles negations correctly if we pass the negated atom as law,
        --     -- or if we assume the law implies the valuation.
        --     -- Here we use (Neg 2) as law.
        --     , (snd $ restrictLaw [[1, 2]] (c_or, node_or_23) ((-.) (t_c_adv, snd dc2))) == (snd dc3) `debug5` "restrictLaw (2 OR 3) | 2=False -> 3"
            ]