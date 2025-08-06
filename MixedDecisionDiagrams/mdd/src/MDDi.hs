
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Move brackets to avoid $" #-}
{-# HLINT ignore "Eta reduce" #-}
module MDDi where
import MDD
    ( Inf(Dc),
      InfL(Dc1),
      Dd(Leaf, Unknown),
      LevelL,
      Level,
      Context,
      Node,
      Position,
      Path(P', P),
      init_manager,
      makeNode,
      unionContext,
      path,
      top,
      bot,
      unk )
import SODDmanipulation
import DrawMDD
import SupportMDD
import Data.List


-- |======================================== Dd Manipulation operators interactive ==============================================



(-.) :: (Context, Node) -> (Context, Node)
(-.) (ca, a) = neg ca a

infix 2 .*.   -- F1 Conjunction / product | F0 Disjunction / sum
(.*.) :: (Context, Node) -> (Context, Node) -> (Context, Node)
(.*.) (ca, a) (cb, b) = con (unionContext ca cb) a b

infixl 3 .+.
(.+.) :: (Context, Node) -> (Context, Node) -> (Context, Node)
(.+.) (ca, a) (cb, b) = dis (unionContext ca cb) a b

infixl 1 .->.
(.->.) :: (Context, Node) -> (Context, Node) -> (Context, Node)
(.->.) a b = (-.) a .+. b

infixl 1 .<-.
(.<-.) :: (Context, Node) -> (Context, Node) -> (Context, Node)
(.<-.) a b = a .+. (-.) b

infixl 1 .<->.
(.<->.) :: (Context, Node) -> (Context, Node) -> (Context, Node)
(.<->.) a b = (a .*. b) .+. ((-.) a .*. (-.) b)

ite :: (Context, Node) -> (Context, Node) -> (Context, Node) -> (Context, Node)
ite x y z = (x .+. y) .*. ((-.) x .+. z)

xor :: (Context, Node) -> (Context, Node) -> (Context, Node)
xor a b = (a .*. (-.) b) .+. ((-.) a .*. b)

forall :: Position -> (Context, Node) -> (Context, Node)
forall n d = (restrict n False d) .*. (restrict n True d)

exist :: Position -> (Context, Node) -> (Context, Node)
exist n d = (restrict n False d) .+. (restrict n True d)



conSet :: [(Context, Node)] -> (Context, Node)
conSet [] = (c, top)
conSet (d:ds) = foldl' (.*.) d ds

disSet :: [(Context, Node)] -> (Context, Node)
disSet [] = (c, bot)
disSet (d:ds) = foldl' (.+.) d ds

xorSet :: [(Context, Node)] -> (Context, Node)
xorSet [] = (c, top)
xorSet (d:ds) = foldl' (xor) d ds

forallSet :: [Position] -> (Context, Node) -> (Context, Node)
forallSet [] d = d
forallSet [n] d = forall n d
forallSet (n : ns) d = (restrict n False (forallSet ns d)) .*. (restrict n True (forallSet ns d))

existSet :: [Position] -> (Context, Node) -> (Context, Node)
existSet [] d = d
existSet [n] d = exist n d
existSet (n : ns) d = (restrict n False (existSet ns d)) .+. (restrict n True (existSet ns d))


-- |======================================== Dd Manipulation operators ==============================================

restrict :: Position -> Bool -> (Context, Node) -> (Context, Node)
restrict n b (c, d) = restrict_node_set @Dc c [n] b d

neg :: Context -> Node -> (Context, Node)
neg c' a = negation (reset_stack c' c) a

con :: Context -> Node -> Node -> (Context, Node)
con c'' a b =
    let (c', (_, r)) = debug_func "INTER" $ apply' @Dc (reset_stack c'' c) "inter" a b
    in applyElimRule @Dc c' r

dis :: Context -> Node -> Node -> (Context, Node)
dis c'' a b =
    let (c', (_, r)) = debug_func "UNION" $ apply' @Dc (reset_stack c'' c) "union" a b
    in applyElimRule @Dc c' r



exists' :: Context -> Position -> Node -> (Context, Node)
exists' c n d = let
        (c', r1) = restrict_node_set @Dc c [n] False d
        (c'', r2) = restrict_node_set @Dc c [n] True d
        in dis c'' r1 r2

forall' :: Context -> Position -> Node -> (Context, Node)
forall' c n d = let
        (c', r1) = restrict_node_set @Dc c [n] False d
        (c'', r2) = restrict_node_set @Dc c [n] True d
        in con c'' r1 r2


getDependentVars :: Context -> [Position] -> Node -> [Position]
getDependentVars c v dd = filter (\n -> (snd $ restrict_node_set @Dc c [n] True dd) /= (snd $ restrict_node_set @Dc c [n] False dd)) v


position_as_BDD :: Position -> Bool -> Path
position_as_BDD ([n]) b = if b then P [n] else P [-n]
position_as_BDD (n : ns) b = P' [(n, Dc1, position_as_BDD ns b)]

-- restrictLaw :: Context -> [Level] -> Node -> Node -> (Context, Node)
-- restrictLaw mgr v d law = loop (getDependentVars mgr v d) d law where
--   loop (n:ns) dd law
--     | law == top = dd -- the law completely covers the dd thus all nodes are restricted out
--     | (dd == top) || (dd == bot) = dd -- the dd is already top/bot, restricting it further does not change anything
--     | law == bot = top
--     -- otherwise do the recursive restriction until terminal cases are met
--     | otherwise =
--         (path (position_as_BDD n True) .*. (loop ns (restrict n True dd) (restrict n True law )))    .+.
--         (path (position_as_BDD n False) .*. (loop ns (restrict n False dd) (restrict n False law)))
--   loop [] dd law
--     | law == top = dd -- the law completely covers the dd thus all nodes are restricted out
--     | (dd == top) || (dd == bot) = dd -- the dd is already top/bot, restricting it further does not change anything
--     | law == bot = top
--     | otherwise = error "impossible? something went wrong in restrictLaw."



ddSwapVars :: Context -> Node -> [Position] -> [Position] -> (Context, Node) -- assumes no overlapping in lists
ddSwapVars mgr z [n1] [n2] =
        ite (path mgr $ position_as_BDD n2 True)
        (ite (path mgr $ position_as_BDD n1 True) a11 a10)
        (ite (path mgr $ position_as_BDD n1 True) a01 a00)
    where
      a11 = restrict n2 True (restrict n1 True (mgr, z))
      a10 = restrict n2 False (restrict n1 True (mgr, z))
      a01 = restrict n2 True (restrict n1 False (mgr, z))
      a00 = restrict n2 False (restrict n1 False (mgr, z))
ddSwapVars mgr z (n1:ns1) (n2:ns2) =
        let (c', r) = ite (path mgr $ position_as_BDD n2 True)
                (ite (path mgr $ position_as_BDD n1 True) a11 a10)
                (ite (path mgr $ position_as_BDD n1 True) a01 a00)
        in ddSwapVars c' r ns1 ns2
    where
      a11 = restrict n2 True (restrict n1 True (mgr, z))
      a10 = restrict n2 False (restrict n1 True (mgr, z))
      a01 = restrict n2 True (restrict n1 False (mgr, z))
      a00 = restrict n2 False (restrict n1 False (mgr, z))
ddSwapVars _ _ _ _ = error "lists for ZddSwapVar are not of equal length"

-- -- | Relabel a DD with a function. Assumption: no int is mapped to itself by rF.
-- relabelFun :: Context -> [Position] -> (Position -> Position) -> Dd a b c -> Dd a b c
-- relabelFun mgr v rF dd = loop dd disjointListOfLists
--   where

--   --get indexes of "overlapping" positions positions (positions in l2 that also occur in L1)
--   --and use that to return the corresponding elements in a tuple
--   getOverlap l1 l2 = (map ((l1 !!) . fromJust) (indexesOverlap l1 l2), l1 `intersect` l2)
--   indexesOverlap l1 l2 = map (`elemIndex` l2) (l1 `intersect` l2)
--   indexesNotOverlap l1 l2 = map (`elemIndex` l1) (l1 `intersect` l2)

--   -- swap the (overlapping l1 ints with the corresponding l1 ints)
--   -- in the not overlapping l1 values we look for the overlapping l2 values

--   newOverlap l1 l2 = (fst $ getOverlap l1 l2, map ((l1 !!) . fromJust) (indexesNotOverlap l1 l2))

--   -- get a list of tuples containing 2 equal length, disjointed lists of vars to be swapped
--   -- by removing the "overlapping" variables and performing a recursive call with them
--   splitCompare [] [] = []
--   splitCompare [] _ = error "varlists used for relabeling do not have equal length."
--   splitCompare _ [] = error "varlists used for relabeling do not have equal length."
--   splitCompare l1 l2 = (l1\\fst (getOverlap l1 l2), l2\\snd (getOverlap l1 l2)) : uncurry splitCompare (newOverlap l1 l2)

--   -- apply the function above to the support variable positions and the resulting positions from applying rf (the Remapping Function)
--   -- and turn the positions into DD nodes (as ddSwapVars requires this)
--   disjointListOfLists = splitCompare support (map rF support)
--   support = getDependentVars mgr v dd

--   -- loop and uncurry ddSwapVars so that it can be applied to the disjointListOfNodeLists
--   loop b (n:ns) = loop (uncurry (ddSwapVars mgr b) n) ns
--   loop b [] = b

-- -- | Relabel a DD with a list of pairs.
-- relabelWith :: Context -> [(Position, Position)] -> Node -> (Context, Node)
-- relabelWith mgr r dd = loop dd disjointListOfLists where
--   --get indexes of "overlapping" positions positions (positions in l2 that also occur in L1)
--   --and use that to return the corresponding elements in a tuple
--   getOverlap l1 l2 = (map ((l1 !!) . fromJust) (indexes l1 l2), l1 `intersect` l2)
--   indexes l1 l2 = map (`elemIndex` l2) (l1 `intersect` l2)
--   indexesNotOverlap l1 l2 = map (`elemIndex` l1) (l1 `intersect` l2)

--   -- swap the (overlapping l1 ints with the corresponding l1 ints)
--   -- in the non overlapping l1 values we look for the overlapping l2 values

--   newOverlap l1 l2 = (fst $ getOverlap l1 l2, map ((l1 !!) . fromJust) (indexesNotOverlap l1 l2))

--   -- get a list of tuples containing 2 equal length, disjointed lists of vars to be swapped
--   -- by removing the "overlapping" variables and performing a recursive call with them
--   splitCompare [] [] = []
--   splitCompare [] _ = error "varlists used for relabeling do not have equal length."
--   splitCompare _ [] = error "varlists used for relabeling do not have equal length."
--   splitCompare l1 l2 = (l1\\fst (getOverlap l1 l2), l2\\snd (getOverlap l1 l2)) : uncurry splitCompare (newOverlap l1 l2)

--   -- apply the function above to the support variable positions and the resulting positions from applying rf (the Remapping Function)
--   -- and turn the positions into BDD nodes (as ddSwapVars requires this)
--   disjointListOfLists = splitCompare listVars1 listVars2

--   loop b (n:ns) = loop (uncurry (ddSwapVars mgr b) n) ns
--   loop b [] = b

--   listIntPairs = sort $ map (fromEnum *** fromEnum) $ filter (uncurry (/=)) r
--   (listVars1,listVars2) = unzip listIntPairs

-- -- | Simultaneous substitution.
-- -- Implemented via `ifte` and `restrict`.
-- substitSimul :: Context -> [(Position, Node)] -> Node -> (Context, Node)
-- substitSimul _ [] dd = dd
-- substitSimul mgr ((n, psi) : ns) dd =
--         ite psi
--         (recurs (restrict n True dd))
--         (recurs (restrict n False dd))
--   where
--         recurs = substitSimul mgr ns













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
c = init_manager

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
                in neg c1 r1
ddOf c (And a b) =
                let
                    (c1, r1) = ddOf c a
                    (c2, r2) = ddOf c1 b
                in con c2 r1 r2
ddOf c (Or a b) =
                let
                    (c1, r1) = ddOf c a
                    (c2, r2) = ddOf c1 b
                in dis c2 r1 r2
ddOf c (Impl a b) = ddOf c $ Or (Negate a) b
ddOf c (ImplR a b) = ddOf c $ Or a (Negate b)
ddOf c (PrpF l) = makeNode c l
ddOf c (Var (_, d)) = (c, d)

ddOf' :: Form -> (Context, Node)
ddOf' Top = (c, ((1,0), Leaf True))
ddOf' Bot = (c, ((2,0), Leaf False))
ddOf' (Negate a) =
                let
                    (c1, r1) = ddOf' a
                in neg c1 r1
ddOf' (And a b) =
                let
                    (c1, r1) = ddOf' a
                    (c2, r2) = ddOf' b
                in con (unionContext c1 c2) r1 r2
ddOf' (Or a b) =
                let
                    (c1, r1) = ddOf' a
                    (c2, r2) = ddOf' b
                in dis (unionContext c1 c2) r1 r2
ddOf' (Impl a b) = ddOf' $ Or (Negate a) b
ddOf' (ImplR a b) = ddOf' $ Or a (Negate b)
ddOf' (PrpF l) = makeNode c l
ddOf' (Var (c, d)) = (c, d)
