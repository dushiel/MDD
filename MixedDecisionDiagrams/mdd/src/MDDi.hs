
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
      Context,
      Node,
      Position,
      Path(P', P''),
      init_manager,
      unionContext,
      path, LevelL, makeNode )
import SODDmanipulation
import DrawMDD
import SupportMDD
import Data.List
import Data.Maybe (fromJust)


-- |======================================== Dd Manipulation operators interactive ==============================================

type MDD = (Context, Node)

c :: Context
c = init_manager

top' :: Node
top' = ((1, 0), Leaf True)

bot' :: Node
bot' = ((2, 0), Leaf False)

unk' :: Node
unk' = ((0, 0), Unknown)

top :: (Context, Node)
top = (c, ((1, 0), Leaf True))

bot :: (Context, Node)
bot = (c, ((2, 0), Leaf False))

unk :: (Context, Node)
unk = (c, ((0, 0), Unknown))

var :: Path -> (Context, Node)
var p = path c p

var' :: LevelL -> (Context, Node)
var' l = makeNode c l

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
conSet [] = top
conSet (d:ds) = foldl' (.*.) d ds

disSet :: [(Context, Node)] -> (Context, Node)
disSet [] = bot
disSet (d:ds) = foldl' (.+.) d ds

xorSet :: [(Context, Node)] -> (Context, Node)
xorSet [] = top
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
restrict n b (c, d) = restrict_node_set @Dc c [0 : n] b d

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
position_as_BDD ([]) _ = error "no list provided"
position_as_BDD ([n]) b = if b then P'' [n] else P'' [-n]
position_as_BDD (n : ns) b = P' [(n, Dc1, position_as_BDD ns b)]

restrictLaw :: [Position] -> (Context, Node) -> (Context, Node) -> (Context, Node)
restrictLaw v (mgr, d) law = loop (getDependentVars mgr v d) (mgr, d) law where
  loop (n:ns) d@(_, dd) l@(_, law)
    | law == top' = d -- the law completely covers the dd thus all nodes are restricted out
    | (dd == top') || (dd == bot') = d -- the dd is already top/bot, restricting it further does not change anything
    | law == bot' = top
    -- otherwise do the recursive restriction until terminal cases are met
    | otherwise =
        ((path init_manager (position_as_BDD n True)) .*. (loop ns (restrict n True d) (restrict n True l )))    .+.
        ((path init_manager (position_as_BDD n False)) .*. (loop ns (restrict n False d) (restrict n False l)))
  loop [] d@(_, dd) (_, law)
    | law == top' = d -- the law completely covers the dd thus all nodes are restricted out
    | (dd == top') || (dd == bot') = d -- the dd is already top/bot, restricting it further does not change anything
    | law == bot' = top
    | otherwise = error "impossible? something went wrong in restrictLaw."



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




-- | Relabel a DD with a function. Assumption: no int is mapped to itself by rF.
relabelFun :: [Position] -> (Position -> Position) -> (Context, Node) -> (Context, Node)
relabelFun v rF (mgr, dd) = loop (mgr, dd) disjointListOfLists
  where

  --get indexes of "overlapping" positions positions (positions in l2 that also occur in L1)
  --and use that to return the corresponding elements in a tuple
  getOverlap l1 l2 = (map ((l1 !!) . fromJust) (indexesOverlap l1 l2), l1 `intersect` l2)
  indexesOverlap l1 l2 = map (`elemIndex` l2) (l1 `intersect` l2)
  indexesNotOverlap l1 l2 = map (`elemIndex` l1) (l1 `intersect` l2)

  -- swap the (overlapping l1 ints with the corresponding l1 ints)
  -- in the not overlapping l1 values we look for the overlapping l2 values

  newOverlap l1 l2 = (fst $ getOverlap l1 l2, map ((l1 !!) . fromJust) (indexesNotOverlap l1 l2))

  -- get a list of tuples containing 2 equal length, disjointed lists of vars to be swapped
  -- by removing the "overlapping" variables and performing a recursive call with them
  splitCompare [] [] = []
  splitCompare [] _ = error "varlists used for relabeling do not have equal length."
  splitCompare _ [] = error "varlists used for relabeling do not have equal length."
  splitCompare l1 l2 = (l1\\fst (getOverlap l1 l2), l2\\snd (getOverlap l1 l2)) : uncurry splitCompare (newOverlap l1 l2)

  -- apply the function above to the support variable positions and the resulting positions from applying rf (the Remapping Function)
  -- and turn the positions into DD nodes (as ddSwapVars requires this)
  disjointListOfLists = splitCompare support (map rF support)
  support = getDependentVars mgr v dd

  -- loop and uncurry ddSwapVars so that it can be applied to the disjointListOfNodeLists
  loop (mgr, dd) (n:ns) = loop (uncurry (ddSwapVars mgr dd) n) ns
  loop d [] = d


-- | Relabel a DD with a list of pairs.
relabelWith ::  [(Position, Position)] -> (Context, Node) -> (Context, Node)
relabelWith r d = loop d disjointListOfLists where
  --get indexes of "overlapping" positions positions (positions in l2 that also occur in L1)
  --and use that to return the corresponding elements in a tuple
  getOverlap l1 l2 = (map ((l1 !!) . fromJust) (indexes l1 l2), l1 `intersect` l2)
  indexes l1 l2 = map (`elemIndex` l2) (l1 `intersect` l2)
  indexesNotOverlap l1 l2 = map (`elemIndex` l1) (l1 `intersect` l2)

  -- swap the (overlapping l1 ints with the corresponding l1 ints)
  -- in the non overlapping l1 values we look for the overlapping l2 values

  newOverlap l1 l2 = (fst $ getOverlap l1 l2, map ((l1 !!) . fromJust) (indexesNotOverlap l1 l2))

  -- get a list of tuples containing 2 equal length, disjointed lists of vars to be swapped
  -- by removing the "overlapping" variables and performing a recursive call with them
  splitCompare [] [] = []
  splitCompare [] _ = error "varlists used for relabeling do not have equal length."
  splitCompare _ [] = error "varlists used for relabeling do not have equal length."
  splitCompare l1 l2 = (l1\\fst (getOverlap l1 l2), l2\\snd (getOverlap l1 l2)) : uncurry splitCompare (newOverlap l1 l2)

  -- apply the function above to the support variable positions and the resulting positions from applying rf (the Remapping Function)
  -- and turn the positions into BDD nodes (as ddSwapVars requires this)
  disjointListOfLists = splitCompare listVars1 listVars2

  loop (mgr, dd) (n:ns) = loop (uncurry (ddSwapVars mgr dd) n) ns
  loop d [] = d

  (listVars1, listVars2) = unzip . sort . filter (uncurry (/=)) $ r

-- | Simultaneous substitution.
-- Implemented via `ifte` and `restrict`.
substitSimul :: [(Position, Node)] -> (Context, Node) -> (Context, Node)
substitSimul [] (mgr, dd) = (mgr, dd)
substitSimul ((n, psi) : ns) (mgr, dd) =
        ite (mgr,  psi)
        (recurs (restrict n True (mgr, dd)))
        (recurs (restrict n False (mgr, dd)))
  where
        recurs = substitSimul ns
