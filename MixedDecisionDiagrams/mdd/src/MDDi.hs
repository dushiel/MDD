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
      NodeLookup,
      NodeId,
      Node,
      Position,
      Path(P', P''),
      init_lookup,
      unionNodeLookup,
      path, LevelL, makeNode,
      BinaryOperatorContext,
      UnaryOperatorContext,
      init_binary_context,
      init_unary_context,
      getLookup,
      getNode,
      l_u, l_0, l_1 )
import SODDmanipulation
import DrawMDD
import SupportMDD
import Data.List
import Data.Maybe (fromJust)
import Debug.Trace (trace)

-- |======================================== Dd Manipulation operators interactive ==============================================

-- | MDDs are represented by (NodeLookup, Node) as a self-contained unit
type MDD = (NodeLookup, Node)

-- Constants for standard leaf nodes
top_n :: Node
top_n = ((1, 0), Leaf True)

bot_n :: Node
bot_n = ((2, 0), Leaf False)

unk_n :: Node
unk_n = ((0, 0), Unknown)

c :: NodeLookup
c = init_lookup

top :: MDD
top = (c, top_n)

bot :: MDD
bot = (c, bot_n)

unk :: MDD
unk = (c, unk_n)

var :: Path -> MDD
var p = let (c', n) = path init_lookup p in (getLookup c', n)

var' :: LevelL -> MDD
var' l = let (c', n) = makeNode init_lookup l in (getLookup c', n)

(-.) :: MDD -> MDD
(-.) (la, a) = neg la a

infix 2 .*.   -- Conjunction / product
(.*.) :: MDD -> MDD -> MDD
(.*.) (la, a) (lb, b) = con (unionNodeLookup la lb) a b

infixl 3 .+.  -- Disjunction / sum
(.+.) :: MDD -> MDD -> MDD
(.+.) (la, a) (lb, b) = dis (unionNodeLookup la lb) a b

infixl 1 .->.
(.->.) :: MDD -> MDD -> MDD
(.->.) a b = (-.) a .+. b

infixl 1 .<-.
(.<-.) :: MDD -> MDD -> MDD
(.<-.) a b = a .+. (-.) b

infixl 1 .<->.
(.<->.) :: MDD -> MDD -> MDD
(.<->.) a b = (a .*. b) .+. ((-.) a .*. (-.) b)

ite :: MDD -> MDD -> MDD -> MDD
ite x y z = (x .*. y) .+. ((-.) x .*. z)

xor :: MDD -> MDD -> MDD
xor a b = (a .*. (-.) b) .+. ((-.) a .*. b)

forall :: Position -> MDD -> MDD
forall n d = (restrict n False d) .*. (restrict n True d)

exist :: Position -> MDD -> MDD
exist n d = (restrict n False d) .+. (restrict n True d)

conSet :: [MDD] -> MDD
conSet [] = top
conSet (d:ds) = foldl' (.*.) d ds

disSet :: [MDD] -> MDD
disSet [] = bot
disSet (d:ds) = foldl' (.+.) d ds

xorSet :: [MDD] -> MDD
xorSet [] = top
xorSet (d:ds) = foldl' (xor) d ds

forallSet :: [Position] -> MDD -> MDD
forallSet [] d = d
forallSet [n] d = forall n d
forallSet (n : ns) d = (restrict n False (forallSet ns d)) .*. (restrict n True (forallSet ns d))

existSet :: [Position] -> MDD -> MDD
existSet [] d = d
existSet [n] d = exist n d
existSet (n : ns) d = (restrict n False (existSet ns d)) .+. (restrict n True (existSet ns d))


-- |======================================== Dd Manipulation operators ==============================================

restrict :: Position -> Bool -> MDD -> MDD
restrict n b (l, d) =
    let ctx = init_unary_context l
        -- Levels are prefixed by 0 in the current addressing scheme
        (ctx', r) = restrict_node_set @Dc ctx [0 : n] b d
    in (getLookup ctx', r)

neg :: NodeLookup -> Node -> MDD
neg l a =
    let ctx = init_unary_context l
        (ctx', r) = negation ctx a
    in (getLookup ctx', r)

con :: NodeLookup -> Node -> Node -> MDD
con l a b =
    let ctx = init_binary_context l
        (ctx', (_, r_dd)) = debug_func "INTER" $ apply' @Dc ctx "inter" a b
        (ctx'', r) = applyElimRule @Dc ctx' r_dd
    in (getLookup ctx'', r)

dis :: NodeLookup -> Node -> Node -> MDD
dis l a b =
    let ctx = init_binary_context l
        (ctx', (_, r_dd)) = debug_func "UNION" $ apply' @Dc ctx "union" a b
        (ctx'', r) = applyElimRule @Dc ctx' r_dd
    in (getLookup ctx'', r)


exists' :: NodeLookup -> Position -> Node -> MDD
exists' l n d =
    let (l', r1) = restrict n False (l, d)
        (l'', r2) = restrict n True (l', d)
    in dis l'' r1 r2

forall' :: NodeLookup -> Position -> Node -> MDD
forall' l n d =
    let (l', r1) = restrict n False (l, d)
        (l'', r2) = restrict n True (l', d)
    in con l'' r1 r2


getDependentVars :: NodeLookup -> [Position] -> Node -> [Position]
getDependentVars l v dd =
    let ctx = init_unary_context l
    in filter (\n -> (snd $ restrict_node_set @Dc ctx [0 : n] True dd) /= (snd $ restrict_node_set @Dc ctx [0 : n] False dd)) v


position_as_BDD :: Position -> Bool -> Path
position_as_BDD ([]) _ = error "no list provided"
position_as_BDD ([n]) b = if b then P'' [n] else P'' [-n]
position_as_BDD (n : ns) b = P' [(n, Dc1, position_as_BDD ns b)]

-- | needs to have full vocab as first argument
restrictLaw :: [Position] -> MDD -> MDD -> MDD
restrictLaw v (mgr, d) law = loop (getDependentVars mgr v d) (mgr, d) law where
  loop (n:ns) d@(_, dd) l@(_, law_node)
    | law_node == top_n = d -- the law completely covers the dd
    | (dd == top_n) || (dd == bot_n) = d
    | law_node == bot_n = top
    | otherwise =
        ((var $ position_as_BDD n True) .*. (loop ns (restrict n True d) (restrict n True l )))    .+.
        ((var $ position_as_BDD n False) .*. (loop ns (restrict n False d) (restrict n False l)))
  loop [] d@(_, dd) (_, law_node)
    | law_node == top_n = d
    | (dd == top_n) || (dd == bot_n) = d
    | law_node == bot_n = top
    | otherwise = error "impossible? something went wrong in restrictLaw."



ddSwapVars :: NodeLookup -> Node -> [Position] -> [Position] -> MDD
ddSwapVars mgr z [n1] [n2] =
        ite (var $ position_as_BDD n2 True)
        (ite (var $ position_as_BDD n1 True) a11 a10)
        (ite (var $ position_as_BDD n1 True) a01 a00)
    where
      a11 = restrict n2 True (restrict n1 True (mgr, z))
      a10 = restrict n2 False (restrict n1 True (mgr, z))
      a01 = restrict n2 True (restrict n1 False (mgr, z))
      a00 = restrict n2 False (restrict n1 False (mgr, z))
ddSwapVars mgr z (n1:ns1) (n2:ns2) =
        let (l', r) = ite (var $ position_as_BDD n2 True)
                (ite (var $ position_as_BDD n1 True) a11 a10)
                (ite (var $ position_as_BDD n1 True) a01 a00)
            r'' = (ddSwapVars l' r ns1 ns2)
        in  r''
    where
      a11 = restrict n2 True (restrict n1 True (mgr, z))
      a10 = restrict n2 False (restrict n1 True (mgr, z))
      a01 = restrict n2 True (restrict n1 False (mgr, z))
      a00 = restrict n2 False (restrict n1 False (mgr, z))
ddSwapVars mgr z n1 n2 = error $ "not covered case? \n" ++ intercalate ", \n" [show_dd settings mgr z, show n1, show n2]


-- | Relabel a DD with a list of pairs.
relabelWith ::  [(Position, Position)] -> MDD -> MDD
relabelWith r d = -- trace ("relabeling with " ++ show r ++ "\n on dd: \n" ++ show_dd settings (fst d) (snd d))
  loop d disjointListOfLists where

  -- Normalize the input to remove symmetric cycles (A->B, B->A)
  -- If we have (A,B) and (B,A), we only keep the one where A < B.
  -- This breaks the cycle and treats it as a single atomic swap.
  normalize [] = []
  normalize ((src, dst):xs)
    | (dst, src) `elem` xs = (src, dst) : normalize (filter (/= (dst, src)) xs)
    | otherwise            = (src, dst) : normalize xs
  -- prepare input
  normalizedR = normalize . sort . filter (uncurry (/=)) $ r
  (listVars1, listVars2) = unzip normalizedR

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

  loop (mgr, dd) (n:ns) = let (mgr', dd') = uncurry (ddSwapVars mgr dd) n in loop (mgr', dd') ns
  loop d [] = d


-- | Simultaneous substitution.
substitSimul :: [(Position, Node)] -> MDD -> MDD
substitSimul [] (mgr, dd) = (mgr, dd)
substitSimul ((n, psi) : ns) (mgr, dd) =
        ite (mgr, psi)
        (recurs (restrict n True (mgr, dd)))
        (recurs (restrict n False (mgr, dd)))
  where
        recurs = substitSimul ns