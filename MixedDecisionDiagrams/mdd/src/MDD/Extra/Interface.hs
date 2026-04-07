{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}

module MDD.Extra.Interface where

import MDD.Types
import MDD.Traversal.Context
import MDD.NodeLookup
import MDD.Construction
import MDD.Traversal.Binary
import MDD.Traversal.Unary
import MDD.Extra.Draw (settings, show_dd, debug)
import Data.List
import Data.Maybe (fromJust)
import Data.List (foldl')


top_n, bot_n, unk_n :: Node
top_n = (l_1, Leaf True)
bot_n = (l_0, Leaf False)
unk_n = (l_u, Unknown)

top, bot, unk :: MDD
top = MDD (init_lookup, top_n)
bot = MDD (init_lookup, bot_n)
unk = MDD (init_lookup, unk_n)

var :: Path -> MDD
var p = path p

var' :: LevelL -> MDD
var' l = makeNode init_lookup l

(-.) :: MDD -> MDD -- Negation
(-.) (MDD (la, a)) =
    let ctx = init_unary_context la
        (ctx', r) = negation ctx a
    in MDD (getLookup ctx', r)

infix 2 .*.   -- Conjunction
(.*.) :: MDD -> MDD -> MDD
(.*.) (MDD (la, a)) (MDD (lb, b)) =
    let ctx = init_binary_context (unionNodeLookup la lb)
        (ctx', r) = apply @Dc ctx "inter" (fst a) (fst b)
    in MDD (getLookup ctx', r)

infixl 3 .+.  -- Disjunction
(.+.) :: MDD -> MDD -> MDD
(.+.) (MDD (la, a)) (MDD (lb, b)) =
    let ctx = init_binary_context (unionNodeLookup la lb)
        (ctx', r) = apply @Dc ctx "union" (fst a) (fst b)
    in MDD (getLookup ctx', r)

ite :: MDD -> MDD -> MDD -> MDD
ite x y z = (x .*. y) .+. ((-.) x .*. z)

xor :: MDD -> MDD -> MDD
xor a b = (a .*. (-.) b) .+. ((-.) a .*. b)

restrict :: Position -> Bool -> MDD -> MDD
restrict n b (MDD (l, d)) =
    let ctx = init_unary_context l
        (ctx', r) = restrict_node_set @Dc ctx [0 : n] b d -- zero is added as for the top level
    in MDD (getLookup ctx', r)


position_as_BDD :: Position -> Bool -> Path
position_as_BDD [] _ = error "no list provided"
position_as_BDD [n] b = if b then P'' [n] else P'' [-n]
position_as_BDD (n : ns) b = P' [(n, Dc1, position_as_BDD ns b)]


ddSwapVars :: MDD -> [Position] -> [Position] -> MDD
ddSwapVars (MDD (mgr, z)) [n1] [n2] =
        ite (var $ position_as_BDD n2 True)
        (ite (var $ position_as_BDD n1 True) a11 a10)
        (ite (var $ position_as_BDD n1 True) a01 a00)
    where
      a11 = restrict n2 True (restrict n1 True (MDD (mgr, z)))
      a10 = restrict n2 False (restrict n1 True (MDD (mgr, z)))
      a01 = restrict n2 True (restrict n1 False (MDD (mgr, z)))
      a00 = restrict n2 False (restrict n1 False (MDD (mgr, z)))
ddSwapVars (MDD (mgr, z)) (n1:ns1) (n2:ns2) =
        let (MDD (l', r)) = ite (var $ position_as_BDD n2 True)
                (ite (var $ position_as_BDD n1 True) a11 a10)
                (ite (var $ position_as_BDD n1 True) a01 a00)
            r'' = ddSwapVars (MDD (l', r)) ns1 ns2
        in  r''
    where
      a11 = restrict n2 True (restrict n1 True (MDD (mgr, z)))
      a10 = restrict n2 False (restrict n1 True (MDD (mgr, z)))
      a01 = restrict n2 True (restrict n1 False (MDD (mgr, z)))
      a00 = restrict n2 False (restrict n1 False (MDD (mgr, z)))
ddSwapVars (MDD (mgr, z)) n1 n2 = error $ "not covered case? \n" ++ intercalate ", \n" [show_dd settings mgr z, show n1, show n2]


relabelWith :: [(Position, Position)] -> MDD -> MDD
relabelWith r d = loop d disjointListOfLists where
  normalize [] = []
  normalize ((src, dst):xs)
    | (dst, src) `elem` xs = (src, dst) : normalize (filter (/= (dst, src)) xs)
    | otherwise            = (src, dst) : normalize xs

  normalizedR = normalize . sort . filter (uncurry (/=)) $ r
  (listVars1, listVars2) = unzip normalizedR

  getOverlap l1 l2 = (map ((l1 !!) . fromJust) (indexes l1 l2), l1 `intersect` l2)
  indexes l1 l2 = map (`elemIndex` l2) (l1 `intersect` l2)
  indexesNotOverlap l1 l2 = map (`elemIndex` l1) (l1 `intersect` l2)

  newOverlap l1 l2 = (fst $ getOverlap l1 l2, map ((l1 !!) . fromJust) (indexesNotOverlap l1 l2))

  splitCompare [] [] = []
  splitCompare [] _ = error "varlists used for relabeling do not have equal length."
  splitCompare _ [] = error "varlists used for relabeling do not have equal length."
  splitCompare l1 l2 = (l1 \\ fst (getOverlap l1 l2), l2 \\ snd (getOverlap l1 l2)) : uncurry splitCompare (newOverlap l1 l2)

  disjointListOfLists = splitCompare listVars1 listVars2

  loop d_ [] = d_
  loop d_ (n:ns) = loop (uncurry (ddSwapVars d_) n) ns


substitSimul :: [(Position, Node)] -> MDD -> MDD
substitSimul [] m = m
substitSimul ((n, psi) : ns) m =
        ite (MDD (fst (unMDD m), psi))
        (substitSimul ns (restrict n True m))
        (substitSimul ns (restrict n False m))


infixl 1 .->.
(.->.) :: MDD -> MDD -> MDD
(.->.) a b = (-.) a .+. b

infixl 1 .<->.
(.<->.) :: MDD -> MDD -> MDD
(.<->.) a b = (a .*. b) .+. ((-.) a .*. (-.) b)

conSet :: [MDD] -> MDD
conSet [] = top
conSet (d:ds) = foldl' (.*.) d ds

disSet :: [MDD] -> MDD
disSet [] = bot
disSet (d:ds) = foldl' (.+.) d ds

xorSet :: [MDD] -> MDD
xorSet [] = top
xorSet (d:ds) = foldl' xor d ds

forall :: Position -> MDD -> MDD
forall n d = (restrict n False d) .*. (restrict n True d)

exist :: Position -> MDD -> MDD
exist n d = (restrict n False d) .+. (restrict n True d)

forallSet :: [Position] -> MDD -> MDD
forallSet [] d = d
forallSet [n] d = forall n d
forallSet (n : ns) d = (restrict n False (forallSet ns d)) .*. (restrict n True (forallSet ns d))

existSet :: [Position] -> MDD -> MDD
existSet [] d = d
existSet [n] d = exist n d
existSet (n : ns) d = (restrict n False (existSet ns d)) .+. (restrict n True (existSet ns d))