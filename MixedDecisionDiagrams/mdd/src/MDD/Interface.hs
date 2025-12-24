{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}

module MDD.Interface where

import MDD.Types
import MDD.Context
import MDD.Manager
import MDD.Construction
import MDD.Ops.Binary
import MDD.Ops.Unary
import MDD.Draw (settings, show_dd)
import Data.List
import Data.Maybe (fromJust)

-- |======================================== Dd Manipulation operators interactive ==============================================

-- Constants for standard leaf nodes
top_n, bot_n, unk_n :: Node
top_n = (l_1, Leaf True)
bot_n = (l_0, Leaf False)
unk_n = (l_u, Unknown)

top, bot, unk :: MDD
top = (init_lookup, top_n)
bot = (init_lookup, bot_n)
unk = (init_lookup, unk_n)

var :: Path -> MDD
var p = let (c', n) = path init_lookup p in (getLookup c', n)

var' :: LevelL -> MDD
var' l = let (c', n) = makeNode init_lookup l in (getLookup c', n)

(-.) :: MDD -> MDD
(-.) (la, a) =
    let ctx = init_unary_context la
        (ctx', r) = negation ctx a
    in (getLookup ctx', r)

infix 2 .*.   -- Conjunction / product
(.*.) :: MDD -> MDD -> MDD
(.*.) (la, a) (lb, b) =
    let ctx = init_binary_context (unionNodeLookup la lb)
        (ctx', r) = apply @Dc ctx "inter" (fst a) (fst b)
    in (getLookup ctx', r)

infixl 3 .+.  -- Disjunction / sum
(.+.) :: MDD -> MDD -> MDD
(.+.) (la, a) (lb, b) =
    let ctx = init_binary_context (unionNodeLookup la lb)
        (ctx', r) = apply @Dc ctx "union" (fst a) (fst b)
    in (getLookup ctx', r)

ite :: MDD -> MDD -> MDD -> MDD
ite x y z = (x .*. y) .+. ((-.) x .*. z)

xor :: MDD -> MDD -> MDD
xor a b = (a .*. (-.) b) .+. ((-.) a .*. b)

restrict :: Position -> Bool -> MDD -> MDD
restrict n b (l, d) =
    let ctx = init_unary_context l
        (ctx', r) = restrict_node_set @Dc ctx [0 : n] b d
    in (getLookup ctx', r)

-- | Relabel a DD with a list of pairs.
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
  splitCompare l1 l2 = (l1 \\ fst (getOverlap l1 l2), l2 \\ snd (getOverlap l1 l2)) : uncurry splitCompare (newOverlap l1 l2)

  disjointListOfLists = splitCompare listVars1 listVars2

  loop d_ [] = d_
  loop d_ (n:ns) = loop (ddSwapVars d_ n) ns

  ddSwapVars m (n1:ns1, n2:ns2) = ite (var $ position_as_BDD n2 True)
                                     (ite (var $ position_as_BDD n1 True) a11 a10)
                                     (ite (var $ position_as_BDD n1 True) a01 a00)
    where a11 = restrict n2 True (restrict n1 True m)
          a10 = restrict n2 False (restrict n1 True m)
          a01 = restrict n2 True (restrict n1 False m)
          a00 = restrict n2 False (restrict n1 False m)
          position_as_BDD ([p]) val = if val then P'' [p] else P'' [-p]
          position_as_BDD (p:ps) val = P' [(p, Dc1, position_as_BDD ps val)]
          position_as_BDD _ _ = error "empty pos"

-- | Simultaneous substitution.
substitSimul :: [(Position, Node)] -> MDD -> MDD
substitSimul [] m = m
substitSimul ((n, psi) : ns) m =
        ite (getLookup (fst m), psi)
        (substitSimul ns (restrict n True m))
        (substitSimul ns (restrict n False m))