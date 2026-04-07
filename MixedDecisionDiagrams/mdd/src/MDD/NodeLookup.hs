{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module MDD.NodeLookup
  ( -- * Hashable instance
    -- $hashable

    -- * NodeLookup operations
    init_lookup
  , match_alternative
  , getFreeKey
  , insert_id
  , unionNodeLookup

    -- * MDD equality
  , eqMDD
  , getDdFrom
  ) where

import MDD.Types
import Data.Hashable
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Map as Map
import qualified Data.Set as Set

-- | refactored with help of AI

instance Hashable Dd where
  hash Unknown = 0
  hash (Leaf b) = if b then 1 else 2
  hash (Node idx l r) = idx `hashWithSalt` fst l `hashWithSalt` fst r
  hash (ClassNode idx dc p n) = idx `hashWithSalt` fst dc `hashWithSalt` fst p `hashWithSalt` fst n
  hash (EndClassNode d) = fst d `hashWithSalt` (3::Int)

  hashWithSalt _ Unknown = 0
  hashWithSalt _ (Leaf b) = if b then 1 else 2
  hashWithSalt s (Node idx l r) = s `hashWithSalt` idx `hashWithSalt` fst l `hashWithSalt` fst r
  hashWithSalt s (ClassNode idx dc n p) = s `hashWithSalt` idx `hashWithSalt` fst dc `hashWithSalt` fst n `hashWithSalt` fst p
  hashWithSalt s (EndClassNode d) = s `hashWithSalt` fst d `hashWithSalt` (3::Int)

-- | Initial lookup table with standard leaf nodes (0: Unknown, 1: True, 2: False)
init_lookup :: NodeLookup
init_lookup = HashMap.fromList [
    (0, Map.fromList [(0, Entry{dd = Unknown, reference_count=1})]),
    (1, Map.fromList [(0, Entry{dd = Leaf True, reference_count=1})]),
    (2, Map.fromList [(0, Entry{dd = Leaf False, reference_count=1})])]

-- | Finds an existing alternative in the lookup entry matching the given Dd
match_alternative :: Dd -> LookupEntry -> Maybe (Int, TableEntry)
match_alternative targetDD = Map.foldrWithKey' check Nothing
  where
    check k entry acc = if dd entry == targetDD then Just (k, entry) else acc

-- | Gets a new key candidate for internal alternatives map
getFreeKey :: Map.Map Int v -> Int
getFreeKey nm
  | Map.null nm = 1
  | otherwise = head [x | x <- [1..n+1], not (Map.member x nm)]
  where n = Map.size nm

-- | Core insertion logic into the global NodeLookup
insert_id :: HashedId -> Dd -> NodeLookup -> (NodeId, NodeLookup)
insert_id k v nm = case HashMap.lookup k nm of
       Just result -> case match_alternative v result of
         Just (nr, t_entry) ->
              ((k, nr), HashMap.insert k (Map.insert nr (Entry{dd = v, reference_count=reference_count t_entry + 1}) result) nm)
         Nothing ->
              let k' = getFreeKey result in
              ((k, k'), HashMap.insert k (Map.insert k' (Entry{dd = v, reference_count=1}) result) nm)
       Nothing ->
        ((k, 0), HashMap.insert k (Map.insert 0 Entry{dd = v, reference_count=1} Map.empty) nm)

-- | Merges two NodeLookups summing reference counts for identical structures
unionNodeLookup :: NodeLookup -> NodeLookup -> NodeLookup
unionNodeLookup nl1 nl2 = HashMap.foldlWithKey' mergeHashed nl1 nl2
  where
    mergeHashed accNL hId lookupEntry = Map.foldlWithKey' (processEntry hId) accNL lookupEntry
    processEntry hId acc _ tableEntry =
      let d = dd tableEntry
          rc = reference_count tableEntry
      in case HashMap.lookup hId acc of
        Just existing -> case match_alternative d existing of
            Just _ -> acc
            Nothing -> let k' = getFreeKey existing
                       in HashMap.insert hId (Map.insert k' (Entry d rc) existing) acc
        Nothing -> HashMap.insert hId (Map.singleton 0 (Entry d rc)) acc


-- todo: add referencing and dereferencing / keep count of "alive" nodes
-- todo: hash nodes based on level
-- todo: improve union / merge of nodelookups (espc conflic handling / for e calls between mdds)


-- * MDD Equality (orphan instance — MDD is defined in Types, logic lives here)


instance Eq MDD where
  (MDD (nl1, (id1, _))) == (MDD (nl2, (id2, _))) = eqMDD nl1 id1 nl2 id2

-- | Deep structural equality for MDD graphs. Recursively compares the Dd
-- structures reachable from two root NodeIds, each in its own NodeLookup.
-- Uses a visited set to avoid exponential blowup on shared subgraphs.
eqMDD :: NodeLookup -> NodeId -> NodeLookup -> NodeId -> Bool
eqMDD nl1 root1 nl2 root2 = go Set.empty root1 root2
  where
    go visited id1 id2
      | id1 == id2 = True
      | (id1, id2) `Set.member` visited = True
      | otherwise =
          let visited' = Set.insert (id1, id2) visited
          in eqDd visited' (getDdFrom nl1 id1) (getDdFrom nl2 id2)

    eqDd _ (Leaf b1) (Leaf b2) = b1 == b2
    eqDd _ Unknown Unknown = True
    eqDd vis (Node p1 pos1 neg1) (Node p2 pos2 neg2) =
      p1 == p2 && go vis pos1 pos2 && go vis neg1 neg2
    eqDd vis (ClassNode p1 dc1 n1 ps1) (ClassNode p2 dc2 n2 ps2) =
      p1 == p2 && go vis dc1 dc2 && go vis n1 n2 && go vis ps1 ps2
    eqDd vis (EndClassNode c1) (EndClassNode c2) = go vis c1 c2
    eqDd _ _ _ = False

-- | Retrieve a Dd from a NodeLookup by NodeId.
getDdFrom :: NodeLookup -> NodeId -> Dd
getDdFrom nl (hId, alt) =
  case HashMap.lookup hId nl of
    Just entry -> case Map.lookup alt entry of
      Just te -> dd te
      Nothing -> error $ "getDdFrom: no alternative " ++ show alt ++ " at hash " ++ show hId
    Nothing -> error $ "getDdFrom: hash not in lookup: " ++ show hId