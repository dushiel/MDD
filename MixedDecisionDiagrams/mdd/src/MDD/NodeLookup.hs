{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}

module MDD.Manager where

import MDD.Types
import Data.Hashable
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Map as Map
import GHC.Generics (Generic)
import Data.List (sortBy)

-- | refactored with help of AI

instance Hashable Dd where
  hash Unknown = 0
  hash (Leaf b) = if b then 1 else 2
  hash (Node idx l r) = idx `hashWithSalt` fst l `hashWithSalt` fst r
  hash (InfNodes idx dc p n) = idx `hashWithSalt` fst dc `hashWithSalt` fst p `hashWithSalt` fst n
  hash (EndInfNode d) = fst d `hashWithSalt` (3::Int)

  hashWithSalt _ Unknown = 0
  hashWithSalt _ (Leaf b) = if b then 1 else 2
  hashWithSalt s (Node idx l r) = s `hashWithSalt` idx `hashWithSalt` fst l `hashWithSalt` fst r
  hashWithSalt s (InfNodes idx dc n p) = s `hashWithSalt` idx `hashWithSalt` fst dc `hashWithSalt` fst n `hashWithSalt` fst p
  hashWithSalt s (EndInfNode d) = s `hashWithSalt` fst d `hashWithSalt` (3::Int)

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