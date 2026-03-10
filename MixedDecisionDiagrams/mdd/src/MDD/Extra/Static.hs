{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}

module MDD.Static where

import MDD.Types
import MDD.Context
import MDD.Manager
import MDD.Stack
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Map as Map
import Data.Hashable
import GHC.Generics (Generic)


-- | AI generated code

-- | Static translation is provided for visualization.
-- This assigns a fixed global order to all declared variables for consistent Graphviz rendering.
data DdStatic =  Node' [Int] NodeId NodeId               -- left = pos (solid line in graph), right = neg (dotted line in graph)
                | InfNodes' [Int] NodeId NodeId NodeId -- in order of types Dc, Neg, Pos
                | EndInfNode' NodeId
                | Leaf' Bool
                | Unknown'
    deriving (Eq, Show, Generic)

type StaticNodeLookup =  HashMap.HashMap HashedId LookupEntryStatic
type LookupEntryStatic = Map.Map Int TableEntryStatic

data TableEntryStatic = Entry' {
  ddStatic :: DdStatic,
  reference_count' :: Int
} deriving (Show, Generic)

type NodeStatic = (NodeId, DdStatic)


instance Hashable DdStatic where
  hash Unknown' = (0::Int)
  hash (Leaf' b) = if b then (1::Int) else (2::Int)
  hash (Node' idx l r) = (last idx) `hashWithSalt` fst l `hashWithSalt` fst r
  hash (InfNodes' idx dc p n) = (last idx) `hashWithSalt` fst dc `hashWithSalt` fst p `hashWithSalt` fst n
  hash (EndInfNode' d) = fst d `hashWithSalt` (3::Int)

  hashWithSalt s Unknown' = s `hashWithSalt` (0::Int)
  hashWithSalt s (Leaf' b) = s `hashWithSalt` (if b then (1::Int) else (2::Int))
  hashWithSalt s (Node' idx l r) = s `hashWithSalt` idx `hashWithSalt` fst l `hashWithSalt` fst r
  hashWithSalt s (InfNodes' idx dc n p) = s `hashWithSalt` idx `hashWithSalt` fst dc `hashWithSalt` fst n `hashWithSalt` fst p
  hashWithSalt s (EndInfNode' d) = s `hashWithSalt` fst d `hashWithSalt` (3::Int)

defaultNodeMapStatic :: StaticNodeLookup
defaultNodeMapStatic = HashMap.fromList [
    (0, Map.fromList [(0, Entry'{ddStatic = Unknown', reference_count'=1})]),
    (1, Map.fromList [(0, Entry'{ddStatic = Leaf' True, reference_count'=1})]),
    (2, Map.fromList [(0, Entry'{ddStatic = Leaf' False, reference_count'=1})])]

insert_id_static :: HashedId -> DdStatic -> StaticNodeLookup -> (NodeId, StaticNodeLookup)
insert_id_static k v nm = case HashMap.lookup k nm of
       Just result -> case match_alternative_static v result of
         Just (nr, t_entry) ->
              ((k, nr), HashMap.insert k (Map.insert nr (Entry'{ddStatic = v, reference_count'=reference_count' t_entry + 1}) result) nm)
         Nothing ->
              let k' = getFreeKey result in
              ((k, k'), HashMap.insert k (Map.insert k' (Entry'{ddStatic = v, reference_count'=1}) result) nm)
       Nothing ->
        ((k, 0), HashMap.insert k (Map.insert 0 Entry'{ddStatic = v, reference_count'=1} Map.empty) nm)

match_alternative_static :: DdStatic -> LookupEntryStatic -> Maybe (Int, TableEntryStatic)
match_alternative_static targetDD = Map.foldrWithKey' check Nothing
  where
    check k entry acc = if ddStatic entry == targetDD then Just (k, entry) else acc

insert_static :: StaticNodeLookup -> DdStatic -> (StaticNodeLookup, NodeStatic)
insert_static nm d = let (new_id, rnm) = insert_id_static (hash d) d nm in (rnm, (new_id, d))

get_static_lv :: UnOpContext -> [Int]
get_static_lv ctx = reverse (map fst (un_current_level ctx))


to_static_form :: UnOpContext -> Node -> (StaticNodeLookup, NodeStatic)
to_static_form ctx node = go defaultNodeMapStatic ctx node
  where
    go :: StaticNodeLookup -> UnOpContext -> Node -> (StaticNodeLookup, NodeStatic)
    go snl c d@(_, Node position pos_child neg_child) =
        let (snl1, (posR, _)) = go snl c (getNode c pos_child)
            (snl2, (negR, _)) = go snl1 c (getNode c neg_child)
        in insert_static snl2 $ Node' (get_static_lv c ++ [position]) posR negR

    go snl c d@(_, InfNodes position dc p n) =
        let c_dc = add_to_level_ (position, Dc) c
            (snl1, (r_dc, _)) = go snl c_dc (getNode c dc)
            c_n = add_to_level_ (position, Neg) (reset_stack_un c_dc c)
            (snl2, (r_n, _)) = go snl1 c_n (getNode c n)
            c_p = add_to_level_ (position, Pos) (reset_stack_un c_n c)
            (snl3, (r_p, _)) = go snl2 c_p (getNode c p)
        in insert_static snl3 $ InfNodes' (get_static_lv c ++ [position]) r_dc r_p r_n

    go snl c d@(_, EndInfNode a) =
        let (_ : lvs) = un_current_level c
            c' = c { un_current_level = lvs }
            (snl1, (result, _)) = go snl c' (getNode c a)
        in insert_static snl1 $ EndInfNode' result

    go snl _ (_, Leaf b) = insert_static snl (Leaf' b)
    go snl _ (_, Unknown) = insert_static snl Unknown'

-- | Retrieves all variable paths present in the diagram
allVars :: UnOpContext -> Node -> [Position]
allVars ctx d@(_, Node position pos_child neg_child) =
  [get_static_lv ctx ++ [position]] ++
   allVars ctx (getNode ctx pos_child) ++ allVars ctx (getNode ctx neg_child)
allVars ctx d@(_, InfNodes position dc p n) =
    let c_dc = add_to_level_ (position, Dc) ctx
        c_n = add_to_level_ (position, Neg) ctx
        c_p = add_to_level_ (position, Pos) ctx
    in [get_static_lv ctx ++ [position]] ++
        allVars c_dc (getNode ctx dc) ++ allVars c_n (getNode ctx n) ++ allVars c_p (getNode ctx p)
allVars ctx d@(_, EndInfNode a) =
    let (_ : lvs) = un_current_level ctx
    in allVars (ctx { un_current_level = lvs }) (getNode ctx a)
allVars _ (_, Leaf _) = []
allVars _ (_, Unknown) = []