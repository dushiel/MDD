{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TupleSections #-}
module MDD where

import Debug.Trace ( trace )
import Data.Hashable
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Map as Map
import System.Console.ANSI
import GHC.Generics (Generic)
import Data.List (sortBy)
import Data.Ord (Down(..))


-- Base module for Mixed Decision Diagrams
-- These mix 3 types of inference / elimination rules in one Decision Diagram

-- ==========================================================================================================
-- * definition + initialization of manager
-- ==========================================================================================================

-- | The distinct types of Contexts for different operations

-- | Common interface for accessing the NodeLookup
class HasNodeLookup a where
    getLookup :: a -> NodeLookup
    setLookup :: NodeLookup -> a -> a


instance HasNodeLookup NodeLookup where
    getLookup = id
    setLookup nl _ = nl

-- | Context for Binary Operations (e.g., union, intersection)
data BinaryOperatorContext = BinaryOperatorContext {
  bin_nodelookup :: NodeLookup, -- hashmap of all nodes in the graph
  bin_cache :: Cache,
  bin_dc_stack :: ([Node], [Node], [Node]), -- remember on what infnode what dc's there are when unknowns need to be resolved
  bin_current_level :: (Level', Level') -- todo implement this still, so that hashing uses a level instead of position only
}

instance HasNodeLookup BinaryOperatorContext where
    getLookup = bin_nodelookup
    setLookup nl ctx = ctx { bin_nodelookup = nl }

-- | Context for Unary Operations (e.g., negation)
data UnaryOperatorContext = UnaryOperatorContext {
  un_nodelookup :: NodeLookup,
  un_cache :: SingleCache,
  un_dc_stack :: ([Node], [Node]), -- remember on what infnode what dc's there are when unknowns need to be resolved for single
  un_current_level :: Level'
}

instance HasNodeLookup UnaryOperatorContext where
    getLookup = un_nodelookup
    setLookup nl ctx = ctx { un_nodelookup = nl }

-- | Context for Drawing/Printing Operations
data DrawOperatorContext = DrawOperatorContext {
  draw_nodelookup :: NodeLookup,
  draw_cache :: ShowCache
}

instance HasNodeLookup DrawOperatorContext where
    getLookup = draw_nodelookup
    setLookup nl ctx = ctx { draw_nodelookup = nl }

-- | MDD Data Type
type MDD = (NodeLookup, NodeId)

-- | Static MDD Data Type
type StaticMDD = (StaticNodeLookup, NodeStatic)


init_lookup :: NodeLookup
init_lookup = defaultNodeMap

init_binary_context :: NodeLookup -> BinaryOperatorContext
init_binary_context nl = BinaryOperatorContext {
    bin_nodelookup = nl,
    bin_cache = Map.fromList (map (, HashMap.empty :: HashMap.HashMap (NodeId, NodeId, ([Node], [Node], [Node])) NodeId) ["union", "intersection", "inter", "interDc", "unionDc", "absorb", "traverse_and_return", "remove_outercomplement"]) :: Map.Map String (HashMap.HashMap (NodeId, NodeId, ([Node], [Node], [Node])) NodeId),
    bin_dc_stack = ([(l_u, Unknown)], [(l_u, Unknown)], [(l_u, Unknown)]),
    bin_current_level = ([(0, Dc)], [(0, Dc)])
}

init_unary_context :: NodeLookup -> UnaryOperatorContext
init_unary_context nl = UnaryOperatorContext {
    un_nodelookup = nl,
    un_cache = HashMap.empty :: HashMap.HashMap NodeId NodeId,
    un_dc_stack = ([(l_u, Unknown)], [(l_u, Unknown)]),
    un_current_level = [(0, Dc)]
}

init_draw_context :: NodeLookup -> DrawOperatorContext
init_draw_context nl = DrawOperatorContext {
    draw_nodelookup = nl,
    draw_cache = HashMap.empty
}


defaultNodeMap :: NodeLookup
defaultNodeMap = HashMap.fromList [
    (0, Map.fromList [(0, Entry{dd = Unknown, reference_count=1})] :: LookupEntry),
    (1, Map.fromList [(0, Entry{dd = Leaf True, reference_count=1})] :: LookupEntry),
    (2, Map.fromList [(0, Entry{dd = Leaf False, reference_count=1})] :: LookupEntry)]

defaultNodeMapStatic :: StaticNodeLookup
defaultNodeMapStatic = HashMap.fromList [
    (0, Map.fromList [(0, Entry'{ddStatic = Unknown', reference_count'=1})] :: LookupEntryStatic),
    (1, Map.fromList [(0, Entry'{ddStatic = Leaf' True, reference_count'=1})] :: LookupEntryStatic),
    (2, Map.fromList [(0, Entry'{ddStatic = Leaf' False, reference_count'=1})] :: LookupEntryStatic)]



-- ==========================================================================================================
-- * definitions and hashmap methods for nodes
-- ==========================================================================================================


data Inf = Dc | Neg | Pos
    deriving (Eq, Show, Generic, Hashable)

data Dd =  Node Int NodeId NodeId               -- left = pos (solid line in graph), right = neg (dotted line in graph)
                | InfNodes Int NodeId NodeId NodeId -- in order of types Dc, Neg, Pos
                | EndInfNode NodeId
                | Leaf Bool
                | Unknown
    deriving (Eq)

type NodeId = (HashedId, Int)
type HashedId = Int


-- | The level a given node resides on
-- e.g. [(3, dc), (1, n)] 4 =
-- <3> dc: (<1> dc: 1, n: (4) )
-- apply abs on the Int if its a pure level, instead of a level used for construction of a node
type Level' = [(Int, Inf)]
data Level = L [(Int, Inf)] Int deriving (Eq, Show)
type Position = [Int]

instance Hashable Dd where
  -- Leaf True : 1
  -- Leaf False : 2
  -- endIfnode : 3
  hash :: Dd -> HashedId
  hash Unknown = 0
  hash (Leaf b) = if b then 1 else 2
  hash (Node idx l r) = idx `hashWithSalt` fst l `hashWithSalt` fst r --`debug` (" hashing " ++ show (Node idx l r) ++ " -> " ++ show (idx `hashWithSalt` fst l `hashWithSalt` fst r))
  hash (InfNodes idx dc p n) = idx `hashWithSalt` fst dc `hashWithSalt` fst p `hashWithSalt` fst n
  hash (EndInfNode d) = fst d `hashWithSalt` (3::Int)
  hashWithSalt :: Int -> Dd -> HashedId
  hashWithSalt _ Unknown = 0
  hashWithSalt _ (Leaf b) = if b then 1 else 2
  hashWithSalt s (Node idx l r) = s `hashWithSalt` idx `hashWithSalt` fst l `hashWithSalt` fst r
  hashWithSalt s (InfNodes idx dc n p) = s `hashWithSalt` idx `hashWithSalt` fst dc `hashWithSalt` fst n `hashWithSalt` fst p
  hashWithSalt s (EndInfNode d) = s `hashWithSalt` fst d `hashWithSalt` (3::Int)

-- i should not implement this before fixing all the bugs, else i would not know whether this has a bug
-- todo add speedup by storing the hashed level up until this point and using that to recompute the current level.
-- for now it is more than fine to recompute the hash of the level by iteration. (remember daniel, it is canonical by definition.)
instance Hashable Level where
  hashWithSalt :: Int -> Level -> Int
  hashWithSalt s (L [] i) = s `hashWithSalt` i
  hashWithSalt s (L ((position, inf) :ns) i) = case inf of
      Dc -> h 4
      Neg -> h 5
      Pos -> h 6
      where
        h :: Int -> Int
        h x = position `hashWithSalt` x `hashWithSalt` hashWithSalt s (L ns i)


type NodeLookup =  HashMap.HashMap HashedId LookupEntry
type LookupEntry = Map.Map Int TableEntry

data TableEntry = Entry {
  dd :: Dd,
  reference_count :: Int
} deriving (Show, Generic)

type Node = (NodeId, Dd)

insert :: (HasNodeLookup c) => c -> Dd -> (c, Node)
insert c d =
    let nm = getLookup c
        (new_id, rnm) = insert_id (hash d) d nm
    in (setLookup rnm c, (new_id, d)) --`debug` ("about to insert " ++ show d  ++ "  ,  " ++ (show new_id))

getDd :: (HasNodeLookup c) => c -> NodeId -> Dd
getDd c node_id =
    let nm = getLookup c
    in case HashMap.lookup (fst node_id) nm of
       Just result -> case Map.lookup (snd node_id) result of
          Just result2 -> dd result2
          Nothing -> error $"Node adress without Alternative in NodeLookup: " ++ show node_id
       Nothing -> error$ "Node adress without Node in NodeLookup table/map: " ++ show node_id

getNode :: (HasNodeLookup c) => c -> NodeId -> Node
getNode c node_id =
    let nm = getLookup c
    in case HashMap.lookup (fst node_id) nm of
       Just result -> case Map.lookup (snd node_id) result of
          Just result2 -> (node_id, dd result2)
          Nothing -> error $"Node adress without Alternative in NodeLookup: " ++ show node_id
       Nothing -> error$ "Node adress without Node in NodeLookup table/map: " ++ show node_id


getDd_ :: NodeLookup -> NodeId -> Dd
getDd_ nm node_id = case HashMap.lookup (fst node_id) nm of
       Just result -> case Map.lookup (snd node_id) result of
          Just result2 -> dd result2
          Nothing -> error $"Node adress without Alternative in NodeLookup: " ++ show node_id ++ "\n\n with nodelookup:"
       Nothing -> error$ "Node adress without Node in NodeLookup table/map: " ++ show node_id ++ "\n\n with nodelookup:"


getEntry :: (HasNodeLookup c) => c -> NodeId -> TableEntry
getEntry c node_id =
    let nm = getLookup c
    in case HashMap.lookup (fst node_id) nm of
       Just result -> case Map.lookup (snd node_id) result of
          Just result2 -> result2
          Nothing -> error "Node adress without Alternative in NodeLookup"
       Nothing -> error "Node adress without Node in NodeLookup table/map"


-- | finds the alternative in the lookupentry which matches the given dd
-- nice-to-have: could add small speed up by checking if the length is 1 before matching
match_alternative :: Dd -> LookupEntry -> Maybe (Int, TableEntry)
match_alternative targetDD = Map.foldrWithKey' check Nothing
  where
    check k entry acc = if dd entry == targetDD
                        then Just (k, entry)
                        else acc

-- | gets a new key candidate
getFreeKey :: Map.Map Int v -> Int
getFreeKey nm
  | Map.null nm = 1
  | otherwise = head [x | x <- [1..n+1], not (Map.member x nm)]
  where
    n = Map.size nm

insert_id :: HashedId -> Dd -> NodeLookup -> (NodeId, NodeLookup)
insert_id k v nm = case HashMap.lookup k nm of
       Just result -> case match_alternative v result of -- there is something inserted at this key
         Just (nr, t_entry) -> -- increment the reference countshow_dd settings c b_id
              ((k, nr) :: NodeId, HashMap.insert k (Map.insert nr (Entry{dd = v, reference_count=reference_count t_entry + 1}) result) nm)
              -- `debug` (colorize "green" "insert: " ++ show k ++ " increment reference count : " ++ show (reference_count t_entry + 1))  -- it is the same Dd object, thus increment its reference count and return the NodeId with its map
         Nothing ->  -- it is not the same Dd object, get unused key in map
              let k' = getFreeKey result in
              ((k, k') :: NodeId, HashMap.insert k (Map.insert k' (Entry{dd = v, reference_count=1}) result) nm)
              -- `debug` (colorize "green" "insert: " ++ show k ++ " as alt with freekey: " ++ show k')
       Nothing -> -- key not found, insert current key with new alternatives map, and set its key 0 to value
        ((k, 0) :: NodeId, HashMap.insert k (Map.insert 0 Entry{dd = v, reference_count=1} Map.empty) nm)
        -- `debug` (colorize "green" "insert: " ++ "new object with key: " ++ show k)


-- todo add referencing and dereferencing of nodes in manager
-- -- | reduce count (and maybe remove) of a node in the nodelookup table
-- dereference :: Context -> Node -> Context
-- dereference c@Context{nodelookup=nm} (node_id@(key, alt_key), _)  =
--   if reference_count e == 1
--     -- find alternatives map in hashmap, delete entry in alternatives map, update in hashmap
--    then c{nodelookup= HashMap.adjust (Map.delete alt_key) key nm}
--     -- reduce the reference count by 1
--    else c{nodelookup= HashMap.adjust (Map.insert alt_key (e{reference_count= reference_count e - 1})) key nm}
--   where
--     e = getEntry c node_id


-- recursive :: Context -> Node -> (Context, Node)
-- recursive c d@(_, Node _ pos_child neg_child) = withCache_ c d $ let
--     (c', _) = recursive c (pos_child, getDd c pos_child)
--     (c'', _) = recursive c' (neg_child, getDd c' neg_child)
--     c''' = dereference c'' d
--     in (c''', d)
-- recursive c d@(_, InfNodes _ dc p n)  = withCache_ c d $ let
--     (c', _) = recursive c (dc, getDd c dc)
--     (c'', _) = recursive c (p, getDd c' p )
--     (c''', _) = recursive c (n, getDd c'' n )
--     c'''' = dereference c''' d
--     in (c'''', d)
-- recursive c d@(_, EndInfNode a) = withCache_ c d $ let
--     (c', _) = recursive c (a, getDd c a)
--     c'' = dereference c' d
--     in (c'', d)

-- -- | as opposed to insert, this will do a recursive/deep call adding a refence for each node
-- reference :: Node -> NodeLookup
-- reference dd = undefined

-- -- | deep equality check
-- deep_equality :: Node -> Node -> Bool
-- deep_equality = undefined


data DdStatic =  Node' [Int] NodeId NodeId               -- left = pos (solid line in graph), right = neg (dotted line in graph)
                | InfNodes' [Int] NodeId NodeId NodeId -- in order of types Dc, Neg, Pos
                | EndInfNode' NodeId
                | Leaf' Bool
                | Unknown'
    deriving (Eq)

type StaticNodeLookup =  HashMap.HashMap HashedId LookupEntryStatic
type LookupEntryStatic = Map.Map Int TableEntryStatic
data TableEntryStatic = Entry' {
  ddStatic :: DdStatic,
  reference_count' :: Int
}
type NodeStatic = (NodeId, DdStatic)

getNodeStatic :: StaticNodeLookup -> NodeId -> NodeStatic
getNodeStatic nm node_id = case HashMap.lookup (fst node_id) nm of
       Just result -> case Map.lookup (snd node_id) result of
          Just result2 -> (node_id, ddStatic result2)
          Nothing -> error $"Node adress without Alternative in NodeLookup: " ++ show node_id
       Nothing -> error$ "Node adress without Node in NodeLookup table/map: " ++ show node_id


instance Hashable DdStatic where
  -- Leaf True : 1
  -- Leaf False : 2
  -- endIfnode : 3
  hash :: DdStatic -> HashedId
  hash Unknown' = 0
  hash (Leaf' b) = if b then 1 else 2
  hash (Node' idx l r) = (last idx) `hashWithSalt` fst l `hashWithSalt` fst r --`debug` (" hashing " ++ show (Node idx l r) ++ " -> " ++ show (idx `hashWithSalt` fst l `hashWithSalt` fst r))
  hash (InfNodes' idx dc p n) = (last idx) `hashWithSalt` fst dc `hashWithSalt` fst p `hashWithSalt` fst n
  hash (EndInfNode' d) = fst d `hashWithSalt` (3::Int)
  hashWithSalt :: Int -> DdStatic -> HashedId
  hashWithSalt _ Unknown' = 0
  hashWithSalt _ (Leaf' b) = if b then 1 else 2
  hashWithSalt s (Node' idx l r) = s `hashWithSalt` idx `hashWithSalt` fst l `hashWithSalt` fst r
  hashWithSalt s (InfNodes' idx dc n p) = s `hashWithSalt` idx `hashWithSalt` fst dc `hashWithSalt` fst n `hashWithSalt` fst p
  hashWithSalt s (EndInfNode' d) = s `hashWithSalt` fst d `hashWithSalt` (3::Int)


match_alternative_static :: DdStatic -> LookupEntryStatic -> Maybe (Int, TableEntryStatic)
match_alternative_static targetDD = Map.foldrWithKey' check Nothing
  where
    check k entry acc = if ddStatic entry == targetDD
                        then Just (k, entry)
                        else acc

insert_id_static :: HashedId -> DdStatic -> StaticNodeLookup -> (NodeId, StaticNodeLookup)
insert_id_static k v nm = case HashMap.lookup k nm of
       Just result -> case match_alternative_static v result of -- there is something inserted at this key
         Just (nr, t_entry) -> -- increment the reference countshow_dd settings c b_id
              ((k, nr) :: NodeId, HashMap.insert k (Map.insert nr (Entry'{ddStatic = v, reference_count'=reference_count' t_entry + 1}) result) nm)
              -- `debug` (colorize "green" "insert: " ++ show k ++ " increment reference count : " ++ show (reference_count t_entry + 1))  -- it is the same Dd object, thus increment its reference count and return the NodeId with its map
         Nothing ->  -- it is not the same Dd object, get unused key in map
              let k' = getFreeKey result in
              ((k, k') :: NodeId, HashMap.insert k (Map.insert k' (Entry'{ddStatic = v, reference_count'=1}) result) nm)
              -- `debug` (colorize "green" "insert: " ++ show k ++ " as alt with freekey: " ++ show k')
       Nothing -> -- key not found, insert current key with new alternatives map, and set its key 0 to value
        ((k, 0) :: NodeId, HashMap.insert k (Map.insert 0 Entry'{ddStatic = v, reference_count'=1} Map.empty) nm)
        -- `debug` (colorize "green" "insert: " ++ "new object with key: " ++ show k)


insert_static :: StaticNodeLookup -> DdStatic -> (StaticNodeLookup, NodeStatic)
insert_static nm d = let (new_id, rnm) = insert_id_static (hash d) d nm in (rnm, (new_id, d))




-- ==========================================================================================================
-- * functions for Caching / Memoization of results during traversal
-- ==========================================================================================================

type Cache =  Map.Map String (HashMap.HashMap (NodeId, NodeId, ([Node], [Node], [Node])) NodeId)
type SingleCache =  HashMap.HashMap NodeId NodeId
type ShowCache =  HashMap.HashMap NodeId [String]


-- A higher-order function for handling cache lookup and update
withCache :: BinaryOperatorContext -> (Node, Node, String) -> (BinaryOperatorContext, Node) -> (BinaryOperatorContext, Node)
withCache c@BinaryOperatorContext{bin_cache = nc, bin_dc_stack = dck} ((keyA, _), (keyB, _), keyFunc) func_with_args =
  case Map.lookup keyFunc nc of
    Just nc' -> case HashMap.lookup (keyA, keyB, dck) nc' of
      Just result -> (c, getNode c result) --`debug` (col Vivid Green "func cache:" ++ " found previous result for " ++ show (keyA, keyB))
      Nothing -> let
        (updatedContext, r@(result, _)) = func_with_args
        new_dck = bin_dc_stack updatedContext
        updatedCache = Map.insert keyFunc (HashMap.insert (keyA, keyB, new_dck) result nc') nc
        in (updatedContext { bin_cache = updatedCache }, r) -- `debug` (col Vivid Green "func cache:" ++ " adding new key`` " ++ show (keyA, keyB))
    Nothing -> error ("function not in map, bad initialisation?: " ++ show keyFunc)

withCache_ :: UnaryOperatorContext -> Node -> (UnaryOperatorContext, Node) -> (UnaryOperatorContext, Node)
withCache_ c@UnaryOperatorContext { un_cache = nc } (key, _) func_with_args =
  case HashMap.lookup key nc of
    Just result -> (c, (result, getDd c result))
    Nothing -> let
      (updatedContext, result@(nodeid, _)) = func_with_args
      updatedCache = HashMap.insert key nodeid nc
      in (updatedContext { un_cache = updatedCache }, result)

showMerged = True

withCache' :: DrawOperatorContext -> Node -> [String] -> (DrawOperatorContext, [String])
withCache' c@DrawOperatorContext { draw_cache = nc } (key, _) func_with_args =
  case HashMap.lookup key nc of
    Just result -> if showMerged
      then (c, ["{" ++ col Dull Magenta ("#" ++ show key) ++ "}"])
      else (c, result)
    Nothing -> let
        result = func_with_args
        updatedCache = HashMap.insert key result nc
      in (c{ draw_cache = updatedCache }, result)


-- ==========================================================================================================
-- * Basic construction of nodes and paths
-- ==========================================================================================================



leaf :: Bool -> Node
leaf b = ((hash $Leaf b, 0), Leaf b)

leafid :: Bool -> NodeId
leafid b = (hash$ Leaf b, 0)

l_1 = (1, 0)
l_0 = (2, 0)
l_u = (0, 0)

data InfL = Dc1 | Dc0 | Neg1 | Pos1 | Neg0 | Pos0
    deriving (Eq, Show, Ord)
data LevelL = Ll [(Int, InfL)] Int deriving (Eq, Show)

instance Ord LevelL where
    compare (Ll xs i) (Ll ys j) = compare (xs, i) (ys, j)

-- given a LevelL create a Mixed Decision Diagram path
-- place a minus sign before a node nr to set it to negative.

levelLtoPath :: LevelL -> Path
levelLtoPath (Ll ((i, inf) : ns) int) = P' [(i, inf, levelLtoPath (Ll ns int))]
levelLtoPath (Ll [] int) = P'' [int]

makeNode :: NodeLookup -> LevelL -> (NodeLookup, Node)
makeNode nl l = path nl (levelLtoPath l)


data Path = P'' [Int]
            | P' [(Int, InfL, Path)] deriving Show


path :: NodeLookup -> Path -> (NodeLookup, Node)
path nl p = path' (-1) (nl, (l_u, Node (-5) l_u l_u)) (sortPathDesc p)

-- Function to sort the Path data structure in a depth-first manner
-- from highest to lowest on the integers.
sortPathDesc :: Path -> Path
sortPathDesc (P'' ints) =
    -- Do not sort the list of integers in descending order
    P'' ints
sortPathDesc (P' taggedPaths) =
    -- Step 1: Recursively sort the Path in each tuple's second element
    let sortedInnerPaths = map (\(tag, inf, p) -> (tag, inf, sortPathDesc p)) taggedPaths
    -- Step 2: Sort the list of tuples based on the tag (the Int) in descending order
        sortedTaggedPaths = sortBy (\(tagA, _, _) (tagB, _, _) -> compare (Down tagA) (Down tagB)) sortedInnerPaths
    in P' sortedTaggedPaths

l0' b
  | b == 0 = l_u
  | otherwise = l_0
l1' b
  | b == 1 = l_u
  | otherwise = l_1


path' :: Int -> (NodeLookup, Node) -> Path -> (NodeLookup, Node)
path' b (c, n) (P' ((i, inf, P'' nodelist) : pl))
    | inf == Dc1 || inf == Dc0 = path' b (insert c' (InfNodes i rid l_u l_u)) (P' pl) -- breadth step
    | inf == Pos1 = path' b (insert c' (InfNodes i (l0' b) rid l_u)) (P' pl) -- breadth step
    | inf == Neg1 = path' b (insert c' (InfNodes i (l0' b) l_u rid)) (P' pl) -- breadth step
    | inf == Pos0 = path' b (insert c' (InfNodes i (l1' b) rid l_u)) (P' pl) -- breadth step
    | inf == Neg0 = path' b (insert c' (InfNodes i (l1' b) l_u rid)) (P' pl) -- breadth step
      where
        (c',(rid,_)) = localpath' (c, n) inf nodelist -- depth first
path' b (c, n) (P' ((i, inf, pc) : pl))
    | inf == Dc1 || inf == Dc0 = path' b (insert cDc (InfNodes i ridDc l_u l_u)) (P' pl) -- breadth step
    | inf == Pos1 = path' b (insert c1 (InfNodes i (l0' b) rid1 l_u)) (P' pl) -- breadth step
    | inf == Neg1 = path' b (insert c1 (InfNodes i (l0' b) l_u rid1)) (P' pl) -- breadth step
    | inf == Pos0 = path' b (insert c0 (InfNodes i (l1' b) rid0 l_u)) (P' pl) -- breadth step
    | inf == Neg0 = path' b (insert c0 (InfNodes i (l1' b) l_u rid0)) (P' pl) -- breadth step
      where
        (c0,(rid0,_)) = path' 1 (c, n) pc -- depth first
        (c1,(rid1,_)) = path' 0 (c, n) pc -- depth first
        (cDc,(ridDc,_)) = path' b (c, n) pc -- depth first
path' b (c, n) (P' []) = (c, n) -- end of breadth step, return accumelator to previous call

-- FIX: Changed signature to use NodeLookup directly as requested
localpath' :: (NodeLookup, Node) -> InfL -> [Int] -> (NodeLookup, Node)
localpath' (c, n) inf nodeList
    | inf == Dc1 = loopDc c True nodeList n
    | inf == Pos1 = loopPos c True nodeList n
    | inf == Neg1 = loopNeg c True nodeList n
    | inf == Dc0 = loopDc c False nodeList n
    | inf == Pos0 = loopPos c False nodeList n
    | inf == Neg0 = loopNeg c False nodeList n
    where
        loopDc c b [] consequence = if consequence == initNode
            then (c, leaf b)
            else insert c $ EndInfNode $ fst consequence -- base case, add endinf for consequence
        loopDc c b (n:ns) consequence = let
          (c', (next_iter,_)) = loopDc c b ns consequence in
            if n ==0 then
              if consequence == initNode then (c, leaf b)
                else insert c' $ EndInfNode $ fst consequence
            else if n >= 0
                  then insert c' (Node n next_iter (leafid $not b))
                  else insert c' (Node (abs n) (leafid$ not b) next_iter)

        loopPos c b [] consequence = if consequence == initNode
            then (c, leaf b)
            else insert c $ EndInfNode $ fst consequence -- base case, add endinf for consequence
        loopPos c b (n:ns) consequence = let
          r@(c', (next_iter,_)) = loopPos c b ns consequence in
            if n ==0  then
              if consequence == initNode then (c, leaf b)
                else insert c' $ EndInfNode $ fst consequence
            else if n >= 0
                  then insert c' (Node n next_iter l_u )
                      else insert c' (Node (abs n) l_u next_iter )

        loopNeg c b [] consequence = if consequence == initNode
            then (c, leaf b)
            else insert c $ EndInfNode $ fst consequence -- base case, add endinf for consequence
        loopNeg c b (n:ns) consequence = let
          r@(c', (next_iter,_)) = loopNeg c b ns consequence in
            if n ==0  then
              if consequence == initNode then (c, leaf b)
                else insert c' $ EndInfNode $ fst consequence
            else if n >= 0
                  then insert c' (Node n next_iter l_u)
                      else insert c' (Node (abs n) l_u next_iter)

        initNode = (l_u, Node (-5) l_u l_u) -- ugly hack for empty accumelator, didnt want to implement maybe type throughout


-- | Helper function to nicely format the NodeLookup table
showNodeLookupDetails :: NodeLookup -> String
showNodeLookupDetails nl = unlines $ concatMap formatHashedEntry sortedEntries
  where
    -- Sort by HashedId for consistent/stable output reading
    sortedEntries = sortBy (\(k1, _) (k2, _) -> compare k1 k2) (HashMap.toList nl)

    formatHashedEntry :: (HashedId, LookupEntry) -> [String]
    formatHashedEntry (hid, entries) =
        map (formatEntry hid) (Map.toList entries)

    formatEntry :: HashedId -> (Int, TableEntry) -> String
    formatEntry hid (altIdx, entry) =
        "    " ++ show_id (hid, altIdx) ++ " -> " ++ show (dd entry) ++
        " " ++ colorize "dark" ("[refs: " ++ show (reference_count entry) ++ "]")

instance Show BinaryOperatorContext where
  show c = "BinaryOperatorContext {\n" ++
           "  -- Node Lookup Table (" ++ show (HashMap.size (bin_nodelookup c)) ++ " keys) --\n" ++
           showNodeLookupDetails (bin_nodelookup c) ++
           "\n  -- Process Managers --" ++
           "\n  cache keys  = " ++ show (Map.map HashMap.size (bin_cache c)) ++
           "\n}\n"

instance Show UnaryOperatorContext where
  show c = "UnaryOperatorContext {\n" ++
           "  -- Node Lookup Table (" ++ show (HashMap.size (un_nodelookup c)) ++ " keys) --\n" ++
           showNodeLookupDetails (un_nodelookup c) ++
           "\n  -- Process Managers --" ++
           "\n  cache_ keys = " ++ show (HashMap.size (un_cache c)) ++
           "\n}\n"

show_context :: (HasNodeLookup c) => c -> [Char]
show_context c = "Context nodelookup keys = " ++ show (HashMap.size (getLookup c))

show_dc_stack :: BinaryOperatorContext -> String
show_dc_stack BinaryOperatorContext{bin_dc_stack = fs} = "\\n" ++ show fs

show_id' :: Node -> String
show_id' (id, _) = show_id id

show_id :: NodeId -> String
show_id (k, alt) = "#" ++ show k ++ ":" ++ show alt


instance Show Dd where
    show Unknown = colorize "purple" "."
    show (Leaf True) = colorize "green" "1"
    show (Leaf False) = colorize "red" "0"
    show (EndInfNode d) = " <> " ++ show d
    show (Node a l r) = " " ++ show a ++ " (" ++ show l ++ ") (" ++ show r ++ ")"
    show (InfNodes a dc (0,0) (0,0)) = " " ++ show a ++ " ( dc: " ++ show dc ++ " )"

    show (InfNodes a dc p (0,0)) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( p: " ++ show p ++ " )"
    show (InfNodes a dc (0,0) n) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n: " ++ show n ++ " )"

    show (InfNodes a dc n p) = " " ++ show a ++ " ( dc: " ++ show dc ++ " ) ( n: " ++ show n ++ " ) ( p: " ++ show p ++ " )"

debug :: c -> String -> c
debug f s = trace s f


col :: ColorIntensity -> Color -> String -> String
col i c s = setSGRCode [SetColor Foreground i c] ++ s ++ setSGRCode [Reset]

colorize :: String -> String -> String
colorize c s
    | c == "red" = setColor24bit 255 100 100  ++ s ++ resetColor
    | c == "soft red" = setColor24bit 255 130 130  ++ s ++ resetColor
    | c == "green" = setColor24bit 100 200 100  ++ s ++ resetColor
    | c == "soft green" = setColor24bit 150 255 150  ++ s ++ resetColor
    | c == "dim green" = "\ESC[2m" ++ setColor24bit 0 255 0  ++ s ++ resetColor
    | c == "dim red" = "\ESC[2m" ++ setColor24bit 255 0 0  ++ s ++ resetColor
    | c == "blue" = "\ESC[2m" ++ setColor24bit 1 100 999  ++ s ++ resetColor
    | c == "chill blue" = setColor24bit 150 200 255  ++ s ++ resetColor
    | c == "orange" = setColor24bit 255 215 50  ++ s ++ resetColor
    | c == "purple" = setColor24bit 153 0 135  ++ s ++ resetColor
    | c == "dark" = setSGRCode [SetColor Foreground Dull White] ++ s ++ setSGRCode [Reset]
    | otherwise = setSGRCode [SetColor Foreground Vivid Blue] ++ s ++ setSGRCode [Reset]

setColor24bit :: Int -> Int -> Int -> String
setColor24bit r g b = "\ESC[38;2;" ++ show r ++ ";" ++ show g ++ ";" ++ show b ++ "m"

resetColor :: String
resetColor = "\ESC[0m"



-- | Merges two NodeLookups
-- All Dd entries from the second context (nl2) are merged into
-- the first context's (nl1) NodeLookup. Reference counts for identical Dds are summed.
unionNodeLookup :: NodeLookup -> NodeLookup -> NodeLookup
unionNodeLookup nl1 nl2 =
    HashMap.foldlWithKey' mergeHashedIdEntryFromNL2IntoAcc nl1 nl2
  where
    -- This function is called for each (HashedId, LookupEntry) pair from nl2.
    -- It merges all Dds within lookupEntryFromNL2 into accNL under hIdFromNL2.
    mergeHashedIdEntryFromNL2IntoAcc :: NodeLookup -> HashedId -> LookupEntry -> NodeLookup
    mergeHashedIdEntryFromNL2IntoAcc accNL hIdFromNL2 lookupEntryFromNL2 =
      -- Fold over the alternatives (TableEntry) within lookupEntryFromNL2.
      -- The 'accNL' is passed through and updated by 'processSingleTableEntry'.
      Map.foldlWithKey' (processSingleTableEntry hIdFromNL2) accNL lookupEntryFromNL2

    -- This function processes a single TableEntry (containing a Dd) from nl2.
    processSingleTableEntry :: HashedId -> NodeLookup -> Int -> TableEntry -> NodeLookup
    processSingleTableEntry hIdFromNL2 accNL _altKeyFromNL2 tableEntryFromNL2 =
      let ddToMerge       = dd tableEntryFromNL2
          refCountToMerge = reference_count tableEntryFromNL2
      in
      case HashMap.lookup hIdFromNL2 accNL of
        Just existingAlternativesMap -> -- HashedId from nl2 already exists in the accumulator
          case match_alternative ddToMerge existingAlternativesMap of
            Just _ -> accNL -- DD structure also matches an existing alternative, so do nothing.
            Nothing -> -- HashedId exists, but this Dd is a new alternative. Add it.
              let newAltIdx = getFreeKey existingAlternativesMap
                  newEntry  = Entry { dd = ddToMerge, reference_count = refCountToMerge }
              in HashMap.insert hIdFromNL2 (Map.insert newAltIdx newEntry existingAlternativesMap) accNL
        Nothing -> -- HashedId from nl2 does not exist in accumulator. Add new HashedId entry with this Dd.
          let newEntry = Entry { dd = ddToMerge, reference_count = refCountToMerge }
          -- Create a new LookupEntry (Map Int TableEntry) with the Dd as alternative 0.
          in HashMap.insert hIdFromNL2 (Map.singleton 0 newEntry) accNL

-- | Helper to create a merged Binary Context from two Lookups (used in operators)
unionContext :: (HasNodeLookup a, HasNodeLookup b) => a -> b -> BinaryOperatorContext
unionContext c1 c2 = init_binary_context (unionNodeLookup (getLookup c1) (getLookup c2))