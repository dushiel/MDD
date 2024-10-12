{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
module MDD where

import Debug.Trace ( trace )
import Data.Hashable
import qualified Data.HashMap.Strict as HashMap
import Data.Foldable
import qualified Data.Map as Map
import System.Console.ANSI

-- proof of concept GenDDs where no merging of isomorphic nodes happen and no cashing / moization of results during traversal.
-- GenDDs can model check second order logic formulas containing variables in multiple (disjointed and/or nested) infinite domains.


-- |======================================== Data Types + Explanation ==============================================

type NodeId = (HashedId, Int)

show_id :: NodeId -> String
show_id (k, alt) = "#" ++ show k ++ ":" ++ show alt

type HashedId = Int

data Inf = Dc | Neg | Pos
    deriving (Eq, Show)

data InfL = Dc1 | Dc0 | Neg1 | Pos1 | Neg0 | Pos0
    deriving (Eq, Show)


 -- sets the inference type when traversing through the tree depending which literal type is inf. We place them at the top (of each sub path of infinite domain). We can have multiple branches due to the multiple possible contexts.
data Dd =  Node Int NodeId NodeId               -- left = pos, right = neg
                | InfNodes Int NodeId NodeId NodeId
                | EndInfNode NodeId
                | Leaf Bool
                | Unknown
    deriving (Eq)

-- type Dd' = (NodeId, Dd)

-- | The level a given node resides on
-- e.g. [(3, dc), (1, n)] 4 =
-- <3> dc: (<1> dc: 1, n: (4) )
-- apply abs on the Int if its a pure level, instead of a level used for construction of a node
data Level = L [(Int, Inf)] Int deriving (Eq, Show)

instance Hashable Dd where
  -- Leaf False : 0
  -- Leaf True : 1
  -- endIfnode : 2
  hash :: Dd -> HashedId
  hash (Leaf b) = if b then 1 else 0
  hash (Node idx l r) = idx `hashWithSalt` fst l `hashWithSalt` fst r --`debug` (" hashing " ++ show (Node idx l r) ++ " -> " ++ show (idx `hashWithSalt` fst l `hashWithSalt` fst r))
  hash (InfNodes idx dc n p) = idx `hashWithSalt` fst dc `hashWithSalt` fst n `hashWithSalt` fst p
  hash (EndInfNode d) = fst d `hashWithSalt` (2::Int)
  hashWithSalt :: Int -> Dd -> HashedId
  hashWithSalt _ Unknown = 0
  hashWithSalt _ (Leaf b) = if b then 2 else 1
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


-- hashLevel :: Level -> Dd -> HashedId
-- hashLevel _ (Leaf b) = if b then 1 else 0
-- hashLevel l (Node idx lc rc) = l `hashLevel` idx `hashLevel` fst lc `hashLevel` fst rc
-- hashLevel l (InfNodes idx dc n1 n p1 p) = s `hashLevel` idx `hashLevel` fst dc `hashLevel` fst n1 `hashLevel` fst n `hashLevel` fst p1 `hashLevel` fst p
-- hashLevel l (EndInfNode d) = s `hashLevel` fst d `hashLevel` (2::NodeId)


data Context = Context {
  cache :: Cache,
  cache_ :: SingleCache,
  cache' :: ShowCache,
  nodelookup:: NodeLookup,
  func_stack :: [(Inf, FType)],
  current_level :: Level -- todo implement this still, so that hashing uses a level instead of position only
}

instance Show Context where
    show c = "Context {nodelookup keys = " ++ show (HashMap.size (nodelookup c)) ++
             "\n\t, cache keys = " ++ show (Map.map HashMap.size (cache c)) ++
             "\n\t, cache_ keys = " ++ show (HashMap.size (cache_ c)) ++ "}\n"

show_context :: Context -> [Char]
show_context c = "Context nodelookup keys = " ++ show (HashMap.size (nodelookup c)) ++
            --  "\\n\\t, cache keys = " ++ show (Map.map HashMap.size (cache c)) ++
             "\\n\\t, cache_ keys = " ++ show (HashMap.size (cache_ c)) ++ "\\n"

show_func_stack :: Context -> String
show_func_stack Context{func_stack = fs} = "\\n" ++ show fs

data FType = Union | Inter | MixedIntersection | MixedIntersection2 | MixedUnion | MixedUnion2 | Absorb | Remove | T_and_r
    deriving (Eq, Show)


type NodeLookup =  HashMap.HashMap HashedId LookupEntry
type LookupEntry = Map.Map Int TableEntry
data TableEntry = Entry {
  dd :: Dd,
  reference_count :: Int
}

getDd :: Context -> NodeId -> Dd
getDd c@Context{nodelookup = nm} node_id = case HashMap.lookup (fst node_id) nm of
       Just result -> case Map.lookup (snd node_id) result of
          Just result2 -> dd result2
          Nothing -> error $ "Node adress without Alternative in NodeLookup: " ++ show node_id ++ "\n\n with context:" ++ show c
       Nothing -> error $ "Node adress without Node in NodeLookup table/map: " ++ show node_id ++ "\n\n with context:" ++ show c

getDd_ :: NodeLookup -> NodeId -> Dd
getDd_ nm node_id = case HashMap.lookup (fst node_id) nm of
       Just result -> case Map.lookup (snd node_id) result of
          Just result2 -> dd result2
          Nothing -> error $ "Node adress without Alternative in NodeLookup: " ++ show node_id ++ "\n\n with nodelookup:"
       Nothing -> error $ "Node adress without Node in NodeLookup table/map: " ++ show node_id ++ "\n\n with nodelookup:"


getEntry :: Context -> NodeId -> TableEntry
getEntry Context{nodelookup = nm} node_id = case HashMap.lookup (fst node_id) nm of
       Just result -> case Map.lookup (snd node_id) result of
          Just result2 -> result2
          Nothing -> error "Node adress without Alternative in NodeLookup"
       Nothing -> error "Node adress without Node in NodeLookup table/map"

getEntry' :: HashedId -> NodeLookup -> LookupEntry
getEntry' node_id nm = case HashMap.lookup node_id nm of
       Just result -> result
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

-- show_dd :: NodeLookup -> NodeId -> String
-- -- show_dd c d = show c ++ show_dd s{display_context=False} c d
-- -- show_dd ShowSetting{draw_tree=True} c d = showTree c (getDd c d)
-- show_dd _ (0,0) = "[" ++ colorize "soft red" "0" ++ "]"
-- show_dd _ (1,0) = "[" ++ colorize "soft green" "1" ++ "]"
-- show_dd c d = case getDd_ c d of
--   Node i rC lC -> show_i i "orange" ++ " (" ++ show_dd c rC ++ ") (" ++ show_dd c lC ++ ")"
--   InfNodes i dc n1 n p1 p -> show_i i "chill blue" ++ " <{dc: " ++ show_dd c dc ++ "} {n1: " ++ show_dd c n1 ++ "} {n: " ++ show_dd c n ++ "} {p1: " ++ show_dd c p1 ++ "} {p: " ++ show_dd c p ++ "}>"
--   EndInfNode child -> colorize "chill blue" "<>" ++ show_dd c child
--   _ -> error "should not be possible"
--   where
--     show_i i c =  colorize "blue" ("#" ++ show d) ++ " "
--       ++ show i



insert :: Context -> Dd -> (Context, NodeId)
insert c@Context{nodelookup = nm} d = let (new_id, rnm) = insert_id (hash d) d nm in (c{nodelookup = rnm}, new_id)


merge_rule :: (Context -> Dd -> Dd -> (Context, Dd)) -> Context -> Dd -> Dd -> (Context, NodeId)
merge_rule f c a b = let
  (rc, result) = f c a b
  in insert rc result

merge_rule_ :: (Context -> Dd -> (Context, Dd)) -> Context -> Dd -> (Context, NodeId)
merge_rule_ f c a = let
  (rc, result) = f c a
  in insert rc result

-- | reduce count (and maybe remove) of a node in the nodelookup table
dereference :: Context -> NodeId -> Context
dereference c@Context{nodelookup=nm} node_id@(key, alt_key)  =
  if reference_count e == 1
    -- find alternatives map in hashmap, delete entry in alternatives map, update in hashmap
   then c{nodelookup= HashMap.adjust (Map.delete alt_key) key nm}
    -- reduce the reference count by 1
   else c{nodelookup= HashMap.adjust (Map.insert alt_key (e{reference_count= reference_count e - 1})) key nm}
  where
    e = getEntry c node_id


recursive :: Context -> Dd -> NodeId -> (Context, NodeId)
recursive c d@(Node _ pos_child neg_child) node_id = withCache_ c node_id $ let
    (c', _) = recursive c (getDd c pos_child) pos_child
    (c'', _) = recursive c' (getDd c' neg_child) neg_child
    c''' = dereference c'' node_id
    in (c''', node_id)
recursive c d@(InfNodes _ dc n p) node_id = withCache_ c node_id $ let
    (c', _) = recursive c (getDd c dc) dc
    (c'', _) = recursive c (getDd c' n) n
    (c''', _) = recursive c (getDd c'' p) p
    c'''' = dereference c''' node_id
    in (c'''', node_id)
recursive c d@(EndInfNode a) node_id = withCache_ c node_id $ let
    (c', _) = recursive c (getDd c a) a
    c'' = dereference c' node_id
    in (c'', node_id)

-- | as opposed to insert, this will do a recursive/deep call adding a refence for each node
reference :: NodeId -> NodeLookup
reference dd = undefined

-- | deep equality check
deep_equality :: NodeId -> NodeId -> Bool
deep_equality = undefined


-- * functions for Caching / Memoization of results during traversal

type Cache =  Map.Map String (HashMap.HashMap (NodeId, NodeId) NodeId)
type SingleCache =  HashMap.HashMap NodeId NodeId
type ShowCache =  HashMap.HashMap NodeId [String]


withCache_ :: Context -> NodeId -> (Context, NodeId) -> (Context, NodeId)
withCache_ c@Context { cache_ = nc } key func_with_args =
  case HashMap.lookup key nc of
    Just result -> (c, result)
    Nothing -> let
      (updatedContext, result) = func_with_args
      updatedCache = HashMap.insert key result nc
      in (updatedContext { cache_ = updatedCache }, result)

showMerged = True

withCache' :: Context -> NodeId -> [String] -> (Context, [String])
withCache' c@Context { cache' = nc } key func_with_args =
  case HashMap.lookup key nc of
    Just result -> if showMerged
      then (c, ["{" ++ col Dull Magenta ("#" ++ show key) ++ "}"])
      else (c, result)
    Nothing -> let
        result = func_with_args
        updatedCache = HashMap.insert key result nc
      in (c{ cache' = updatedCache }, result)


-- A higher-order function for handling cache lookup and update
withCache :: Context -> (NodeId, NodeId, String) -> (Context, NodeId) -> (Context, NodeId)
withCache c@Context{cache = nc} (keyA, keyB, keyFunc) func_with_args =
  case Map.lookup keyFunc nc of
    Just nc' -> case HashMap.lookup (keyA, keyB) nc' of
      Just result -> (c, result) `debug` (col Vivid Green "func cache:" ++ " found previous result for " ++ show (keyA, keyB))
      Nothing -> let
        (updatedContext, result) = func_with_args
        x = case getDd updatedContext result of
          --(EndInfNode d) -> error ("EndInf to be inserted in func cache" ++ show d)
          _ -> updatedContext
        updatedCache = Map.insert keyFunc (HashMap.insert (keyA, keyB) result nc') nc
        in (x { cache = updatedCache }, result) -- `debug` (col Vivid Green "func cache:" ++ " adding new key`` " ++ show (keyA, keyB))
    Nothing -> error ("function not in map, bad initialisation?: " ++ show keyFunc)


-- * Basic construction of nodes

-- At the variable class given represented by the ordinal, create a path containing the specified nodes from the list with the given inference rule.
-- We assume fixed variable classes, it is the responsibility of the user to give the correct ordinal
-- give empty list to create empty ZDD, e.g. : makePath (Order [1,2]) [] Neg

-- For making paths that take multiple Infnodes through finite types.
-- used for e.g. [2::Neg, 1::Neg, 3::Neg]
-- possible to give an empty list for the nodes to be set to positive
-- place a minus sign before a node nr to set it to negative.


defaultNodeMap :: NodeLookup
defaultNodeMap = HashMap.fromList [
    (0, Map.fromList [(0, Entry{dd = Leaf False, reference_count=1})] :: LookupEntry),
    (1, Map.fromList [(0, Entry{dd = Leaf True, reference_count=1})] :: LookupEntry)]

top :: Dd
top = Leaf True

bot :: Dd
bot = Leaf False

leaf :: Bool -> NodeId
leaf b = (hash $ Leaf b, 0)

l1 =(1, 0)
l0 = (2, 0)
u = (0, 0)


makeNode :: Context -> Bool -> Level -> (Context, NodeId)
makeNode _ b (L [] _) = error "empty context"
makeNode c b (L [(i, inf)] nodePosition)
    -- since we want the identity law in all our models,
    -- we set the default of dc to Leaf False (or leaf not end) instead of Unknown
    -- instead of manually applying the first order statement of
    -- forall paths a: -.(a ^ -. a)  (law of contradiction)
    | inf == Dc = let (c', rid) = loopDc nodePosition in ins' c' (InfNodes i rid u u) --`debug` ("nodePosition:  " ++ show nodePosition)
    | inf == Pos = let (c', rid) = loopPos nodePosition in ins' c' (InfNodes i (leaf $ not b) rid u)
    | inf == Neg = let (c', rid) = loopNeg nodePosition in ins' c' (InfNodes i (leaf $ not b) u rid)
    where
        ins' c d = insert c d
        ins d = insert c d
        -- 0 is for the InfNodes position, vars start from 1
        loopDc n = if n >=0 then ins (Node n (leaf b) (leaf $ not b)) else ins (Node (abs n) (leaf $ not b) (leaf b))
        loopPos n = if n >=0 then ins (Node (abs n) (leaf b) u) else ins (Node n (leaf $ not b) u)
        loopNeg n = if n >=0 then ins (Node (abs n) u (leaf b)) else ins (Node n u (leaf $ not b))
        -- close = (!! l) . iterate EndInfNode
makeNode c b (L ((i, inf):cs) nodePosition)
    | inf == Dc = let (c', rid) = makeNode c b (L cs nodePosition) in ins' c' (InfNodes i rid u u)
    | inf == Neg = let (c', rid) = makeNode c b (L cs nodePosition) in ins' c' (InfNodes i (leaf $ not b) u rid)
    | inf == Pos = let (c', rid) = makeNode c b (L cs nodePosition) in ins' c' (InfNodes i (leaf $ not b) rid u)
    where
        ins' c d = insert c d
        -- close = (!! l) . iterate EndInfNode




path :: Context -> [(Int, InfL)] -> [Int] -> (Context, NodeId)
path = makeLocalPath

makeLocalPath :: Context -> [(Int, InfL)] -> [Int] -> (Context, NodeId)
makeLocalPath = makeLocalPath'

-- unpackEndInf :: Dd -> Dd
-- unpackEndInf (EndInfNode d) = d
-- unpackEndInf _ = error "not possible"
-- < 0:dc > 3' 4' <2: n1>

makeLocalPath' :: Context -> [(Int, InfL)] -> [Int] -> (Context, NodeId)
makeLocalPath' _ [] _ = error "empty context"

makeLocalPath' c [(i, inf)] nodeList
    | inf == Dc1 = let (c', rid) = loopDc c True nodeList in insert c' (InfNodes i rid u u )
    | inf == Pos1 = let (c', rid) = loopPos c True nodeList in insert c' (InfNodes i l0 rid u )
    | inf == Neg1 = let (c', rid) = loopNeg c True nodeList in insert c' (InfNodes i l0 u rid )
    | inf == Dc0 = let (c', rid) = loopDc c False nodeList in insert c' (InfNodes i rid u u )
    | inf == Pos0 = let (c', rid) = loopPos c False nodeList in insert c' (InfNodes i l1 rid u )
    | inf == Neg0 = let (c', rid) = loopNeg c False nodeList in insert c' (InfNodes i l1 u rid )
    where
        loopDc c b (n:ns) = let
          (c', next_iter) = loopDc c b ns in
          if n >=0  then insert c' (Node (abs n) next_iter (leaf $ not b))
                    else insert c' (Node n (leaf $ not b) next_iter)
        loopDc c b [] = (c, leaf b)

        loopPos c b [] = (c, leaf b)
        loopPos c b (n:ns) = let
          (c', next_iter) = loopPos c b ns in
            if n >=0  then insert c' (Node n next_iter (leaf $ not b))
                      else insert c' (Node (abs n) (leaf $ not b) next_iter)

        loopNeg c b [] = (c, leaf b)
        loopNeg c b (n:ns) = let
          (c', next_iter) = loopNeg c b ns in
            if n >=0  then insert c' (Node (abs n) next_iter (leaf $ not b))
                      else insert c'  (Node n (leaf $ not b) next_iter)

makeLocalPath' c ((i, inf):ns) nodeList
    | inf == Dc1 || inf == Dc0 = let ( c',rid) = makeLocalPath' c ns nodeList in insert c' (InfNodes i rid u u)
    | inf == Pos1 = let ( c',rid) = makeLocalPath' c ns nodeList in insert c' (InfNodes i l0 rid u)
    | inf == Neg1 = let ( c',rid) = makeLocalPath' c ns nodeList in insert c' (InfNodes i l0 u rid)
    | inf == Pos0 = let ( c',rid) = makeLocalPath' c ns nodeList in insert c' (InfNodes i l1 rid u)
    | inf == Neg0 = let ( c',rid) = makeLocalPath' c ns nodeList in insert c' (InfNodes i l1 u rid)


instance Show Dd where
    show Unknown = colorize "purple" "."
    show (Leaf True) = colorize "red" "1"
    show (Leaf False) = colorize "green" "0"
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
