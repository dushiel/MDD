{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use bimap" #-}
{-# LANGUAGE InstanceSigs #-}

import Data.Hashable
import qualified Data.HashMap.Strict as HashMap
type NodeId = Int
-- NodiId should be some kind of hash type


data Dd = Node Int NodeId NodeId
        | Leaf Bool
        deriving (Eq, Show)

instance Hashable Dd where
  hash :: Dd -> Int
  hash (Leaf b) = if b then 1 else 0
  hash (Node idx l r) = idx `hashWithSalt` l `hashWithSalt` r
  hashWithSalt :: Int -> Dd -> Int
  hashWithSalt _ (Leaf b) = if b then 1 else 0
  hashWithSalt s (Node idx l r) = s `hashWithSalt` idx `hashWithSalt` l `hashWithSalt` r


data Context = Context {
  nodelookup :: NodeLookup,
  cache :: Cache
}

type NodeLookup =  HashMap.HashMap NodeId (NodeId, Dd)

type Cache =  HashMap.HashMap (NodeId, NodeId) Dd

getDd :: Context -> NodeId -> Dd
getDd Context{nodelookup = nm} node_id = case HashMap.lookup node_id nm of
       Just result -> snd result
       Nothing -> error "Node adress without Node in NodeLookup table/map"

traversal :: (Context -> Dd -> Dd -> (Context, Dd)) -> Context -> Dd -> Dd -> (Context, Int)
traversal f c a b = let
  (rc@Context{nodelookup=rnm}, result) = f c a b
  (new_id, new_map) =  insert_id (hash result) result rnm
  in (rc{nodelookup=new_map}, new_id)

-- A higher-order function for handling cache lookup and update
withCache :: Context -> (NodeId, NodeId) -> (Context, Dd) -> (Context, Dd)
withCache c@Context { cache = nc } (keyA, keyB) func_with_args =
  case HashMap.lookup (keyA, keyB) nc of
    Just result -> (c, result)
    Nothing -> let
      (updatedContext, result) = func_with_args
      updatedCache = HashMap.insert (keyA, keyB) result nc
      in (updatedContext { cache = updatedCache }, result)


union :: Context -> Dd -> Dd -> (Context, Dd)
union c (Leaf b) (Leaf a) = (c, Leaf $ a || b )
union c a@(Node positionA posA negA) b@(Leaf _) = withCache c (hash a, hash b) $ let
    g = getDd c
    (Context{nodelookup=pos_nm, cache=pos_cache},posR) = traversal union c (g posA) b
    (Context{nodelookup=neg_nm, cache=neg_cache},negR) = traversal union c (g negA) b
   in (c{nodelookup = HashMap.union pos_nm neg_nm, cache = HashMap.union pos_cache neg_cache}, Node positionA posR negR)

union c a@(Leaf _) b@(Node positionB posB negB)  = withCache c (hash a, hash b) $ let
    g = getDd c
    (Context{nodelookup=pos_nm, cache=pos_cache},posR) = traversal union c a (g posB)
    (Context{nodelookup=neg_nm, cache=neg_cache},negR) = traversal union c a (g negB)
      in (c{nodelookup = HashMap.union pos_nm neg_nm, cache = HashMap.union pos_cache neg_cache}, Node positionB posR negR)
union c a@(Node _ posA negA) b@(Node positionB posB negB) = withCache c (hash a, hash b) $ let
    g = getDd c
    (Context{nodelookup=pos_nm, cache=pos_cache},posR) = traversal union c (g posA) (g posB)
    (Context{nodelookup=neg_nm, cache=neg_cache},negR) = traversal union c (g negA) (g negB)
      in (c{nodelookup = HashMap.union pos_nm neg_nm, cache = HashMap.union pos_cache neg_cache}, Node positionB posR negR)

-- union _ _ _ = undefined


main :: IO ()
main = do
  let nm_empty = HashMap.empty :: HashMap.HashMap Int (Int, Dd)
  let a = insert_id (hash $ Leaf True) (Leaf True) nm_empty
  print $ snd a
  let b = insert_id (hash $ Leaf False) (Leaf False) nm_empty
  print $ snd b
  let x = Node 1 (fst a) (fst b)
  let r1 = insert_id (hash x) x (HashMap.union (snd a) (snd b))
  let y = Node 1 (fst b) (fst a)
  let r2 = insert_id (hash y) y (snd r1)
  let r3 = union (snd r2) (getDd (snd r2) $ fst r1) (getDd (snd r2) $ fst r2)
  print $ snd r1
  print $ snd r2
  print r3

insert_id :: Int -> Dd -> NodeLookup -> (Int, NodeLookup)
insert_id k v nm = case HashMap.lookup k nm of
       Just result -> if v == snd result
         then (k, nm) -- future-todo keep track of how many nodes there are for garbage collection
         else insert_id (getFreeKey nm) v nm
       Nothing -> (k, HashMap.insert k (getFreeKey nm, v) nm)

getFreeKey :: HashMap.HashMap Int v -> Int
getFreeKey nm
  | HashMap.null nm = 1
  | otherwise = head [x | x <- [1..n+1], not (HashMap.member x nm)]
  where
    n = HashMap.size nm

remove :: NodeId -> Context -> Context
remove id c@Context{nodelookup = nm} = c{nodelookup = HashMap.delete id nm}


-- h(K) = floor (M (kA mod 1))

-- Here,
-- M is the size of the hash table.
-- k is the key value.
-- A is a constant value.


  -- let r = HashMap.lookup 2 nm
  -- let dd1 = Node 1 (hash $ Leaf True) (hash $ Leaf False)
  -- let dd2 = Node 2 (hash $ Leaf False) (hash $ Leaf True)
  -- let (_, result) = union HashMap.empty dd1 dd2
-- traversal nm f (Node i posA negA) b@(Leaf _) = let
--   t = traversal nm f
--   r1 = t (getDd posA) b
--   r2 = t (getDd negA) b
--   result = Node i (snd r1) (snd r2)
--   new_id = show result
--   in (Map.insert_id new_id result (Map.union (fst r1) (fst r2)), new_id)

-- type Memo = HashMap Int Dd

-- union' :: Dd -> Dd -> Memo -> (Memo, Dd)
-- union' a b memo =
--   let key = (hash a, hash b)
--   in case HashMap.lookup key memo of
--        Just result -> (memo, result)  -- If found, return the memo and result
--        Nothing -> let (memo', result) = computeUnion a b memo
--                   in (HashMap.insert key result memo', result)  -- Update memo with new result

-- computeUnion :: Dd -> Dd -> Memo -> (Memo, Dd)
-- computeUnion (Leaf a) (Leaf b) memo = (memo, Leaf (a || b))
-- computeUnion (Node idx la ra) (Leaf True) memo = (memo, Leaf True)
-- computeUnion (Node idx la ra) (Leaf False) memo =
--   let (memo', result) = union' la (inferNode (Leaf False)) memo
--   in (memo', result)
-- computeUnion (Leaf True) (Node idx la ra) memo = (memo, Leaf True)
-- computeUnion (Leaf False) (Node idx la ra) memo =
--   let (memo', result) = union' la (inferNode (Leaf False)) memo
--   in (memo', result)
-- -- todo combine memo
-- computeUnion (Node idx la ra) (Node idxb lb rb) memo = (memo, Node idx (snd $ computeUnion la lb memo) (snd $ computeUnion ra rb memo))
-- computeUnion a b m = error (""+||a||++||b||++||m||+"")
-- -- Placeholder for inferNode function
-- inferNode :: Dd -> Dd
-- inferNode (Leaf b) = Leaf b  -- Actual logic needed here
-- inferNode n = n
-- Example usage
