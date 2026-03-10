{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}

module MDD.Types where

import GHC.Generics (Generic)
import Data.Hashable
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Map as Map


-- | MDDs are represented by (NodeLookup, Node) as a self-contained unit.
-- The Eq instance compares the NodeId (hashcode + collision id) of the root node
-- todo perform a proper merge of NodeLookups before Eq check
newtype MDD = MDD { unMDD :: (NodeLookup, Node) }
instance Eq MDD where
  (MDD (_, (id1, _))) == (MDD (_, (id2, _))) = id1 == id2

instance Show MDD where
  show (MDD (_, (_, dd))) = show dd

-- | Inference types for the edges of the Mixed Decision Diagram.
data Inf = Dc | Neg | Pos
    deriving (Eq, Show, Generic, Hashable)

-- Node: Node with a context dependent index and two children (Positive, Negative).
-- InfNodes: Node with a context dependent index and three children (Continuous/Dc, Negative, Positive).
-- EndInfNode: A terminal marker for entering/exiting a variable class / domain.
data Dd =  Node Int NodeId NodeId               -- left = pos (solid line in graph), right = neg (dotted line in graph)
                | InfNodes Int NodeId NodeId NodeId -- in order of types Dc, Neg, Pos
                | EndInfNode NodeId
                | Leaf Bool
                | Unknown
    deriving (Eq, Show, Generic)

-- | Unique identifier for a node: (Hash of the Dd structure, Alternative index for collisions)
type NodeId = (HashedId, Int)
type HashedId = Int

type Node = (NodeId, Dd)

type NodeLookup = HashMap.HashMap HashedId LookupEntry
type LookupEntry = Map.Map Int TableEntry

data TableEntry = Entry {
  dd :: Dd,
  reference_count :: Int
} deriving (Show, Generic)


type Level' = [(Int, Inf)]

data Level = L [(Int, Inf)] Int
    deriving (Eq, Show, Generic, Hashable)

type Position = [Int]


data InfL = Dc1 | Dc0 | Neg1 | Pos1 | Neg0 | Pos0
    deriving (Eq, Show, Ord, Generic, Hashable)

data LevelL = Ll [(Int, InfL)] Int
    deriving (Eq, Ord, Show, Generic, Hashable)

data Path = P'' [Int]
          | P' [(Int, InfL, Path)]
    deriving (Show, Generic)

-- Standard Node IDs as shortcuts for terminal leaves
l_1, l_0, l_u :: NodeId
l_1 = (1, 0) -- Leaf True
l_0 = (2, 0) -- Leaf False
l_u = (0, 0) -- Unknown