{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}

module MDD.Types where

import GHC.Generics (Generic)
import Data.Hashable
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Map as Map

-- ==========================================================================================================
-- * Core MDD Types
-- ==========================================================================================================

-- | MDDs are represented by (NodeLookup, Node) as a self-contained unit
type MDD = (NodeLookup, Node)

-- | Inference types for the edges of the Mixed Decision Diagram.
data Inf = Dc | Neg | Pos
    deriving (Eq, Show, Generic, Hashable)

-- | The core Decision Diagram data structure.
-- Node: standard BDD-style node with an index and two children (Positive, Negative).
-- InfNodes: MDD-style node with an index and three children (Continuous/Dc, Negative, Positive).
-- EndInfNode: A terminal marker for entering/exiting an infinity domain.
data Dd =  Node Int NodeId NodeId               -- left = pos (solid line in graph), right = neg (dotted line in graph)
                | InfNodes Int NodeId NodeId NodeId -- in order of types Dc, Neg, Pos
                | EndInfNode NodeId
                | Leaf Bool
                | Unknown
    deriving (Eq, Show, Generic)

-- | Unique identifier for a node: (Hash of the Dd structure, Alternative index for collisions)
type NodeId = (HashedId, Int)
type HashedId = Int

-- | Represents a full node (its ID and its data)
type Node = (NodeId, Dd)

-- | node lookup table
type NodeLookup = HashMap.HashMap HashedId LookupEntry
type LookupEntry = Map.Map Int TableEntry

data TableEntry = Entry {
  dd :: Dd,
  reference_count :: Int
} deriving (Show, Generic)

-- ==========================================================================================================
-- * Level and Position Types
-- ==========================================================================================================

-- | The level a given node resides on, tracking the path of inference types.
type Level' = [(Int, Inf)]

-- | Structured level representation for hashing and ordering.
data Level = L [(Int, Inf)] Int
    deriving (Eq, Show, Generic, Hashable)

-- | A position in the variable ordering.
type Position = [Int]

-- ==========================================================================================================
-- * Construction Helper Types
-- ==========================================================================================================

-- | Specific inference types used during construction to specify terminal values.
data InfL = Dc1 | Dc0 | Neg1 | Pos1 | Neg0 | Pos0
    deriving (Eq, Show, Ord, Generic, Hashable)

-- | A construction-time level used to define paths into the MDD.
data LevelL = Ll [(Int, InfL)] Int
    deriving (Eq, Show, Generic, Hashable)

-- | Path representation for creating MDDs from high-level descriptions.
data Path = P'' [Int]
          | P' [(Int, InfL, Path)]
    deriving (Show, Generic)

-- ==========================================================================================================
-- * Constants
-- ==========================================================================================================

-- Standard Node IDs for terminal leaves
l_1, l_0, l_u :: NodeId
l_1 = (1, 0) -- Leaf True
l_0 = (2, 0) -- Leaf False
l_u = (0, 0) -- Unknown