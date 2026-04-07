{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}

module MDD.Types
  ( -- * Core MDD Type
    MDD(..)
    -- * Node Identifiers
  , HashedId
  , NodeId
    -- * Decision Diagram Node Types
  , Inf(..)
  , Dd(..)
    -- * Node Storage Types
  , Node
  , NodeLookup
  , LookupEntry
  , TableEntry(..)
    -- * Path and Level Types
  , Position
  , Level'
  , Level(..)
  , InfL(..)
  , LevelL(..)
  , Path(..)
    -- * Standard Node ID Constants
  , l_1
  , l_0
  , l_u
    -- * Position Validation Helpers
  , isValidPosition
  , hasNonNegativeIndices
  , validatePosition
  , positionLength
  , isTopLevelPosition
  , outermostClassId
  , innermostVariable
  ) where

import GHC.Generics (Generic)
import Data.Hashable
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Map as Map


-- * Core MDD Type


-- | Mixed Decision Diagram: (NodeLookup, root Node).
-- Eq compares root NodeId only. TODO: merge NodeLookups before comparison.
newtype MDD = MDD { unMDD :: (NodeLookup, Node) }
  deriving (Generic)

instance Eq MDD where
  (MDD (_, (id1, _))) == (MDD (_, (id2, _))) = id1 == id2

instance Show MDD where
  show (MDD (_, (_, dd))) = show dd


-- * Node Identifiers


-- | Hash of a Dd structure (first component of NodeId).
type HashedId = Int

-- | Unique node identifier: (HashedId, alternative index for collisions).
type NodeId = (HashedId, Int)


-- * Decision Diagram Node Types


-- | Inference types: Dc (don't-care), Pos (positive literal), Neg (negative literal).
data Inf = Dc | Neg | Pos
  deriving (Eq, Show, Generic, Hashable)

-- | Decision diagram node types.
data Dd
  = Node Int NodeId NodeId
    -- ^ Branching node: (position, pos child, neg child)
  | ClassNode Int NodeId NodeId NodeId
    -- ^ Class node: (position, dc, neg, pos branches)
  | EndClassNode NodeId
    -- ^ Class exit marker
  | Leaf Bool
    -- ^ Terminal (True/False)
  | Unknown
    -- ^ Terminal (resolves from the closest dc branch)
  deriving (Eq, Show, Generic)


-- * Node Storage Types


-- | Complete node: (NodeId, Dd)
type Node = (NodeId, Dd)

-- | Global node storage: HashedId -> LookupEntry
type NodeLookup = HashMap.HashMap HashedId LookupEntry

-- | Lookup entry for hash collisions: alternative index -> TableEntry
type LookupEntry = Map.Map Int TableEntry

-- | Node entry with reference count
data TableEntry = Entry
  { dd :: Dd
  , reference_count :: Int
  }
  deriving (Show, Generic)


-- * Path and Level Types


-- | Position in MDD hierarchy: [class1, class2, ..., variable]
type Position = [Int]

-- | class prefix with inference types: [(position, Inf), ...]
type Level' = [(Int, Inf)]

-- | class prefix with inference types - with terminal position.
-- | complete adress of a node: Position with inference types added
data Level = L [(Int, Inf)] Int
  deriving (Eq, Show, Generic, Hashable)

-- | Inference literal for construction: suffix 0/1 = default False/True
-- | used only for parsing / construction
data InfL = Dc1 | Dc0 | Neg1 | Pos1 | Neg0 | Pos0
  deriving (Eq, Show, Ord, Generic, Hashable)

-- | Level with inference literals, for construction
data LevelL = Ll [(Int, InfL)] Int
  deriving (Eq, Ord, Show, Generic, Hashable)

-- | Path: P'' [Int] for terminals, P' [(class_id, InfL, Path)] for nested classes
-- | instead of only describing a single node, this can describe a full path
-- | terminal position can be 0 (top/bot), positive or negative int/literal
-- | used for construction
data Path
  = P'' [Int]
  | P' [(Int, InfL, Path)]
  deriving (Show, Generic)


-- * Standard Node ID Constants


-- | Standard node IDs for terminals
l_1, l_0, l_u :: NodeId
l_1 = (1, 0)  -- Leaf True
l_0 = (2, 0)  -- Leaf False
l_u = (0, 0)  -- Unknown


-- * Position Validation Helpers
-- not sure yet whether i want to use these

-- | Position validation helpers
isValidPosition :: Position -> Bool
isValidPosition = not . null

hasNonNegativeIndices :: Position -> Bool
hasNonNegativeIndices = all (>= 0)

validatePosition :: Position -> Bool
validatePosition pos = isValidPosition pos && hasNonNegativeIndices pos

positionLength :: Position -> Int
positionLength = length

isTopLevelPosition :: Position -> Bool
isTopLevelPosition = (== 1) . length

outermostClassId :: Position -> Maybe Int
outermostClassId [] = Nothing
outermostClassId (x:_) = Just x

innermostVariable :: Position -> Maybe Int
innermostVariable [] = Nothing
innermostVariable xs = Just (last xs)