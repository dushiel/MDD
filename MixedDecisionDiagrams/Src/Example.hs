module  MixedDecisionDiagrams.Src.Example where

import qualified Data.Map.Strict as Map
import MixedDecisionDiagrams.Src.MDDi
import MixedDecisionDiagrams.Src.MDD
import MixedDecisionDiagrams.Src.Internal.Language


--Order 0: world with agents (B + Z)
-- friends share information, distributed knowledge

type Class = Ordinal

agentClass :: Class
agentClass = Order [0]
experienceClass :: Class
experienceClass = Order [1]
wordClass :: Class
wordClass = Order [2]

agents = Map.fromList [("alice", Order [1]),("bob", Order [2])]
colors = Map.fromList [("green", Order [1,1,1]),("yellow", Order [1,1,2]),("blue", Order [1,1,3])]
shapes = Map.fromList [("round", Order [1,2,1]),("square", Order [1,2,2]),("big", Order [1,2,3])]
feeling = Map.fromList [("friendly", Order [1,3,1]),("dangerous", Order [1,3,2]),("interesting", Order [1,3,3])]
symbols = Map.fromList [("a", Order [2,0,1]),("b", Order [1,0,2]),("c", Order [1,0,3])]

focusField = Map.fromList [("pos1", Order [3,0,1]),("pos2", Order [3,0,2]),("pos1", Order [3,0,3])]

--Order 1: B properties
-- yellow
-- green
-- blue
-- brown

-- shape class of properties
-- round
-- square
-- big
-- small

-- emotional response class of properties
-- feels friendly!
-- feels like danger!
-- feels interesting!
-- feels dull!

--2: Z in a existence realm context (mass/essence)
-- that which is it, and that which is not it.
-- when structured/ordered:
-- 1 class for each spatial/time dimension
-- where each object has a volume in that dimension
-- when unordered we can only capture relative membership
-- e.g. we get a frame of the object and its parts and its surroundings, these weels are parts of this car

--3: Z word to refer to the properties or the referentials
-- 1 for each used symbol, unlimited length, 0 for each not-used symbol.
