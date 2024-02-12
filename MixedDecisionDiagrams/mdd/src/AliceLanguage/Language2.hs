module AliceLanguage.Language2 where
import MDDi
import Prelude hiding (Word)

newtype Sentence = S [Word]
newtype Word = W String

-- add functor for lifting DD functions to functions over words.

names :: [String]
names = ["Blueball, Redball, Bobball, Alice, Bob, Mom1, Dad1, daniel"]

-- and :: Sentence -> Sentence -> Sentence
-- and a b = a .*. b

-- or :: Sentence -> Sentence -> Sentence
-- or a b = a .+. b
