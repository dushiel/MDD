{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Use newtype instead of data" #-}
import MDDi
import MDD
import DrawMDD
import Prelude hiding (Word)
import qualified Data.Map as Map
import Internal.Language

newtype Sentence = Sentence_statement (Name, Statement, Consequence)
data Word = Word_name Name | Word_combinator Combinator | Word_statement Statement | Word_property Consequence
newtype Statement = Statement_is String
newtype Name = Name' String
data Property = Property' String

data Object = Object_name Name | Object_set_result_left Name Combinator Object | Object_set_result_right Object Combinator Name
data Consequence = Consequence_name Property | Consequence_set_result_left Property Combinator Consequence | Consequence_set_result_right Consequence Combinator Property
data Combinator = Combinator_and And | Combinator_or Or
newtype And = And' String -- add functor for lifting DD functions to functions over Strings.
newtype Or = Or' String



names_alice_currently_knows :: [Name]
names_alice_currently_knows = ["Blueball, Redball, Bobball, Alice, Bob, Mom1, Dad1, daniel"]

properties_alice_currently_knows :: [Name]
properties_alice_currently_knows = ["tasty", "blue", "small", "big"]


-- map decision diagram variables to meaningful concepts
newtype DdM = DdM' (Dd, Map.Map Ordinal Sentence)

-- one of names lifted to Dd land,
-- together with information linking its domain to its type (names),
-- and its variables to its instances (name)
name :: DdM
name = undefined

object :: DdM
object = undefined

property :: DdM
property = undefined

is :: DdM -> DdM -> DdM
is = undefined

and :: DdM -> DdM -> DdM
and a b = a .^. b

or :: Sentence -> Sentence -> Sentence
or a b = a .+. b

-- generate function: generate a list of all possible combinations in some order. try to make this order seem random, and an input argument


main :: IO ()
main =  do
    seed randomIO :: IO Float
    run seed


