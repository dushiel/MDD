{-# LANGUAGE AllowAmbiguousTypes, TypeApplications, RankNTypes, ScopedTypeVariables, KindSignatures #-}
{-# LANGUAGE DataKinds #-}

module Main where

import Data.Kind (Type)

data One
data Two

-- Example 1

class Context x where
  doThing :: Int -> Int

instance Context One where
  doThing = (+1)

instance Context Two where
  doThing = (+2)

mainOld :: IO ()
mainOld = do
  let x = 2
  let a = doThing @One x
  let b = doThing @Two x
  print (a + b)

-- Example 2

data FType = Dc | Neg1 | Neg0 | Pos1 | Pos0

class ComplicatedContext x where
  doIt :: Int -> Int
  doWith :: (forall (a :: FType). ComplicatedContext a => Int -> Int) -> Int -> [Int]

instance ComplicatedContext Dc where
  doIt = (+1)
  doWith f x = [f @Dc x]

instance ComplicatedContext Neg1 where
  doIt = (+2)
  doWith f x = [f @Neg1 x, f @Neg1 x]

thrice :: forall a . ComplicatedContext a => Int -> Int
thrice = doIt @a . doIt @a . doIt @a

main :: IO ()
main = do
  let x = 2
  putStrLn "\nOne examples:"
  print $ thrice @Dc x -- 5
  print $ doWith @Dc (thrice @Dc) x -- [5]
  putStrLn "\nTwo examples:"
