{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# TypeApplications #-}
module Lib where

data Inf = Neg0 | Neg1

-- class F a where
--     foo :: Int -> (Int -> Int) -> Int
--     bar :: Int -> Int

-- instance F Neg1 where
--      bar a = a + 3
--      foo a f = f a


-- x = foo @Neg1 2 (bar @Neg1)