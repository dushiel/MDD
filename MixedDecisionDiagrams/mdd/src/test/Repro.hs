{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
module Main where

import MDD.Extra.Interface
import MDD.Extra.Draw (show_mdd, drawTree3)
import MDD.Test.Fixtures
import SMCDEL.Symbolic.Bool (ddOf, Form(..))
import System.IO (hSetEncoding, stdout, stderr, utf8)

main :: IO ()
main = do
    hSetEncoding stdout utf8
    hSetEncoding stderr utf8

    let a = ddOf t_c (Var nn1)
        b = ddOf t_c (Var n_n1)
        c = ddOf t_c (Var n_n2)

    putStrLn "=== a (nn1) ==="
    drawTree3 a

    putStrLn "\n=== b (n_n1) ==="
    drawTree3 b

    putStrLn "\n=== c (n_n2) ==="
    drawTree3 c

    putStrLn "\n=== a .*. b ==="
    let ab = a .*. b
    drawTree3 ab

    putStrLn "\n=== LHS: (a .*. b) .*. c ==="
    let lhs = ab .*. c
    drawTree3 lhs

    putStrLn "\n=== b .*. c ==="
    let bc = b .*. c
    drawTree3 bc

    putStrLn "\n=== RHS: a .*. (b .*. c) ==="
    let rhs = a .*. bc
    drawTree3 rhs

    putStrLn "\n=== LHS == RHS ==="
    putStrLn $ show (lhs == rhs)
