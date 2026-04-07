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

    let a = ddOf t_c (Var dnpd2)
        b = ddOf t_c (Var dnpd3)
        c = ddOf t_c (Var dddd2)

    putStrLn "=== a (dnpd2: Dc->Neg->Pos->Dc, var 2) ==="
    putStrLn $ "flat: " ++ show_mdd a
    drawTree3 a

    putStrLn "\n=== b (dnpd3: Dc->Neg->Pos->Dc, var 3) ==="
    putStrLn $ "flat: " ++ show_mdd b
    drawTree3 b

    putStrLn "\n=== c (dddd2: Dc->Dc->Dc->Dc, var 2) ==="
    putStrLn $ "flat: " ++ show_mdd c
    drawTree3 c

    putStrLn "\n=== b .*. c  (dnpd3 AND dddd2) ==="
    let bc = b .*. c
    putStrLn $ "flat: " ++ show_mdd bc
    drawTree3 bc

    putStrLn "\n=== LHS: a .+. (b .*. c)  (dnpd2 OR (dnpd3 AND dddd2)) ==="
    let lhs = a .+. bc
    putStrLn $ "flat: " ++ show_mdd lhs
    drawTree3 lhs

    putStrLn "\n=== a .+. b  (dnpd2 OR dnpd3) ==="
    let ab = a .+. b
    putStrLn $ "flat: " ++ show_mdd ab
    drawTree3 ab

    putStrLn "\n=== a .+. c  (dnpd2 OR dddd2) ==="
    let ac = a .+. c
    putStrLn $ "flat: " ++ show_mdd ac
    drawTree3 ac

    putStrLn "\n=== RHS: (a .+. b) .*. (a .+. c) ==="
    let rhs = ab .*. ac
    putStrLn $ "flat: " ++ show_mdd rhs
    drawTree3 rhs

    putStrLn "\n=== Distributivity: LHS == RHS ==="
    putStrLn $ "LHS == RHS: " ++ show (lhs == rhs)
    putStrLn $ "LHS flat: " ++ show_mdd lhs
    putStrLn $ "RHS flat: " ++ show_mdd rhs
