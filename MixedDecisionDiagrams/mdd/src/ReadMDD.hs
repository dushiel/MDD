module ReadMDD where

-- import MixedDecisionDiagrams.Src.Internal.Lex
-- import MixedDecisionDiagrams.Src.Internal.Parse
import Internal.Language

main :: IO ()
main = do
  (input,options) <- getInputAndSettings
  case parse $ alexScanTokens input of
    Left (lin,col) -> error ("Parse error in line " ++ show lin ++ ", column " ++ show col)
    Right ci@(Query form jobs) ->  do
        let myMDD = boolMddOf form
        mapM_ (doJob outHandle myMDD) jobs
        putStrLn "\nDoei!"