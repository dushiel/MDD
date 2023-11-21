{-# LANGUAGE OverloadedStrings #-}
module DotMDD where
import Data.GraphViz
import Data.GraphViz.Attributes.Complete
import Data.GraphViz.Types
import Data.GraphViz.Types.Canonical
import Data.Text.Lazy (pack, Text)
import Data.Text.Lazy.IO (putStrLn)

data Dd = Node Int Dd Dd
        | InfNodes Int Dd Dd Dd Dd Dd
        | EndInfNode Dd
        | Leaf Bool
        deriving (Eq)

data Inf = Dc | Neg1 | Neg0 | Pos1 | Pos0
        deriving (Eq, Show)

-- Helper function to render Dd nodes as Dot nodes
renderDdNode :: Dd -> DotNode Text
renderDdNode (Node position _ _) =
    DotNode (pack $ show position) [shape BoxShape]
renderDdNode (InfNodes position _ _ _ _ _) =
    DotNode (pack $ show position) [shape BoxShape]
renderDdNode (EndInfNode _) =
    DotNode (pack "<>") [shape BoxShape]
renderDdNode (Leaf b) =
    DotNode (pack $ show b) [shape BoxShape]

-- Helper function to render Dd edges as Dot edges
renderDdEdge :: Dd -> Dd -> DotEdge Text
renderDdEdge from to = DotEdge (pack $ show from) (pack $ show to) []

-- Function to generate the Dot graph from a Dd instance
generateDotGraph :: Dd -> DotGraph Text
generateDotGraph dd =
    DotGraph { strictGraph = False
             , directedGraph = True
             , graphID = Nothing
             , graphStatements =
                [ DotStmtNode $ renderDdNode dd
                , DotStmtEdge $ renderDdEdge dd dd
                ]
             }

-- Main function to generate and display the Dot graph
main :: IO ()
main = do
    let myDd = Node 1 (Leaf True) (Node 2 (Leaf False) (Leaf True))
    let dotGraph = generateDotGraph myDd
    Data.Text.Lazy.IO.putStrLn $ printDotGraph dotGraph