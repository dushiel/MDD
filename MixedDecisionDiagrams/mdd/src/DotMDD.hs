{-# LANGUAGE OverloadedStrings #-}
module DotMDD where
import Data.GraphViz
import Data.Text.Lazy (pack, Text)
import Data.Text.Lazy.IO (putStrLn)

data Dd = Node Int Dd Dd
        | Leaf Bool
        deriving (Eq, Show)

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




generateDotGraph :: Dd -> DotGraph Text
generateDotGraph dd = DotGraph
    { strictGraph = False
    , directedGraph = True
    , graphID = Nothing
    , graphStatements = DotStmts { attrStmts = []
                                 , subGraphs = []
                                 , nodeStmts = nodes
                                 , edgeStmts = edges
                                 }
    }
  where
    (nodes, edges) = generateStatements dd

generateStatements :: Dd -> ([DotNode Text], [DotEdge Text])
generateStatements dd = go dd ([], [])
  where
    go (Node position left right) (nodes, edges) =
        let node = renderDdNode (Node position left right)
            leftEdge = renderDdEdge (Node position left right) left
            rightEdge = renderDdEdge (Node position left right) right
            (nodesLeft, edgesLeft) = go left (nodes, edges)
            (nodesRight, edgesRight) = go right (nodesLeft, edgesLeft)
        in (node : nodesRight, leftEdge : rightEdge : edgesRight)

    go (Leaf b) acc = (renderDdNode (Leaf b) : fst acc, snd acc)

    go (EndInfNode child) acc =
        let node = renderDdNode (EndInfNode child)
            edge = renderDdEdge (EndInfNode child) child
            (nodesChild, edgesChild) = go child acc
        in (node : nodesChild, edge : edgesChild)

    go (InfNodes position n1 n2 n3 n4 n5) acc =
        let node = renderDdNode (InfNodes position n1 n2 n3 n4 n5)
            edge1 = renderDdEdge (InfNodes position n1 n2 n3 n4 n5) n1
            edge2 = renderDdEdge (InfNodes position n1 n2 n3 n4 n5) n2
            edge3 = renderDdEdge (InfNodes position n1 n2 n3 n4 n5) n3
            edge4 = renderDdEdge (InfNodes position n1 n2 n3 n4 n5) n4
            edge5 = renderDdEdge (InfNodes position n1 n2 n3 n4 n5) n5
            (nodesN1, edgesN1) = go n1 acc
            (nodesN2, edgesN2) = go n2 (nodesN1, edgesN1)
            (nodesN3, edgesN3) = go n3 (nodesN2, edgesN2)
            (nodesN4, edgesN4) = go n4 (nodesN3, edgesN3)
            (nodesN5, edgesN5) = go n5 (nodesN4, edgesN4)
        in (node : nodesN5, edge1 : edge2 : edge3 : edge4 : edge5 : edgesN5)

    -- Add additional cases as needed

-- Main function to generate and display the Dot graph
main :: IO ()
main = do
    let myDd = Node 1 (Leaf True) (Node 2 (Leaf False) (Leaf True))
    let dotGraph = generateDotGraph myDd
    Data.Text.Lazy.IO.putStrLn $ printDotGraph dotGraph