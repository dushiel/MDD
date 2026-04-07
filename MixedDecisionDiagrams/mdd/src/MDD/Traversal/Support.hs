{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE AllowAmbiguousTypes #-}   -- Required to allow methods where the class type variable 'a' is not in the signature
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE InstanceSigs #-}

module MDD.Traversal.Support where

import MDD.Types
import MDD.Traversal.Context
import MDD.Traversal.Stack
import MDD.Extra.Draw (debug_dc_traverse, debug_dc_traverse_unary, debug_naiveAbsorb_open, debug_naiveAbsorb_close, myTrace, show_node)

-- *| Shared code for traversal functions (from Unary and Binary).

-- | Elimination and Inference rule typeclass (DdF3).
-- |
-- | This typeclass defines the inference and elimination rules for the three inference types: Dc, Neg, Pos
-- | Each instance implements:
-- |   - infer(Inf)NodeA/infer(Inf)NodeB: Create inferred nodes when one argument is missing a variable at the lowest position of the two
-- |   - applyElimRule: Apply the elimination rule to remove redundant nodes
-- |   - catchup: Synchronize dc_stack traversal when main traversal skips variables
class DdF3 (a :: Inf) where
    inferNodeA :: (BiOpContext -> String -> Node -> Node -> (BiOpContext, Node))
               -> BiOpContext -> String -> Node -> Node -> (BiOpContext, Dd)
    inferNodeB :: (BiOpContext -> String -> Node -> Node -> (BiOpContext, Node))
               -> BiOpContext -> String -> Node -> Node -> (BiOpContext, Dd)

    applyElimRule :: (HasNodeLookup c) => c -> Dd -> (c, Node)
    inferNode :: (HasNodeLookup c) => c -> Int -> Node -> (c, Node)
    inferClassNode :: (HasNodeLookup c) => c -> Int -> Node -> (c, Node)
    catchup :: (HasNodeLookup c) => c -> Node -> Int -> Node
    to_str :: String
    to_inf :: Inf
    isNeg :: Bool
    isPos :: Bool
    isDc :: Bool

    -- | Infer a ClassNode for the A-side.
    -- For compound modes, projects A's inference type (e.g. NegDc -> @Neg).
    inferClassNodeForA :: (HasNodeLookup c) => c -> Int -> Node -> (c, Node)
    -- | Infer a ClassNode for the B-side.
    -- For compound modes, projects B's inference type (e.g. NegDc -> @Dc).
    inferClassNodeForB :: (HasNodeLookup c) => c -> Int -> Node -> (c, Node)

    -- | In leaf_cases, when A is Unknown: True = return A as-is; False = pop dcA and recurse.
    -- Compound modes where A is already in Dc role return True (A was already popped).
    aUnknownReturn :: Bool
    -- | In leaf_cases, when B is Unknown: True = return B as-is; False = pop dcB and recurse.
    -- Compound modes where B is already in Dc role return True.
    bUnknownReturn :: Bool

    -- | Which Inf mode to recurse with after popping dcA for an Unknown on A.
    dcAMode :: Inf
    -- | Which Inf mode to recurse with after popping dcB for an Unknown on B.
    dcBMode :: Inf

    -- | True = use pop_dc_stack ... True (dropLevel) when resolving Unknown A.
    popADropLevel :: Bool
    -- | True = use pop_dc_stack ... True (dropLevel) when resolving Unknown B.
    popBDropLevel :: Bool

    -- | Inf to push on level stack and use for the neg-branch traversal inside applyClass'.
    -- Compound modes carry the asymmetry into the nested class (e.g. NegDc -> NegDc).
    negClassInf :: Inf
    -- | Inf to push on level stack and use for the pos-branch traversal inside applyClass'.
    posClassInf :: Inf

applyElimRule' :: forall a. (DdF3 a) => (UnOpContext, Dd) -> (UnOpContext, Node)
applyElimRule' (c, d) = applyElimRule @a c d





-- * Naive Absorb Implementation
-- Naive absorb minimizes the pos / neg branches of a class with respect to the class' resulting dc branch - Or a dc branch with respect to the outer dc branch.
-- simultaneous traversal for 2 branches. Recurses depth-first; at EndClassNode boundaries of the local class, an equality check determines absorption.
-- When entering a nested class, a non-absorbing traversal is used until returning to the original class level.
-- The dcR stack is kept up-to-date during traversal for subsituting any Unknowns encountered on the absorbingBranch.


naiveAbsorb :: forall a. (DdF3 a) => UnOpContext -> Node -> Node -> (UnOpContext, Node)
naiveAbsorb c absingB branch =
    let (c', r) = myTrace (debug_naiveAbsorb_open ("absorb " ++ to_str @a) c absingB branch) $
                  naiveAbsorb' @a c absingB branch
    in myTrace (debug_naiveAbsorb_close ("absorb " ++ to_str @a) c' absingB branch r) (c', r)

naiveAbsorb' :: forall a. (DdF3 a) => UnOpContext -> Node -> Node -> (UnOpContext, Node)

-- Already absorbed (Unknown in branch means it was previously set to dc)
naiveAbsorb' c _absingB branch@(_, Unknown) = (c, branch)

-- EndClassNode vs EndClassNode: local class boundary — check equality - otherwise no absorb will happen
naiveAbsorb' c absingB@(_, EndClassNode dcChild) branch@(_, EndClassNode branchChild)
    | branch == absingB = (c, ((0,0), Unknown))
    | otherwise = (c, branch)
-- Leaf vs Leaf: direct comparison at the (implicit) class boundary
naiveAbsorb' c absingB@(_, Leaf _) branch@(_, Leaf _)
    | branch == absingB = (c, ((0,0), Unknown))
    | otherwise     = (c, branch)

-- absorbingBranch is Unknown: resolve it from the outer dcR stack
naiveAbsorb' c (_, Unknown) branch = -- todo double check the logic here
    case un_dc_stack c of
        (_ : outer : rest) -> naiveAbsorb @a (c { un_dc_stack = outer : rest }) outer branch
        _                  -> (c, branch)

-- Node one, Leaf in other: the Leaf implicitly has the Node's variable resolved through the inference rule. Infer to reach the Leaf's level.
naiveAbsorb' c absingB@(_, Node _ _ _) branch@(_, Leaf _) = travNodeAbs @a c absingB branch (naiveAbsorb @a)
naiveAbsorb' c absingB@(_, Leaf _) branch@(_, Node{}) =
    -- because absorbingBranch has dc rule we do not have to explicitly infer nodes for it and can traverse on tested branch node directly
    travNodeBranch @a c absingB branch (naiveAbsorb @a)

-- Leaf implicitly has EndClassNodes for all outer classes
naiveAbsorb' c absingB@(_, EndClassNode dcChild) branch@(_, Leaf _) =
    let (c', branchWrapped) = insert c (EndClassNode (fst branch))
    in naiveAbsorb @a c' absingB branchWrapped
naiveAbsorb' c absingB@(_, Leaf _) branch@(_, EndClassNode branchChild) =
    let (c', absingBWrapped) = insert c (EndClassNode (fst absingB))
    in naiveAbsorb @a c' absingBWrapped branch
naiveAbsorb' c absingB@(_, Leaf _) branch@(_, ClassNode pos d p n) =
    inferClassAbsing c pos absingB branch (naiveAbsorb @a)
naiveAbsorb' c absingB@(_, ClassNode dcPos _ _ _) branch@(_, Leaf _) =
    inferClassBranch @a c dcPos absingB branch (naiveAbsorb @a)


-- === Node vs Node ===: simultaneous traversal of matching variable positions
naiveAbsorb' c absingB@(absingBId, Node dcPos dcP dcN) branch@(branchId, Node pos p n)
    | branch == absingB = (c, ((0,0), Unknown))
    | dcPos == pos = travNodeBoth @a c absingB branch (naiveAbsorb @a)
    | dcPos < pos = travNodeAbs @a c absingB branch (naiveAbsorb @a)
    | dcPos > pos = travNodeBranch @a c absingB branch (naiveAbsorb @a)

-- === Node vs EndClassNode ===
naiveAbsorb' c absingB@(absingBId, Node dcPos dcP dcN) branch@(_, EndClassNode _) = travNodeAbs @a c absingB branch (naiveAbsorb @a)
-- because absorbingBranch has dc rule we do not have to explicitly infer nodes for it
naiveAbsorb' c absingB@(_, EndClassNode _) branch@(_, Node{}) = travNodeBranch @a c absingB branch (naiveAbsorb @a)

-- === ClassNode in branch and absorbingBranch ===
-- Switch to non-absorbing simultaneous traversal (with elimination rules)
-- until the same class level is reached again, then absorption continues.
--
naiveAbsorb' c absingB@(_, ClassNode dcPos _ _ _) branch@(_, ClassNode pos _ _ _)
    | branch == absingB = (c, ((0,0), Unknown))
    | dcPos == pos = travClassBoth @a c absingB branch
            (naiveTraverse @Dc 1) (naiveTraverse @Pos 1) (naiveTraverse @Neg 1)
    | dcPos < pos = inferClassBranch @a c dcPos absingB branch (naiveAbsorb @a)
    | dcPos > pos = inferClassAbsing c pos absingB branch (naiveAbsorb @a)

naiveAbsorb' c absingB@(_, ClassNode dcPos _ _ _) branch@(_, EndClassNode _) =
    inferClassBranch @a c dcPos absingB branch (naiveAbsorb @a)
naiveAbsorb' c absingB@(_, EndClassNode _) branch@(_, ClassNode pos _ _ _) =
    inferClassAbsing c pos absingB branch (naiveAbsorb @a)

-- === Node in absorbingBranch, ClassNode in branch ===
naiveAbsorb' _ (_, Node _ _ _) (_, ClassNode _ _ _ _) = error "should not happen: node vs class node in absorb"
naiveAbsorb' _ (_, ClassNode _ _ _ _) (_, Node _ _ _) =
    error "naiveAbsorb: ClassNode absingB vs Node branch should not happen"


-- | Simultaneous traversal without absorption for nested classes.
-- Walks absorbingBranch and branch in lockstep, creating new nodes with elimination rules applied, but never replacing nodes with Unknown.
-- The Int parameter tracks nesting depth of Class(Nodes)' relative to where naiveAbsorb handed off.
-- At depth 0, the next EndClassNode exit returns to the absorbing class level

naiveTraverse :: forall a. (DdF3 a) => Int -> UnOpContext -> Node -> Node -> (UnOpContext, Node)
naiveTraverse depth c absingB branch =
    let (c', r) = myTrace (debug_naiveAbsorb_open ("traverse " ++ to_str @a ++ " depth=" ++ show depth) c absingB branch) $
                  naiveTraverse' @a depth c absingB branch
    in myTrace (debug_naiveAbsorb_close ("traverse " ++ to_str @a ++ " depth=" ++ show depth) c' absingB branch r) (c', r)

naiveTraverse' :: forall a. (DdF3 a) => Int -> UnOpContext -> Node -> Node -> (UnOpContext, Node)

naiveTraverse' _ c _ branch@(_, Unknown) = (c, branch)
naiveTraverse' depth c (_, Unknown) branch = -- todo double check the logic here
    case un_dc_stack c of
        (_ : outer : rest) -> naiveTraverse @a depth (c { un_dc_stack = outer : rest }) outer branch
        _                  -> (c, branch)

naiveTraverse' depth c absingB@(absingBId, EndClassNode dcChild) branch@(_, Leaf _) =
    let (c_end, inf, c_) = exitClass c absingBId
        go f = f c_ (getNode c_end dcChild) branch
    in case inf of
        Dc  -> go $ if depth == 1 then naiveAbsorb @Dc  else naiveTraverse @Dc  (depth - 1)
        Neg -> go $ if depth == 1 then naiveAbsorb @Neg else naiveTraverse @Neg (depth - 1)
        Pos -> go $ if depth == 1 then naiveAbsorb @Pos else naiveTraverse @Pos (depth - 1)
naiveTraverse' depth c absingB@(_, Node _ _ _) branch@(_, Leaf _) =
    travNodeAbs @a c absingB branch (naiveTraverse @a depth)

-- === EndClassNode: exiting a class ===
-- depth == 1: about to go back at the absorbing class level — hand to naiveAbsorb
-- depth > 1: still inside a deeper nested class — stay in naiveTraverse
naiveTraverse' depth c absingB@(absingBId, EndClassNode dcChild) branch@(_, EndClassNode branchChild) =
    let (c_end, inf, c_) = exitClass c absingBId
        go f = wrapEndClass @a (f c_ (getNode c_end dcChild) (getNode c_end branchChild))
    in case inf of
        Dc  -> go $ if depth == 1 then naiveAbsorb @Dc  else naiveTraverse @Dc  (depth - 1)
        Neg -> go $ if depth == 1 then naiveAbsorb @Neg else naiveTraverse @Neg (depth - 1)
        Pos -> go $ if depth == 1 then naiveAbsorb @Pos else naiveTraverse @Pos (depth - 1)
naiveTraverse' depth c absingB@(absingBId, Leaf _) branch@(_, EndClassNode branchChild) =
    let (c_end, inf, c_) = exitClass c absingBId
        go f = wrapEndClass @a (f c_ absingB (getNode c_end branchChild))
    in case inf of
        Dc  -> go $ if depth == 1 then naiveAbsorb @Dc  else naiveTraverse @Dc  (depth - 1)
        Neg -> go $ if depth == 1 then naiveAbsorb @Neg else naiveTraverse @Neg (depth - 1)
        Pos -> go $ if depth == 1 then naiveAbsorb @Pos else naiveTraverse @Pos (depth - 1)
naiveTraverse' depth c absingB@(absingBId, Leaf _) branch@(_, Leaf _) =
    let (_, inf, c_) = exitClass c absingBId
        go f = f c_ absingB branch
    in case inf of
        Dc  -> go $ if depth == 1 then naiveAbsorb @Dc  else naiveTraverse @Dc  (depth - 1)
        Neg -> go $ if depth == 1 then naiveAbsorb @Neg else naiveTraverse @Neg (depth - 1)
        Pos -> go $ if depth == 1 then naiveAbsorb @Pos else naiveTraverse @Pos (depth - 1)

naiveTraverse' depth c absingB@(_, Node _ _ _) branch@(_, EndClassNode _) =
    travNodeAbs @a c absingB branch (naiveTraverse @a depth)
naiveTraverse' depth c absingB@(_, EndClassNode _) branch@(_, Node{}) =
    travNodeBranch @a c absingB branch (naiveTraverse @a depth)

-- === Node vs Node: simultaneous traversal (same class level) ===
naiveTraverse' depth c absingB@(_, Node dcPos _ _) branch@(_, Node pos _ _)
    | dcPos == pos = travNodeBoth @a c absingB branch (naiveTraverse @a depth)
    | dcPos < pos  = travNodeAbs @a c absingB branch (naiveTraverse @a depth)
    | otherwise    = travNodeBranch @a c absingB branch (naiveTraverse @a depth)

naiveTraverse' depth c absingB@(_, Leaf _) branch@(_, Node{}) =
    travNodeBranch @a c absingB branch (naiveTraverse @a depth)

naiveTraverse' depth c absingB@(_, ClassNode dcPos _ _ _) branch@(_, Leaf _) =
    inferClassBranch @a c dcPos absingB branch (naiveTraverse @a depth)

-- === ClassNode: entering a deeper nested class (depth + 1) ===
naiveTraverse' depth c absingB@(_, ClassNode dcPos _ _ _) branch@(_, ClassNode pos _ _ _)
    | dcPos == pos =
        travClassBoth @a c absingB branch
            (naiveTraverse @Dc (depth + 1)) (naiveTraverse @Pos (depth + 1)) (naiveTraverse @Neg (depth + 1))
    | dcPos < pos  = inferClassBranch @a c dcPos absingB branch (naiveTraverse @a depth)
    | otherwise    = inferClassAbsing c pos absingB branch (naiveTraverse @a depth)

naiveTraverse' _ _ (_, Node _ _ _) (_, ClassNode _ _ _ _) = error "should not happen: node vs class node in naiveTraverse"
naiveTraverse' depth c absingB@(_, EndClassNode _) branch@(_, ClassNode pos _ _ _) =
    inferClassAbsing c pos absingB branch (naiveTraverse @a depth)
naiveTraverse' depth c absingB@(_, Leaf _) branch@(_, ClassNode pos _ _ _) =
    inferClassAbsing c pos absingB branch (naiveTraverse @a depth)
naiveTraverse' _ _ (_, ClassNode _ _ _ _) (_, Node _ _ _) = error "should not happen: class node vs node in naiveTraverse"
naiveTraverse' depth c absingB@(_, ClassNode dcPos _ _ _) branch@(_, EndClassNode _) =
    inferClassBranch @a c dcPos absingB branch (naiveTraverse @a depth)


instance DdF3 Dc where
    inferNodeA f c s (a_id, _) (b_id, Node positionB _ _) =
        let (c', r) = insert c (Node positionB a_id a_id)
            (c'', (r_node_id, _)) = f c' s r (getNode c' b_id)
        in (c'', getDd c'' r_node_id)

    inferNodeB f c s (a_id, Node positionA _ _) (b_id, _) =
        let (c', r) = insert c (Node positionA b_id b_id)
            (c'', (r_node_id, _)) = f c' s (getNode c' a_id) r
        in (c'', getDd c'' r_node_id)


    applyElimRule c d@(Node _ p n) = if p == n then (c, getNode c p) else insert c d
    applyElimRule c (ClassNode _ (1,0) (0,0) (0,0)) = (c, ((1,0), Leaf True))
    applyElimRule c (ClassNode _ (2,0) (0,0) (0,0)) = (c, ((2,0), Leaf False))
    applyElimRule c (ClassNode _ (0,0) (0,0) (0,0)) = (c, ((0,0), Unknown))
    applyElimRule c d@(ClassNode _ consq (0,0) (0,0)) = case getDd c consq of
        EndClassNode d' -> (c, getNode c d')
        _ -> insert c d
    applyElimRule c d@(EndClassNode r) = case getDd c r of
        Leaf _ -> (c, getNode c r)
        Unknown -> (c, getNode c r)
        _ -> insert c d
    applyElimRule c d = insert c d

    inferNode :: HasNodeLookup c => c -> Int -> Node -> (c, Node)
    inferNode c position (n_id, _) = insert c (Node position n_id n_id)
    inferClassNode c position (n_id, _) = insert c $ ClassNode position n_id (0,0) (0,0)
    catchup _ (_, ClassNode _ _ _ _) _ = error "ClassNode catchup not yet implemented"
    catchup _ n _ = n
    to_str = "Dc"
    to_inf = Dc
    isNeg = False
    isPos = False
    isDc  = True
    inferClassNodeForA = inferClassNode @Dc
    inferClassNodeForB = inferClassNode @Dc
    aUnknownReturn = False
    bUnknownReturn = False
    dcAMode = DcDcA
    dcBMode = DcDcB
    popADropLevel = False
    popBDropLevel = False
    negClassInf = Neg
    posClassInf = Pos

-- | Instance for Pos (Positive literal) inference/elimination rule.
instance DdF3 Pos where
    -- | Pos rule: Create a Node with pos branch = a_id, neg branch = (0,0) (Unknown).
    inferNodeA f c s (a_id, _) (b_id, Node positionB _ _) =
        let (c', r) = insert c (Node positionB a_id (0,0))
            (c'', (r_node_id, _)) = f c' s r (getNode c' b_id)
        in (c'', getDd c'' r_node_id)

    inferNodeB f c s (a_id, Node positionA _ _) (b_id, _) =
        let (c', r) = insert c (Node positionA b_id (0,0))
            (c'', (r_node_id, _)) = f c' s (getNode c' a_id) r
        in (c'', getDd c'' r_node_id)

    -- | Pos elimination rule: Eliminate nodes where neg branch is Unknown (only pos is valid).
    applyElimRule c (Node _ posC (0, 0)) = (c, getNode c posC)
    applyElimRule c (ClassNode _ (0,0) (1,0) (0,0)) = (c, ((1,0), Leaf True))
    applyElimRule c (ClassNode _ (0,0) (2,0) (0,0)) = (c, ((2,0), Leaf False))
    applyElimRule c (ClassNode _ (0,0) (0,0) (0,0)) = (c, ((0,0), Unknown))
    applyElimRule c d@(ClassNode _ (0,0) consq (0,0)) = case getDd c consq of
        EndClassNode d' -> (c, getNode c d')
        _ -> insert c d
    applyElimRule c d@(EndClassNode r) = case getDd c r of
        Leaf _ -> (c, getNode c r)
        Unknown -> (c, getNode c r)
        _ -> insert c d
    applyElimRule c d = insert c d


    -- pos node inference
    inferNode c position (n_id, _) = insert c (Node position n_id (0,0))
    -- pos class node inference
    inferClassNode c position (n_id, _) = insert c $ ClassNode position (0,0) n_id (0,0)

    catchup c n@(_, Node positionA pos_child _) idx
        | idx == -1       = catchup @Pos c (getNode c pos_child) idx
        | idx > positionA = catchup @Pos c (getNode c pos_child) idx
        | otherwise = n
    catchup _ (_, ClassNode _ _ _ _) _ = error "ClassNode catchup not yet implemented"
    catchup _ n _ = n
    to_str = "Pos"
    to_inf = Pos
    isNeg = False
    isPos = True
    isDc  = False
    inferClassNodeForA = inferClassNode @Pos
    inferClassNodeForB = inferClassNode @Pos
    aUnknownReturn = False
    bUnknownReturn = False
    dcAMode = DcPos
    dcBMode = PosDc
    popADropLevel = False
    popBDropLevel = False
    negClassInf = Neg
    posClassInf = Pos

-- | Instance for Neg (Negative literal) inference/elimination rule.
instance DdF3 Neg where
    -- | Neg rule: Create a Node with pos branch = (0,0) (Unknown), neg branch = a_id.
    inferNodeA f c s (a_id, _) (b_id, Node positionB _ _) =
        let (c', r) = insert c (Node positionB (0,0) a_id)  -- pos=Unknown, neg=a_id
            (c'', (r_node_id, _)) = f c' s r (getNode c' b_id)
        in (c'', getDd c'' r_node_id)
    inferNodeB f c s (a_id, Node positionA _ _) (b_id, _) =
        let (c', r) = insert c (Node positionA (0,0) b_id)  -- pos=Unknown, neg=b_id
            (c'', (r_node_id, _)) = f c' s (getNode c' a_id) r
        in (c'', getDd c'' r_node_id)
    applyElimRule c (Node _ (0, 0) negC) = (c, getNode c negC)
    applyElimRule c (ClassNode _ (0,0) (0,0) (1,0)) = (c, ((1,0), Leaf True))
    applyElimRule c (ClassNode _ (0,0) (0,0) (2,0)) = (c, ((2,0), Leaf False))
    applyElimRule c (ClassNode _ (0,0) (0,0) (0,0)) = (c, ((0,0), Unknown))
    applyElimRule c d@(ClassNode _ (0,0) (0,0) consq) = case getDd c consq of
        EndClassNode d' -> (c, getNode c d')
        _ -> insert c d
    applyElimRule c d@(EndClassNode r) = case getDd c r of
        Leaf _ -> (c, getNode c r)
        Unknown -> (c, getNode c r)
        _ -> insert c d
    applyElimRule c d = insert c d


    inferNode c position (n_id, _) = insert c (Node position (0,0) n_id)
    inferClassNode c position (n_id, _) = insert c $ ClassNode position (0,0) (0,0) n_id

    catchup c n@(_, Node positionA _ neg_child) idx
        | idx == -1       = catchup @Neg c (getNode c neg_child) idx
        | idx > positionA = catchup @Neg c (getNode c neg_child) idx
        | otherwise = n
    catchup _ (_, ClassNode _ _ _ _) _ = error "ClassNode catchup not yet implemented"
    catchup _ n _ = n
    to_str = "Neg"
    to_inf = Neg
    isNeg = True
    isPos = False
    isDc  = False
    inferClassNodeForA = inferClassNode @Neg
    inferClassNodeForB = inferClassNode @Neg
    aUnknownReturn = False
    bUnknownReturn = False
    dcAMode = DcNeg
    dcBMode = NegDc
    popADropLevel = False
    popBDropLevel = False
    negClassInf = Neg
    posClassInf = Pos


-- * Compound DdF3 instances (asymmetric traversal modes)
-- Each compound mode XY means: side A is in context X, side B is in context Y.
-- Methods delegate to the simple instances for the respective A/B projections.

-- | NegDc: A=Neg, B=Dc (replaces applyDcB' @Neg)
instance DdF3 NegDc where
    inferNodeA f c s a b = inferNodeA @Neg f c s a b
    inferNodeB f c s a b = inferNodeB @Dc  f c s a b
    applyElimRule         = applyElimRule @Neg
    inferNode             = inferNode     @Neg
    inferClassNode        = inferClassNode @Neg
    catchup               = catchup @Neg
    to_str = "NegDc"; to_inf = NegDc; isNeg = True; isPos = False; isDc = False
    inferClassNodeForA    = inferClassNode @Neg
    inferClassNodeForB    = inferClassNode @Dc
    aUnknownReturn = True;  bUnknownReturn = False
    dcAMode = NegDc;        dcBMode = NegDc
    popADropLevel = True;   popBDropLevel = True
    negClassInf = NegDc;    posClassInf = PosDc

-- | DcNeg: A=Dc, B=Neg (replaces applyDcA' @Neg)
instance DdF3 DcNeg where
    inferNodeA f c s a b = inferNodeA @Dc  f c s a b
    inferNodeB f c s a b = inferNodeB @Neg f c s a b
    applyElimRule         = applyElimRule @Neg
    inferNode             = inferNode     @Dc
    inferClassNode        = inferClassNode @Dc
    catchup               = catchup @Neg
    to_str = "DcNeg"; to_inf = DcNeg; isNeg = True; isPos = False; isDc = False
    inferClassNodeForA    = inferClassNode @Dc
    inferClassNodeForB    = inferClassNode @Neg
    aUnknownReturn = False; bUnknownReturn = True
    dcAMode = DcNeg;        dcBMode = DcNeg
    popADropLevel = True;   popBDropLevel = True
    negClassInf = DcNeg;    posClassInf = DcPos

-- | PosDc: A=Pos, B=Dc (replaces applyDcB' @Pos)
instance DdF3 PosDc where
    inferNodeA f c s a b = inferNodeA @Pos f c s a b
    inferNodeB f c s a b = inferNodeB @Dc  f c s a b
    applyElimRule         = applyElimRule @Pos
    inferNode             = inferNode     @Pos
    inferClassNode        = inferClassNode @Pos
    catchup               = catchup @Pos
    to_str = "PosDc"; to_inf = PosDc; isNeg = False; isPos = True; isDc = False
    inferClassNodeForA    = inferClassNode @Pos
    inferClassNodeForB    = inferClassNode @Dc
    aUnknownReturn = True;  bUnknownReturn = False
    dcAMode = PosDc;        dcBMode = PosDc
    popADropLevel = True;   popBDropLevel = True
    negClassInf = NegDc;    posClassInf = PosDc

-- | DcPos: A=Dc, B=Pos (replaces applyDcA' @Pos)
instance DdF3 DcPos where
    inferNodeA f c s a b = inferNodeA @Dc  f c s a b
    inferNodeB f c s a b = inferNodeB @Pos f c s a b
    applyElimRule         = applyElimRule @Pos
    inferNode             = inferNode     @Dc
    inferClassNode        = inferClassNode @Dc
    catchup               = catchup @Pos
    to_str = "DcPos"; to_inf = DcPos; isNeg = False; isPos = True; isDc = False
    inferClassNodeForA    = inferClassNode @Dc
    inferClassNodeForB    = inferClassNode @Pos
    aUnknownReturn = False; bUnknownReturn = True
    dcAMode = DcPos;        dcBMode = DcPos
    popADropLevel = True;   popBDropLevel = True
    negClassInf = DcNeg;    posClassInf = DcPos

-- | DcDcA: A=Dc (sourced), B=Dc (replaces applyDcA' @Dc)
instance DdF3 DcDcA where
    inferNodeA f c s a b = inferNodeA @Dc f c s a b
    inferNodeB f c s a b = inferNodeB @Dc f c s a b
    applyElimRule         = applyElimRule @Dc
    inferNode             = inferNode     @Dc
    inferClassNode        = inferClassNode @Dc
    catchup               = catchup @Dc
    to_str = "DcDcA"; to_inf = DcDcA; isNeg = False; isPos = False; isDc = True
    inferClassNodeForA    = inferClassNode @Dc
    inferClassNodeForB    = inferClassNode @Dc
    aUnknownReturn = False; bUnknownReturn = True
    dcAMode = DcDcA;        dcBMode = DcDcA
    popADropLevel = True;   popBDropLevel = True
    negClassInf = Neg;      posClassInf = Pos

-- | DcDcB: A=Dc, B=Dc (sourced) (replaces applyDcB' @Dc)
instance DdF3 DcDcB where
    inferNodeA f c s a b = inferNodeA @Dc f c s a b
    inferNodeB f c s a b = inferNodeB @Dc f c s a b
    applyElimRule         = applyElimRule @Dc
    inferNode             = inferNode     @Dc
    inferClassNode        = inferClassNode @Dc
    catchup               = catchup @Dc
    to_str = "DcDcB"; to_inf = DcDcB; isNeg = False; isPos = False; isDc = True
    inferClassNodeForA    = inferClassNode @Dc
    inferClassNodeForB    = inferClassNode @Dc
    aUnknownReturn = True;  bUnknownReturn = False
    dcAMode = DcDcB;        dcBMode = DcDcB
    popADropLevel = True;   popBDropLevel = True
    negClassInf = Neg;      posClassInf = Pos

-- | Synchronize a single dc_stack element with the main traversal.
traverse_dc_generic :: forall (a :: Inf) c. (DdF3 a, HasNodeLookup c) =>
    Move   -- ^ which branch to follow
    -> c -> Node -> Node -> Node
traverse_dc_generic s c refNode dcNode =
    let validMove = case (snd refNode, s) of
            (Node{},         MvPos) -> True
            (Node{},         MvNeg) -> True
            (ClassNode{},    MvClassDc)  -> True
            (ClassNode{},    MvClassNeg) -> True
            (ClassNode{},    MvClassPos) -> True
            (EndClassNode{}, ExitClass)  -> True
            _                             -> False
    in if not validMove
        then error $ "traverse_dc_generic: invalid move '" ++ show s ++ "' for refNode type " ++ show_node c refNode
        else case (dcNode, refNode) of
            -- Case 5: dcNode is Unknown — pass-through
            ((_, Unknown), _) -> dcNode

            -- Case 1: (Node, Node) — both are variable nodes
            ((_, Node position _ _), (_, Node idx _ _))
                | position > idx  -> dcNode
                | position == idx -> move_dc c s dcNode
                | position < idx  -> move_dc c s (catchup @a c dcNode idx)

            -- Case 3: (Node, EndClassNode) — dc is behind, catch up to terminal then move
            ((_, Node{}), (_, EndClassNode{})) ->
                move_dc c s (catchup @a c dcNode (-1))

            -- Case 4: (EndClassNode, EndClassNode) — both exiting class
            ((_, EndClassNode{}), (_, EndClassNode{})) -> move_dc c s dcNode

            -- Case 7: (ClassNode, ClassNode) — both are class nodes
            ((_, ClassNode position _ _ _), (_, ClassNode idx _ _ _))
                | position > idx  -> let (_, inferred) = inferClassNode @a c idx dcNode
                                     in move_dc c s inferred
                | position == idx -> move_dc c s dcNode
                | position < idx  -> error "traverse_dc_generic: ClassNode catchup not yet implemented"

            -- Case 8: (Leaf, EndClassNode) — dc terminated at Leaf, ref exiting class
            ((_, Leaf{}), (_, EndClassNode{})) -> dcNode

            -- Case 9: (ClassNode, EndClassNode) — dc has ClassNode, ref exiting (deferred)
            ((_, ClassNode{}), (_, EndClassNode{})) ->
                error "traverse_dc_generic: ClassNode vs EndClassNode not yet implemented"

            -- Case 10: (Leaf, Node) or (Leaf, ClassNode) — dc terminated
            ((_, Leaf{}), (_, Node{})) -> dcNode
            ((_, Leaf{}), (_, ClassNode idx _ _ _)) ->
                let (_, inferred) = inferClassNode @Dc c idx dcNode
                in move_dc c s inferred

            -- Case 11: (EndClassNode, Node) — dc at end class, ref still inside
            ((_, EndClassNode{}), (_, Node{})) -> dcNode

            -- Case 13: (EndClassNode, ClassNode) — dc at end, ref at ClassNode
            ((_, EndClassNode{}), (_, ClassNode idx _ _ _)) ->
                let (_, inferred) = inferClassNode @Dc c idx dcNode
                in move_dc c s inferred

            ((_, Node _ _ _), (_, ClassNode _ _ _ _)) -> error "node vs classnode should not happen on the same local domain"
            ((_, ClassNode _ _ _ _), (_, Node _ _ _)) -> error "classnode vs node should not happen on the same local domain"

            _ -> error $ "traverse_dc_generic unhandled case:\n (dcNode=" ++ show_node c dcNode
                      ++ ",\n  refNode=" ++ show_node c refNode ++ ")"





-- * Helper functions

class Dd1_helper (a :: Inf) where
    traverse_dc :: Move -> BiOpContext -> NodeId -> NodeId -> BiOpContext
instance (DdF3 a) => Dd1_helper a where
    -- | Synchronizes the entire dc_stack with the main traversal.
    traverse_dc s c a b = debug_dc_traverse (show s) c a b $
            let (dcAs, dcBs, dcRs) = (bin_dc_stack c)
                refA = getNode c a
                refB = getNode c b
                isLeaf (_, Leaf{}) = True
                isLeaf _           = False
                new_dcAs = if isLeaf refA then dcAs else map (traverse_dc_generic @a s c refA) dcAs
                new_dcBs = if isLeaf refB then dcBs else map (traverse_dc_generic @a s c refB) dcBs
                new_dcRs = if isLeaf refA then dcRs else map (traverse_dc_generic @a s c refA) dcRs
            in c { bin_dc_stack = (new_dcAs, new_dcBs, new_dcRs) }

absorb :: forall a. (DdF3 a) => BiOpContext -> Int -> Node -> Node -> (BiOpContext, Node)
absorb c positionA dcR branch =
    let (_, _, outerDcRs) = bin_dc_stack c
        unCtx_base = binaryToUnaryContext c
        -- Restore the correct outer inference context that might have been overwritten by pop_dcA'
        lvs = un_current_level unCtx_base
        fixed_lvs = case lvs of
            ((pos, _) : rest) -> (pos, to_inf @a) : rest
            [] -> []
        unCtx = unCtx_base { un_dc_stack = dcR : outerDcRs, un_current_level = fixed_lvs }
        (unCtx', branch') = myTrace (debug_naiveAbsorb_open ("absorb " ++ to_str @a ++ " pos=" ++ show positionA) unCtx dcR branch) $
                            let r@(uc, n) = naiveAbsorb' @a unCtx dcR branch
                            in myTrace (debug_naiveAbsorb_close ("absorb " ++ to_str @a ++ " pos=" ++ show positionA) uc dcR branch n) r
    in (unaryToBinaryContext unCtx' c, branch')


outerDcR :: [Node] -> Node
outerDcR (h : _) = h
outerDcR []      = error "requested from empty dcR stack"

-- | Absorb dcR against the outer dcR from the stack.
absorb_dc :: forall a. (DdF3 a) => BiOpContext -> Int -> Node -> (BiOpContext, Node)
absorb_dc c positionA dcR =
    let (_, _, outerDcRs) = bin_dc_stack c
    in absorb @a c positionA (outerDcR outerDcRs) dcR

absorb_unary :: forall a. (DdF3 a) => UnOpContext -> Node -> Node -> (UnOpContext, Node)
absorb_unary c dcR branch = naiveAbsorb @a c dcR branch

absorb_dc_unary :: forall a. (DdF3 a) => UnOpContext -> Node -> (UnOpContext, Node)
absorb_dc_unary c dcR = absorb_unary @a c (outerDcR (drop 1 (un_dc_stack c))) dcR

pop_level_ :: UnOpContext -> (UnOpContext, Inf)
pop_level_ ctx =
    let (_ : lv@(_, inf) : lvs') = un_current_level ctx
    in (ctx { un_current_level = lv : lvs' }, inf)


traverse_dc_unary :: forall (a :: Inf). (DdF3 a) => Move -> UnOpContext -> NodeId -> UnOpContext
traverse_dc_unary s c d =
    let ref = getNode c d
    in case snd ref of
        Leaf{} -> c
        _      -> let new_dcRs = map (traverse_dc_generic @a s c ref) (un_dc_stack c)
                      c' = c { un_dc_stack = new_dcRs }
                  in debug_dc_traverse_unary (show s) (to_str @a) c d c'

-- | Wrap a traversal result in EndClassNode, applying the elimination rule @a.
wrapEndClass :: forall a. (DdF3 a) => (UnOpContext, Node) -> (UnOpContext, Node)
wrapEndClass (c', r) = applyElimRule @a c' $ EndClassNode (fst r)

-- | Exit the current class: sync dc_stack, pop the level, return (c_end, inf, c_after_pop).
exitClass :: UnOpContext -> NodeId -> (UnOpContext, Inf, UnOpContext)
exitClass c absingBId =
    let c_end       = traverse_dc_unary @Dc ExitClass c absingBId
        (c_, inf)   = pop_level_ c_end
    in (c_end, inf, c_)

-- | Infer a ClassNode wrapper for `branch` using rule @a, then call cont with absingB fixed.
inferClassBranch :: forall a r. (DdF3 a)
    => UnOpContext -> Int -> Node -> Node
    -> (UnOpContext -> Node -> Node -> r) -> r
inferClassBranch c pos absingB branch cont =
    let (c', b') = inferClassNode @a c pos branch
    in cont c' absingB b'

-- | Infer a ClassNode wrapper for `absingB` using @Dc, then call cont with branch fixed.
inferClassAbsing :: forall r. UnOpContext -> Int -> Node -> Node
    -> (UnOpContext -> Node -> Node -> r) -> r
inferClassAbsing c pos absingB branch cont =
    let (c', a') = inferClassNode @Dc c pos absingB
    in cont c' a' branch

-- | Traverse an absorbing Node's children according to the inference context, applying f.
travNodeAbs :: forall a. (DdF3 a)
    => UnOpContext
    -> Node  -- absingB: the absorbing branch (must be a Node constructor)
    -> Node  -- branch: the branch being tested
    -> (UnOpContext -> Node -> Node -> (UnOpContext, Node))
    -> (UnOpContext, Node)
travNodeAbs c absingB@(absingBId, Node dcPos dcP dcN) branch f
    | isNeg @a =
        let c_ = traverse_dc_unary @Dc MvNeg c absingBId
        in f c_ (getNode c dcN) branch
    | isPos @a =
        let c_ = traverse_dc_unary @Dc MvPos c absingBId
        in f c_ (getNode c dcP) branch
    | otherwise =  -- Dc: traverse both children
        let c_p = traverse_dc_unary @Dc MvPos c absingBId
            (c',  r1) = f c_p (getNode c dcP) branch
            c_n = traverse_dc_unary @Dc MvNeg (reset_stack_un c' c) absingBId
            (c'', r2) = f c_n (getNode c dcN) branch
        in applyElimRule @a (reset_stack_un c'' c) $ Node dcPos (fst r1) (fst r2)
travNodeAbs _ _ _ _ = error "travNodeAbs: absingB must be a Node constructor"

-- | Traverse a tested branch's node
-- synchronise via @b, recurse with absPos/absNeg as left args, recombine via @a.
travNodeStep :: forall b a. (DdF3 b, DdF3 a)
    => UnOpContext
    -> NodeId           -- reference node for traverse_dc_unary @b
    -> Node -> Node     -- absPos and Neg
    -> Node             -- branch (must be a Node constructor)
    -> (UnOpContext -> Node -> Node -> (UnOpContext, Node))
    -> (UnOpContext, Node)
travNodeStep c refId absPos absNeg branch@(_, Node pos p n) f =
    let c_p = traverse_dc_unary @b MvPos c refId
        (c',  r1) = f c_p absPos (getNode c p)
        c_n = traverse_dc_unary @b MvNeg (reset_stack_un c' c) refId
        (c'', r2) = f c_n absNeg (getNode c n)
    in applyElimRule @a (reset_stack_un c'' c) $ Node pos (fst r1) (fst r2)
travNodeStep _ _ _ _ _ _ = error "travNodeStep: branch must be a Node constructor"

-- | Step the branch Node with @a; absingB is fixed on both branches.
travNodeBranch :: forall a. (DdF3 a)
    => UnOpContext -> Node -> Node -> (UnOpContext -> Node -> Node -> (UnOpContext, Node)) -> (UnOpContext, Node)
travNodeBranch c absingB branch@(branchId, _) = travNodeStep @a @a c branchId absingB absingB branch

-- | Step both Nodes at matching positions; absorbing Node uses @Dc.
travNodeBoth :: forall a. (DdF3 a)
    => UnOpContext -> Node -> Node -> (UnOpContext -> Node -> Node -> (UnOpContext, Node)) -> (UnOpContext, Node)
travNodeBoth c absingB@(absingBId, Node _ dcP dcN) branch = travNodeStep @Dc @a c absingBId (getNode c dcP) (getNode c dcN) branch
travNodeBoth _ _ _ = error "travNodeBoth: absingB must be a Node constructor"

-- | Traverse matching ClassNodes at the same position; absingB uses @Dc, branch uses @a.
-- Takes three callbacks — one per branch type — because each must be called with a different
-- type-level inference parameter (@Dc, @Pos, @Neg) that cannot be abstracted as a value.
travClassBoth :: forall a. (DdF3 a)
    => UnOpContext
    -> Node  -- absingB (must be a ClassNode)
    -> Node  -- branch  (must be a ClassNode, same position)
    -> (UnOpContext -> Node -> Node -> (UnOpContext, Node))  -- fDc:  recurse on dc  branch
    -> (UnOpContext -> Node -> Node -> (UnOpContext, Node))  -- fPos: recurse on pos branch
    -> (UnOpContext -> Node -> Node -> (UnOpContext, Node))  -- fNeg: recurse on neg branch
    -> (UnOpContext, Node)
travClassBoth c absingB@(absingBId, ClassNode _ dcD dcP dcN) branch@(_, ClassNode pos d p n) fDc fPos fNeg =
    let c_dc = traverse_dc_unary @Dc MvClassDc c absingBId
        c_   = add_to_stack_ (pos, Dc)  (getNode c_dc dcD, ((0,0), Unknown)) c_dc
        (c1, rD) = fDc c_ (getNode c_dc dcD) (getNode c_dc d)
        c1'  = reset_stack_un c1 c
        c_p  = traverse_dc_unary @Dc MvClassPos c1' absingBId
        c2_  = add_to_stack_ (pos, Pos) (getNode c_p dcD, rD) c_p
        (c2, rP) = fPos c2_ (getNode c_p dcP) (getNode c_p p)
        c2'  = reset_stack_un c2 c
        c_n  = traverse_dc_unary @Dc MvClassNeg c2' absingBId
        c3_  = add_to_stack_ (pos, Neg) (getNode c_n dcD, rD) c_n
        (c3, rN) = fNeg c3_ (getNode c_n dcN) (getNode c_n n)
    in applyElimRule @a (reset_stack_un c3 c) $ ClassNode pos (fst rD) (fst rP) (fst rN)
travClassBoth _ _ _ _ _ _ = error "travClassBoth: both arguments must be ClassNode constructors"