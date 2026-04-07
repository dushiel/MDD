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
{-# LANGUAGE RankNTypes #-}

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
data TraversalMode = TM
  { tmName               :: String
  , tmToInf              :: Inf
  , tmIsNeg              :: Bool
  , tmIsPos              :: Bool
  , tmIsDc               :: Bool
  , tmInferNodeA         :: (BiOpContext -> String -> Node -> Node -> (BiOpContext, Node))
                         -> BiOpContext -> String -> Node -> Node -> (BiOpContext, Dd)
  , tmInferNodeB         :: (BiOpContext -> String -> Node -> Node -> (BiOpContext, Node))
                         -> BiOpContext -> String -> Node -> Node -> (BiOpContext, Dd)
  , tmApplyElimRule      :: forall c. HasNodeLookup c => c -> Dd -> (c, Node)
  , tmInferNode          :: forall c. HasNodeLookup c => c -> Int -> Node -> (c, Node)
  , tmInferClassNode     :: forall c. HasNodeLookup c => c -> Int -> Node -> (c, Node)
  , tmCatchup            :: forall c. HasNodeLookup c => c -> Node -> Int -> Node
  , tmInferClassNodeForA :: forall c. HasNodeLookup c => c -> Int -> Node -> (c, Node)
  , tmInferClassNodeForB :: forall c. HasNodeLookup c => c -> Int -> Node -> (c, Node)
  , tmAUnknownReturn     :: Bool
  , tmBUnknownReturn     :: Bool
  , tmDcAMode            :: TraversalMode
  , tmDcBMode            :: TraversalMode
  , tmPopADropLevel      :: Bool
  , tmPopBDropLevel      :: Bool
  , tmNegClassInf        :: TraversalMode
  , tmPosClassInf        :: TraversalMode
  }

modeDcSourced :: TraversalMode
modeDcSourced = modeDc { tmName = "DcSourced", tmIsDc = False } -- we trick compoundMode by saying it's not Dc!

compoundMode :: TraversalMode -> TraversalMode -> TraversalMode
compoundMode modeA modeB = 
  let baseOp = if not (tmIsDc modeA) && tmName modeA /= "DcSourced" then modeA 
               else if not (tmIsDc modeB) && tmName modeB /= "DcSourced" then modeB 
               else modeDc
      isCompound = tmName modeA /= tmName modeB
      popDropA = isCompound || tmName modeA == "DcSourced"
      popDropB = isCompound || tmName modeB == "DcSourced"

      isA_RealDc = tmName modeA `elem` ["Dc", "DcSourced"]
      isB_RealDc = tmName modeB `elem` ["Dc", "DcSourced"]

      isA_DcSourced = tmName modeA == "DcSourced"
      isB_DcSourced = tmName modeB == "DcSourced"

      negA = if not isA_RealDc && isB_RealDc then tmNegClassInf modeA else if isA_RealDc && not isB_RealDc then modeA else tmNegClassInf modeA
      negB = if not isA_RealDc && isB_RealDc then modeB else if isA_RealDc && not isB_RealDc then tmNegClassInf modeB else tmNegClassInf modeB
      posA = if not isA_RealDc && isB_RealDc then tmPosClassInf modeA else if isA_RealDc && not isB_RealDc then modeA else tmPosClassInf modeA
      posB = if not isA_RealDc && isB_RealDc then modeB else if isA_RealDc && not isB_RealDc then tmPosClassInf modeB else tmPosClassInf modeB

      -- Unknown returns:
      -- If one side is a real Dc and the other is not, the non-Dc side returns Unknown.
      -- If both are real Dcs, the one that is DcSourced pops (returns False), the other returns Unknown (returns True).
      -- If neither is real Dc, both pop (returns False).
      aUnkRet = if not isA_RealDc && isB_RealDc then True
                else if isA_RealDc && not isB_RealDc then False
                else if isA_RealDc && isB_RealDc then isB_DcSourced
                else False

      bUnkRet = if not isB_RealDc && isA_RealDc then True
                else if isB_RealDc && not isA_RealDc then False
                else if isA_RealDc && isB_RealDc then isA_DcSourced
                else False

  in TM
  { tmName               = if tmName modeA == tmName modeB then tmName modeA else tmName modeA ++ tmName modeB
  , tmToInf              = pairToInf (tmToInf modeA) (tmToInf modeB)
  , tmIsNeg              = tmIsNeg baseOp
  , tmIsPos              = tmIsPos baseOp
  , tmIsDc               = tmIsDc baseOp
  , tmInferNodeA         = tmInferNodeA modeA
  , tmInferNodeB         = tmInferNodeB modeB
  , tmApplyElimRule      = tmApplyElimRule baseOp
  , tmInferNode          = tmInferNode baseOp
  , tmInferClassNode     = tmInferClassNode baseOp
  , tmCatchup            = tmCatchup baseOp
  , tmInferClassNodeForA = tmInferClassNodeForA modeA
  , tmInferClassNodeForB = tmInferClassNodeForB modeB
  , tmAUnknownReturn     = aUnkRet
  , tmBUnknownReturn     = bUnkRet
  , tmDcAMode            = if not (tmIsDc modeA) then compoundMode modeA modeB else compoundMode modeDcSourced modeB
  , tmDcBMode            = if not (tmIsDc modeB) then compoundMode modeA modeB else compoundMode modeA modeDcSourced
  , tmPopADropLevel      = popDropA
  , tmPopBDropLevel      = popDropB
  , tmNegClassInf        = compoundMode negA negB
  , tmPosClassInf        = compoundMode posA posB
  }

baseMode :: Inf -> TraversalMode
baseMode Dc = modeDc
baseMode Neg = modeNeg
baseMode Pos = modePos
baseMode _ = error "baseMode: expected simple Inf"

pairToInf :: Inf -> Inf -> Inf
pairToInf Dc    Dc    = Dc
pairToInf Neg   Neg   = Neg
pairToInf Pos   Pos   = Pos
pairToInf NegDc NegDc = NegDc
pairToInf DcNeg DcNeg = DcNeg
pairToInf PosDc PosDc = PosDc
pairToInf DcPos DcPos = DcPos
pairToInf DcDcA DcDcA = DcDcA
pairToInf DcDcB DcDcB = DcDcB
pairToInf Neg   Dc    = NegDc
pairToInf Pos   Dc    = PosDc
pairToInf Dc    Neg   = DcNeg
pairToInf Dc    Pos   = DcPos
pairToInf NegDc Dc    = NegDc
pairToInf PosDc Dc    = PosDc
pairToInf Dc    DcNeg = DcNeg
pairToInf Dc    DcPos = DcPos
pairToInf DcDcA Dc    = DcDcA
pairToInf Dc    DcDcB = DcDcB
pairToInf a     b     = error ("pairToInf: unexpected level-stack pair: " ++ show a ++ ", " ++ show b)

infToMode :: Inf -> TraversalMode
infToMode Dc = modeDc
infToMode Neg = modeNeg
infToMode Pos = modePos
infToMode NegDc = compoundMode modeNeg modeDc
infToMode DcNeg = compoundMode modeDc modeNeg
infToMode PosDc = compoundMode modePos modeDc
infToMode DcPos = compoundMode modeDc modePos
infToMode DcDcA = compoundMode modeDcSourced modeDc
infToMode DcDcB = compoundMode modeDc modeDcSourced






-- * Naive Absorb Implementation
-- Naive absorb minimizes the pos / neg branches of a class with respect to the class' resulting dc branch - Or a dc branch with respect to the outer dc branch.
-- simultaneous traversal for 2 branches. Recurses depth-first; at EndClassNode boundaries of the local class, an equality check determines absorption.
-- When entering a nested class, a non-absorbing traversal is used until returning to the original class level.
-- The dcR stack is kept up-to-date during traversal for subsituting any Unknowns encountered on the absorbingBranch.


naiveAbsorb :: TraversalMode -> UnOpContext -> Node -> Node -> (UnOpContext, Node)
naiveAbsorb tm c absingB branch =
    let (c', r) = myTrace (debug_naiveAbsorb_open ("absorb " ++ tmName tm) c absingB branch) $
                  naiveAbsorb' tm c absingB branch
    in myTrace (debug_naiveAbsorb_close ("absorb " ++ tmName tm) c' absingB branch r) (c', r)

naiveAbsorb' :: TraversalMode -> UnOpContext -> Node -> Node -> (UnOpContext, Node)

-- Already absorbed (Unknown in branch means it was previously set to dc)
naiveAbsorb' tm c _absingB branch@(_, Unknown) = (c, branch)

-- EndClassNode vs EndClassNode: local class boundary — check equality - otherwise no absorb will happen
naiveAbsorb' tm c absingB@(_, EndClassNode dcChild) branch@(_, EndClassNode branchChild)
    | branch == absingB = (c, ((0,0), Unknown))
    | otherwise = (c, branch)
-- Leaf vs Leaf: direct comparison at the (implicit) class boundary
naiveAbsorb' tm c absingB@(_, Leaf _) branch@(_, Leaf _)
    | branch == absingB = (c, ((0,0), Unknown))
    | otherwise     = (c, branch)

-- absorbingBranch is Unknown: resolve it from the outer dcR stack
naiveAbsorb' tm c (_, Unknown) branch = -- todo double check the logic here
    case un_dc_stack c of
        (_ : outer : rest) -> naiveAbsorb tm (c { un_dc_stack = outer : rest }) outer branch
        _                  -> (c, branch)

-- Node one, Leaf in other: the Leaf implicitly has the Node's variable resolved through the inference rule. Infer to reach the Leaf's level.
naiveAbsorb' tm c absingB@(_, Node _ _ _) branch@(_, Leaf _) = travNodeAbs tm c absingB branch (naiveAbsorb tm)
naiveAbsorb' tm c absingB@(_, Leaf _) branch@(_, Node{}) =
    -- because absorbingBranch has dc rule we do not have to explicitly infer nodes for it and can traverse on tested branch node directly
    travNodeBranch tm c absingB branch (naiveAbsorb tm)

-- Leaf implicitly has EndClassNodes for all outer classes
naiveAbsorb' tm c absingB@(_, EndClassNode dcChild) branch@(_, Leaf _) =
    let (c', branchWrapped) = insert c (EndClassNode (fst branch))
    in naiveAbsorb tm c' absingB branchWrapped
naiveAbsorb' tm c absingB@(_, Leaf _) branch@(_, EndClassNode branchChild) =
    let (c', absingBWrapped) = insert c (EndClassNode (fst absingB))
    in naiveAbsorb tm c' absingBWrapped branch
naiveAbsorb' tm c absingB@(_, Leaf _) branch@(_, ClassNode pos d p n) =
    inferClassAbsing c pos absingB branch (naiveAbsorb tm)
naiveAbsorb' tm c absingB@(_, ClassNode dcPos _ _ _) branch@(_, Leaf _) =
    inferClassBranch tm c dcPos absingB branch (naiveAbsorb tm)


-- === Node vs Node ===: simultaneous traversal of matching variable positions
naiveAbsorb' tm c absingB@(absingBId, Node dcPos dcP dcN) branch@(branchId, Node pos p n)
    | branch == absingB = (c, ((0,0), Unknown))
    | dcPos == pos = travNodeBoth tm c absingB branch (naiveAbsorb tm)
    | dcPos < pos = travNodeAbs tm c absingB branch (naiveAbsorb tm)
    | dcPos > pos = travNodeBranch tm c absingB branch (naiveAbsorb tm)

-- === Node vs EndClassNode ===
naiveAbsorb' tm c absingB@(absingBId, Node dcPos dcP dcN) branch@(_, EndClassNode _) = travNodeAbs tm c absingB branch (naiveAbsorb tm)
-- because absorbingBranch has dc rule we do not have to explicitly infer nodes for it
naiveAbsorb' tm c absingB@(_, EndClassNode _) branch@(_, Node{}) = travNodeBranch tm c absingB branch (naiveAbsorb tm)

-- === ClassNode in branch and absorbingBranch ===
-- Switch to non-absorbing simultaneous traversal (with elimination rules)
-- until the same class level is reached again, then absorption continues.
--
naiveAbsorb' tm c absingB@(_, ClassNode dcPos _ _ _) branch@(_, ClassNode pos _ _ _)
    | branch == absingB = (c, ((0,0), Unknown))
    | dcPos == pos = travClassBoth tm c absingB branch
            (naiveTraverse modeDc 1) (naiveTraverse modePos 1) (naiveTraverse modeNeg 1)
    | dcPos < pos = inferClassBranch tm c dcPos absingB branch (naiveAbsorb tm)
    | dcPos > pos = inferClassAbsing c pos absingB branch (naiveAbsorb tm)

naiveAbsorb' tm c absingB@(_, ClassNode dcPos _ _ _) branch@(_, EndClassNode _) =
    inferClassBranch tm c dcPos absingB branch (naiveAbsorb tm)
naiveAbsorb' tm c absingB@(_, EndClassNode _) branch@(_, ClassNode pos _ _ _) =
    inferClassAbsing c pos absingB branch (naiveAbsorb tm)

-- === Node in absorbingBranch, ClassNode in branch ===
naiveAbsorb' _ _ (_, Node _ _ _) (_, ClassNode _ _ _ _) = error "should not happen: node vs class node in absorb"
naiveAbsorb' _ _ (_, ClassNode _ _ _ _) (_, Node _ _ _) =
    error "naiveAbsorb: ClassNode absingB vs Node branch should not happen"


-- | Simultaneous traversal without absorption for nested classes.
-- Walks absorbingBranch and branch in lockstep, creating new nodes with elimination rules applied, but never replacing nodes with Unknown.
-- The Int parameter tracks nesting depth of Class(Nodes)' relative to where naiveAbsorb handed off.
-- At depth 0, the next EndClassNode exit returns to the absorbing class level

naiveTraverse :: TraversalMode -> Int -> UnOpContext -> Node -> Node -> (UnOpContext, Node)
naiveTraverse tm depth c absingB branch =
    let (c', r) = myTrace (debug_naiveAbsorb_open ("traverse " ++ tmName tm ++ " depth=" ++ show depth) c absingB branch) $
                  naiveTraverse' tm depth c absingB branch
    in myTrace (debug_naiveAbsorb_close ("traverse " ++ tmName tm ++ " depth=" ++ show depth) c' absingB branch r) (c', r)

naiveTraverse' :: TraversalMode -> Int -> UnOpContext -> Node -> Node -> (UnOpContext, Node)

naiveTraverse' tm _ c _ branch@(_, Unknown) = (c, branch)
naiveTraverse' tm depth c (_, Unknown) branch = -- todo double check the logic here
    case un_dc_stack c of
        (_ : outer : rest) -> naiveTraverse tm depth (c { un_dc_stack = outer : rest }) outer branch
        _                  -> (c, branch)

naiveTraverse' tm depth c absingB@(absingBId, EndClassNode dcChild) branch@(_, Leaf _) =
    let (c_end, inf, c_) = exitClass c absingBId
        go f = f c_ (getNode c_end dcChild) branch
    in case inf of
        Dc  -> go $ if depth == 1 then naiveAbsorb modeDc  else naiveTraverse modeDc  (depth - 1)
        Neg -> go $ if depth == 1 then naiveAbsorb modeNeg else naiveTraverse modeNeg (depth - 1)
        Pos -> go $ if depth == 1 then naiveAbsorb modePos else naiveTraverse modePos (depth - 1)
naiveTraverse' tm depth c absingB@(_, Node _ _ _) branch@(_, Leaf _) =
    travNodeAbs tm c absingB branch (naiveTraverse tm depth)

-- === EndClassNode: exiting a class ===
-- depth == 1: about to go back at the absorbing class level — hand to naiveAbsorb
-- depth > 1: still inside a deeper nested class — stay in naiveTraverse
naiveTraverse' tm depth c absingB@(absingBId, EndClassNode dcChild) branch@(_, EndClassNode branchChild) =
    let (c_end, inf, c_) = exitClass c absingBId
        go f = wrapEndClass tm (f c_ (getNode c_end dcChild) (getNode c_end branchChild))
    in case inf of
        Dc  -> go $ if depth == 1 then naiveAbsorb modeDc  else naiveTraverse modeDc  (depth - 1)
        Neg -> go $ if depth == 1 then naiveAbsorb modeNeg else naiveTraverse modeNeg (depth - 1)
        Pos -> go $ if depth == 1 then naiveAbsorb modePos else naiveTraverse modePos (depth - 1)
naiveTraverse' tm depth c absingB@(absingBId, Leaf _) branch@(_, EndClassNode branchChild) =
    let (c_end, inf, c_) = exitClass c absingBId
        go f = wrapEndClass tm (f c_ absingB (getNode c_end branchChild))
    in case inf of
        Dc  -> go $ if depth == 1 then naiveAbsorb modeDc  else naiveTraverse modeDc  (depth - 1)
        Neg -> go $ if depth == 1 then naiveAbsorb modeNeg else naiveTraverse modeNeg (depth - 1)
        Pos -> go $ if depth == 1 then naiveAbsorb modePos else naiveTraverse modePos (depth - 1)
naiveTraverse' tm depth c absingB@(absingBId, Leaf _) branch@(_, Leaf _) =
    let (_, inf, c_) = exitClass c absingBId
        go f = f c_ absingB branch
    in case inf of
        Dc  -> go $ if depth == 1 then naiveAbsorb modeDc  else naiveTraverse modeDc  (depth - 1)
        Neg -> go $ if depth == 1 then naiveAbsorb modeNeg else naiveTraverse modeNeg (depth - 1)
        Pos -> go $ if depth == 1 then naiveAbsorb modePos else naiveTraverse modePos (depth - 1)

naiveTraverse' tm depth c absingB@(_, Node _ _ _) branch@(_, EndClassNode _) =
    travNodeAbs tm c absingB branch (naiveTraverse tm depth)
naiveTraverse' tm depth c absingB@(_, EndClassNode _) branch@(_, Node{}) =
    travNodeBranch tm c absingB branch (naiveTraverse tm depth)

-- === Node vs Node: simultaneous traversal (same class level) ===
naiveTraverse' tm depth c absingB@(_, Node dcPos _ _) branch@(_, Node pos _ _)
    | dcPos == pos = travNodeBoth tm c absingB branch (naiveTraverse tm depth)
    | dcPos < pos  = travNodeAbs tm c absingB branch (naiveTraverse tm depth)
    | otherwise    = travNodeBranch tm c absingB branch (naiveTraverse tm depth)

naiveTraverse' tm depth c absingB@(_, Leaf _) branch@(_, Node{}) =
    travNodeBranch tm c absingB branch (naiveTraverse tm depth)

naiveTraverse' tm depth c absingB@(_, ClassNode dcPos _ _ _) branch@(_, Leaf _) =
    inferClassBranch tm c dcPos absingB branch (naiveTraverse tm depth)

-- === ClassNode: entering a deeper nested class (depth + 1) ===
naiveTraverse' tm depth c absingB@(_, ClassNode dcPos _ _ _) branch@(_, ClassNode pos _ _ _)
    | dcPos == pos =
        travClassBoth tm c absingB branch
            (naiveTraverse modeDc (depth + 1)) (naiveTraverse modePos (depth + 1)) (naiveTraverse modeNeg (depth + 1))
    | dcPos < pos  = inferClassBranch tm c dcPos absingB branch (naiveTraverse tm depth)
    | otherwise    = inferClassAbsing c pos absingB branch (naiveTraverse tm depth)

naiveTraverse' tm _ _ (_, Node _ _ _) (_, ClassNode _ _ _ _) = error "should not happen: node vs class node in naiveTraverse"
naiveTraverse' tm depth c absingB@(_, EndClassNode _) branch@(_, ClassNode pos _ _ _) =
    inferClassAbsing c pos absingB branch (naiveTraverse tm depth)
naiveTraverse' tm depth c absingB@(_, Leaf _) branch@(_, ClassNode pos _ _ _) =
    inferClassAbsing c pos absingB branch (naiveTraverse tm depth)
naiveTraverse' tm _ _ (_, ClassNode _ _ _ _) (_, Node _ _ _) = error "should not happen: class node vs node in naiveTraverse"
naiveTraverse' tm depth c absingB@(_, ClassNode dcPos _ _ _) branch@(_, EndClassNode _) =
    inferClassBranch tm c dcPos absingB branch (naiveTraverse tm depth)


modeDc :: TraversalMode
modeDc = TM
    { tmName = "Dc"
    , tmToInf = Dc
    , tmIsNeg = False
    , tmIsPos = False
    , tmIsDc = True
    , tmInferNodeA = \f c s (a_id, _) (b_id, Node positionB _ _) ->
        let (c', r) = insert c (Node positionB a_id a_id)
            (c'', (r_node_id, _)) = f c' s r (getNode c' b_id)
        in (c'', getDd c'' r_node_id)
    , tmInferNodeB = \f c s (a_id, Node positionA _ _) (b_id, _) ->
        let (c', r) = insert c (Node positionA b_id b_id)
            (c'', (r_node_id, _)) = f c' s (getNode c' a_id) r
        in (c'', getDd c'' r_node_id)
    , tmApplyElimRule = \c d -> case d of
        Node _ p n | p == n -> (c, getNode c p)
        ClassNode _ (1,0) (0,0) (0,0) -> (c, ((1,0), Leaf True))
        ClassNode _ (2,0) (0,0) (0,0) -> (c, ((2,0), Leaf False))
        ClassNode _ (0,0) (0,0) (0,0) -> (c, ((0,0), Unknown))
        ClassNode _ consq (0,0) (0,0) -> case getDd c consq of
            EndClassNode d' -> (c, getNode c d')
            _ -> insert c d
        EndClassNode r -> case getDd c r of
            Leaf _ -> (c, getNode c r)
            Unknown -> (c, getNode c r)
            _ -> insert c d
        _ -> insert c d
    , tmInferNode = \c position (n_id, _) -> insert c (Node position n_id n_id)
    , tmInferClassNode = \c position (n_id, _) -> insert c $ ClassNode position n_id (0,0) (0,0)
    , tmCatchup = \c n idx -> case n of
        (_, ClassNode _ _ _ _) -> error "ClassNode catchup not yet implemented"
        _ -> n
    , tmInferClassNodeForA = \c position (n_id, _) -> insert c $ ClassNode position n_id (0,0) (0,0)
    , tmInferClassNodeForB = \c position (n_id, _) -> insert c $ ClassNode position n_id (0,0) (0,0)
    , tmAUnknownReturn = False
    , tmBUnknownReturn = False
    , tmDcAMode = compoundMode modeDcSourced modeDc
    , tmDcBMode = compoundMode modeDc modeDcSourced
    , tmPopADropLevel = False
    , tmPopBDropLevel = False
    , tmNegClassInf = modeNeg
    , tmPosClassInf = modePos
    }

modePos :: TraversalMode
modePos = TM
    { tmName = "Pos"
    , tmToInf = Pos
    , tmIsNeg = False
    , tmIsPos = True
    , tmIsDc = False
    , tmInferNodeA = \f c s (a_id, _) (b_id, Node positionB _ _) ->
        let (c', r) = insert c (Node positionB a_id (0,0))
            (c'', (r_node_id, _)) = f c' s r (getNode c' b_id)
        in (c'', getDd c'' r_node_id)
    , tmInferNodeB = \f c s (a_id, Node positionA _ _) (b_id, _) ->
        let (c', r) = insert c (Node positionA b_id (0,0))
            (c'', (r_node_id, _)) = f c' s (getNode c' a_id) r
        in (c'', getDd c'' r_node_id)
    , tmApplyElimRule = \c d -> case d of
        Node _ posC (0, 0) -> (c, getNode c posC)
        ClassNode _ (0,0) (1,0) (0,0) -> (c, ((1,0), Leaf True))
        ClassNode _ (0,0) (2,0) (0,0) -> (c, ((2,0), Leaf False))
        ClassNode _ (0,0) (0,0) (0,0) -> (c, ((0,0), Unknown))
        ClassNode _ (0,0) consq (0,0) -> case getDd c consq of
            EndClassNode d' -> (c, getNode c d')
            _ -> insert c d
        EndClassNode r -> case getDd c r of
            Leaf _ -> (c, getNode c r)
            Unknown -> (c, getNode c r)
            _ -> insert c d
        _ -> insert c d
    , tmInferNode = \c position (n_id, _) -> insert c (Node position n_id (0,0))
    , tmInferClassNode = \c position (n_id, _) -> insert c $ ClassNode position (0,0) n_id (0,0)
    , tmCatchup = \c n idx -> case n of
        (_, Node positionA pos_child _)
            | idx == -1       -> tmCatchup modePos c (getNode c pos_child) idx
            | idx > positionA -> tmCatchup modePos c (getNode c pos_child) idx
            | otherwise -> n
        (_, ClassNode _ _ _ _) -> error "ClassNode catchup not yet implemented"
        _ -> n
    , tmInferClassNodeForA = \c position (n_id, _) -> insert c $ ClassNode position (0,0) n_id (0,0)
    , tmInferClassNodeForB = \c position (n_id, _) -> insert c $ ClassNode position (0,0) n_id (0,0)
    , tmAUnknownReturn = False
    , tmBUnknownReturn = False
    , tmDcAMode = compoundMode modeDc modePos
    , tmDcBMode = compoundMode modePos modeDc
    , tmPopADropLevel = False
    , tmPopBDropLevel = False
    , tmNegClassInf = modeNeg
    , tmPosClassInf = modePos
    }

modeNeg :: TraversalMode
modeNeg = TM
    { tmName = "Neg"
    , tmToInf = Neg
    , tmIsNeg = True
    , tmIsPos = False
    , tmIsDc = False
    , tmInferNodeA = \f c s (a_id, _) (b_id, Node positionB _ _) ->
        let (c', r) = insert c (Node positionB (0,0) a_id)
            (c'', (r_node_id, _)) = f c' s r (getNode c' b_id)
        in (c'', getDd c'' r_node_id)
    , tmInferNodeB = \f c s (a_id, Node positionA _ _) (b_id, _) ->
        let (c', r) = insert c (Node positionA (0,0) b_id)
            (c'', (r_node_id, _)) = f c' s (getNode c' a_id) r
        in (c'', getDd c'' r_node_id)
    , tmApplyElimRule = \c d -> case d of
        Node _ (0, 0) negC -> (c, getNode c negC)
        ClassNode _ (0,0) (0,0) (1,0) -> (c, ((1,0), Leaf True))
        ClassNode _ (0,0) (0,0) (2,0) -> (c, ((2,0), Leaf False))
        ClassNode _ (0,0) (0,0) (0,0) -> (c, ((0,0), Unknown))
        ClassNode _ (0,0) (0,0) consq -> case getDd c consq of
            EndClassNode d' -> (c, getNode c d')
            _ -> insert c d
        EndClassNode r -> case getDd c r of
            Leaf _ -> (c, getNode c r)
            Unknown -> (c, getNode c r)
            _ -> insert c d
        _ -> insert c d
    , tmInferNode = \c position (n_id, _) -> insert c (Node position (0,0) n_id)
    , tmInferClassNode = \c position (n_id, _) -> insert c $ ClassNode position (0,0) (0,0) n_id
    , tmCatchup = \c n idx -> case n of
        (_, Node positionA _ neg_child)
            | idx == -1       -> tmCatchup modeNeg c (getNode c neg_child) idx
            | idx > positionA -> tmCatchup modeNeg c (getNode c neg_child) idx
            | otherwise -> n
        (_, ClassNode _ _ _ _) -> error "ClassNode catchup not yet implemented"
        _ -> n
    , tmInferClassNodeForA = \c position (n_id, _) -> insert c $ ClassNode position (0,0) (0,0) n_id
    , tmInferClassNodeForB = \c position (n_id, _) -> insert c $ ClassNode position (0,0) (0,0) n_id
    , tmAUnknownReturn = False
    , tmBUnknownReturn = False
    , tmDcAMode = compoundMode modeDc modeNeg
    , tmDcBMode = compoundMode modeNeg modeDc
    , tmPopADropLevel = False
    , tmPopBDropLevel = False
    , tmNegClassInf = modeNeg
    , tmPosClassInf = modePos
    }

-- | Synchronize a single dc_stack element with the main traversal.
traverse_dc_generic :: forall c. (HasNodeLookup c) => TraversalMode -> Move -> c -> Node -> Node -> Node
traverse_dc_generic tm s c refNode dcNode =
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
                | position < idx  -> move_dc c s (tmCatchup tm c dcNode idx)

            -- Case 3: (Node, EndClassNode) — dc is behind, catch up to terminal then move
            ((_, Node{}), (_, EndClassNode{})) ->
                move_dc c s (tmCatchup tm c dcNode (-1))

            -- Case 4: (EndClassNode, EndClassNode) — both exiting class
            ((_, EndClassNode{}), (_, EndClassNode{})) -> move_dc c s dcNode

            -- Case 7: (ClassNode, ClassNode) — both are class nodes
            ((_, ClassNode position _ _ _), (_, ClassNode idx _ _ _))
                | position > idx  -> let (_, inferred) = tmInferClassNode tm c idx dcNode
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
                let (_, inferred) = tmInferClassNode modeDc c idx dcNode
                in move_dc c s inferred

            -- Case 11: (EndClassNode, Node) — dc at end class, ref still inside
            ((_, EndClassNode{}), (_, Node{})) -> dcNode

            -- Case 13: (EndClassNode, ClassNode) — dc at end, ref at ClassNode
            ((_, EndClassNode{}), (_, ClassNode idx _ _ _)) ->
                let (_, inferred) = tmInferClassNode modeDc c idx dcNode
                in move_dc c s inferred

            ((_, Node _ _ _), (_, ClassNode _ _ _ _)) -> error "node vs classnode should not happen on the same local domain"
            ((_, ClassNode _ _ _ _), (_, Node _ _ _)) -> error "classnode vs node should not happen on the same local domain"

            _ -> error $ "traverse_dc_generic unhandled case:\n (dcNode=" ++ show_node c dcNode
                      ++ ",\n  refNode=" ++ show_node c refNode ++ ")"





-- * Helper functions

traverse_dc :: TraversalMode -> Move -> BiOpContext -> NodeId -> NodeId -> BiOpContext
-- | Synchronizes the entire dc_stack with the main traversal.
traverse_dc tm s c a b = debug_dc_traverse (show s) c a b $
            let (dcAs, dcBs, dcRs) = (bin_dc_stack c)
                refA = getNode c a
                refB = getNode c b
                isLeaf (_, Leaf{}) = True
                isLeaf _           = False
                new_dcAs = if isLeaf refA then dcAs else map (traverse_dc_generic tm s c refA) dcAs
                new_dcBs = if isLeaf refB then dcBs else map (traverse_dc_generic tm s c refB) dcBs
                new_dcRs = if isLeaf refA then dcRs else map (traverse_dc_generic tm s c refA) dcRs
            in c { bin_dc_stack = (new_dcAs, new_dcBs, new_dcRs) }

absorb :: TraversalMode -> BiOpContext -> Int -> Node -> Node -> (BiOpContext, Node)
absorb tm c positionA dcR branch =
    let (_, _, outerDcRs) = bin_dc_stack c
        unCtx_base = binaryToUnaryContext c
        -- Restore the correct outer inference context that might have been overwritten by pop_dcA'
        lvs = un_current_level unCtx_base
        fixed_lvs = case lvs of
            ((pos, _) : rest) -> (pos, tmToInf tm) : rest
            [] -> []
        unCtx = unCtx_base { un_dc_stack = dcR : outerDcRs, un_current_level = fixed_lvs }
        (unCtx', branch') = myTrace (debug_naiveAbsorb_open ("absorb " ++ tmName tm ++ " pos=" ++ show positionA) unCtx dcR branch) $
                            let r@(uc, n) = naiveAbsorb' tm unCtx dcR branch
                            in myTrace (debug_naiveAbsorb_close ("absorb " ++ tmName tm ++ " pos=" ++ show positionA) uc dcR branch n) r
    in (unaryToBinaryContext unCtx' c, branch')


outerDcR :: [Node] -> Node
outerDcR (h : _) = h
outerDcR []      = error "requested from empty dcR stack"

-- | Absorb dcR against the outer dcR from the stack.
absorb_dc :: TraversalMode -> BiOpContext -> Int -> Node -> (BiOpContext, Node)
absorb_dc tm c positionA dcR =
    let (_, _, outerDcRs) = bin_dc_stack c
    in absorb tm c positionA (outerDcR outerDcRs) dcR

absorb_unary :: TraversalMode -> UnOpContext -> Node -> Node -> (UnOpContext, Node)
absorb_unary tm c dcR branch = naiveAbsorb tm c dcR branch

absorb_dc_unary :: TraversalMode -> UnOpContext -> Node -> (UnOpContext, Node)
absorb_dc_unary tm c dcR = absorb_unary tm c (outerDcR (drop 1 (un_dc_stack c))) dcR

pop_level_ :: UnOpContext -> (UnOpContext, Inf)
pop_level_ ctx =
    let (_ : lv@(_, inf) : lvs') = un_current_level ctx
    in (ctx { un_current_level = lv : lvs' }, inf)


traverse_dc_unary :: TraversalMode -> Move -> UnOpContext -> NodeId -> UnOpContext
traverse_dc_unary tm s c d =
    let ref = getNode c d
    in case snd ref of
        Leaf{} -> c
        _      -> let new_dcRs = map (traverse_dc_generic tm s c ref) (un_dc_stack c)
                      c' = c { un_dc_stack = new_dcRs }
                  in debug_dc_traverse_unary (show s) (tmName tm) c d c'

-- | Wrap a traversal result in EndClassNode, applying the elimination rule @a.
wrapEndClass :: TraversalMode -> (UnOpContext, Node) -> (UnOpContext, Node)
wrapEndClass tm (c', r) = tmApplyElimRule tm c' $ EndClassNode (fst r)

-- | Exit the current class: sync dc_stack, pop the level, return (c_end, inf, c_after_pop).
exitClass :: UnOpContext -> NodeId -> (UnOpContext, Inf, UnOpContext)
exitClass c absingBId =
    let c_end       = traverse_dc_unary modeDc ExitClass c absingBId
        (c_, inf)   = pop_level_ c_end
    in (c_end, inf, c_)

-- | Infer a ClassNode wrapper for `branch` using rule @a, then call cont with absingB fixed.
inferClassBranch :: forall r. TraversalMode -> UnOpContext -> Int -> Node -> Node -> (UnOpContext -> Node -> Node -> r) -> r
inferClassBranch tm c pos absingB branch cont =
    let (c', b') = tmInferClassNode tm c pos branch
    in cont c' absingB b'

-- | Infer a ClassNode wrapper for `absingB` using @Dc, then call cont with branch fixed.
inferClassAbsing :: forall r. UnOpContext -> Int -> Node -> Node
    -> (UnOpContext -> Node -> Node -> r) -> r
inferClassAbsing c pos absingB branch cont =
    let (c', a') = tmInferClassNode modeDc c pos absingB
    in cont c' a' branch

-- | Traverse an absorbing Node's children according to the inference context, applying f.
travNodeAbs :: TraversalMode -> UnOpContext -> Node -> Node -> (UnOpContext -> Node -> Node -> (UnOpContext, Node)) -> (UnOpContext, Node)
travNodeAbs tm c absingB@(absingBId, Node dcPos dcP dcN) branch f
    | tmIsNeg tm =
        let c_ = traverse_dc_unary modeDc MvNeg c absingBId
        in f c_ (getNode c dcN) branch
    | tmIsPos tm =
        let c_ = traverse_dc_unary modeDc MvPos c absingBId
        in f c_ (getNode c dcP) branch
    | otherwise =  -- Dc: traverse both children
        let c_p = traverse_dc_unary modeDc MvPos c absingBId
            (c',  r1) = f c_p (getNode c dcP) branch
            c_n = traverse_dc_unary modeDc MvNeg (reset_stack_un c' c) absingBId
            (c'', r2) = f c_n (getNode c dcN) branch
        in tmApplyElimRule tm (reset_stack_un c'' c) $ Node dcPos (fst r1) (fst r2)
travNodeAbs _ _ _ _ _ = error "travNodeAbs: absingB must be a Node constructor"

-- | Traverse a tested branch's node
-- synchronise via @b, recurse with absPos/absNeg as left args, recombine via @a.
travNodeStep :: TraversalMode -> TraversalMode -> UnOpContext -> NodeId -> Node -> Node -> Node -> (UnOpContext -> Node -> Node -> (UnOpContext, Node)) -> (UnOpContext, Node)
travNodeStep tmb tma c refId absPos absNeg branch@(_, Node pos p n) f =
    let c_p = traverse_dc_unary tmb MvPos c refId
        (c',  r1) = f c_p absPos (getNode c p)
        c_n = traverse_dc_unary tmb MvNeg (reset_stack_un c' c) refId
        (c'', r2) = f c_n absNeg (getNode c n)
    in tmApplyElimRule tma (reset_stack_un c'' c) $ Node pos (fst r1) (fst r2)
travNodeStep _ _ _ _ _ _ _ _ = error "travNodeStep: branch must be a Node constructor"

-- | Step the branch Node with @a; absingB is fixed on both branches.
travNodeBranch :: TraversalMode -> UnOpContext -> Node -> Node -> (UnOpContext -> Node -> Node -> (UnOpContext, Node)) -> (UnOpContext, Node)
travNodeBranch tm c absingB branch@(branchId, _) = travNodeStep tm tm c branchId absingB absingB branch

-- | Step both Nodes at matching positions; absorbing Node uses @Dc.
travNodeBoth :: TraversalMode -> UnOpContext -> Node -> Node -> (UnOpContext -> Node -> Node -> (UnOpContext, Node)) -> (UnOpContext, Node)
travNodeBoth tm c absingB@(absingBId, Node _ dcP dcN) branch f = travNodeStep modeDc tm c absingBId (getNode c dcP) (getNode c dcN) branch f
travNodeBoth _ _ _ _ _ = error "travNodeBoth: absingB must be a Node constructor"

-- | Traverse matching ClassNodes at the same position; absingB uses @Dc, branch uses @a.
-- Takes three callbacks — one per branch type — because each must be called with a different
-- type-level inference parameter (@Dc, @Pos, @Neg) that cannot be abstracted as a value.
travClassBoth :: TraversalMode -> UnOpContext -> Node -> Node -> (UnOpContext -> Node -> Node -> (UnOpContext, Node)) -> (UnOpContext -> Node -> Node -> (UnOpContext, Node)) -> (UnOpContext -> Node -> Node -> (UnOpContext, Node)) -> (UnOpContext, Node)
travClassBoth tm c absingB@(absingBId, ClassNode _ dcD dcP dcN) branch@(_, ClassNode pos d p n) fDc fPos fNeg =
    let c_dc = traverse_dc_unary modeDc MvClassDc c absingBId
        c_   = add_to_stack_ (pos, Dc)  (getNode c_dc dcD, ((0,0), Unknown)) c_dc
        (c1, rD) = fDc c_ (getNode c_dc dcD) (getNode c_dc d)
        c1'  = reset_stack_un c1 c
        c_p  = traverse_dc_unary modeDc MvClassPos c1' absingBId
        c2_  = add_to_stack_ (pos, Pos) (getNode c_p dcD, rD) c_p
        (c2, rP) = fPos c2_ (getNode c_p dcP) (getNode c_p p)
        c2'  = reset_stack_un c2 c
        c_n  = traverse_dc_unary modeDc MvClassNeg c2' absingBId
        c3_  = add_to_stack_ (pos, Neg) (getNode c_n dcD, rD) c_n
        (c3, rN) = fNeg c3_ (getNode c_n dcN) (getNode c_n n)
    in tmApplyElimRule tm (reset_stack_un c3 c) $ ClassNode pos (fst rD) (fst rP) (fst rN)
travClassBoth _ _ _ _ _ _ _ = error "travClassBoth: both arguments must be ClassNode constructors"