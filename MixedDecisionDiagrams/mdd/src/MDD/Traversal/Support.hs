{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE AllowAmbiguousTypes #-}   -- Required to allow methods where the class type variable 'a' is not in the signature
{-# LANGUAGE FlexibleInstances #-}     -- Required for the instance Dd1_helper a
{-# LANGUAGE UndecidableInstances #-}  -- Required because the constraint DdF3 a is not smaller than the head Dd1_helper a
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE InstanceSigs #-}

module MDD.Traversal.Support where

import MDD.Types
import MDD.Traversal.Context
import MDD.Traversal.Stack
import MDD.Extra.Draw (debug_dc_traverse, debug_naiveAbsorb_open, debug_naiveAbsorb_close, myTrace)

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

applyElimRule' :: forall a. (DdF3 a) => (UnOpContext, Dd) -> (UnOpContext, Node)
applyElimRule' (c, d) = applyElimRule @a c d





absorb :: forall a. (DdF3 a) => BiOpContext -> Int -> Node -> Node -> (BiOpContext, Node)
absorb c positionA dcR branch =
    let (_, _, outerDcRs) = bin_dc_stack c
        unCtx = (binaryToUnaryContext c) { un_dc_stack = dcR : outerDcRs }
        (unCtx', branch') = myTrace (debug_naiveAbsorb_open (to_str @a ++ " pos=" ++ show positionA) unCtx dcR branch) $
                            let r@(uc, n) = naiveAbsorb @a unCtx dcR branch
                            in myTrace (debug_naiveAbsorb_close (to_str @a ++ " pos=" ++ show positionA) uc dcR branch n) r
    in (unaryToBinaryContext unCtx' c, branch')

-- | Absorb dcR against the outer dcR from the stack.
absorb_dc :: forall a. (DdF3 a) => BiOpContext -> Int -> Node -> (BiOpContext, Node)
absorb_dc c positionA dcR =
    let (_, _, outerDcRs) = bin_dc_stack c
        outerDcR = case outerDcRs of { (h : _) -> h; [] -> ((0,0), Unknown) }
    in absorb @a c positionA outerDcR dcR


absorb_unary :: forall a. (DdF3 a) => UnOpContext -> Node -> Node -> (UnOpContext, Node)
absorb_unary c dcR branch = naiveAbsorb @a c dcR branch

absorb_dc_unary :: forall a. (DdF3 a) => UnOpContext -> Node -> (UnOpContext, Node)
absorb_dc_unary c dcR =
    let outerDcR = case un_dc_stack c of { (_ : outer : _) -> outer; _ -> ((0,0), Unknown) }
    in absorb_unary @a c outerDcR dcR


-- * Naive Absorb Implementation
-- Naive absorb minimizes pos/neg branches of a class w.r.t. the class' resulting dc branch.
-- It does a simultaneous depth-first traversal of the pos/neg branch with the local dcR.
-- At EndClassNode boundaries of the local class, an equality check determines absorption.
-- When entering a nested class, a non-absorbing traversal is used until returning to the
-- original class level. The dcR stack is kept up-to-date during traversal.

-- | Core naive absorb: simultaneous traversal of pos/neg branch and dcR within the local class. Recurses depth-first; at EndClassNode of the current local class, checks equality for absorbtion or not.
naiveAbsorb :: forall a. (DdF3 a) => UnOpContext -> Node -> Node -> (UnOpContext, Node)

-- Already absorbed (Unknown in branch means it was previously set to dc)
naiveAbsorb c _dcR branch@(_, Unknown) = (c, branch)
-- EndClassNode vs EndClassNode: local class boundary — check equality - otherwise no absorb will happen
naiveAbsorb c dcR@(_, EndClassNode dcChild) branch@(_, EndClassNode branchChild)
    | branch == dcR = (c, ((0,0), Unknown))
    | otherwise = (c, branch)
-- Leaf vs Leaf: direct comparison at the (implicit) class boundary
naiveAbsorb c dcR@(_, Leaf _) branch@(_, Leaf _)
    | branch == dcR = (c, ((0,0), Unknown))
    | otherwise     = (c, branch)

-- dcR is Unknown: resolve it from the outer dcR stack
naiveAbsorb c (_, Unknown) branch =
    case un_dc_stack c of
        (_ : outer : rest) -> naiveAbsorb @a (c { un_dc_stack = outer : rest }) outer branch
        _                  -> (c, branch)

-- Node one, Leaf in other: the Leaf implicitly has the Node's variable resolved through the inference rule. Infer to reach the Leaf's level.
naiveAbsorb c dcR@(_, Node dcPos dcP dcN) branch@(_, Leaf _) =
    case to_str @a of
        "Neg" -> naiveAbsorb @a c (getNode c dcN) branch
        "Pos" -> naiveAbsorb @a c (getNode c dcP) branch
        _     -> let (c',  r1) = naiveAbsorb @a c  (getNode c dcP) branch
                     (c'', r2) = naiveAbsorb @a c' (getNode c dcN) branch
                     absorbed = applyElimRule @a c'' $ Node dcPos (fst r1) (fst r2)
                 in if snd absorbed == dcR then (fst absorbed, ((0,0), Unknown)) else absorbed
naiveAbsorb c dcR@(_, Leaf _) branch@(_, Node pos p n) =
    -- because dcR has dc rule we do not have to explicitly infer nodes for it
    let (c',  r1) = naiveAbsorb @a c  dcR (getNode c p)
        (c'', r2) = naiveAbsorb @a c' dcR (getNode c n)
        absorbed = applyElimRule @a c'' $ Node pos (fst r1) (fst r2)
    in if snd absorbed == dcR then (fst absorbed, ((0,0), Unknown)) else absorbed

-- Leaf implicitly has EndClassNodes for all outer classes
naiveAbsorb c dcR@(_, EndClassNode dcChild) branch@(_, Leaf _) =
    let (c', branchWrapped) = insert c (EndClassNode (fst branch))
    in naiveAbsorb @a c' dcR branchWrapped
naiveAbsorb c dcR@(_, Leaf _) branch@(_, EndClassNode branchChild) =
    let (c', dcRWrapped) = insert c (EndClassNode (fst dcR))
    in naiveAbsorb @a c' dcRWrapped branch
naiveAbsorb c dcR@(_, Leaf _) branch@(_, ClassNode pos d p n) =
    let (c', dcRInferred) = inferClassNode @a c pos dcR
    in naiveAbsorb @a c' dcRInferred branch
naiveAbsorb c dcR@(_, ClassNode dcPos _ _ _) branch@(_, Leaf _) =
    let (c', branchInferred) = inferClassNode @a c dcPos branch
    in naiveAbsorb @a c' dcR branchInferred


-- === Node vs Node ===: simultaneous traversal of matching variable positions
naiveAbsorb c dcR@(_, Node dcPos dcP dcN) branch@(_, Node pos p n)
    | branch == dcR = (c, ((0,0), Unknown))
    | dcPos == pos =
        let (c',  r1) = naiveAbsorb @a c  (getNode c dcP) (getNode c p)
            (c'', r2) = naiveAbsorb @a c' (getNode c dcN) (getNode c n)
            absorbed = applyElimRule @a c'' $ Node pos (fst r1) (fst r2)
        in if snd absorbed == dcR then (fst absorbed, ((0,0), Unknown)) else absorbed
    | dcPos < pos =
        case to_str @a of
            "Neg" -> naiveAbsorb @a c (getNode c dcN) branch
            "Pos" -> naiveAbsorb @a c (getNode c dcP) branch
            _     -> let (c',  r1) = naiveAbsorb @a c  (getNode c dcP) branch
                         (c'', r2) = naiveAbsorb @a c' (getNode c dcN) branch
                         absorbed = applyElimRule @a c'' $ Node dcPos (fst r1) (fst r2)
                     in if snd absorbed == dcR then (fst absorbed, ((0,0), Unknown)) else absorbed
    | dcPos > pos =
        let (c',  r1) = naiveAbsorb @a c  dcR (getNode c p)
            (c'', r2) = naiveAbsorb @a c' dcR (getNode c n)
            absorbed = applyElimRule @a c'' $ Node pos (fst r1) (fst r2)
        in if snd absorbed == dcR then (fst absorbed, ((0,0), Unknown)) else absorbed

-- === Node vs EndClassNode ===
naiveAbsorb c dcR@(_, Node dcPos dcP dcN) branch@(_, EndClassNode _) =
    case to_str @a of
        "Neg" -> naiveAbsorb @a c (getNode c dcN) branch
        "Pos" -> naiveAbsorb @a c (getNode c dcP) branch
        _     -> let (c',  r1) = naiveAbsorb @a c  (getNode c dcP) branch
                     (c'', r2) = naiveAbsorb @a c' (getNode c dcN) branch
                     absorbed = applyElimRule @a c'' $ Node dcPos (fst r1) (fst r2)
                 in if snd absorbed == dcR then (fst absorbed, ((0,0), Unknown)) else absorbed
-- because dcR has dc rule we do not have to explicitly infer nodes for it
naiveAbsorb c dcR@(_, EndClassNode _) branch@(_, Node pos p n) =
    let (c',  r1) = naiveAbsorb @a c  dcR (getNode c p)
        (c'', r2) = naiveAbsorb @a c' dcR (getNode c n)
        absorbed = applyElimRule @a c'' $ Node pos (fst r1) (fst r2)
    in if snd absorbed == dcR then (fst absorbed, ((0,0), Unknown)) else absorbed

-- === ClassNode in branch and dcR ===
-- Switch to non-absorbing simultaneous traversal (with elimination rules)
-- until the same class level is reached again, then absorption continues.
--
naiveAbsorb c dcR@(_, ClassNode dcPos dcD dcP dcN) branch@(_, ClassNode pos d p n)
    | branch == dcR = (c, ((0,0), Unknown))
    | dcPos == pos =
        let (c1, rD) = naiveTraverse @Dc  1 c  (getNode c dcD) (getNode c d)
            (c2, rP) = naiveTraverse @Pos 1 c1 (getNode c dcP) (getNode c p)
            (c3, rN) = naiveTraverse @Neg 1 c2 (getNode c dcN) (getNode c n)
        in applyElimRule @a c3 $ ClassNode pos (fst rD) (fst rP) (fst rN)
    | dcPos > pos =
        let (c', branchInferred) = inferClassNode @a c dcPos branch
        in naiveAbsorb @a c' dcR branchInferred
    | dcPos < pos =
        let (c', dcRInferred) = inferClassNode @a c pos dcR
        in naiveAbsorb @a c' dcRInferred branch

naiveAbsorb c dcR@(_, ClassNode dcPos _ _ _) branch@(_, EndClassNode _) =
    let (c', branchInferred) = inferClassNode @a c dcPos branch
    in naiveAbsorb @a c' dcR branchInferred
naiveAbsorb c dcR@(_, EndClassNode _) branch@(_, ClassNode pos _ _ _) =
    let (c', dcRInferred) = inferClassNode @a c pos dcR
    in naiveAbsorb @a c' dcRInferred branch

-- === Node in dcR, ClassNode in branch ===
naiveAbsorb c dcR@(_, Node _ _ _) branch@(_, ClassNode _ _ _ _) = error "should not happen: node vs class node in absorb"
naiveAbsorb c dcR@(_, ClassNode dcPos _ _ _) branch@(_, Node _ _ _) =
    error "naiveAbsorb: ClassNode dcR vs Node branch should not happen"

-- | Simultaneous traversal without absorption for nested classes.
-- Walks dcR and branch in lockstep, creating new nodes with elimination rules applied,
-- but never replacing nodes with Unknown.
--
-- The Int parameter tracks nesting depth relative to where naiveAbsorb handed off.
-- At depth 0, the next EndClassNode exit returns to the absorbing class level,
-- so we hand back to naiveAbsorb. At depth > 0, we are still inside deeper nested
-- classes, so EndClassNode decrements depth and ClassNode increments it.
naiveTraverse :: forall a. (DdF3 a) => Int -> UnOpContext -> Node -> Node -> (UnOpContext, Node)

naiveTraverse _ c _ branch@(_, Unknown) = (c, branch)
naiveTraverse _ c (_, Unknown) branch = (c, branch)

naiveTraverse depth c dcR@(_, EndClassNode dcChild) branch@(_, Leaf _)
    | depth == 1 = naiveAbsorb @a c (getNode c dcChild) branch
    | otherwise  = naiveTraverse @a (depth - 1) c (getNode c dcChild) branch
naiveTraverse depth c dcR@(_, Node dcPos dcP dcN) branch@(_, Leaf _) =
    case to_str @a of
        "Neg" -> naiveTraverse @a depth c (getNode c dcN) branch
        "Pos" -> naiveTraverse @a depth c (getNode c dcP) branch
        _     -> let (c',  r1) = naiveTraverse @a depth c  (getNode c dcP) branch
                     (c'', r2) = naiveTraverse @a depth c' (getNode c dcN) branch
                 in applyElimRule @a c'' $ Node dcPos (fst r1) (fst r2)
naiveTraverse _ c _ branch@(_, Leaf _) = (c, branch)

-- === EndClassNode: exiting a class ===
-- depth == 1: about to go back at the absorbing class level — hand to naiveAbsorb
-- depth > 1: still inside a deeper nested class — stay in naiveTraverse
naiveTraverse depth c dcR@(_, EndClassNode dcChild) branch@(_, EndClassNode branchChild)
    | depth == 1 =
        let (c', r) = naiveAbsorb @a c (getNode c dcChild) (getNode c branchChild)
        in applyElimRule @a c' $ EndClassNode (fst r)
    | otherwise =
        let (c', r) = naiveTraverse @a (depth - 1) c (getNode c dcChild) (getNode c branchChild)
        in applyElimRule @a c' $ EndClassNode (fst r)
naiveTraverse depth c dcR@(_, Leaf _) branch@(_, EndClassNode branchChild)
    | depth == 1 =
        let (c', r) = naiveAbsorb @a c dcR (getNode c branchChild)
        in applyElimRule @a c' $ EndClassNode (fst r)
    | otherwise =
        let (c', r) = naiveTraverse @a (depth - 1) c dcR (getNode c branchChild)
        in applyElimRule @a c' $ EndClassNode (fst r)
naiveTraverse depth c dcR@(_, Node dcPos dcP dcN) branch@(_, EndClassNode branchChild) =
    case to_str @a of
        "Neg" -> naiveTraverse @a depth c (getNode c dcN) branch
        "Pos" -> naiveTraverse @a depth c (getNode c dcP) branch
        _     -> let (c',  r1) = naiveTraverse @a depth c  (getNode c dcP) branch
                     (c'', r2) = naiveTraverse @a depth c' (getNode c dcN) branch
                 in applyElimRule @a c'' $ Node dcPos (fst r1) (fst r2)


naiveTraverse depth c dcR@(_, EndClassNode _) branch@(_, Node pos p n) =
    let (c',  r1) = naiveTraverse @a depth c  dcR (getNode c p)
        (c'', r2) = naiveTraverse @a depth c' dcR (getNode c n)
    in applyElimRule @a c'' $ Node pos (fst r1) (fst r2)

-- === Node vs Node: simultaneous traversal (same class level) ===
naiveTraverse depth c dcR@(_, Node dcPos dcP dcN) branch@(_, Node pos p n)
    | dcPos == pos =
        let (c',  r1) = naiveTraverse @a depth c  (getNode c dcP) (getNode c p)
            (c'', r2) = naiveTraverse @a depth c' (getNode c dcN) (getNode c n)
        in applyElimRule @a c'' $ Node pos (fst r1) (fst r2)
    | dcPos < pos =
        case to_str @a of
            "Neg" -> naiveTraverse @a depth c (getNode c dcN) branch
            "Pos" -> naiveTraverse @a depth c (getNode c dcP) branch
            _     -> let (c',  r1) = naiveTraverse @a depth c  (getNode c dcP) branch
                         (c'', r2) = naiveTraverse @a depth c' (getNode c dcN) branch
                     in applyElimRule @a c'' $ Node dcPos (fst r1) (fst r2)
    | dcPos > pos =
        let (c',  r1) = naiveTraverse @a depth c  dcR (getNode c p)
            (c'', r2) = naiveTraverse @a depth c' dcR (getNode c n)
        in applyElimRule @a c'' $ Node pos (fst r1) (fst r2)

naiveTraverse depth c dcR@(_, Leaf _) branch@(_, Node pos p n) =
    let (c',  r1) = naiveTraverse @a depth c  dcR (getNode c p)
        (c'', r2) = naiveTraverse @a depth c' dcR (getNode c n)
    in applyElimRule @a c'' $ Node pos (fst r1) (fst r2)
-- === ClassNode: entering a deeper nested class (depth + 1) ===
naiveTraverse depth c dcR@(_, ClassNode dcPos dcD dcP dcN) branch@(_, ClassNode pos d p n)
    | dcPos == pos =
        let (c1, rD) = naiveTraverse @Dc  (depth + 1) c  (getNode c dcD) (getNode c d)
            (c2, rP) = naiveTraverse @Pos (depth + 1) c1 (getNode c dcP) (getNode c p)
            (c3, rN) = naiveTraverse @Neg (depth + 1) c2 (getNode c dcN) (getNode c n)
        in applyElimRule @a c3 $ ClassNode pos (fst rD) (fst rP) (fst rN)
    | dcPos > pos =
        let (c', branchInferred) = inferClassNode @a c dcPos branch
        in naiveTraverse @a depth c' dcR branchInferred
    | dcPos < pos =
        let (c', dcRInferred) = inferClassNode @a c pos dcR
        in naiveTraverse @a depth c' dcRInferred branch

naiveTraverse depth c dcR@(_, Node _ _ _) branch@(_, ClassNode pos _ _ _) = error "should not happen: node vs class node in naiveTraverse"
naiveTraverse depth c dcR@(_, EndClassNode _) branch@(_, ClassNode pos _ _ _) =
    let (c', dcRInferred) = inferClassNode @a c pos dcR
    in naiveTraverse @a depth c' dcRInferred branch
naiveTraverse depth c dcR@(_, Leaf _) branch@(_, ClassNode pos _ _ _) =
    let (c', dcRInferred) = inferClassNode @a c pos dcR
    in naiveTraverse @a depth c' dcRInferred branch
naiveTraverse depth c dcR@(_, ClassNode dcPos dcD dcP dcN) branch@(_, Node _ _ _) = error "should not happen: class node vs node in naiveTraverse"
naiveTraverse depth c dcR@(_, ClassNode dcPos dcD dcP dcN) branch@(_, EndClassNode _) =
    let (c', branchInferred) = inferClassNode @a c dcPos branch
    in naiveTraverse @a depth c' dcR branchInferred


instance DdF3 Dc where
    inferNodeA f c s a (_, Node positionB pos_childB neg_childB) =
        let (c', (pos_result, _)) = f c s a (getNode c pos_childB)
            (c'', (neg_result, _)) = f c' s a (getNode c neg_childB)
        in (c'', Node positionB pos_result neg_result)

    inferNodeB f c s (_, Node positionA pos_childA neg_childA) b =
        -- trace ("inferB at : " ++ show positionA
        --     ++ " \n posA: " ++ show_node c (getNode c pos_childA)
        --     ++ " \n neg: " ++ show_node c (getNode c neg_childA)) (
            let
                (c', (pos_result, _)) = f c s (getNode c pos_childA) b
                (c'', (neg_result, _)) = f c' s (getNode c neg_childA) b
            in (c'', Node positionA pos_result neg_result)


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
        EndClassNode _ -> (c, getNode c r)
        _ -> insert c d
    applyElimRule c d = insert c d

    inferNode :: HasNodeLookup c => c -> Int -> Node -> (c, Node)
    inferNode c position (n_id, n) = insert c (Node position n_id n_id)
    inferClassNode c position (n_id, n) = insert c $ ClassNode position n_id (0,0) (0,0)
    catchup _ n _ = n
    to_str = "Dc"

-- | Instance for Pos (Positive literal) inference/elimination rule.
instance DdF3 Pos where
    -- | Pos rule: Create a Node with pos branch = a_id, neg branch = (0,0) (Unknown).
    inferNodeA f c s a@(a_id, _) b@(b_id, Node positionB _ _) =
        let (c', r) = insert c (Node positionB a_id (0,0))
            (c'', (r_node_id, _)) = f c' s r (getNode c' b_id)
        in (c'', getDd c'' r_node_id)

    inferNodeB f c s a@(a_id, Node positionA _ _) b@(b_id, _) =
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
        EndClassNode _ -> (c, getNode c r)
        _ -> insert c d
    applyElimRule c d = insert c d


    -- pos node inference
    inferNode c position (n_id, n) = insert c (Node position n_id (0,0))
    -- pos class node inference
    inferClassNode c position (n_id, n) = insert c $ ClassNode position (0,0) n_id (0,0)

    catchup c n@(_, Node positionA pos_child _) idx
        | idx == -1       = catchup @Pos c (getNode c pos_child) idx
        | idx > positionA = catchup @Pos c (getNode c pos_child) idx
        | otherwise = n
    catchup _ n _ = n
    to_str = "Pos"

-- | Instance for Neg (Negative literal) inference/elimination rule.
instance DdF3 Neg where
    -- | Neg rule: Create a Node with pos branch = (0,0) (Unknown), neg branch = a_id.
    inferNodeA f c s a@(a_id, _) b@(b_id, Node positionB _ _) =
        let (c', r) = insert c (Node positionB (0,0) a_id)  -- pos=Unknown, neg=a_id
            (c'', (r_node_id, _)) = f c' s r (getNode c' b_id)
        in (c'', getDd c'' r_node_id)
    inferNodeB f c s a@(a_id, Node positionA _ _) b@(b_id, _) =
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
        EndClassNode _ -> (c, getNode c r)
        _ -> insert c d
    applyElimRule c d = insert c d


    inferNode c position (n_id, n) = insert c (Node position (0,0) n_id)
    inferClassNode c position (n_id, n) = insert c $ ClassNode position (0,0) (0,0) n_id

    catchup c n@(_, Node positionA _ neg_child) idx
        | idx == -1       = catchup @Neg c (getNode c neg_child) idx
        | idx > positionA = catchup @Neg c (getNode c neg_child) idx
        | otherwise = n
    catchup _ n _ = n
    to_str = "Neg"

-- | Traversal Helper (Dd1_helper).
-- This typeclass provides functions to synchronize the dc_stack traversal with the main  MDD traversal.
-- When the main traversal skips variables (due to elimination rules), the dc_stack needs to "catch up" to stay synchronized.
class Dd1_helper (a :: Inf) where
    traverse_dc :: String -> BiOpContext -> NodeId -> NodeId -> BiOpContext

instance (DdF3 a) => Dd1_helper a where
    -- | Synchronizes the entire dc_stack with the main traversal.
    traverse_dc s c a b = debug_dc_traverse s c a b $
            let (dcAs, dcBs, dcRs) = (bin_dc_stack c)
                refA = getNode c a
                refB = getNode c b
                isLeaf (_, Leaf{}) = True
                isLeaf _           = False
                new_dcAs = if isLeaf refA then dcAs else map (traverse_dc_generic (catchup @a) (to_str @a) s c refA) dcAs
                new_dcBs = if isLeaf refB then dcBs else map (traverse_dc_generic (catchup @a) (to_str @a) s c refB) dcBs
                new_dcRs = if isLeaf refA then dcRs else map (traverse_dc_generic (catchup @a) (to_str @a) s c refA) dcRs
            in c { bin_dc_stack = (new_dcAs, new_dcBs, new_dcRs) }
