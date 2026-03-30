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
import MDD.Extra.Draw (debug_dc_traverse)
import Debug.Trace (trace)

-- *| Shared code for traversal functions (from Unary and Binary).

-- | Elimination and Inference rule typeclass (DdF3).
-- |
-- | This typeclass defines the inference and elimination rules for the three inference types: Dc, Neg, Pos
-- | Each instance implements:
-- |   - infer(Inf)NodeA/infer(Inf)NodeB: Create inferred nodes when one argument is missing a variable at the lowest position of the two
-- |   - applyElimRule: Apply the elimination rule to remove redundant nodes
-- |   - catchup: Synchronize dc_stack traversal when main traversal skips variables
class DdF3 (a :: Inf) where
    -- | Infers a node for Argument A when Argument B is at a lower position.
    inferNodeA :: (BiOpContext -> String -> Node -> Node -> (BiOpContext, Node))
               -> BiOpContext -> String -> Node -> Node -> (BiOpContext, Dd)
    -- | Infers a node for Argument B when Argument A is at a lower position.
    inferNodeB :: (BiOpContext -> String -> Node -> Node -> (BiOpContext, Node))
               -> BiOpContext -> String -> Node -> Node -> (BiOpContext, Dd)

    applyElimRule :: (HasNodeLookup c) => c -> Dd -> (c, Node)
    inferNode :: (HasNodeLookup c) => c -> Int -> Node -> (c, Node)
    inferClassNode :: (HasNodeLookup c) => c -> Int -> Node -> (c, Node)
    catchup :: (HasNodeLookup c) => String -> c -> Node -> Int -> Node
    to_str :: String

applyElimRule' :: forall a. (DdF3 a) => (UnOpContext, Dd) -> (UnOpContext, Node)
applyElimRule' (c, d) = applyElimRule @a c d



-- * Redundancy Elimination (absorb)

-- | Absorb is a unary MDD manipulation
-- | The absorb function maintains canonical representation by eliminating redundant branches.

-- | Calling this from a binary operator function needs a context adjustment
absorb :: forall a. (DdF3 a) => (BiOpContext, Node) -> (BiOpContext, Node)
absorb (c, n) =
    let
        unaryCtx = binaryToUnaryContext c
        (unaryCtx', n') = absorb_unary @a (unaryCtx, n)
    in
        (unaryToBinaryContext unaryCtx' c, n')


-- | Main entry point for the absorb function for unary operations.
absorb_unary :: forall a. (DdF3 a) => (UnOpContext, Node) -> (UnOpContext, Node)
absorb_unary (c, n) = absorb' @a (c, n)


-- * Naive Absorb Implementation
--
-- Naive absorb minimizes pos/neg branches of a class w.r.t. the class' resulting dc branch.
-- It does a simultaneous depth-first traversal of the pos/neg branch with the local dcR.
-- At EndClassNode boundaries of the local class, an equality check determines absorption.
-- When entering a nested class, a non-absorbing traversal is used until returning to the
-- original class level. The dcR stack is kept up-to-date during traversal.
--
-- The non-naive (old) version tried to absorb on multiple levels simultaneously.

absorb' :: forall a. (DdF3 a) => (UnOpContext, Node) -> (UnOpContext, Node)
absorb' (c, branch) =
    let dcR_stack = un_dc_stack c
    in case dcR_stack of
        []       -> (c, branch)
        (dcR : _) -> naiveAbsorb @a c dcR branch

-- | Core naive absorb: simultaneous traversal of branch and dcR within the local class.
-- Recurses depth-first; at EndClassNode of the local class, checks equality.
--
-- Key principle: A Leaf Bool implicitly has a chain of EndClassNodes before it for
-- every active class level. These are normally eliminated (EndClassNode(Leaf _) -> Leaf _).
-- During simultaneous traversal, when one side is a Leaf and the other crosses a class
-- boundary, the Leaf is treated as crossing that boundary with the same value.
naiveAbsorb :: forall a. (DdF3 a) => UnOpContext -> Node -> Node -> (UnOpContext, Node)

-- Already absorbed (Unknown in branch means it was previously set to dc)
naiveAbsorb c _dcR branch@(_, Unknown) = (c, branch)

-- dcR is Unknown: resolve it from the outer dcR stack
naiveAbsorb c (_, Unknown) branch =
    case un_dc_stack c of
        (_ : outer : rest) -> naiveAbsorb @a (c { un_dc_stack = outer : rest }) outer branch
        _                  -> (c, branch)

-- === EndClassNode vs EndClassNode: local class boundary — check equality ===
naiveAbsorb c dcR@(_, EndClassNode dcChild) branch@(_, EndClassNode branchChild)
    | branch == dcR = (c, ((0,0), Unknown))
    | otherwise =
        let (c', r) = naiveAbsorb @a c (getNode c dcChild) (getNode c branchChild)
        in case snd r of
            Unknown -> (c', ((0,0), Unknown))
            _       -> insert c' (EndClassNode (fst r))

-- === Leaf in branch: implicitly has EndClassNodes for all active classes ===
-- Unwrap dcR's EndClassNode (the Leaf passes through it implicitly).
naiveAbsorb c dcR@(_, EndClassNode dcChild) branch@(_, Leaf _) =
    naiveAbsorb @a c (getNode c dcChild) branch
-- Leaf vs Leaf: direct comparison at the (implicit) class boundary
naiveAbsorb c dcR@(_, Leaf _) branch@(_, Leaf _)
    | branch == dcR = (c, ((0,0), Unknown))
    | otherwise     = (c, branch)
-- Node in dcR, Leaf in branch: the Leaf implicitly has the Node's variable
-- resolved through the inference rule. Infer dcR to reach the Leaf's level.
naiveAbsorb c dcR@(_, Node dcPos dcP dcN) branch@(_, Leaf _) =
    let dcChild = case to_str @a of
            "Neg" -> getNode c dcN
            "Pos" -> getNode c dcP
            _     -> getNode c dcP
    in naiveAbsorb @a c dcChild branch
-- ClassNode in dcR, Leaf in branch: structural mismatch.
-- The Leaf is at a higher level; it doesn't have dcR's nested class.
naiveAbsorb c dcR@(_, ClassNode _ _ _ _) branch@(_, Leaf _) = (c, branch)

-- === Leaf in dcR: constant within this class ===
-- Traverse branch depth-first; compare at every terminal.
naiveAbsorb c dcR@(_, Leaf _) branch@(_, Node pos p n) =
    let (c',  r1) = naiveAbsorb @a c  dcR (getNode c p)
        (c'', r2) = naiveAbsorb @a c' dcR (getNode c n)
        absorbed = applyElimRule @a c'' $ Node pos (fst r1) (fst r2)
    in if snd absorbed == dcR then (fst absorbed, ((0,0), Unknown)) else absorbed
naiveAbsorb c dcR@(_, Leaf _) branch@(_, EndClassNode branchChild) =
    let (c', r) = naiveAbsorb @a c dcR (getNode c branchChild)
    in case snd r of
        Unknown -> (c', ((0,0), Unknown))
        _       -> let absorbed = applyElimRule @a c' $ EndClassNode (fst r)
                   in if snd absorbed == dcR then (fst absorbed, ((0,0), Unknown)) else absorbed
-- Leaf dcR vs ClassNode branch: the Leaf implicitly enters the nested class
-- (same value at all branches). Use naiveTraverse for the inner class.
naiveAbsorb c dcR@(_, Leaf _) branch@(_, ClassNode pos d p n) =
    let (c1, rD) = naiveTraverse @Dc  c  dcR (getNode c d)
        (c2, rP) = naiveTraverse @Pos c1 dcR (getNode c p)
        (c3, rN) = naiveTraverse @Neg c2 dcR (getNode c n)
        absorbed = applyElimRule @a c3 $ ClassNode pos (fst rD) (fst rP) (fst rN)
    in if snd absorbed == dcR then (fst absorbed, ((0,0), Unknown)) else absorbed

-- === Node vs Node: simultaneous traversal of matching variable positions ===
naiveAbsorb c dcR@(_, Node dcPos dcP dcN) branch@(_, Node pos p n)
    | branch == dcR = (c, ((0,0), Unknown))
    | dcPos == pos =
        let (c',  r1) = naiveAbsorb @a c  (getNode c dcP) (getNode c p)
            (c'', r2) = naiveAbsorb @a c' (getNode c dcN) (getNode c n)
            absorbed = applyElimRule @a c'' $ Node pos (fst r1) (fst r2)
        in if snd absorbed == dcR then (fst absorbed, ((0,0), Unknown)) else absorbed
    | dcPos > pos =
        let dcChild = case to_str @a of
                "Neg" -> getNode c dcN
                "Pos" -> getNode c dcP
                _     -> getNode c dcP
        in naiveAbsorb @a c dcChild branch
    | otherwise =
        let (c',  r1) = naiveAbsorb @a c  dcR (getNode c p)
            (c'', r2) = naiveAbsorb @a c' dcR (getNode c n)
            absorbed = applyElimRule @a c'' $ Node pos (fst r1) (fst r2)
        in if snd absorbed == dcR then (fst absorbed, ((0,0), Unknown)) else absorbed

-- === Node vs EndClassNode: one side exited the class, the other didn't ===
-- Node in dcR, EndClassNode in branch: branch exited class before dcR's variable.
-- The branch is structurally different from dcR at this level; keep it unchanged.
naiveAbsorb c dcR@(_, Node _ _ _) branch@(_, EndClassNode _) = (c, branch)
-- EndClassNode in dcR, Node in branch: dcR exited class before branch's variable.
naiveAbsorb c dcR@(_, EndClassNode _) branch@(_, Node pos p n) =
    let (c',  r1) = naiveAbsorb @a c  dcR (getNode c p)
        (c'', r2) = naiveAbsorb @a c' dcR (getNode c n)
        absorbed = applyElimRule @a c'' $ Node pos (fst r1) (fst r2)
    in if snd absorbed == dcR then (fst absorbed, ((0,0), Unknown)) else absorbed

-- === ClassNode in branch: entering a nested class ===
-- Switch to non-absorbing simultaneous traversal (with elimination rules)
-- until the same class level is reached again, then absorption continues.
naiveAbsorb c dcR branch@(_, ClassNode pos d p n)
    | branch == dcR = (c, ((0,0), Unknown))
    | otherwise = case snd dcR of
        ClassNode dcPos dcD dcP dcN | dcPos == pos ->
            let (c1, rD) = naiveTraverse @Dc  c  (getNode c dcD) (getNode c d)
                (c2, rP) = naiveTraverse @Pos c1 (getNode c dcP) (getNode c p)
                (c3, rN) = naiveTraverse @Neg c2 (getNode c dcN) (getNode c n)
                absorbed = applyElimRule @a c3 $ ClassNode pos (fst rD) (fst rP) (fst rN)
            in if snd absorbed == dcR then (fst absorbed, ((0,0), Unknown)) else absorbed
        -- dcR is EndClassNode: it exited the outer class, but branch enters a nested class.
        -- The EndClassNode's child is at the parent level; the Leaf/value implicitly enters
        -- the nested class with the same value at all branches.
        EndClassNode _ ->
            let (c1, rD) = naiveTraverse @Dc  c  dcR (getNode c d)
                (c2, rP) = naiveTraverse @Pos c1 dcR (getNode c p)
                (c3, rN) = naiveTraverse @Neg c2 dcR (getNode c n)
                absorbed = applyElimRule @a c3 $ ClassNode pos (fst rD) (fst rP) (fst rN)
            in if snd absorbed == dcR then (fst absorbed, ((0,0), Unknown)) else absorbed
        -- dcR is a Node or Leaf: it doesn't have a ClassNode at this position.
        -- The dcR value implicitly enters the nested class (same value at all branches).
        _ ->
            let (c1, rD) = naiveTraverse @Dc  c  dcR (getNode c d)
                (c2, rP) = naiveTraverse @Pos c1 dcR (getNode c p)
                (c3, rN) = naiveTraverse @Neg c2 dcR (getNode c n)
                absorbed = applyElimRule @a c3 $ ClassNode pos (fst rD) (fst rP) (fst rN)
            in if snd absorbed == dcR then (fst absorbed, ((0,0), Unknown)) else absorbed

-- === ClassNode in dcR but not in branch ===
-- Structural mismatch: dcR has a nested class that branch doesn't.
naiveAbsorb c (_, ClassNode _ _ _ _) branch = (c, branch)

-- === Node in dcR, ClassNode in branch ===
-- This shouldn't normally happen (ClassNode and Node are at different hierarchy levels),
-- but handle defensively.
naiveAbsorb c dcR@(_, Node _ _ _) branch@(_, ClassNode _ _ _ _) = (c, branch)


-- | Simultaneous traversal without absorption for nested classes.
-- Walks dcR and branch in lockstep, creating new nodes with elimination rules applied,
-- but never replacing nodes with Unknown. This ensures the structure is properly reduced
-- so that equality checks at the outer class level work correctly.
--
-- Same implicit-EndClassNode principle as naiveAbsorb: a Leaf implicitly has
-- EndClassNodes for every active class, so it crosses class boundaries transparently.
--
-- At EndClassNode boundaries (exiting the nested class), hands back to naiveAbsorb
-- since we've returned to the outer class level where absorption should resume.
naiveTraverse :: forall a. (DdF3 a) => UnOpContext -> Node -> Node -> (UnOpContext, Node)

naiveTraverse c _ branch@(_, Unknown) = (c, branch)
naiveTraverse c (_, Unknown) branch = (c, branch)

-- === Leaf in branch: implicitly crosses all class boundaries ===
naiveTraverse c _ branch@(_, Leaf _) = (c, branch)

-- === EndClassNode: exiting the nested class — hand back to naiveAbsorb ===
naiveTraverse c dcR@(_, EndClassNode dcChild) branch@(_, EndClassNode branchChild) =
    let (c', r) = naiveAbsorb @a c (getNode c dcChild) (getNode c branchChild)
    in applyElimRule @a c' $ EndClassNode (fst r)
-- Leaf dcR + EndClassNode branch: Leaf implicitly has EndClassNode, hand back to absorb
naiveTraverse c dcR@(_, Leaf _) branch@(_, EndClassNode branchChild) =
    let (c', r) = naiveAbsorb @a c dcR (getNode c branchChild)
    in applyElimRule @a c' $ EndClassNode (fst r)
-- EndClassNode dcR + Leaf branch: Leaf implicitly has EndClassNode, hand back to absorb
naiveTraverse c dcR@(_, EndClassNode dcChild) branch@(_, Leaf _) =
    naiveAbsorb @a c (getNode c dcChild) branch
-- Node dcR + EndClassNode branch: infer dcR through Node, then hand back to absorb
naiveTraverse c dcR@(_, Node dcPos dcP dcN) branch@(_, EndClassNode branchChild) =
    let dcChild = case to_str @a of
            "Neg" -> getNode c dcN
            "Pos" -> getNode c dcP
            _     -> getNode c dcP
        (c', r) = naiveAbsorb @a c dcChild (getNode c branchChild)
    in applyElimRule @a c' $ EndClassNode (fst r)
-- EndClassNode dcR + Node branch: dcR exited class, branch still has variables
naiveTraverse c dcR@(_, EndClassNode _) branch@(_, Node pos p n) =
    let (c',  r1) = naiveTraverse @a c  dcR (getNode c p)
        (c'', r2) = naiveTraverse @a c' dcR (getNode c n)
    in applyElimRule @a c'' $ Node pos (fst r1) (fst r2)

-- === Node vs Node: simultaneous traversal ===
naiveTraverse c dcR@(_, Node dcPos dcP dcN) branch@(_, Node pos p n)
    | dcPos == pos =
        let (c',  r1) = naiveTraverse @a c  (getNode c dcP) (getNode c p)
            (c'', r2) = naiveTraverse @a c' (getNode c dcN) (getNode c n)
        in applyElimRule @a c'' $ Node pos (fst r1) (fst r2)
    | dcPos > pos =
        let dcChild = case to_str @a of
                "Neg" -> getNode c dcN
                "Pos" -> getNode c dcP
                _     -> getNode c dcP
        in naiveTraverse @a c dcChild branch
    | otherwise =
        let (c',  r1) = naiveTraverse @a c  dcR (getNode c p)
            (c'', r2) = naiveTraverse @a c' dcR (getNode c n)
        in applyElimRule @a c'' $ Node pos (fst r1) (fst r2)

-- Leaf dcR + Node branch: Leaf is constant, traverse branch
naiveTraverse c dcR@(_, Leaf _) branch@(_, Node pos p n) =
    let (c',  r1) = naiveTraverse @a c  dcR (getNode c p)
        (c'', r2) = naiveTraverse @a c' dcR (getNode c n)
    in applyElimRule @a c'' $ Node pos (fst r1) (fst r2)
-- Node dcR + Leaf branch: Leaf implicitly has EndClassNode, infer dcR
naiveTraverse c dcR@(_, Node dcPos dcP dcN) branch@(_, Leaf _) =
    let dcChild = case to_str @a of
            "Neg" -> getNode c dcN
            "Pos" -> getNode c dcP
            _     -> getNode c dcP
    in naiveTraverse @a c dcChild branch

-- === ClassNode vs ClassNode: deeper nesting ===
naiveTraverse c dcR@(_, ClassNode dcPos dcD dcP dcN) branch@(_, ClassNode pos d p n)
    | dcPos == pos =
        let (c1, rD) = naiveTraverse @Dc  c  (getNode c dcD) (getNode c d)
            (c2, rP) = naiveTraverse @Pos c1 (getNode c dcP) (getNode c p)
            (c3, rN) = naiveTraverse @Neg c2 (getNode c dcN) (getNode c n)
        in applyElimRule @a c3 $ ClassNode pos (fst rD) (fst rP) (fst rN)
    | otherwise = (c, branch)

-- ClassNode in dcR, non-ClassNode in branch: branch implicitly enters the class
naiveTraverse c dcR@(_, ClassNode dcPos dcD dcP dcN) branch@(_, Node _ _ _) =
    let (c1, rD) = naiveTraverse @Dc  c  (getNode c dcD) branch
        (c2, rP) = naiveTraverse @Pos c1 (getNode c dcP) branch
        (c3, rN) = naiveTraverse @Neg c2 (getNode c dcN) branch
    in applyElimRule @a c3 $ ClassNode dcPos (fst rD) (fst rP) (fst rN)
naiveTraverse c dcR@(_, ClassNode dcPos dcD dcP dcN) branch@(_, EndClassNode _) =
    let (c1, rD) = naiveTraverse @Dc  c  (getNode c dcD) branch
        (c2, rP) = naiveTraverse @Pos c1 (getNode c dcP) branch
        (c3, rN) = naiveTraverse @Neg c2 (getNode c dcN) branch
    in applyElimRule @a c3 $ ClassNode dcPos (fst rD) (fst rP) (fst rN)

-- ClassNode in branch, non-ClassNode in dcR: dcR implicitly enters the class
naiveTraverse c dcR branch@(_, ClassNode pos d p n) =
    let (c1, rD) = naiveTraverse @Dc  c  dcR (getNode c d)
        (c2, rP) = naiveTraverse @Pos c1 dcR (getNode c p)
        (c3, rN) = naiveTraverse @Neg c2 dcR (getNode c n)
    in applyElimRule @a c3 $ ClassNode pos (fst rD) (fst rP) (fst rN)

naiveTraverse c _ branch = (c, branch)



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
        EndClassNode d' -> (c, getNode c d') -- Elim ClassNode and EndClassNode pair if they immediatly follow up on each other
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
    catchup _ _ n _ = n
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

    -- | Pos catchup: When dc_stack lags behind main traversal, infer missing nodes.
    catchup s c n@(_, Node positionA _ _) idx
        | idx == -1 = catchup @Pos s c (move_dc c s n ) idx  -- Follow pos branch
        | idx > positionA = catchup @Pos s c (move_dc c s n ) idx  -- Follow pos branch
        | otherwise = n
    catchup _ _ n _ = n  -- Non-Node: no catchup needed
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

    -- | Neg catchup: When dc_stack lags behind main traversal, infer missing nodes.
    catchup s c n@(_, Node positionA _ _) idx
        | idx == -1 = catchup @Neg s c (move_dc c s n) idx  -- Follow neg branch
        | idx > positionA = catchup @Neg s c (move_dc c s n) idx  -- Follow neg branch
        | otherwise = n
    catchup _ _ n _ = n  -- Non-Node: no catchup needed
    to_str = "Neg"

-- | Traversal Helper (Dd1_helper).
-- This typeclass provides functions to synchronize the dc_stack traversal with the main  MDD traversal.
-- When the main traversal skips variables (due to elimination rules), the dc_stack needs to "catch up" to stay synchronized.
class Dd1_helper (a :: Inf) where
    traverse_dc :: String -> BiOpContext -> NodeId -> NodeId -> BiOpContext

instance (DdF3 a) => Dd1_helper a where
    -- | Synchronizes the entire dc_stack with the main traversal.
    traverse_dc s c a b = debug_dc_traverse s c a b $
        if to_str @a == "Dc" then c  -- Dc: no catchup needed -- todo this is not true! fix this in the future.
        else
            let (dcAs, dcBs, dcRs) = (bin_dc_stack c)
                -- Update dcA branches using reference node A
                new_dcAs = map (traverse_dc_generic (catchup @a) s c (getNode c a)) dcAs
                -- Update dcB branches using reference node B
                new_dcBs = map (traverse_dc_generic (catchup @a) s c (getNode c b)) dcBs
                -- Update dcR branches using reference node A (should be at the same level as B)
                new_dcRs = map (traverse_dc_generic (catchup @a) s c (getNode c a)) dcRs
            in c { bin_dc_stack = (new_dcAs, new_dcBs, new_dcRs) }
