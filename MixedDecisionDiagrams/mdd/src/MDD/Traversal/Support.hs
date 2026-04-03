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
import MDD.Extra.Draw (debug_dc_traverse, debug_naiveAbsorb_open, debug_naiveAbsorb_close, myTrace, show_node)

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

pop_level_ :: UnOpContext -> (UnOpContext, Inf)
pop_level_ ctx =
    let (_ : lv@(_, inf) : lvs') = un_current_level ctx
    in (ctx { un_current_level = lv : lvs' }, inf)


-- * DC Stack Synchronization for Naive Absorb/Traverse
traverse_dc_unary_ :: forall (a :: Inf). (DdF3 a) => String -> UnOpContext -> NodeId -> UnOpContext
traverse_dc_unary_ s c d =
    let ref = getNode c d
    in case snd ref of
        Leaf{} -> c
        _      -> let new_dcRs = map (traverse_dc_generic @a s c ref) (un_dc_stack c)
                  in c { un_dc_stack = new_dcRs }


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
naiveAbsorb c (_, Unknown) branch = -- todo double check the logic here
    case un_dc_stack c of
        (_ : outer : rest) -> naiveAbsorb @a (c { un_dc_stack = outer : rest }) outer branch
        _                  -> (c, branch)

-- Node one, Leaf in other: the Leaf implicitly has the Node's variable resolved through the inference rule. Infer to reach the Leaf's level.
naiveAbsorb c dcR@(dcRId, Node dcPos dcP dcN) branch@(_, Leaf _) =
    case to_str @a of
        "Neg" -> let c_ = traverse_dc_unary_ @Dc "neg child" c dcRId
                 in naiveAbsorb @a c_ (getNode c dcN) branch
        "Pos" -> let c_ = traverse_dc_unary_ @Dc "pos child" c dcRId
                 in naiveAbsorb @a c_ (getNode c dcP) branch
        _     -> let c_p = traverse_dc_unary_ @Dc "pos child" c dcRId
                     (c',  r1) = naiveAbsorb @a c_p (getNode c dcP) branch
                     c_n = traverse_dc_unary_ @Dc "neg child" (reset_stack_un c' c) dcRId
                     (c'', r2) = naiveAbsorb @a c_n (getNode c dcN) branch
                     absorbed = applyElimRule @a (reset_stack_un c'' c) $ Node dcPos (fst r1) (fst r2)
                 in if snd absorbed == dcR then (fst absorbed, ((0,0), Unknown)) else absorbed
naiveAbsorb c dcR@(_, Leaf _) branch@(branchId, Node pos p n) =
     -- because dcR has dc rule we do not have to explicitly infer nodes for it
    let c_p = traverse_dc_unary_ @a "pos child" c branchId
        (c',  r1) = naiveAbsorb @a c_p dcR (getNode c p)
        c_n = traverse_dc_unary_ @a "neg child" (reset_stack_un c' c) branchId
        (c'', r2) = naiveAbsorb @a c_n dcR (getNode c n)
        absorbed = applyElimRule @a (reset_stack_un c'' c) $ Node pos (fst r1) (fst r2)
    in if snd absorbed == dcR then (fst absorbed, ((0,0), Unknown)) else absorbed

-- Leaf implicitly has EndClassNodes for all outer classes
naiveAbsorb c dcR@(_, EndClassNode dcChild) branch@(_, Leaf _) =
    let (c', branchWrapped) = insert c (EndClassNode (fst branch))
    in naiveAbsorb @a c' dcR branchWrapped
naiveAbsorb c dcR@(_, Leaf _) branch@(_, EndClassNode branchChild) =
    let (c', dcRWrapped) = insert c (EndClassNode (fst dcR))
    in naiveAbsorb @a c' dcRWrapped branch
naiveAbsorb c dcR@(_, Leaf _) branch@(_, ClassNode pos d p n) =
    let (c', dcRInferred) = inferClassNode @Dc c pos dcR
    in naiveAbsorb @a c' dcRInferred branch
naiveAbsorb c dcR@(_, ClassNode dcPos _ _ _) branch@(_, Leaf _) =
    let (c', branchInferred) = inferClassNode @a c dcPos branch
    in naiveAbsorb @a c' dcR branchInferred


-- === Node vs Node ===: simultaneous traversal of matching variable positions
naiveAbsorb c dcR@(dcRId, Node dcPos dcP dcN) branch@(branchId, Node pos p n)
    | branch == dcR = (c, ((0,0), Unknown))
    | dcPos == pos =
        let c_p = traverse_dc_unary_ @Dc "pos child" c dcRId
            (c',  r1) = naiveAbsorb @a c_p (getNode c dcP) (getNode c p)
            c_n = traverse_dc_unary_ @Dc "neg child" (reset_stack_un c' c) dcRId
            (c'', r2) = naiveAbsorb @a c_n (getNode c dcN) (getNode c n)
            absorbed = applyElimRule @a (reset_stack_un c'' c) $ Node pos (fst r1) (fst r2)
        in if snd absorbed == dcR then (fst absorbed, ((0,0), Unknown)) else absorbed
    | dcPos < pos =
        case to_str @a of
            "Neg" -> let c_ = traverse_dc_unary_ @Dc "neg child" c dcRId
                     in naiveAbsorb @a c_ (getNode c dcN) branch
            "Pos" -> let c_ = traverse_dc_unary_ @Dc "pos child" c dcRId
                     in naiveAbsorb @a c_ (getNode c dcP) branch
            _     -> let c_p = traverse_dc_unary_ @Dc "pos child" c dcRId
                         (c',  r1) = naiveAbsorb @a c_p (getNode c dcP) branch
                         c_n = traverse_dc_unary_ @Dc "neg child" (reset_stack_un c' c) dcRId
                         (c'', r2) = naiveAbsorb @a c_n (getNode c dcN) branch
                         absorbed = applyElimRule @a (reset_stack_un c'' c) $ Node dcPos (fst r1) (fst r2)
                     in if snd absorbed == dcR then (fst absorbed, ((0,0), Unknown)) else absorbed
    | dcPos > pos =
        let c_p = traverse_dc_unary_ @a "pos child" c branchId
            (c',  r1) = naiveAbsorb @a c_p dcR (getNode c p)
            c_n = traverse_dc_unary_ @a "neg child" (reset_stack_un c' c) branchId
            (c'', r2) = naiveAbsorb @a c_n dcR (getNode c n)
            absorbed = applyElimRule @a (reset_stack_un c'' c) $ Node pos (fst r1) (fst r2)
        in if snd absorbed == dcR then (fst absorbed, ((0,0), Unknown)) else absorbed

-- === Node vs EndClassNode ===
naiveAbsorb c dcR@(dcRId, Node dcPos dcP dcN) branch@(_, EndClassNode _) =
    case to_str @a of
        "Neg" -> let c_ = traverse_dc_unary_ @Dc "neg child" c dcRId
                 in naiveAbsorb @a c_ (getNode c dcN) branch
        "Pos" -> let c_ = traverse_dc_unary_ @Dc "pos child" c dcRId
                 in naiveAbsorb @a c_ (getNode c dcP) branch
        _     -> let c_p = traverse_dc_unary_ @Dc "pos child" c dcRId
                     (c',  r1) = naiveAbsorb @a c_p (getNode c dcP) branch
                     c_n = traverse_dc_unary_ @Dc "neg child" (reset_stack_un c' c) dcRId
                     (c'', r2) = naiveAbsorb @a c_n (getNode c dcN) branch
                     absorbed = applyElimRule @a (reset_stack_un c'' c) $ Node dcPos (fst r1) (fst r2)
                 in if snd absorbed == dcR then (fst absorbed, ((0,0), Unknown)) else absorbed
-- because dcR has dc rule we do not have to explicitly infer nodes for it
naiveAbsorb c dcR@(_, EndClassNode _) branch@(branchId, Node pos p n) =
    let c_p = traverse_dc_unary_ @a "pos child" c branchId
        (c',  r1) = naiveAbsorb @a c_p dcR (getNode c p)
        c_n = traverse_dc_unary_ @a "neg child" (reset_stack_un c' c) branchId
        (c'', r2) = naiveAbsorb @a c_n dcR (getNode c n)
        absorbed = applyElimRule @a (reset_stack_un c'' c) $ Node pos (fst r1) (fst r2)
    in if snd absorbed == dcR then (fst absorbed, ((0,0), Unknown)) else absorbed

-- === ClassNode in branch and dcR ===
-- Switch to non-absorbing simultaneous traversal (with elimination rules)
-- until the same class level is reached again, then absorption continues.
--
naiveAbsorb c dcR@(_, ClassNode dcPos dcD dcP dcN) branch@(_, ClassNode pos d p n)
    | branch == dcR = (c, ((0,0), Unknown))
    | dcPos == pos =
        let c_ = add_to_stack_ (pos, Dc) (getNode c dcD, ((0,0), Unknown)) c
            (c1, rD) = naiveTraverse @Dc  1 c_ (getNode c dcD) (getNode c d)
            c1' = reset_stack_un c1 c
            c2_ = add_to_stack_ (pos, Pos) (getNode c dcD, rD) c1'
            (c2, rP) = naiveTraverse @Pos 1 c2_ (getNode c dcP) (getNode c p)
            c2' = reset_stack_un c2 c
            c3_ = add_to_stack_ (pos, Neg) (getNode c dcD, rD) c2'
            (c3, rN) = naiveTraverse @Neg 1 c3_ (getNode c dcN) (getNode c n)
            absorbed = applyElimRule @a (reset_stack_un c3 c) $ ClassNode pos (fst rD) (fst rP) (fst rN)
        in if snd absorbed == dcR then (fst absorbed, ((0,0), Unknown)) else absorbed
    | dcPos < pos =
        let (c', branchInferred) = inferClassNode @a c dcPos branch
        in naiveAbsorb @a c' dcR branchInferred
    | dcPos > pos =
        let (c', dcRInferred) = inferClassNode @Dc c pos dcR
        in naiveAbsorb @a c' dcRInferred branch

naiveAbsorb c dcR@(_, ClassNode dcPos _ _ _) branch@(_, EndClassNode _) =
    let (c', branchInferred) = inferClassNode @a c dcPos branch
    in naiveAbsorb @a c' dcR branchInferred
naiveAbsorb c dcR@(_, EndClassNode _) branch@(_, ClassNode pos _ _ _) =
    let (c', dcRInferred) = inferClassNode @Dc c pos dcR
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
naiveTraverse depth c (_, Unknown) branch = -- todo double check the logic here
    case un_dc_stack c of
        (_ : outer : rest) -> naiveTraverse @a depth (c { un_dc_stack = outer : rest }) outer branch
        _                  -> (c, branch)

naiveTraverse depth c dcR@(dcRId, EndClassNode dcChild) branch@(_, Leaf _)
    | depth == 1 =
        let (c_, inf) = pop_level_ c
        in case inf of
            Dc  -> naiveAbsorb @Dc  c_ (getNode c dcChild) branch
            Neg -> naiveAbsorb @Neg c_ (getNode c dcChild) branch
            Pos -> naiveAbsorb @Pos c_ (getNode c dcChild) branch
    | otherwise =
        let (c_, inf) = pop_level_ c
        in case inf of
            Dc  -> naiveTraverse @Dc  (depth - 1) c_ (getNode c dcChild) branch
            Neg -> naiveTraverse @Neg (depth - 1) c_ (getNode c dcChild) branch
            Pos -> naiveTraverse @Pos (depth - 1) c_ (getNode c dcChild) branch
naiveTraverse depth c dcR@(dcRId, Node dcPos dcP dcN) branch@(_, Leaf _) =
    case to_str @a of
        "Neg" -> let c_ = traverse_dc_unary_ @Dc "neg child" c dcRId
                 in naiveTraverse @a depth c_ (getNode c dcN) branch
        "Pos" -> let c_ = traverse_dc_unary_ @Dc "pos child" c dcRId
                 in naiveTraverse @a depth c_ (getNode c dcP) branch
        _     -> let c_p = traverse_dc_unary_ @Dc "pos child" c dcRId
                     (c',  r1) = naiveTraverse @a depth c_p (getNode c dcP) branch
                     c_n = traverse_dc_unary_ @Dc "neg child" (reset_stack_un c' c) dcRId
                     (c'', r2) = naiveTraverse @a depth c_n (getNode c dcN) branch
                 in applyElimRule @a (reset_stack_un c'' c) $ Node dcPos (fst r1) (fst r2)

-- === EndClassNode: exiting a class ===
-- depth == 1: about to go back at the absorbing class level — hand to naiveAbsorb
-- depth > 1: still inside a deeper nested class — stay in naiveTraverse
naiveTraverse depth c dcR@(_, EndClassNode dcChild) branch@(_, EndClassNode branchChild)
    | depth == 1 =
        let (c_, inf) = pop_level_ c
        in case inf of
            Dc  -> let (c', r) = naiveAbsorb @Dc  c_ (getNode c dcChild) (getNode c branchChild)
                   in applyElimRule @a c' $ EndClassNode (fst r)
            Neg -> let (c', r) = naiveAbsorb @Neg c_ (getNode c dcChild) (getNode c branchChild)
                   in applyElimRule @a c' $ EndClassNode (fst r)
            Pos -> let (c', r) = naiveAbsorb @Pos c_ (getNode c dcChild) (getNode c branchChild)
                   in applyElimRule @a c' $ EndClassNode (fst r)
    | otherwise =
        let (c_, inf) = pop_level_ c
        in case inf of
            Dc  -> let (c', r) = naiveTraverse @Dc  (depth - 1) c_ (getNode c dcChild) (getNode c branchChild)
                   in applyElimRule @a c' $ EndClassNode (fst r)
            Neg -> let (c', r) = naiveTraverse @Neg (depth - 1) c_ (getNode c dcChild) (getNode c branchChild)
                   in applyElimRule @a c' $ EndClassNode (fst r)
            Pos -> let (c', r) = naiveTraverse @Pos (depth - 1) c_ (getNode c dcChild) (getNode c branchChild)
                   in applyElimRule @a c' $ EndClassNode (fst r)
naiveTraverse depth c dcR@(_, Leaf _) branch@(_, EndClassNode branchChild)
    | depth == 1 =
        let (c_, inf) = pop_level_ c
        in case inf of
            Dc  -> let (c', r) = naiveAbsorb @Dc  c_ dcR (getNode c branchChild)
                   in applyElimRule @a c' $ EndClassNode (fst r)
            Neg -> let (c', r) = naiveAbsorb @Neg c_ dcR (getNode c branchChild)
                   in applyElimRule @a c' $ EndClassNode (fst r)
            Pos -> let (c', r) = naiveAbsorb @Pos c_ dcR (getNode c branchChild)
                   in applyElimRule @a c' $ EndClassNode (fst r)
    | otherwise =
        let (c_, inf) = pop_level_ c
        in case inf of
            Dc  -> let (c', r) = naiveTraverse @Dc  (depth - 1) c_ dcR (getNode c branchChild)
                   in applyElimRule @a c' $ EndClassNode (fst r)
            Neg -> let (c', r) = naiveTraverse @Neg (depth - 1) c_ dcR (getNode c branchChild)
                   in applyElimRule @a c' $ EndClassNode (fst r)
            Pos -> let (c', r) = naiveTraverse @Pos (depth - 1) c_ dcR (getNode c branchChild)
                   in applyElimRule @a c' $ EndClassNode (fst r)
naiveTraverse depth c dcR@(_, Leaf _) branch@(_, Leaf _)
    | depth == 1 =
        let (c_, inf) = pop_level_ c
        in case inf of
            Dc  -> naiveAbsorb @Dc  c_ dcR branch
            Neg -> naiveAbsorb @Neg c_ dcR branch
            Pos -> naiveAbsorb @Pos c_ dcR branch
    | otherwise =
        let (c_, inf) = pop_level_ c
        in case inf of
            Dc  -> naiveTraverse @Dc  (depth - 1) c_ dcR branch
            Neg -> naiveTraverse @Neg (depth - 1) c_ dcR branch
            Pos -> naiveTraverse @Pos (depth - 1) c_ dcR branch

naiveTraverse depth c dcR@(dcRId, Node dcPos dcP dcN) branch@(_, EndClassNode branchChild) =
    case to_str @a of
        "Neg" -> let c_ = traverse_dc_unary_ @Dc "neg child" c dcRId
                 in naiveTraverse @a depth c_ (getNode c dcN) branch
        "Pos" -> let c_ = traverse_dc_unary_ @Dc "pos child" c dcRId
                 in naiveTraverse @a depth c_ (getNode c dcP) branch
        _     -> let c_p = traverse_dc_unary_ @Dc "pos child" c dcRId
                     (c',  r1) = naiveTraverse @a depth c_p (getNode c dcP) branch
                     c_n = traverse_dc_unary_ @Dc "neg child" (reset_stack_un c' c) dcRId
                     (c'', r2) = naiveTraverse @a depth c_n (getNode c dcN) branch
                 in applyElimRule @a (reset_stack_un c'' c) $ Node dcPos (fst r1) (fst r2)


naiveTraverse depth c dcR@(_, EndClassNode _) branch@(branchId, Node pos p n) =
    let c_p = traverse_dc_unary_ @a "pos child" c branchId
        (c',  r1) = naiveTraverse @a depth c_p dcR (getNode c p)
        c_n = traverse_dc_unary_ @a "neg child" (reset_stack_un c' c) branchId
        (c'', r2) = naiveTraverse @a depth c_n dcR (getNode c n)
    in applyElimRule @a (reset_stack_un c'' c) $ Node pos (fst r1) (fst r2)

-- === Node vs Node: simultaneous traversal (same class level) ===
naiveTraverse depth c dcR@(dcRId, Node dcPos dcP dcN) branch@(branchId, Node pos p n)
    | dcPos == pos =
        let c_p = traverse_dc_unary_ @Dc "pos child" c dcRId
            (c',  r1) = naiveTraverse @a depth c_p (getNode c dcP) (getNode c p)
            c_n = traverse_dc_unary_ @Dc "neg child" (reset_stack_un c' c) dcRId
            (c'', r2) = naiveTraverse @a depth c_n (getNode c dcN) (getNode c n)
        in applyElimRule @a (reset_stack_un c'' c) $ Node pos (fst r1) (fst r2)
    | dcPos < pos =
        case to_str @a of
            "Neg" -> let c_ = traverse_dc_unary_ @Dc "neg child" c dcRId
                     in naiveTraverse @a depth c_ (getNode c dcN) branch
            "Pos" -> let c_ = traverse_dc_unary_ @Dc "pos child" c dcRId
                     in naiveTraverse @a depth c_ (getNode c dcP) branch
            _     -> let c_p = traverse_dc_unary_ @Dc "pos child" c dcRId
                         (c',  r1) = naiveTraverse @a depth c_p (getNode c dcP) branch
                         c_n = traverse_dc_unary_ @Dc "neg child" (reset_stack_un c' c) dcRId
                         (c'', r2) = naiveTraverse @a depth c_n (getNode c dcN) branch
                     in applyElimRule @a (reset_stack_un c'' c) $ Node dcPos (fst r1) (fst r2)
    | dcPos > pos =
        let c_p = traverse_dc_unary_ @a "pos child" c branchId
            (c',  r1) = naiveTraverse @a depth c_p dcR (getNode c p)
            c_n = traverse_dc_unary_ @a "neg child" (reset_stack_un c' c) branchId
            (c'', r2) = naiveTraverse @a depth c_n dcR (getNode c n)
        in applyElimRule @a (reset_stack_un c'' c) $ Node pos (fst r1) (fst r2)

naiveTraverse depth c dcR@(_, Leaf _) branch@(branchId, Node pos p n) =
    let c_p = traverse_dc_unary_ @a "pos child" c branchId
        (c',  r1) = naiveTraverse @a depth c_p dcR (getNode c p)
        c_n = traverse_dc_unary_ @a "neg child" (reset_stack_un c' c) branchId
        (c'', r2) = naiveTraverse @a depth c_n dcR (getNode c n)
    in applyElimRule @a (reset_stack_un c'' c) $ Node pos (fst r1) (fst r2)
-- === ClassNode: entering a deeper nested class (depth + 1) ===
naiveTraverse depth c dcR@(_, ClassNode dcPos dcD dcP dcN) branch@(_, ClassNode pos d p n)
    | dcPos == pos =
        let c_ = add_to_stack_ (pos, Dc) (getNode c dcD, ((0,0), Unknown)) c
            (c1, rD) = naiveTraverse @Dc  (depth + 1) c_ (getNode c dcD) (getNode c d)
            c1' = reset_stack_un c1 c
            c2_ = add_to_stack_ (pos, Pos) (getNode c dcD, rD) c1'
            (c2, rP) = naiveTraverse @Pos (depth + 1) c2_ (getNode c dcP) (getNode c p)
            c2' = reset_stack_un c2 c
            c3_ = add_to_stack_ (pos, Neg) (getNode c dcD, rD) c2'
            (c3, rN) = naiveTraverse @Neg (depth + 1) c3_ (getNode c dcN) (getNode c n)
        in applyElimRule @a (reset_stack_un c3 c) $ ClassNode pos (fst rD) (fst rP) (fst rN)
    | dcPos < pos =
        let (c', branchInferred) = inferClassNode @a c dcPos branch
        in naiveTraverse @a depth c' dcR branchInferred
    | dcPos > pos =
        let (c', dcRInferred) = inferClassNode @Dc c pos dcR
        in naiveTraverse @a depth c' dcRInferred branch

naiveTraverse depth c dcR@(_, Node _ _ _) branch@(_, ClassNode pos _ _ _) = error "should not happen: node vs class node in naiveTraverse"
naiveTraverse depth c dcR@(_, EndClassNode _) branch@(_, ClassNode pos _ _ _) =
    let (c', dcRInferred) = inferClassNode @Dc c pos dcR
    in naiveTraverse @a depth c' dcRInferred branch
naiveTraverse depth c dcR@(_, Leaf _) branch@(_, ClassNode pos _ _ _) =
    let (c', dcRInferred) = inferClassNode @Dc c pos dcR
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
    catchup _ n@(_, ClassNode _ _ _ _) _ = error "ClassNode catchup not yet implemented"
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
    catchup _ n@(_, ClassNode _ _ _ _) _ = error "ClassNode catchup not yet implemented"
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
    catchup _ n@(_, ClassNode _ _ _ _) _ = error "ClassNode catchup not yet implemented"
    catchup _ n _ = n
    to_str = "Neg"

-- | Synchronize a single dc_stack element with the main traversal.
-- Parameterized by inference type @a (determines catchup and inferClassNode behaviour).
-- Moved from Stack.hs to Support.hs so it can use catchup @a and inferClassNode @a directly.
traverse_dc_generic :: forall (a :: Inf) c. (DdF3 a, HasNodeLookup c) =>
    String   -- ^ move string ("pos child", "neg child", "class dc", etc.)
    -> c -> Node -> Node -> Node
traverse_dc_generic s c refNode dcNode =
    let validMove = case (snd refNode, s) of
            (Node{},         "pos child") -> True
            (Node{},         "neg child") -> True
            (ClassNode{},    "class dc")  -> True
            (ClassNode{},    "class neg") -> True
            (ClassNode{},    "class pos") -> True
            (EndClassNode{}, "endclass")  -> True
            _                             -> False
    in if not validMove
        then error $ "traverse_dc_generic: invalid move '" ++ s ++ "' for refNode type " ++ show_node c refNode
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
                let (_, inferred) = inferClassNode @a c idx dcNode
                in move_dc c s inferred

            -- Case 11: (EndClassNode, Node) — dc at end class, ref still inside
            ((_, EndClassNode{}), (_, Node{})) -> dcNode

            -- Case 13: (EndClassNode, ClassNode) — dc at end, ref at ClassNode
            ((_, EndClassNode{}), (_, ClassNode idx _ _ _)) ->
                let (_, inferred) = inferClassNode @a c idx dcNode
                in move_dc c s inferred

            ((_, Node _ _ _), (_, ClassNode _ _ _ _)) -> error "node vs classnode should not happen on the same local domain"
            ((_, ClassNode _ _ _ _), (_, Node _ _ _)) -> error "classnode vs node should not happen on the same local domain"

            _ -> error $ "traverse_dc_generic unhandled case:\n (dcNode=" ++ show_node c dcNode
                      ++ ",\n  refNode=" ++ show_node c refNode ++ ")"

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
                new_dcAs = if isLeaf refA then dcAs else map (traverse_dc_generic @a s c refA) dcAs
                new_dcBs = if isLeaf refB then dcBs else map (traverse_dc_generic @a s c refB) dcBs
                new_dcRs = if isLeaf refA then dcRs else map (traverse_dc_generic @a s c refA) dcRs
            in c { bin_dc_stack = (new_dcAs, new_dcBs, new_dcRs) }
