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
-- | This typeclass defines the inference and elimination rules for the three inference types:
-- |   - Dc (Don't-care): Nodes where both positive and negative evaluations lead to the same child are eliminated
-- |   - Pos (Positive literal): Nodes where only the positive evaluation is valid (negative leads to Unknown) are eliminated
-- |   - Neg (Negative literal): Nodes where only the negative evaluation is valid (positive leads to Unknown) are eliminated
-- |
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
    inferInfNode :: (HasNodeLookup c) => c -> Int -> Node -> (c, Node)
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
        -- Convert binary context to unary context for absorb operation
        unaryCtx = binaryToUnaryContext c
        -- Call unary absorb (using Dc inference type since we're comparing with continuous background)
        (unaryCtx', n') = absorb_unary @a (unaryCtx, n)
    in
        -- Convert back to binary context, preserving original state
        (unaryToBinaryContext unaryCtx' c, n')


-- | Main entry point for the absorb function for unary operations.
absorb_unary :: forall a. (DdF3 a) => (UnOpContext, Node) -> (UnOpContext, Node)
absorb_unary (c, n) = absorb' @a (c, n)

absorb' :: forall a. (DdF3 a) => (UnOpContext, Node) -> (UnOpContext, Node)
-- | given a dcR and a pos or ng results, sets sub-paths in the local inf-domain which agree with the dcR to unknown ("absorbing them")
absorb' (c@UCxt{un_dc_stack = dc@(_, Unknown) : fs }, a) = absorb' @a (c{un_dc_stack = fs}, a) -- resolve Unknown in dc traversal to a previous layer
absorb' (c@UCxt{un_dc_stack = dc : fs }, a@(_, Unknown)) = (c, a)
absorb' (c@UCxt{un_dc_stack = dc : fs }, a@(_, Leaf _))
    | a == dc = (c, ((0,0), Unknown))
    | otherwise = (c,a)
absorb' (c@UCxt{un_dc_stack = dc  : fs }, a@(_, InfNodes int d p n))
    | a == dc = (c, ((0,0), Unknown))
    | otherwise =
        let (c', r1) = absorb' @a (c, getNode c d)
            (c'', r2) = absorb' @a (c', getNode c p)
            (c''', r3) = absorb' @a (c'', getNode c n)
            absorbed_inf = applyElimRule @a c''' $ InfNodes int (fst r1) (fst r2) (fst r3)
        in if (snd absorbed_inf) == dc then (c, ((0,0), Unknown)) else absorbed_inf
absorb' (c@UCxt{un_dc_stack = dc  : fs }, a@(_, Node int p n))  =
    let (c', r1) = absorb' @a (c, getNode c p)
        (c'', r2) = absorb' @a (c', getNode c n)
        absorbed_node = applyElimRule @a c'' $ Node int (fst r1) (fst r2)
    in if (snd absorbed_node) == dc then (c, ((0,0), Unknown)) else absorbed_node

absorb' (c@UCxt{un_dc_stack = dc@(_, EndInfNode dc') : fs }, a@(_, EndInfNode a'))
    | a == dc = (c, ((0,0), Unknown))
    | otherwise = absorb' @a (c{un_dc_stack = getNode c dc' : fs}, getNode c a')
-- todo: need to add many traversal cases still (?), where inference happens.
absorb' (c@UCxt{un_dc_stack = dc : fs }, a)
    | a == dc = (c, ((0,0), Unknown))
    | otherwise = (c,a)
absorb' (c@UCxt{un_dc_stack = [] }, a) = (c, a) -- error "empty dc stack in absorb?"

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
    applyElimRule c (InfNodes _ (1,0) (0,0) (0,0)) = (c, ((1,0), Leaf True))
    applyElimRule c (InfNodes _ (2,0) (0,0) (0,0)) = (c, ((2,0), Leaf False))
    applyElimRule c (InfNodes _ (0,0) (0,0) (0,0)) = (c, ((0,0), Unknown))
    applyElimRule c d@(InfNodes _ consq (0,0) (0,0)) = case getDd c consq of
        EndInfNode d' -> (c, getNode c d') -- Elim InfNode and EndInfNode pair if they immediatly follow up on each other
        _ -> insert c d
    applyElimRule c d@(EndInfNode r) = case getDd c r of
        Leaf _ -> (c, getNode c r)
        Unknown -> (c, getNode c r)
        _ -> insert c d
    applyElimRule c d = insert c d

    inferNode :: HasNodeLookup c => c -> Int -> Node -> (c, Node)
    inferNode c position (n_id, n) = insert c (Node position n_id n_id)
    inferInfNode c position (n_id, n) = insert c $ InfNodes position n_id (0,0) (0,0)
    -- | Dc catchup: No catchup needed for Dc (both branches are valid, no inference needed).
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
    applyElimRule c (InfNodes _ (0,0) (1,0) (0,0)) = (c, ((1,0), Leaf True))
    applyElimRule c (InfNodes _ (0,0) (2,0) (0,0)) = (c, ((2,0), Leaf False))
    applyElimRule c (InfNodes _ (0,0) (0,0) (0,0)) = (c, ((0,0), Unknown))
    applyElimRule c d@(InfNodes _ (0,0) consq (0,0)) = case getDd c consq of
        EndInfNode d' -> (c, getNode c d')
        _ -> insert c d
    applyElimRule c d@(EndInfNode r) = case getDd c r of
        Leaf _ -> (c, getNode c r)
        Unknown -> (c, getNode c r)
        _ -> insert c d
    applyElimRule c d = insert c d

    -- | Create inferred Node at position: pos branch set, neg = Unknown (only pos valid).
    inferNode c position (n_id, n) = insert c (Node position n_id (0,0))
    -- | Create inferred InfNodes at position: only pos branch set (dc/neg empty).
    inferInfNode c position (n_id, n) = insert c $ InfNodes position (0,0) n_id (0,0)

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
    applyElimRule c (InfNodes _ (0,0) (0,0) (1,0)) = (c, ((1,0), Leaf True))
    applyElimRule c (InfNodes _ (0,0) (0,0) (2,0)) = (c, ((2,0), Leaf False))
    applyElimRule c (InfNodes _ (0,0) (0,0) (0,0)) = (c, ((0,0), Unknown))
    applyElimRule c d@(InfNodes _ (0,0) (0,0) consq) = case getDd c consq of
        EndInfNode d' -> (c, getNode c d')
        _ -> insert c d
    applyElimRule c d@(EndInfNode r) = case getDd c r of
        Leaf _ -> (c, getNode c r)
        Unknown -> (c, getNode c r)
        _ -> insert c d
    applyElimRule c d = insert c d


    inferNode c position (n_id, n) = insert c (Node position (0,0) n_id)
    inferInfNode c position (n_id, n) = insert c $ InfNodes position (0,0) (0,0) n_id

    -- | Neg catchup: When dc_stack lags behind main traversal, infer missing nodes.
    catchup s c n@(_, Node positionA _ _) idx
        | idx == -1 = catchup @Neg s c (move_dc c s n) idx  -- Follow neg branch
        | idx > positionA = catchup @Neg s c (move_dc c s n) idx  -- Follow neg branch
        | otherwise = n
    catchup _ _ n _ = n  -- Non-Node: no catchup needed
    to_str = "Neg"

-- | Traversal Helper (Dd1_helper).
-- |
-- | This typeclass provides functions to synchronize the dc_stack traversal with the main
-- | MDD traversal. When the main traversal skips variables (due to elimination rules),
-- | the dc_stack needs to "catch up" to stay synchronized.
class Dd1_helper (a :: Inf) where
    -- | Synchronizes the dc_stack with the main traversal for two NodeIds.
    -- | Updates all dc branches (dcA, dcB, dcR) in the stack to match the current position.
    traverse_dc :: String -> BiOpContext -> NodeId -> NodeId -> BiOpContext

instance (DdF3 a) => Dd1_helper a where
    -- | Synchronizes the entire dc_stack with the main traversal.
    -- | If inference type is Dc, no synchronization needed (both branches valid).
    -- | Otherwise, update all dc branches in the stack using traverse_dc_generic.
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
