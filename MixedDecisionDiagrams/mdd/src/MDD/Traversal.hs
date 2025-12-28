{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE AllowAmbiguousTypes #-}   -- Required to allow methods where the class type variable 'a' is not in the signature
{-# LANGUAGE FlexibleInstances #-}     -- Required for the instance Dd1_helper a
{-# LANGUAGE UndecidableInstances #-}  -- Required because the constraint DdF3 a is not smaller than the head Dd1_helper a
{-# LANGUAGE FlexibleContexts #-}

module MDD.Traversal where

import MDD.Types
import MDD.Context
import MDD.Stack
import MDD.Draw (debug_dc_traverse)
import Data.Kind (Constraint)

-- | Shared helper function to move down the tree based on semantic role.
-- Used to step into sub-branches during recursive traversal.
move_dc :: (HasNodeLookup c) => c -> String -> Node -> Node
move_dc c m node =
    case node of
        (_, Node position pos_child neg_child) ->
            if m == "pos child" then getNode c pos_child
            else if m == "neg child" then getNode c neg_child
            else error $ "processStackElement: undefined move '" ++ m ++ "' for Node pattern"

        (_, EndInfNode child) ->
            if m == "endinf" then getNode c child
            else (if m `elem` ["pos child", "neg child", "inf pos", "inf neg", "inf dc"] then node
            else error $ "processStackElement: undefined move '" ++ m ++ "' for EndInfNode pattern")

        (_, InfNodes position dc p n) ->
            if m == "inf pos" then getNode c p
            else if m == "inf neg" then getNode c n
            else if m == "inf dc" then getNode c dc
            else error $ "processStackElement: undefined move '" ++ m ++ "' for InfNodes pattern"

        (_, Leaf _) ->
            node
        (_, Unknown) ->
            node
        _ -> error $ "processStackElement: Unhandled Node pattern"

-- | Elimination and Inference rule typeclass (DdF3).
class DdF3 (a :: Inf) where
    -- | Infers a node for Argument A when Argument B is at a lower position.
    inferNodeA :: (BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node))
               -> BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Dd)
    -- | Infers a node for Argument B when Argument A is at a lower position.
    inferNodeB :: (BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Node))
               -> BinaryOperatorContext -> String -> Node -> Node -> (BinaryOperatorContext, Dd)

    applyElimRule :: BinaryOperatorContext -> Dd -> (BinaryOperatorContext, Node)
    inferNode :: (HasNodeLookup c) => c -> Int -> Node -> (c, Node)
    inferInfNode :: (HasNodeLookup c) => c -> Int -> Node -> (c, Node)
    catchup :: (HasNodeLookup c) => String -> c -> Node -> Int -> Node
    to_str :: String

instance DdF3 Dc where
    inferNodeA f c s a (_, Node positionB pos_childB neg_childB) =
        let (c', (pos_result, _)) = f c s a (getNode c pos_childB)
            (c'', (neg_result, _)) = f c' s a (getNode c neg_childB)
        in (c'', Node positionB pos_result neg_result)

    inferNodeB f c s (_, Node positionA pos_childA neg_childA) b =
        let (c', (pos_result, _)) = f c s (getNode c pos_childA) b
            (c'', (neg_result, _)) = f c' s (getNode c neg_childA) b
        in (c'', Node positionA pos_result neg_result)

    -- applyElimRule :: BinaryOperatorContext -> Dd -> (BinaryOperatorContext, Node)
    applyElimRule c d@(Node _ p n) = if p == n then (c, getNode c p) else insert c d
    applyElimRule c (InfNodes _ (1,0) (0,0) (0,0)) = (c, ((1,0), Leaf True))
    applyElimRule c (InfNodes _ (2,0) (0,0) (0,0)) = (c, ((2,0), Leaf False))
    applyElimRule c (InfNodes _ (0,0) (0,0) (0,0)) = (c, ((0,0), Unknown))
    applyElimRule c (EndInfNode (1,0)) = (c, ((1,0), Leaf True))
    applyElimRule c (EndInfNode (2,0)) = (c, ((2,0), Leaf False))
    applyElimRule c (EndInfNode (0,0)) = (c, ((0,0), Unknown))
    -- Eliminate EndInfNode if it points to a Leaf Bool or Unknown (general case)
    applyElimRule c d@(EndInfNode r) = case getDd c r of
        Leaf _ -> (c, getNode c r)  -- Eliminate EndInfNode if it points to any Leaf
        Unknown -> (c, getNode c r)  -- Eliminate EndInfNode if it points to Unknown
        _ -> insert c d
    applyElimRule c d@(InfNodes _ consq (0,0) (0,0)) = case getDd c consq of
        EndInfNode d' -> (c, getNode c d')
        _ -> insert c d
    applyElimRule c d = insert c d

    inferNode c position (n_id, n) = insert c (Node position n_id n_id)
    inferInfNode c position (n_id, n) = insert c $ InfNodes position n_id (0,0) (0,0)
    catchup _ _ n _ = n
    to_str = "Dc"

instance DdF3 Pos where
    inferNodeA f c s a@(a_id, _) b@(b_id, Node positionB _ _) =
        let (c', r) = insert c (Node positionB a_id (0,0))
            (c'', (r_node_id, _)) = f c' s r (getNode c' b_id)
        in (c'', getDd c'' r_node_id)

    inferNodeB f c s a@(a_id, Node positionA _ _) b@(b_id, _) =
        let (c', r) = insert c (Node positionA b_id (0,0))
            (c'', (r_node_id, _)) = f c' s (getNode c' a_id) r
        in (c'', getDd c'' r_node_id)

    -- applyElimRule :: BinaryOperatorContext -> Dd -> (BinaryOperatorContext, Node)
    applyElimRule c (Node _ posC (0, 0)) = (c, getNode c posC)
    applyElimRule c (InfNodes _ (0,0) (1,0) (0,0)) = (c, ((1,0), Leaf True))
    applyElimRule c (InfNodes _ (0,0) (2,0) (0,0)) = (c, ((2,0), Leaf False))
    -- Eliminate EndInfNode if it points to a Leaf Bool or Unknown
    applyElimRule c d@(EndInfNode r) = case getDd c r of
        Leaf _ -> (c, getNode c r)  -- Eliminate EndInfNode if it points to any Leaf
        Unknown -> (c, getNode c r)  -- Eliminate EndInfNode if it points to Unknown
        _ -> insert c d
    applyElimRule c d = insert c d

    inferNode c position (n_id, n) = insert c (Node position n_id (0,0))
    inferInfNode c position (n_id, n) = insert c $ InfNodes position (0,0) n_id (0,0)

    catchup s c n@(_, Node positionA _ _) idx
        | idx == -1 = catchup @Pos s c (move_dc c s n ) idx
        | idx > positionA = catchup @Pos s c (move_dc c s n ) idx
        | otherwise = n
    catchup _ _ n _ = n
    to_str = "Pos"

instance DdF3 Neg where
    inferNodeA f c s a@(a_id, _) b@(b_id, Node positionB _ _) =
        let (c', r) = insert c (Node positionB (0,0) a_id)
            (c'', (r_node_id, _)) = f c' s r (getNode c' b_id)
        in (c'', getDd c'' r_node_id)

    inferNodeB f c s a@(a_id, Node positionA _ _) b@(b_id, _) =
        let (c', r) = insert c (Node positionA (0,0) b_id)
            (c'', (r_node_id, _)) = f c' s (getNode c' a_id) r
        in (c'', getDd c'' r_node_id)

    -- applyElimRule :: BinaryOperatorContext -> Dd -> (BinaryOperatorContext, Node)
    applyElimRule c (Node _ (0, 0) negC) = (c, getNode c negC)
    applyElimRule c (InfNodes _ (0,0) (0,0) (1,0)) = (c, ((1,0), Leaf True))
    applyElimRule c (InfNodes _ (0,0) (0,0) (2,0)) = (c, ((2,0), Leaf False))
    -- Eliminate EndInfNode if it points to a Leaf Bool or Unknown
    applyElimRule c d@(EndInfNode r) = case getDd c r of
        Leaf _ -> (c, getNode c r)  -- Eliminate EndInfNode if it points to any Leaf
        Unknown -> (c, getNode c r)  -- Eliminate EndInfNode if it points to Unknown
        _ -> insert c d
    applyElimRule c d = insert c d

    inferNode c position (n_id, n) = insert c (Node position (0,0) n_id)
    inferInfNode c position (n_id, n) = insert c $ InfNodes position (0,0) (0,0) n_id

    catchup s c n@(_, Node positionA _ _) idx
        | idx == -1 = catchup @Neg s c (move_dc c s n) idx
        | idx > positionA = catchup @Neg s c (move_dc c s n) idx
        | otherwise = n
    catchup _ _ n _ = n
    to_str = "Neg"

-- | Traversal Helper (Dd1_helper).
class Dd1_helper (a :: Inf) where
    traverse_dc :: String -> BinaryOperatorContext -> NodeId -> NodeId -> BinaryOperatorContext
    traverse_dc_generic :: String -> BinaryOperatorContext -> Node -> Node -> Node

instance (DdF3 a) => Dd1_helper a where
    traverse_dc s c a b = debug_dc_traverse s c a b $
        if to_str @a == "Dc" then c
        else
            let (dcAs, dcBs, dcRs) = bin_dc_stack c
                new_dcAs = map (traverse_dc_generic @a s c (getNode c a)) dcAs
                new_dcBs = map (traverse_dc_generic @a s c (getNode c b)) dcBs
                new_dcRs = map (traverse_dc_generic @a s c (getNode c a)) dcRs
            in c { bin_dc_stack = (new_dcAs, new_dcBs, new_dcRs) }

    traverse_dc_generic s c refNode dcNode =
        case (dcNode, refNode) of
            ( tNode@(_, Node position _ _), rNode@(_, Node idx _ _) ) ->
                if | position > idx -> dcNode
                    | position == idx -> move_dc c s dcNode
                    | position < idx -> move_dc c s (catchup @a s c dcNode idx)
            ( (_, Node{}), (_, Leaf _) ) -> move_dc c s (catchup @a s c dcNode (-1))
            ( (_, Node{}), (_, EndInfNode{}) ) -> move_dc c s (catchup @a s c dcNode (-1))
            ( (_, EndInfNode{}), (_, EndInfNode{}) ) -> move_dc c s dcNode
            ( _, (_, Unknown) ) -> move_dc c s dcNode
            ( (_, Unknown), _ ) -> dcNode
            ( (_, InfNodes position _ _ _), (_, InfNodes idx _ _ _) ) ->
                if | position > idx -> dcNode
                    | position == idx -> move_dc c s dcNode
                    | position < idx -> dcNode
            _ -> dcNode