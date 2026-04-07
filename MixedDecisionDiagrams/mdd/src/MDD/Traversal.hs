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
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module MDD.Traversal where

import MDD.Types
import MDD.Context
import MDD.Stack
import MDD.Draw (debug_dc_traverse, show_node)
import Data.Kind (Constraint)
import Debug.Trace (trace)
import qualified Data.HashMap.Strict as HashMap


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
-- |   - to_str: String representation for debugging
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


-- ==========================================================================================================
-- * Redundancy Elimination (absorb)
-- ==========================================================================================================

-- | Absorb is a unary MDD manipulation
-- | The absorb function maintains canonical representation by eliminating redundant branches.

-- | Calling this from a binary operator function needs a context adjusment
absorb :: forall a. (DdF3 a) => (BiOpContext, Node) -> (BiOpContext, Node)
absorb (c, n) =
    let
        -- Extract dcR from binary context (third element of bin_dc_stack tuple)
        (_, _, dcRs) = bin_dc_stack c
        -- Extract first element from bin_current_level (unary only tracks one level)
        (lvA, _) = bin_current_level c
        -- Convert to unary context
        unaryCtx = UCxt {
            un_nodelookup = bin_nodelookup c,
            un_cache = HashMap.empty,  -- Cache not needed for absorb
            un_dc_stack = dcRs,  -- Use dcR from binary context
            un_current_level = lvA  -- Use first level from binary context
        }
        -- Call unary absorb (using Dc inference type since we're comparing with continuous background)
        (unaryCtx', n') = absorb_unary @a (unaryCtx, n)
    in
        (BCxt {
            bin_nodelookup = un_nodelookup unaryCtx',  -- Updated nodelookup from unary context
            bin_cache = bin_cache c,  -- Preserve original cache
            bin_dc_stack = bin_dc_stack c, -- Preserve original stack
            bin_current_level = bin_current_level c  -- Preserve original current level
        }, n')


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
    -- | Uses Pos inference rule: follow the pos branch (neg leads to Unknown).
    -- | Case 1: idx == -1 (terminal reached) -> recursively catchup following pos branch
    -- | Case 2: idx > positionA (need to catch up to idx) -> recursively catchup following pos branch
    -- | Case 3: Otherwise -> already caught up, return node
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
    -- | Uses Neg inference rule: follow the neg branch (pos leads to Unknown).
    -- | Case 1: idx == -1 (terminal reached) -> recursively catchup following neg branch
    -- | Case 2: idx > positionA (need to catch up to idx) -> recursively catchup following neg branch
    -- | Case 3: Otherwise -> already caught up, return node
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
    -- | Synchronizes a single dc branch node with a reference node.
    -- | Uses the inference rule @a@ to catch up when positions don't match.
    traverse_dc_generic :: String -> BiOpContext -> Node -> Node -> Node

instance (DdF3 a) => Dd1_helper a where
    -- | Synchronizes the entire dc_stack with the main traversal.
    -- | If inference type is Dc, no synchronization needed (both branches valid).
    -- | Otherwise, update all dc branches in the stack using traverse_dc_generic.
    traverse_dc s c a b = debug_dc_traverse s c a b $
        if to_str @a == "Dc" then c  -- Dc: no catchup needed -- todo this is not true! fix this in the future.
        else
            let (dcAs, dcBs, dcRs) = bin_dc_stack c
                -- Update dcA branches using reference node A
                new_dcAs = map (traverse_dc_generic @a s c (getNode c a)) dcAs
                -- Update dcB branches using reference node B
                new_dcBs = map (traverse_dc_generic @a s c (getNode c b)) dcBs
                -- Update dcR branches using reference node A (should be at the same level as B)
                new_dcRs = map (traverse_dc_generic @a s c (getNode c a)) dcRs
            in c { bin_dc_stack = (new_dcAs, new_dcBs, new_dcRs) }

    -- | Synchronizes a single dc branch node with a reference node.
    -- | This handles the "catch-up" logic when the main traversal skips variables.
    -- |
    -- | Case 1: Both dcNode and refNode are Nodes
    -- |   -> If positions match: move down dcNode following the move string
    -- |   -> If dcNode position > refNode position: dcNode ahead, return as-is
    -- |   -> If dcNode position < refNode position: dcNode behind, catch up using inference rule
    -- | Case 2: dcNode is Node, refNode is Leaf/EndInfNode (terminal)
    -- |   -> Catch up dcNode to terminal (idx=-1) using inference rule
    -- | Case 3: Both are EndInfNodes
    -- |   -> Move down both following the move string
    -- | Case 4: refNode is Unknown
    -- |   -> Move down dcNode (Unknown doesn't block traversal)
    -- | Case 5: dcNode is Unknown
    -- |   -> Return as-is (Unknown will resolve from stack later)
    -- | Case 6: Both are InfNodes
    -- |   -> If positions match: move down dcNode
    -- |   -> If dcNode position > refNode position: dcNode ahead, return as-is
    -- |   -> If dcNode position < refNode position: dcNode behind, return as-is (no catchup for InfNodes)
    -- | Case 7: Default -> return dcNode as-is
    traverse_dc_generic s c refNode dcNode =
        case (dcNode, refNode) of
            ( tNode@(_, Node position _ _), rNode@(_, Node idx _ _) ) ->
                if | position > idx -> dcNode  -- dcNode ahead: no catchup needed
                    | position == idx -> move_dc c s dcNode  -- Positions match: move down
                    | position < idx -> move_dc c s (catchup @a s c dcNode idx)  -- dcNode behind: catch up
            ( (_, Node{}), (_, Leaf _) ) -> move_dc c s (catchup @a s c dcNode (-1))  -- Catch up to terminal
            ( (_, Node{}), (_, EndInfNode{}) ) -> move_dc c s (catchup @a s c dcNode (-1))  -- Catch up to terminal
            ( (_, EndInfNode{}), (_, EndInfNode{}) ) -> move_dc c s dcNode  -- Both EndInfNodes: move down
            ( _, (_, Unknown) ) -> move_dc c s dcNode  -- refNode Unknown: move down dcNode
            ( (_, Unknown), _ ) -> dcNode  -- dcNode Unknown: return as-is (resolves from stack)
            ( (_, InfNodes position _ _ _), (_, InfNodes idx _ _ _) ) ->
                if | position > idx -> dcNode  -- dcNode ahead: no catchup
                    | position == idx -> move_dc c s dcNode  -- Positions match: move down
                    | position < idx -> dcNode  -- dcNode behind: no catchup (InfNodes handled separately)
            _ -> dcNode  -- Default: return as-is