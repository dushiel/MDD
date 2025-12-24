{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}

module MDD.Ops.Unary where

import MDD.Types
import MDD.Context
import MDD.Manager
import MDD.Stack
import MDD.Traversal

import Data.Hashable
import qualified Data.HashMap.Strict as HashMap
import Data.Kind (Constraint)

-- ==========================================================================================================
-- * Unary Caching Helper
-- ==========================================================================================================

withCache_ :: UnaryOperatorContext -> Node -> (UnaryOperatorContext, Node) -> (UnaryOperatorContext, Node)
withCache_ c@UnaryOperatorContext { un_cache = nc } (key, _) func_with_args =
  case HashMap.lookup key nc of
    Just result -> (c, (result, getDd c result))
    Nothing -> let
      (updatedContext, result@(nodeid, _)) = func_with_args
      updatedCache = HashMap.insert key nodeid nc
      in (updatedContext { un_cache = updatedCache }, result)

-- ==========================================================================================================
-- * Negation Logic
-- ==========================================================================================================

negation :: UnaryOperatorContext -> Node -> (UnaryOperatorContext, Node)
negation = negation'

negation' :: UnaryOperatorContext -> Node -> (UnaryOperatorContext, Node)
negation' c d@(node_id, Node position pos_child neg_child)  = withCache_ c d $ let
    (c1, (posR, _)) = negation' c (getNode c pos_child)
    (c2, (negR, _)) = negation' c1 (getNode c1 neg_child)
    in insert c2 $ Node position posR negR
negation' c d@(node_id, InfNodes position dc p n) = withCache_ c d $ let
    (c1, (r_dc, _)) = negation' c (getNode c dc)
    (c2, (r_n, _)) = negation' c1 (getNode c1 n)
    (c3, (r_p, _)) = negation' c2 (getNode c2 p)
        in insert c3 $ InfNodes position r_dc r_p r_n
negation' c d@(node_id, EndInfNode a) = withCache_ c  d $ let
    (c1, (result, _)) = negation' c (getNode c a)
    in insert c1 $ EndInfNode result
negation' c (_, Leaf b) = (c, ((hash $ Leaf (not b), 0), Leaf (not b)))
negation' c u@(_, Unknown) = (c, u)

-- ==========================================================================================================
-- * Unary Operation Typeclass and Instances
-- ==========================================================================================================

type DdUnary :: Inf -> Constraint
class DdUnary a where
    swap_node_set :: UnaryOperatorContext -> [Position] -> Node -> (UnaryOperatorContext, Node)
    swap_node_set' :: UnaryOperatorContext -> [Position] -> Node -> (UnaryOperatorContext, Node)
    restrict_node_set :: UnaryOperatorContext -> [Position] -> Bool -> Node -> (UnaryOperatorContext, Node)
    restrict_node_set' :: UnaryOperatorContext -> [Position] -> Bool -> Node -> (UnaryOperatorContext, Node)
    traverse_dc_unary :: String -> UnaryOperatorContext -> NodeId -> UnaryOperatorContext

instance (DdF3 a) => DdUnary a where
    traverse_dc_unary s c@UnaryOperatorContext{un_dc_stack = dcs@(dcs', dcRs'), un_current_level = lv} d =
        if to_str @a == "Dc" then c
            else let
                -- Logic depends on which context is being used (unary/binary)
                new_dcs' = map (traverse_dc_generic @a s (dummyBin c) (getNode c d)) dcs'
                new_dcRs = map (traverse_dc_generic @a s (dummyBin c) (getNode c d)) dcRs'
                new_dcs = (new_dcs', new_dcRs)
            in c{un_dc_stack = new_dcs, un_current_level=lv}
      where
        -- Helper to satisfy traverse_dc_generic signature which expects Binary context
        dummyBin u = init_binary_context (getLookup u)

    swap_node_set c (na : nas) d@(node_id, Node position pos_child neg_child)  = let
        (b, nas') = if (reverse $ map fst $ un_current_level c) ++ [position] == na
            then (True, nas)
            else (False, na : nas)

        (c1, posR) = if nas' /= []
            then (fst traverse_pos, fst $ snd traverse_pos)
            else (c, pos_child) -- terminal case, all vars have been replaced
        traverse_pos = swap_node_set @a c_ nas' (getNode c pos_child)
        c_ = traverse_dc_unary @a "pos child" c pos_child


        (c2, negR) = if nas' /= []
            then (fst traverse_neg, fst $ snd traverse_neg)
            else (c, neg_child) -- terminal case, all vars have been replaced
        traverse_neg = swap_node_set @a c1_ nas' (getNode c1 neg_child)
        c1_ = traverse_dc_unary @a "neg child" (reset_stack_un c1 c) neg_child

        -- Use a dummy BinaryOperatorContext to perform elimination since it's shared logic
        in if b
            then undefined -- logic from original: requires crossover to Binary logic
            else undefined


    swap_node_set c nas d@(node_id, InfNodes position dc p n) =  let
        c_ = add_to_stack_ (position, Dc) (((0, 0), Unknown), ((0, 0), Unknown)) c
        (c1, dcR) = swap_node_set @Dc (traverse_dc_unary @a "inf dc" c_ dc) nas (getNode c dc)
        c2_ = add_to_stack_ (position, Neg) (getNode c1 dc, dcR) (reset_stack_un c1 c)
        (c2, nR) = swap_node_set @Neg (traverse_dc_unary @a "inf neg" c2_ n) nas (getNode c1 n)
        c3_ = add_to_stack_ (position, Pos) (getNode c2 dc, dcR) (reset_stack_un c2 c)
        (c3, pR) = swap_node_set @Pos (traverse_dc_unary @a "inf pos" c3_ p) nas (getNode c2 p)

        in undefined -- todo for absorb; we should infer nodes for zdd side...


    swap_node_set c nas d@(node_id, EndInfNode child) =  let
        (c_, inf) = pop_stack_ c
        c' = traverse_dc_unary @a "endinf" c_ node_id
        (c'', (r, _)) = case inf of
             Dc -> swap_node_set @Dc c' nas (getNode c child)
             Pos -> swap_node_set @Pos c' nas (getNode c child)
             Neg -> swap_node_set @Neg c' nas (getNode c child)
        in undefined

    swap_node_set c nas b@(_, Leaf _) = (c, b)
    swap_node_set c nas u@(_, Unknown) = (c, u)

    -- do inference whenever the node which should be swapped is eliminated
    swap_node_set' c (na : nas) d@(node_id, Node position pos_child neg_child) = if (reverse $ map fst $ un_current_level c) ++ [position] > na
        then let (c', d') = inferNode @a c (last na) d
            in swap_node_set @a c' (na : nas) d'
        else swap_node_set @a c (na : nas) d
    swap_node_set' c (na : nas) d@(node_id, InfNodes position dc p n) = if (reverse $ map fst $ un_current_level c) ++ [position] > na
        -- todo! infer the infnode which is needed to reach the flip node
        then let (c', d') = inferInfNode @a c (last na) d
            in swap_node_set @a c' (na : nas) d'
        else swap_node_set @a c (na : nas) d
    swap_node_set' c (na : nas) d = swap_node_set @a c (na : nas) d

    restrict_node_set c (na : nas) b d@(node_id, Node position pos_child neg_child)  = let
        (b', nas') = if (reverse $ map fst $ un_current_level c) ++ [position] == na
            then (True, nas)
            else (False, na : nas)

        (c1, posR) = if nas' /= []
            then (fst traverse_pos, fst $ snd traverse_pos)
            else (c, pos_child) -- terminal case, all vars have been replaced
        traverse_pos = restrict_node_set @a c_ nas' b (getNode c pos_child)
        c_ = traverse_dc_unary @a "pos child" c pos_child

        (c2, negR) = if nas' /= []
            then (fst traverse_neg, fst $ snd traverse_neg)
            else (c, neg_child) -- terminal case, all vars have been replaced
        traverse_neg = restrict_node_set @a c1_ nas' b (getNode c1 neg_child)
        c1_ = traverse_dc_unary @a "neg child" (reset_stack_un c1 c) neg_child

        in undefined

    restrict_node_set c nas b d@(node_id, InfNodes position dc p n) =
        let
        c_ = add_to_stack_ (position, Dc) (((0, 0), Unknown), ((0, 0), Unknown)) c
        (c1, dcR) = restrict_node_set @Dc (traverse_dc_unary @a "inf dc" c_ dc) nas b (getNode c dc)
        c2_ = add_to_stack_ (position, Neg) (getNode c1 dc, dcR) (reset_stack_un c1 c)
        (c2, nR) = restrict_node_set @Neg (traverse_dc_unary @a "inf neg" c2_ n) nas b (getNode c1 n)
        c3_ = add_to_stack_ (position, Pos) (getNode c2 dc, dcR) (reset_stack_un c2 c)
        (c3, pR) = restrict_node_set @Pos (traverse_dc_unary @a "inf pos" c3_ p) nas b (getNode c2 p)

        in undefined

    restrict_node_set c nas b d@(node_id, EndInfNode child) =  let
        (c_, inf) = pop_stack_ c
        c' = traverse_dc_unary @a "endinf" c_ node_id
        (c'', (r, _)) = case inf of
             Dc -> restrict_node_set @Dc c' nas b (getNode c child)
             Pos -> restrict_node_set @Pos c' nas b (getNode c child)
             Neg -> restrict_node_set @Neg c' nas b (getNode c child)
        in undefined

    restrict_node_set c nas _ b@(_, Leaf _) = (c, b)
    restrict_node_set c nas _ u@(_, Unknown) = (c, u)

    restrict_node_set c n a b = error ("nonexhaustive " ++ "\n c: \n" ++ show (getLookup c) ++ "\n n: \n" ++ show n ++ "\n a: \n" ++ show a ++ "\n b: \n" ++ show b)

    -- do inference whenever the node which should be restricted is eliminated
    restrict_node_set' c (na : nas) b d@(node_id, Node position pos_child neg_child) = if (reverse $ map fst $ un_current_level c) ++ [position] > na
        then let (c', d') = inferNode @a c (last na) d
            in restrict_node_set @a c' (na : nas) b d'
        else restrict_node_set @a c (na : nas) b d
    restrict_node_set' c (na : nas) b d@(node_id, InfNodes position dc p n) = if (reverse $ map fst $ un_current_level c) ++ [position] > na
        -- todo! infer the infnode which is needed to reach the flip node
        then let (c', d') = inferInfNode @a c (last na) d
            in restrict_node_set @a c' (na : nas) b d'
        else restrict_node_set @a c (na : nas) b d
    restrict_node_set' c (na : nas) b d = restrict_node_set @a c (na : nas) b d