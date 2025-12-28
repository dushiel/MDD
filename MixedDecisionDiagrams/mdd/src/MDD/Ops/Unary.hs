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
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Move brackets to avoid $" #-}
{-# HLINT ignore "Use second" #-}

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
-- * Unary Elimination Rules
-- ==========================================================================================================

-- | Apply elimination rules for unary operations (similar to binary but for UnaryOperatorContext)
-- This uses a temporary binary context to leverage the existing applyElimRule logic from DdF3
applyElimRule_unary :: forall a. (DdF3 a) => UnaryOperatorContext -> Dd -> (UnaryOperatorContext, Node)
applyElimRule_unary c d =
    -- Convert to binary context temporarily to use the existing applyElimRule logic
    -- This works because applyElimRule only uses HasNodeLookup methods, not the stack
    let binCtx = init_binary_context (getLookup c)
        (binCtx', result) = applyElimRule @a binCtx d
    in (c { un_nodelookup = getLookup binCtx' }, result)

-- | Apply elimination rules for unary operations (takes tuple form)
applyElimRule'_unary :: forall a. (DdF3 a) => (UnaryOperatorContext, Dd) -> (UnaryOperatorContext, Node)
applyElimRule'_unary (c, d) = applyElimRule_unary @a c d

-- ==========================================================================================================
-- * Redundancy Elimination (absorb) for Unary
-- ==========================================================================================================

absorb_unary :: (UnaryOperatorContext, Node) -> (UnaryOperatorContext, Node)
absorb_unary (c, n) = absorb'_unary (c, n)

absorb'_unary :: (UnaryOperatorContext, Node) -> (UnaryOperatorContext, Node)
-- | given a dcR and a pos or ng results, sets sub-paths in the local inf-domain which agree with the dcR to unknown ("absorbing them")
absorb'_unary (c@UnaryOperatorContext{un_dc_stack = (dcs, dc@(_, Unknown) : fs) }, a)  =
    let (c', r) = absorb'_unary (c{un_dc_stack = (dcs, fs)}, a) in (c, r)
absorb'_unary (c@UnaryOperatorContext{un_dc_stack = (_, dc : fs) }, a@(_, Unknown)) = (c, a)
absorb'_unary (c@UnaryOperatorContext{un_dc_stack = (_, dc : fs) }, a@(_, Leaf _))
    | a == dc = (c, ((0,0), Unknown))
    | otherwise = (c,a)
absorb'_unary (c@UnaryOperatorContext{un_dc_stack = (_, dc@(_, Leaf _)  : fs) }, a@(_, InfNodes _ d p n))  =  let
    (_, r1) = absorb'_unary (c, getNode c d)
    (_, r2) = absorb'_unary (c, getNode c p)
    (_, r3) = absorb'_unary (c, getNode c n)
    in if r1 == r2 && r2 == r3 then (c, ((0,0), Unknown)) else (c, a)
absorb'_unary (c@UnaryOperatorContext{un_dc_stack = (_, dc@(_, Leaf _)  : fs) }, a@(_, EndInfNode a_child)) = if getNode c a_child == dc then (c, ((0,0), Unknown)) else (c, a)
absorb'_unary (c@UnaryOperatorContext{un_dc_stack = (_, dc@(_, EndInfNode dc') : fs) }, a@(_, EndInfNode a'))
    | a' == dc' = (c, ((0,0), Unknown))
    | otherwise = (c,a)
absorb'_unary (c@UnaryOperatorContext{un_dc_stack = (_, dc : fs) }, a)
    | a == dc = (c, ((0,0), Unknown))
    | otherwise = (c,a)
absorb'_unary (c@UnaryOperatorContext{un_dc_stack = (_, []) }, a) = (c, a)

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

        in if b'  -- hit, so remove na from nas
            then if b  -- depending on b, take positive or negative evaluation
                then applyElimRule_unary @a c2 $ Node position posR posR
                else applyElimRule_unary @a c2 $ Node position negR negR
            else applyElimRule_unary @a c2 $ Node position posR negR  -- otherwise continue with original nas and no quantification

    restrict_node_set c nas b d@(node_id, InfNodes position dc p n) =
        let
        c_ = add_to_stack_ (position, Dc) (((0, 0), Unknown), ((0, 0), Unknown)) c
        (c1, dcR) = restrict_node_set @Dc (traverse_dc_unary @a "inf dc" c_ dc) nas b (getNode c dc)
        c2_ = add_to_stack_ (position, Neg) (getNode c1 dc, dcR) (reset_stack_un c1 c)
        (c2, nR) = restrict_node_set @Neg (traverse_dc_unary @a "inf neg" c2_ n) nas b (getNode c1 n)
        c3_ = add_to_stack_ (position, Pos) (getNode c2 dc, dcR) (reset_stack_un c2 c)
        (c3, pR) = restrict_node_set @Pos (traverse_dc_unary @a "inf pos" c3_ p) nas b (getNode c2 p)

        in absorb_unary $ applyElimRule_unary @a (reset_stack_un c3 c) $ InfNodes position (fst dcR) (fst pR) (fst nR)

    restrict_node_set c nas b d@(node_id, EndInfNode child) =  let
        (c_, inf) = pop_stack_ c
        c' = traverse_dc_unary @a "endinf" c_ node_id
        (c'', (r, _)) = case inf of
             Dc -> restrict_node_set @Dc c' nas b (getNode c child)
             Pos -> restrict_node_set @Pos c' nas b (getNode c child)
             Neg -> restrict_node_set @Neg c' nas b (getNode c child)
        in absorb_unary $ applyElimRule'_unary @a (reset_stack_un c'' c, EndInfNode r)

    restrict_node_set c nas _ b@(_, Leaf _) = absorb_unary (c, b)
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