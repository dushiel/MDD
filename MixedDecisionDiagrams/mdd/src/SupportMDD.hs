{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes, KindSignatures #-}
{-# HLINT ignore "Use notElem" #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# HLINT ignore "Eta reduce" #-}
{-# HLINT ignore "Move brackets to avoid $" #-}
{-# HLINT ignore "Use guards" #-}
{-# LANGUAGE MultiWayIf #-}

module SupportMDD where
import MDD
import Data.Kind
import Data.Bimap ()


-- ==========================================================================================================
-- * Stack Manipulation for BinaryOperatorContext
-- ==========================================================================================================

get_dcA :: BinaryOperatorContext -> Node
get_dcA ctx@BinaryOperatorContext{bin_dc_stack = (dcA : fs, dcB, dcR)} = dcA
get_dcA ctx@BinaryOperatorContext{bin_dc_stack = ([], dcB, dcR)} = error "requeated dcA from empty stack"

get_dcB :: BinaryOperatorContext -> Node
get_dcB ctx@BinaryOperatorContext{bin_dc_stack = (dcA, dcB : fs, dcR)} = dcB
get_dcB ctx@BinaryOperatorContext{bin_dc_stack = (dcA, [], dcR)} = error "requeated dcB from empty stack"

get_dcR :: BinaryOperatorContext -> Node
get_dcR ctx@BinaryOperatorContext{bin_dc_stack = (dcA, dcB, dcR : fs)} = dcR
get_dcR ctx@BinaryOperatorContext{bin_dc_stack = (dcA, dcB, [])} = error "requeated dcR from empty stack"

pop_dcA :: BinaryOperatorContext -> (BinaryOperatorContext, Node)
pop_dcA ctx@BinaryOperatorContext{bin_dc_stack = (dcA : fs, dcB, dcR), bin_current_level = ((i, _) : lvsA, lvB : lvsB)} =
    (ctx{bin_dc_stack = (fs, dcB, dcR), bin_current_level = (lvsA, lvB : lvsB)}, dcA) --`debug` "popped dcA"
pop_dcA ctx@BinaryOperatorContext{bin_dc_stack = ([], dcB, dcR)} = error "requeated dcA from empty stack"

pop_dcB :: BinaryOperatorContext -> (BinaryOperatorContext, Node)
pop_dcB ctx@BinaryOperatorContext{bin_dc_stack = (dcA, dcB : fs, dcR), bin_current_level = (lvA : lvsA, (i, _) : lvsB)} =
    (ctx{bin_dc_stack = (dcA, fs, dcR), bin_current_level = (lvA : lvsA, lvsB)}, dcB)
pop_dcB ctx@BinaryOperatorContext{bin_dc_stack = (dcA, [], dcR)} = error "requeated dcB from empty stack"

pop_dcA' :: BinaryOperatorContext -> (BinaryOperatorContext, Node)
pop_dcA' ctx@BinaryOperatorContext{bin_dc_stack = (dcA : fs, dcB, dcR), bin_current_level = ((i, _) : lvsA, lvB : lvsB)} =
    (ctx{bin_dc_stack = (fs, dcB, dcR), bin_current_level = ((i, Dc) : lvsA, lvB : lvsB)}, dcA) --`debug` "popped dcA"
pop_dcA' ctx@BinaryOperatorContext{bin_dc_stack = ([], dcB, dcR)} = error "requeated dcA from empty stack"

pop_dcB' :: BinaryOperatorContext -> (BinaryOperatorContext, Node)
pop_dcB' ctx@BinaryOperatorContext{bin_dc_stack = (dcA, dcB : fs, dcR), bin_current_level = (lvA : lvsA, (i, _) : lvsB)} =
    (ctx{bin_dc_stack = (dcA, fs, dcR), bin_current_level = (lvA : lvsA, (i, Dc) : lvsB)}, dcB)
pop_dcB' ctx@BinaryOperatorContext{bin_dc_stack = (dcA, [], dcR)} = error "requeated dcB from empty stack"

pop_dcA'' :: BinaryOperatorContext -> (BinaryOperatorContext, Node)
pop_dcA'' ctx@BinaryOperatorContext{bin_dc_stack = (dcA : fs, dcB, dcR), bin_current_level = (_ : (i, _) : lvsA, lvB : lvsB)} =
    (ctx{bin_dc_stack = (fs, dcB, dcR), bin_current_level = ((i, Dc) : lvsA, lvB : lvsB)}, dcA) --`debug` "popped dcA"
pop_dcA'' ctx@BinaryOperatorContext{bin_dc_stack = ([], dcB, dcR)} = error "requeated dcA from empty stack"

pop_dcB'' :: BinaryOperatorContext -> (BinaryOperatorContext, Node)
pop_dcB'' ctx@BinaryOperatorContext{bin_dc_stack = (dcA, dcB : fs, dcR), bin_current_level = (lvA : lvsA, _ : (i, _) : lvsB)} =
    (ctx{bin_dc_stack = (dcA, fs, dcR), bin_current_level = (lvA : lvsA, (i, Dc) : lvsB)}, dcB)
pop_dcB'' ctx@BinaryOperatorContext{bin_dc_stack = (dcA, [], dcR)} = error "requeated dcB from empty stack"

pop_dcR :: BinaryOperatorContext -> (BinaryOperatorContext, Node)
pop_dcR ctx@BinaryOperatorContext{bin_dc_stack = (dcA, dcB, dcR : fs)} = (ctx{bin_dc_stack = (dcA, dcB, fs)}, dcR)
pop_dcR ctx@BinaryOperatorContext{bin_dc_stack = (dcA, dcB, [])} = error "requeated dcR from empty stack"

add_to_stack :: (Int, Inf) -> (Node, Node, Node) -> BinaryOperatorContext -> BinaryOperatorContext
add_to_stack inf (dcA, dcB, dcR) ctx@BinaryOperatorContext{bin_dc_stack = (dcAs, dcBs, dcRs)} =
    let (lvsA, lvsB) = bin_current_level ctx in
    ctx{bin_dc_stack = (dcA : dcAs, dcB : dcBs, dcR : dcRs), bin_current_level = (inf : lvsA, inf : lvsB)}

replace_on_stack :: (Int, Inf) -> (Node, Node, Node) -> BinaryOperatorContext -> BinaryOperatorContext
replace_on_stack inf (dcA, dcB, dcR) ctx@BinaryOperatorContext{bin_dc_stack = (_ : dcAs, _ : dcBs, _ : dcRs), bin_current_level = (lvA : lvsA, lvB : lvsB)} =
    ctx{bin_dc_stack = (dcA : dcAs, dcB : dcBs, dcR : dcRs), bin_current_level = (inf : lvsA, inf : lvsB)}

-- removes the current level and returns information about the previous level
pop_stack' :: BinaryOperatorContext -> (BinaryOperatorContext, (Inf, Inf))
pop_stack' ctx@BinaryOperatorContext{bin_dc_stack = (dcAs, dcBs, dcRs), bin_current_level = (lAs, lBs)}
    | length lAs == length lBs = let (_ : lvA@(_, infA) : lvsA, _: lvB@(_, infB) : lvsB) = bin_current_level ctx in
        (ctx{bin_dc_stack = (trimListToSize n dcAs, trimListToSize n dcBs , trimListToSize n dcRs ), bin_current_level= (lvA : lvsA, lvB : lvsB)}, (infA, infB))
    | length lAs > length lBs = let (_ : lvA@(_, infA) : lvsA, lvB@(_, infB) : lvsB) = bin_current_level ctx in
        (ctx{bin_dc_stack = (trimListToSize n dcAs, trimListToSize n dcBs , trimListToSize n dcRs ), bin_current_level= (lvA : lvsA, lvB : lvsB)}, (infA, infB))
    | length lAs < length lBs = let (lvA@(_, infA) : lvsA, _ : lvB@(_, infB) : lvsB) = bin_current_level ctx in
        (ctx{bin_dc_stack = (trimListToSize n dcAs, trimListToSize n dcBs , trimListToSize n dcRs ), bin_current_level= (lvA : lvsA, lvB : lvsB)}, (infA, infB))
        where n = (max (length $ lAs) (length $ lBs)) -1

func_tail :: BinaryOperatorContext -> BinaryOperatorContext
func_tail ctx@BinaryOperatorContext{bin_dc_stack = (dcA : dcAs, dcB : dcBs, dcR : dcRs), bin_current_level = (lvA@(_, infA) : lvsA, lvB@(_, infB) : lvsB)} =
    ctx{bin_dc_stack = (dcAs, dcBs, dcRs), bin_current_level=(lvsA, lvsB)}


-- ==========================================================================================================
-- * Stack Manipulation for UnaryOperatorContext
-- ==========================================================================================================

add_to_stack_ :: (Int, Inf) -> (Node, Node) -> UnaryOperatorContext -> UnaryOperatorContext
add_to_stack_ inf (dc, dcR) ctx@UnaryOperatorContext{un_dc_stack = (dcs, dcRs)} =
    let lvs = un_current_level ctx in
    ctx{un_dc_stack = (dc : dcs, dcR : dcRs), un_current_level = (inf : lvs)}

add_to_level_ :: (Int, Inf) -> UnaryOperatorContext -> UnaryOperatorContext
add_to_level_ inf ctx =
    let (lvs) = un_current_level ctx in
    ctx{un_current_level = inf : lvs}

-- removes the current level and returns information about the previous level
pop_stack_ :: UnaryOperatorContext -> (UnaryOperatorContext, Inf)
pop_stack_ ctx@UnaryOperatorContext{un_dc_stack = (dcs, dcRs), un_current_level = lvs} =
    let (_ : lv@(_, inf) : lvs') = un_current_level ctx
        n = (length $ lvs') - 1
    in
        (ctx{un_dc_stack = (trimListToSize n dcs, trimListToSize n dcRs ), un_current_level = lv : lvs'}, inf)


pop_current_level_ :: UnaryOperatorContext -> UnaryOperatorContext
pop_current_level_ ctx@UnaryOperatorContext{un_current_level = (_ : lvs) } = ctx{un_current_level = lvs}


-- ==========================================================================================================
-- * General Helpers
-- ==========================================================================================================

trimListToSize :: Int -> [a] -> [a]
trimListToSize n xs
  | n < 0     = xs
  | length xs <= n = xs
  | otherwise = drop (length xs - n) xs

class ResettableContext a where
    reset_stack :: a -> a -> a

instance ResettableContext BinaryOperatorContext where
    reset_stack new old = new { bin_dc_stack = bin_dc_stack old, bin_current_level = bin_current_level old }

instance ResettableContext UnaryOperatorContext where
    reset_stack new old = new { un_dc_stack = un_dc_stack old, un_current_level = un_current_level old }

class All a where
    error_display :: (HasNodeLookup c) => String -> c -> Node -> Node -> a
    error_display s c (a_id, a) (b_id, b) =
        error (show s ++ " : [Context Size: " ++ show (length $ Prelude.show (getLookup c)) ++ "] " ++ show a ++ ", " ++ show b)

instance All (NodeLookup, Node)
instance All (BinaryOperatorContext, Node)

-- Combined helper function: Processes a single Node based on the move string.
move_dc :: (HasNodeLookup c) => c -> String -> Node -> Node
move_dc c m node =
    case node of
        (_, Node position pos_child neg_child) ->
            if m == "pos child" then getNode c pos_child
            else if m == "neg child" then getNode c neg_child
            else error $ "processStackElement: undefined move '" ++ m ++ "' for Node pattern: " ++ show node

        (_, EndInfNode child) ->
            if m == "endinf" then getNode c child
            else (if m `elem` ["pos child", "neg child", "inf pos", "inf neg", "inf dc"] then node
            else error $ "processStackElement: undefined move '" ++ m ++ "' for EndInfNode pattern: " ++ show node)

        (_, InfNodes position dc p n) ->
            if m == "inf pos" then getNode c p
            else if m == "inf neg" then getNode c n
            else if m == "inf dc" then getNode c dc
            else error $ "processStackElement: undefined move '" ++ m ++ "' for InfNodes pattern: " ++ show node

        (_, Leaf _) ->
            node
        (_, Unknown) ->
            node
        _ -> error $ "processStackElement: Unhandled Node pattern: " ++ show node ++ ", move: " ++ m


-- ==========================================================================================================
-- * Static Transformation
-- ==========================================================================================================

get_static_lv :: UnaryOperatorContext -> [Int]
get_static_lv ctx = reverse (map fst (un_current_level ctx))

-- | Plan implementation: becomes Context -> Node -> (StaticNodeLookup, NodeStatic)
-- Using UnaryOperatorContext as the carrier for the current level and transient lookup.
to_static_form' :: UnaryOperatorContext -> Node -> (StaticNodeLookup, NodeStatic)
to_static_form' ctx d@(_, Node position pos_child neg_child) = let
    (nl1, (posR, _)) = to_static_form' ctx (getNode ctx pos_child)
    (nl2, (negR, _)) = to_static_form' (setLookup (unionNodeLookup (getLookup ctx) (getLookup ctx)) ctx) (getNode ctx neg_child) -- Note: simplified lookup management for recursion
    -- Actually we need a way to thread the StaticNodeLookup through the recursion.
    -- Let's define a recursive helper.
    in undefined -- Placeholder: see below for full implementation with static lookup threading

-- Better implementation threading the static lookup
to_static_form :: UnaryOperatorContext -> Node -> (StaticNodeLookup, NodeStatic)
to_static_form ctx node = go (defaultNodeMapStatic) ctx node
  where
    go :: StaticNodeLookup -> UnaryOperatorContext -> Node -> (StaticNodeLookup, NodeStatic)
    go snl c d@(_, Node position pos_child neg_child) =
        let (snl1, (posR, _)) = go snl c (getNode c pos_child)
            (snl2, (negR, _)) = go snl1 c (getNode c neg_child)
        in insert_static snl2 $ Node' (get_static_lv c ++ [position]) posR negR

    go snl c d@(_, InfNodes position dc p n) =
        let c_dc = add_to_level_ (position, Dc) c
            (snl1, (r_dc, _)) = go snl c_dc (getNode c dc)
            c_n = add_to_level_ (position, Neg) (reset_stack c_dc c)
            (snl2, (r_n, _)) = go snl1 c_n (getNode c n)
            c_p = add_to_level_ (position, Pos) (reset_stack c_n c)
            (snl3, (r_p, _)) = go snl2 c_p (getNode c p)
        in insert_static snl3 $ InfNodes' (get_static_lv c ++ [position]) r_dc r_p r_n

    go snl c d@(_, EndInfNode a) =
        let c' = pop_current_level_ c
            (snl1, (result, _)) = go snl c' (getNode c a)
        in insert_static snl1 $ EndInfNode' result

    go snl c (_, Leaf b) = insert_static snl (Leaf' b)
    go snl c (_, Unknown) = insert_static snl Unknown'


allVars :: UnaryOperatorContext -> Node -> [Position]
allVars ctx d@(_, Node position pos_child neg_child) =
  [get_static_lv ctx ++ [position]] ++
   allVars ctx (getNode ctx pos_child) ++ allVars ctx (getNode ctx neg_child)
allVars ctx d@(_, InfNodes position dc p n) =
    let c_dc = add_to_level_ (position, Dc) ctx
        c_n = add_to_level_ (position, Neg) ctx
        c_p = add_to_level_ (position, Pos) ctx
    in [get_static_lv ctx ++ [position]] ++
        allVars c_dc (getNode ctx dc) ++ allVars c_n (getNode ctx n) ++ allVars c_p (getNode ctx p)
allVars ctx d@(_, EndInfNode a) = allVars (pop_current_level_ ctx) (getNode ctx a)
allVars ctx (_, Leaf b) = []
allVars ctx (_, Unknown) = []