module MDD.Stack where

import MDD.Types
import MDD.Context

-- ==========================================================================================================
-- * Stack Manipulation for BiOpContext
-- ==========================================================================================================

pop_dcA' :: BiOpContext -> (BiOpContext, Node)
pop_dcA' ctx@BCxt{bin_dc_stack = (dcA : fs, dcB, dcR), bin_current_level = ((i, _) : lvsA, lvB : lvsB)} =
    (ctx{bin_dc_stack = (fs, dcB, dcR), bin_current_level = ((i, Dc) : lvsA, lvB : lvsB)}, dcA)
pop_dcA' _ = error "requested dcA from empty stack"

pop_dcB' :: BiOpContext -> (BiOpContext, Node)
pop_dcB' ctx@BCxt{bin_dc_stack = (dcA, dcB : fs, dcR), bin_current_level = (lvA : lvsA, (i, _) : lvsB)} =
    (ctx{bin_dc_stack = (dcA, fs, dcR), bin_current_level = (lvA : lvsA, (i, Dc) : lvsB)}, dcB)
pop_dcB' _ = error "requested dcB from empty stack"

pop_dcA'' :: BiOpContext -> (BiOpContext, Node)
pop_dcA'' ctx@BCxt{bin_dc_stack = (dcA : fs, dcB, dcR), bin_current_level = (_ : (i, _) : lvsA, lvB : lvsB)} =
    (ctx{bin_dc_stack = (fs, dcB, dcR), bin_current_level = ((i, Dc) : lvsA, lvB : lvsB)}, dcA)
pop_dcA'' _ = error "requested dcA from empty stack"

pop_dcB'' :: BiOpContext -> (BiOpContext, Node)
pop_dcB'' ctx@BCxt{bin_dc_stack = (dcA, dcB : fs, dcR), bin_current_level = (lvA : lvsA, _ : (i, _) : lvsB)} =
    (ctx{bin_dc_stack = (dcA, fs, dcR), bin_current_level = (lvA : lvsA, (i, Dc) : lvsB)}, dcB)
pop_dcB'' _ = error "requested dcB from empty stack"

add_to_stack :: (Int, Inf) -> (Node, Node, Node) -> BiOpContext -> BiOpContext
add_to_stack inf (dcA, dcB, dcR) ctx@BCxt{bin_dc_stack = (dcAs, dcBs, dcRs)} =
    let (lvsA, lvsB) = bin_current_level ctx in
    ctx{bin_dc_stack = (dcA : dcAs, dcB : dcBs, dcR : dcRs), bin_current_level = (inf : lvsA, inf : lvsB)}

pop_stack' :: BiOpContext -> (BiOpContext, (Inf, Inf))
pop_stack' ctx@BCxt{bin_dc_stack = (dcAs, dcBs, dcRs), bin_current_level = (lAs, lBs)}
    | length lAs == length lBs = let (_ : lvA@(_, infA) : lvsA, _: lvB@(_, infB) : lvsB) = bin_current_level ctx in
        (ctx{bin_dc_stack = (trim n dcAs, trim n dcBs, trim n dcRs), bin_current_level= (lvA : lvsA, lvB : lvsB)}, (infA, infB))
    | length lAs > length lBs = let (_ : lvA@(_, infA) : lvsA, lvB@(_, infB) : lvsB) = bin_current_level ctx in
        (ctx{bin_dc_stack = (trim n dcAs, trim n dcBs, trim n dcRs), bin_current_level= (lvA : lvsA, lvB : lvsB)}, (infA, infB))
    | length lAs < length lBs = let (lvA@(_, infA) : lvsA, _ : lvB@(_, infB) : lvsB) = bin_current_level ctx in
        (ctx{bin_dc_stack = (trim n dcAs, trim n dcBs, trim n dcRs), bin_current_level= (lvA : lvsA, lvB : lvsB)}, (infA, infB))
        where
            n = (max (length lAs) (length lBs)) - 1
            trim k xs = if length xs <= k then xs else drop (length xs - k) xs

reset_stack_bin :: BiOpContext -> BiOpContext -> BiOpContext
reset_stack_bin new old = new { bin_dc_stack = bin_dc_stack old, bin_current_level = bin_current_level old }

-- ==========================================================================================================
-- * Stack Manipulation for UnOpContext
-- ==========================================================================================================

add_to_stack_ :: (Int, Inf) -> (Node, Node) -> UnOpContext -> UnOpContext
add_to_stack_ inf (dc, dcR) ctx@UCxt{un_dc_stack = dcRs} =
    let lvs = un_current_level ctx in
    ctx{un_dc_stack = dcR : dcRs, un_current_level = (inf : lvs)}  -- Only track dcR, dc is unused

add_to_level_ :: (Int, Inf) -> UnOpContext -> UnOpContext
add_to_level_ inf ctx =
    let lvs = un_current_level ctx in
    ctx{un_current_level = inf : lvs}

pop_stack_ :: UnOpContext -> (UnOpContext, Inf)
pop_stack_ ctx@UCxt{un_dc_stack = dcRs, un_current_level = lvs} =
    let (_ : lv@(_, inf) : lvs') = lvs
        n = (length lvs') - 1
        trim k xs = if length xs <= k then xs else drop (length xs - k) xs
    in (ctx{un_dc_stack = trim n dcRs, un_current_level = lv : lvs'}, inf)  -- Only track dcRs

reset_stack_un :: UnOpContext -> UnOpContext -> UnOpContext
reset_stack_un new old = new { un_dc_stack = un_dc_stack old, un_current_level = un_current_level old }