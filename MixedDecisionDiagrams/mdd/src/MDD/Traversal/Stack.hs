{-# LANGUAGE MultiWayIf #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}

module MDD.Traversal.Stack
  ( pop_dcA'
  , pop_dcB'
  , pop_dcA''
  , pop_dcB''
  , add_to_stack
  , pop_stack'
  , reset_stack_bin
  , add_to_stack_
  , add_to_level_
  , pop_stack_
  , reset_stack_un
  , DCBranch(..)
  , pop_dc
  , pop_dc'
  , move_dc
  , traverse_dc_generic
  ) where

import MDD.Types
import MDD.Traversal.Context
import MDD.Extra.Draw (show_node)

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
add_to_stack class (dcA, dcB, dcR) ctx@BCxt{bin_dc_stack = (dcAs, dcBs, dcRs)} =
    let (lvsA, lvsB) = bin_current_level ctx in
    ctx{bin_dc_stack = (dcA : dcAs, dcB : dcBs, dcR : dcRs), bin_current_level = (class : lvsA, class : lvsB)}

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

pop_stackA :: BiOpContext -> (BiOpContext, Inf)
pop_stackA ctx =
    let (_ : lvA@(_, infA) : lvsA, lvsB) = bin_current_level ctx
    in (ctx{bin_current_level = (lvA : lvsA, lvsB)}, infA)

pop_stackB :: BiOpContext -> (BiOpContext, Inf)
pop_stackB ctx =
    let (lvsA, _ : lvB@(_, infB) : lvsB) = bin_current_level ctx
    in (ctx{bin_current_level = (lvsA, lvB : lvsB)}, infB)

reset_stack_bin :: BiOpContext -> BiOpContext -> BiOpContext
reset_stack_bin new old = new { bin_dc_stack = bin_dc_stack old, bin_current_level = bin_current_level old }

add_to_stack_ :: (Int, Inf) -> (Node, Node) -> UnOpContext -> UnOpContext
add_to_stack_ class (dc, dcR) ctx@UCxt{un_dc_stack = dcRs} =
    let lvs = un_current_level ctx in
    ctx{un_dc_stack = dcR : dcRs, un_current_level = (class : lvs)}

add_to_level_ :: (Int, Inf) -> UnOpContext -> UnOpContext
add_to_level_ class ctx =
    let lvs = un_current_level ctx in
    ctx{un_current_level = class : lvs}

pop_stack_ :: UnOpContext -> (UnOpContext, Inf)
pop_stack_ ctx@UCxt{un_dc_stack = dcRs, un_current_level = lvs} =
    let (_ : lv@(_, inf) : lvs') = lvs
        n = (length lvs') - 1
        trim k xs = if length xs <= k then xs else drop (length xs - k) xs
    in (ctx{un_dc_stack = trim n dcRs, un_current_level = lv : lvs'}, inf)

reset_stack_un :: UnOpContext -> UnOpContext -> UnOpContext
reset_stack_un new old = new { un_dc_stack = un_dc_stack old, un_current_level = un_current_level old }

data DCBranch = DcA | DcB
  deriving (Eq, Show)

pop_dc :: DCBranch -> BiOpContext -> (BiOpContext, Node)
pop_dc DcA = pop_dcA'
pop_dc DcB = pop_dcB'

pop_dc' :: DCBranch -> BiOpContext -> (BiOpContext, Node)
pop_dc' DcA = pop_dcA''
pop_dc' DcB = pop_dcB''

move_dc :: (HasNodeLookup c) => c -> String -> Node -> Node
move_dc c m node =
    case node of
        (_, Node position pos_child neg_child) ->
            if m == "pos child" then getNode c pos_child
            else if m == "neg child" then getNode c neg_child
            else error $ "processStackElement: undefined move '" ++ m ++ "' for Node pattern: " ++ show_node c node

        (_, EndClassNode child) ->
            if m == "endclass" then getNode c child
            else (if m `elem` ["pos child", "neg child", "class pos", "class neg", "class dc"] then node
            else error $ "processStackElement: undefined move '" ++ m ++ "' for EndClassNode pattern: " ++ show_node c node)

        (_, ClassNode position dc p n) ->
            if m == "class pos" then getNode c p
            else if m == "class neg" then getNode c n
            else if m == "class dc" then getNode c dc
            else error $ "processStackElement: undefined move '" ++ m ++ "' for ClassNode pattern: " ++ show_node c node

        (_, Leaf _) ->
            node
        (_, Unknown) ->
            node
        _ -> error $ "processStackElement: Unhandled Node pattern"


traverse_dc_generic :: (HasNodeLookup c) =>
    (String -> c -> Node -> Int -> Node)  -- ^ catchup function (from DdF3 instance)
    -> String -> c -> Node -> Node -> Node
traverse_dc_generic catchupFn s c refNode dcNode =
    let result = case (dcNode, refNode) of
            ( (_, Node position _ _), (_, Node idx _ _) ) ->
                if | position > idx -> dcNode -- if the dcnode is ahead, we do not have to infer a node and apply the move, since both edges lead to the same child. returning as is is more efficient.
                   | position == idx -> move_dc c s dcNode
                   | position < idx -> move_dc c s (catchupFn s c dcNode idx)
            ( (_, Node{}), (_, Leaf _) ) = undefined -- there are no moves applicable on refnode=leaf, throw an error in such a case?
            ( (_, Node{}), (_, EndClassNode{}) ) = undefined -- dc needs to be caught up until an endclassnode is reached
            ( (_, EndClassNode{}), (_, EndClassNode{}) ) -> move_dc c s dcNode -- only endclassnode move is valid, apply it
            ( _, (_, Unknown) ) -> dcNode -- if a dcnode is unknown, we can leave it be (it will be resolved to a more outer layer)
            ( (_, Unknown), _ ) -> undefined -- it should not be possible to receive an unknown as refnode (should be resolved before calling dc_traversal)
            ( (_, ClassNode position _ _ _), (_, ClassNode idx _ _ _) ) ->
                if | position > idx -> dcNode -- if the dcnode is ahead, we do not have to infer a node and apply the move, since both edges lead to the same child. returning as is is more efficient.
                   | position == idx -> move_dc c s dcNode
                   | position < idx -> undefined
            ( (_, Leaf _), (_, EndClassNode{}) ) -> undefined -- infer an endclass node for dc, and then pass through it: keeps dcnode the same.
            ( (_, ClassNode _ dc _ _), (_, EndClassNode{}) ) -> undefined -- catch dcnode up until endclass node... so this would require inference of class node for the refnode side inside catchup. do not fix this one case yet, in a later step we will design a solution.
    in result

traverse_dcA_endclass :: BiOpContext -> NodeId -> BiOpContext
traverse_dcA_endclass ctx refA =
    let (dcAs, dcBs, dcRs) = bin_dc_stack ctx
        refNode = getNode ctx refA
        moveDc dc = traverse_dc_generic (\_ _ n _ -> n) "endclass" ctx refNode dc
        new_dcAs = map moveDc dcAs
    in ctx { bin_dc_stack = (new_dcAs, dcBs, dcRs) }

traverse_dcB_endclass :: BiOpContext -> NodeId -> BiOpContext
traverse_dcB_endclass ctx refB =
    let (dcAs, dcBs, dcRs) = bin_dc_stack ctx
        refNode = getNode ctx refB
        moveDc dc = traverse_dc_generic (\_ _ n _ -> n) "endclass" ctx refNode dc
        new_dcBs = map moveDc dcBs
    in ctx { bin_dc_stack = (dcAs, new_dcBs, dcRs) }
