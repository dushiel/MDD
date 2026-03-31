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
  , traverse_dcA_endclass
  , traverse_dcB_endclass
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
add_to_stack cls (dcA, dcB, dcR) ctx@BCxt{bin_dc_stack = (dcAs, dcBs, dcRs)} =
    let (lvsA, lvsB) = bin_current_level ctx in
    ctx{bin_dc_stack = (dcA : dcAs, dcB : dcBs, dcR : dcRs), bin_current_level = (cls : lvsA, cls : lvsB)}

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
add_to_stack_ cls (dc, dcR) ctx@UCxt{un_dc_stack = dcRs} =
    let lvs = un_current_level ctx in
    ctx{un_dc_stack = dcR : dcRs, un_current_level = (cls : lvs)}

add_to_level_ :: (Int, Inf) -> UnOpContext -> UnOpContext
add_to_level_ cls ctx =
    let lvs = un_current_level ctx in
    ctx{un_current_level = cls : lvs}

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
    (c -> Node -> Int -> Node)  -- ^ catchup function (from DdF3 instance)
    -> String                   -- ^ inference type name ("Dc", "Pos", "Neg")
    -> String                   -- ^ move string ("pos child", "neg child", "class dc", etc.)
    -> c -> Node -> Node -> Node
traverse_dc_generic catchupFn infType s c refNode dcNode =
    -- Guard rail: validate move string vs refNode type
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
                | otherwise       -> move_dc c s (catchupFn c dcNode idx)

            -- Case 3: (Node, EndClassNode) — dc is behind, catch up to terminal then move
            ((_, Node{}), (_, EndClassNode{})) ->
                move_dc c s (catchupFn c dcNode (-1))

            -- Case 4: (EndClassNode, EndClassNode) — both exiting class
            ((_, EndClassNode{}), (_, EndClassNode{})) -> move_dc c s dcNode

            -- Case 7: (ClassNode, ClassNode) — both are class nodes
            ((_, ClassNode position _ _ _), (_, ClassNode idx _ _ _))
                | position > idx  -> dcNode
                | position == idx -> move_dc c s dcNode
                | otherwise       -> error "traverse_dc_generic: ClassNode catchup not yet implemented (dcNode class pos < refNode class pos)"

            -- Case 8: (Leaf, EndClassNode) — dc terminated at Leaf, ref exiting class
            ((_, Leaf{}), (_, EndClassNode{})) -> dcNode

            -- Case 9: (ClassNode, EndClassNode) — dc has ClassNode, ref exiting (deferred)
            ((_, ClassNode{}), (_, EndClassNode{})) ->
                error "traverse_dc_generic: ClassNode vs EndClassNode catchup not yet implemented"

            -- Case 10: (Leaf, Node) or (Leaf, ClassNode) — dc terminated
            ((_, Leaf{}), (_, Node{})) -> dcNode
            ((_, Leaf{}), (_, ClassNode{})) -> dcNode

            -- Case 11: (EndClassNode, Node) — dc exited class, ref still inside
            ((_, EndClassNode{}), (_, Node{})) -> dcNode

            -- Case 13: (EndClassNode, ClassNode) — dc exited, ref at ClassNode
            -- Infer a ClassNode for dc (content on @a's branch), then apply move.
            -- Result is dcNode when infType's branch matches s, Unknown otherwise.
            ((_, EndClassNode{}), (_, ClassNode{})) ->
                let contentBranch = case infType of
                        "Dc"  -> "class dc"
                        "Pos" -> "class pos"
                        "Neg" -> "class neg"
                        _     -> error $ "traverse_dc_generic: unknown infType '" ++ infType ++ "'"
                in if s == contentBranch
                    then dcNode
                    else ((0,0), Unknown)

            -- Case 12: (Node, ClassNode) or (ClassNode, Node) — structural mismatch
            ((_, Node{}), (_, ClassNode{})) ->
                error "traverse_dc_generic: Node vs ClassNode structural mismatch"
            ((_, ClassNode{}), (_, Node{})) ->
                error "traverse_dc_generic: ClassNode vs Node structural mismatch"

            -- Case 2/6: refNode is Leaf or Unknown — caught by guard rail above,
            -- but handle Unknown dcNode + any refNode via Case 5 above.
            _ -> error $ "traverse_dc_generic: unhandled case (dcNode=" ++ show_node c dcNode
                      ++ ", refNode=" ++ show_node c refNode ++ ")"

traverse_dcA_endclass :: BiOpContext -> NodeId -> BiOpContext
traverse_dcA_endclass ctx refA =
    let (dcAs, dcBs, dcRs) = bin_dc_stack ctx
        refNode = getNode ctx refA
        moveDc dc = traverse_dc_generic (\_ n _ -> n) "Dc" "endclass" ctx refNode dc
        new_dcAs = map moveDc dcAs
    in ctx { bin_dc_stack = (new_dcAs, dcBs, dcRs) }

traverse_dcB_endclass :: BiOpContext -> NodeId -> BiOpContext
traverse_dcB_endclass ctx refB =
    let (dcAs, dcBs, dcRs) = bin_dc_stack ctx
        refNode = getNode ctx refB
        moveDc dc = traverse_dc_generic (\_ n _ -> n) "Dc" "endclass" ctx refNode dc
        new_dcBs = map moveDc dcBs
    in ctx { bin_dc_stack = (dcAs, new_dcBs, dcRs) }
