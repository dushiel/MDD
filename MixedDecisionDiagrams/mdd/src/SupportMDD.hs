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


import DrawMDD (debug_manipulation, debug_dc_traverse)
import Data.Bimap ()


get_dcA :: Context -> Node
get_dcA c@Context{dc_stack = (dcA : fs, dcB, dcR)} = dcA
get_dcA c@Context{dc_stack = ([], dcB, dcR)} = error "requeated dcA from empty stack"

get_dcB :: Context -> Node
get_dcB c@Context{dc_stack = (dcA, dcB : fs, dcR)} = dcB
get_dcB c@Context{dc_stack = (dcA, [], dcR)} = error "requeated dcB from empty stack"

get_dcR :: Context -> Node
get_dcR c@Context{dc_stack = (dcA, dcB, dcR : fs)} = dcR
get_dcR c@Context{dc_stack = (dcA, dcB, [])} = error "requeated dcR from empty stack"

pop_dcA :: Context -> (Context, Node)
pop_dcA c@Context{dc_stack = (dcA : fs, dcB, dcR), current_level = ((i, _) : lvsA, lvB : lvsB)} =
    (c{dc_stack = (fs, dcB, dcR), current_level = (lvsA, lvB : lvsB)}, dcA) --`debug` "popped dcA"
pop_dcA c@Context{dc_stack = ([], dcB, dcR)} = error "requeated dcA from empty stack"

pop_dcB :: Context -> (Context, Node)
pop_dcB c@Context{dc_stack = (dcA, dcB : fs, dcR), current_level = (lvA : lvsA, (i, _) : lvsB)} =
    (c{dc_stack = (dcA, fs, dcR), current_level = (lvA : lvsA, lvsB)}, dcB)
pop_dcB c@Context{dc_stack = (dcA, [], dcR)} = error "requeated dcB from empty stack"

pop_dcA' :: Context -> (Context, Node)
pop_dcA' c@Context{dc_stack = (dcA : fs, dcB, dcR), current_level = ((i, _) : lvsA, lvB : lvsB)} =
    (c{dc_stack = (fs, dcB, dcR), current_level = ((i, Dc) : lvsA, lvB : lvsB)}, dcA) --`debug` "popped dcA"
pop_dcA' c@Context{dc_stack = ([], dcB, dcR)} = error "requeated dcA from empty stack"

pop_dcB' :: Context -> (Context, Node)
pop_dcB' c@Context{dc_stack = (dcA, dcB : fs, dcR), current_level = (lvA : lvsA, (i, _) : lvsB)} =
    (c{dc_stack = (dcA, fs, dcR), current_level = (lvA : lvsA, (i, Dc) : lvsB)}, dcB)
pop_dcB' c@Context{dc_stack = (dcA, [], dcR)} = error "requeated dcB from empty stack"

pop_dcA'' :: Context -> (Context, Node)
pop_dcA'' c@Context{dc_stack = (dcA : fs, dcB, dcR), current_level = (_ : (i, _) : lvsA, lvB : lvsB)} =
    (c{dc_stack = (fs, dcB, dcR), current_level = ((i, Dc) : lvsA, lvB : lvsB)}, dcA) --`debug` "popped dcA"
pop_dcA'' c@Context{dc_stack = ([], dcB, dcR)} = error "requeated dcA from empty stack"

pop_dcB'' :: Context -> (Context, Node)
pop_dcB'' c@Context{dc_stack = (dcA, dcB : fs, dcR), current_level = (lvA : lvsA, _ : (i, _) : lvsB)} =
    (c{dc_stack = (dcA, fs, dcR), current_level = (lvA : lvsA, (i, Dc) : lvsB)}, dcB)
pop_dcB'' c@Context{dc_stack = (dcA, [], dcR)} = error "requeated dcB from empty stack"

pop_dcR :: Context -> (Context, Node)
pop_dcR c@Context{dc_stack = (dcA, dcB, dcR : fs)} = (c{dc_stack = (dcA, dcB, fs)}, dcR)
pop_dcR c@Context{dc_stack = (dcA, dcB, [])} = error "requeated dcR from empty stack"

add_to_stack' :: [(Int, Inf)] -> ([Node], [Node], [Node]) -> Context -> Context
add_to_stack' infs (dcA, dcB, dcR) c@Context{dc_stack = (dcAs, dcBs, dcRs)} =
    let (lvsA, lvsB) = current_level c in
    c{dc_stack = (dcA ++ dcAs, dcB ++ dcBs, dcR ++ dcRs), current_level = (infs ++ lvsA, infs ++ lvsB) }

add_to_stack :: (Int, Inf) -> (Node, Node, Node) -> Context -> Context
add_to_stack inf (dcA, dcB, dcR) c@Context{dc_stack = (dcAs, dcBs, dcRs)} =
    let (lvsA, lvsB) = current_level c in
    c{dc_stack = (dcA : dcAs, dcB : dcBs, dcR : dcRs), current_level = (inf : lvsA, inf : lvsB)}

add_to_level :: (Int, Inf) -> Context -> Context
add_to_level inf c =
    let (lvsA, lvsB) = current_level c in
    c{current_level = (inf : lvsA, inf : lvsB)}


replace_on_stack :: (Int, Inf) -> (Node, Node, Node) -> Context -> Context
replace_on_stack inf (dcA, dcB, dcR) c@Context{dc_stack = (_ : dcAs, _ : dcBs, _ : dcRs), current_level = (lvA : lvsA, lvB : lvsB)} =
    c{dc_stack = (dcA : dcAs, dcB : dcBs, dcR : dcRs), current_level = (inf : lvsA, inf : lvsB)}

pop_stack1 :: Context -> (Context, ((Inf, Inf), (Node, Node, Node)))
pop_stack1 c@Context{dc_stack = (dcA : dcAs, dcB : dcBs, dcR : dcRs), current_level = (lvA@(_, infA) : lvsA, lvB@(_, infB) : lvsB)} =
    (c{dc_stack = (dcAs, dcBs, dcRs), current_level=(lvsA, lvsB)}, ((infA, infB), (dcA, dcB, dcR)))

-- removes the current level and returns information about the previous level
-- todo: popping the dcs is naive currently
pop_stack :: Context -> (Context, ((Inf, Inf), (Node, Node, Node)))
pop_stack c@Context{dc_stack = (current_A : dcA : dcAs, current_B : dcB : dcBs, current_R : dcR : dcRs), current_level = (lAs, lBs)}
    | length lAs == length lBs = let (_ : lvA@(_, infA) : lvsA, _: lvB@(_, infB) : lvsB) = current_level c in
        (c{dc_stack = (trimListToSize n (current_A: dcA : dcAs), trimListToSize n (current_B : dcB : dcBs), trimListToSize n (current_R : dcR : dcRs)), current_level= (lvA : lvsA, lvB : lvsB)}, ((infA, infB), (dcA, dcB, dcR)))
    | length lAs > length lBs = let (_ : lvA@(_, infA) : lvsA, lvB@(_, infB) : lvsB) = current_level c in
        (c{dc_stack = (trimListToSize n (current_A: dcA : dcAs), trimListToSize n (current_B : dcB : dcBs), trimListToSize n (current_R : dcR : dcRs)), current_level= (lvA : lvsA, lvB : lvsB)}, ((infA, infB), (dcA, dcB, dcR)))
    | length lAs < length lBs = let (lvA@(_, infA) : lvsA, _ : lvB@(_, infB) : lvsB) = current_level c in
        (c{dc_stack = (trimListToSize n (current_A: dcA : dcAs), trimListToSize n (current_B : dcB : dcBs), trimListToSize n (current_R : dcR : dcRs)), current_level= (lvA : lvsA, lvB : lvsB)}, ((infA, infB), (dcA, dcB, dcR)))
        where n = (max (length $ lAs) (length $ lBs)) -1 `debug` ("n = " ++ (show $ (max (length $ lAs) (length $ lBs)) -1) ++ ", " ++ (show $ length lAs)  ++ ", " ++ (show $ length lBs))



-- removes the current level and returns information about the previous level
-- todo: popping the dcs is naive currently
pop_stack' :: Context -> (Context, (Inf, Inf))
pop_stack' c@Context{dc_stack = (dcAs, dcBs, dcRs), current_level = (lAs, lBs)}
    | length lAs == length lBs = let (_ : lvA@(_, infA) : lvsA, _: lvB@(_, infB) : lvsB) = current_level c in
        (c{dc_stack = (trimListToSize n dcAs, trimListToSize n dcBs , trimListToSize n dcRs ), current_level= (lvA : lvsA, lvB : lvsB)}, (infA, infB))
    | length lAs > length lBs = let (_ : lvA@(_, infA) : lvsA, lvB@(_, infB) : lvsB) = current_level c in
        (c{dc_stack = (trimListToSize n dcAs, trimListToSize n dcBs , trimListToSize n dcRs ), current_level= (lvA : lvsA, lvB : lvsB)}, (infA, infB))
    | length lAs < length lBs = let (lvA@(_, infA) : lvsA, _ : lvB@(_, infB) : lvsB) = current_level c in
        (c{dc_stack = (trimListToSize n dcAs, trimListToSize n dcBs , trimListToSize n dcRs ), current_level= (lvA : lvsA, lvB : lvsB)}, (infA, infB))
        where n = (max (length $ lAs) (length $ lBs)) -1 `debug` ("n' = " ++ (show $ (max (length $ lAs) (length $ lBs)) -1) ++ ", " ++ (show $ length lAs)  ++ ", " ++ (show $ length lBs))







    -- (_ : lvA@(_, infA) : lvsA, _: lvB@(_, infB) : lvsB)} =
    -- (c{dc_stack = (trimListToSize n dcAs, trimListToSize n dcBs , trimListToSize n dcRs ), current_level= (lvA : lvsA, lvB : lvsB)}, (infA, infB))
    -- where n = max (length $ lvA : lvsA) (length $ lvB : lvsB) `debug` ("n' = " ++ (show $ max (length $ lvA : lvsA) (length $ lvB : lvsB)))

trimListToSize :: Int -> [a] -> [a]
trimListToSize n xs
  | n < 0     = xs -- Or error, depending on desired behavior for negative n
  | length xs <= n = xs
  | otherwise = drop (length xs - n) xs -- `debug` ("dropping to length: " ++ show n ++ " from length " ++ show (length xs))

func_tail :: Context -> Context
func_tail c@Context{dc_stack = (dcA : dcAs, dcB : dcBs, dcR : dcRs), current_level = (lvA@(_, infA) : lvsA, lvB@(_, infB) : lvsB)} =
    c{dc_stack = (dcAs, dcBs, dcRs), current_level=(lvsA, lvsB)}

reset_stack :: Context -> Context -> Context
reset_stack new_c old_c =
    new_c{dc_stack = dc_stack old_c, current_level = current_level old_c}

    -- update_dc_stack :: String -> Int -> Context -> Context
-- update_dc_stack s idx c@Context{dc_stack = fl} = traverse_dcB s idx (traverse_dcA s idx c)
-- todo map over full dc_stack


class All a where
    error_display :: String -> Context -> Node -> Node -> a
    error_display s c (a_id, a) (b_id, b) = error (show s ++ " : " ++ show c ++ ", " ++ show a ++ ", " ++ show b)

instance All (Context, Node)

-- func_tail :: String -> Context -> Context
-- func_tail s c@Context{dc_stack = _ : fs } =
--     if s == "Dc" then c else c{dc_stack = fs} --`debug` "applying func_tail"
-- func_tail s c@Context{dc_stack = [] } =
--     if s == "Dc" then c else error "func_tail should not be called on an empty dc_stack"

-- func_alt :: String -> Context -> (Inf, (Node,Node, Node)) -> Context
-- func_alt s c@Context{dc_stack = _ : fs } alt_head =
--     if s == "Dc" then c else c{dc_stack = alt_head : fs} --`debug` "applying func_alt"
-- func_alt s c@Context{dc_stack = [] } alt_head =
--     if s == "Dc" then c else c{dc_stack = [alt_head]} --`debug` "applying func_alt"

-- Combined helper function: Processes a single Node based on the move string.
-- Takes the specific node to process and returns the new Node resulting from the move.
move_dc :: Context -> String -> Node -> Node
move_dc c m node =
    case node of -- Pattern match directly on the Node structure passed in
        (_, Node position pos_child neg_child) -> -- Use generic pattern variable names
            if m == "pos child" then getNode c pos_child -- `debug` ("node pos move : " ++ (show node))
            else if m == "neg child" then getNode c neg_child -- `debug` ("node neg move : " ++ (show node))
            -- Add conditions for "neginf", "posinf" if needed
            else error $ "processStackElement: undefined move '" ++ m ++ "' for Node pattern: " ++ show node

        (_, EndInfNode child) ->
            if m == "endinf" then getNode c child --`debug` ("endinf " ++ show (EndInfNode child) )
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
        -- Add cases for any other constructors of Node if they exist
        _ -> error $ "processStackElement: Unhandled Node pattern: " ++ show node ++ ", move: " ++ m



to_static_form':: Context -> Node -> (Context, NodeStatic)
to_static_form' c d@(node_id, Node position pos_child neg_child)  = let
    (c1, (posR, _)) = to_static_form' c (pos_child, getDd c pos_child)
    (c2, (negR, _)) = to_static_form' c1 (neg_child, getDd c1 neg_child)
    in insert_static c2 $ Node' (get_static_lv c ++ [position]) posR negR `debug` ("node: " ++ (show $  get_static_lv c ++ [position]) )
to_static_form' c d@(node_id, InfNodes position dc p n) =  let
    c_ = add_to_level (position, Dc) c
    (c1, (r_dc, _)) = to_static_form' c_ (dc, getDd c dc)
    c2_ = add_to_level (position, Neg) (reset_stack c1 c)
    (c2, (r_n, _)) = to_static_form' c2_ (n, getDd c n)
    c3_ = add_to_level (position, Neg) (reset_stack c2 c)
    (c3, (r_p, _)) = to_static_form' c3_ (p, getDd c p)
        in insert_static (reset_stack c3 c) $ InfNodes' (get_static_lv c ++ [position]) r_dc r_p r_n `debug` ("infnodes: " ++ (show $  get_static_lv c ++ [position]))
to_static_form' c d@(node_id, EndInfNode a) =  let
    c' = pop_current_level c
    (c1, (result, _)) = to_static_form' c' (a, getDd c a)
    in insert_static c1 $ EndInfNode' result
to_static_form' c (_, Leaf b) = insert_static c (Leaf' b)
to_static_form' c (_, Unknown) = insert_static c Unknown'


pop_current_level :: Context -> Context
pop_current_level c@Context{current_level = ( _ : lvsA, lvsB)} = c{current_level = (lvsA, lvsB)}