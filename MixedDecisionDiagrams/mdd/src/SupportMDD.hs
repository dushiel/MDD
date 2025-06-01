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
pop_dcA c@Context{dc_stack = (dcA : fs, dcB, dcR)} = (c{dc_stack = (fs, dcB, dcR)}, dcA) --`debug` "popped dcA"
pop_dcA c@Context{dc_stack = ([], dcB, dcR)} = error "requeated dcA from empty stack"

pop_dcB :: Context -> (Context, Node)
pop_dcB c@Context{dc_stack = (dcA, dcB : fs, dcR)} = (c{dc_stack = (dcA, fs, dcR)}, dcB) 
pop_dcB c@Context{dc_stack = (dcA, [], dcR)} = error "requeated dcB from empty stack"

pop_dcR :: Context -> (Context, Node)
pop_dcR c@Context{dc_stack = (dcA, dcB, dcR : fs)} = (c{dc_stack = (dcA, dcB, fs)}, dcR) 
pop_dcR c@Context{dc_stack = (dcA, dcB, [])} = error "requeated dcR from empty stack"

add_to_stack' :: [(Int, Inf)] -> ([Node], [Node], [Node]) -> Context -> Context
add_to_stack' infs (dcA, dcB, dcR) c@Context{dc_stack = (dcAs, dcBs, dcRs)} = 
    c{dc_stack = (dcA ++ dcAs, dcB ++ dcBs, dcR ++ dcRs), current_level = infs ++ current_level c}

add_to_stack :: (Int, Inf) -> (Node, Node, Node) -> Context -> Context
add_to_stack inf (dcA, dcB, dcR) c@Context{dc_stack = (dcAs, dcBs, dcRs)} = 
    c{dc_stack = (dcA : dcAs, dcB : dcBs, dcR : dcRs), current_level = inf : current_level c}

replace_on_stack :: (Int, Inf) -> (Node, Node, Node) -> Context -> Context
replace_on_stack inf (dcA, dcB, dcR) c@Context{dc_stack = (_ : dcAs, _ : dcBs, _ : dcRs), current_level = lv : lvs} = 
    c{dc_stack = (dcA : dcAs, dcB : dcBs, dcR : dcRs), current_level = inf : lvs}

pop_stack1 :: Context -> (Context, (Inf, (Node, Node, Node)))
pop_stack1 c@Context{dc_stack = (dcA : dcAs, dcB : dcBs, dcR : dcRs), current_level = lv@(_, inf) : lvs} = 
    (c{dc_stack = (dcAs, dcBs, dcRs), current_level=lvs}, (inf, (dcA, dcB, dcR)))

-- removes the current level and returns information about the previous level
-- todo: popping the dcs is naive currently
pop_stack :: Context -> (Context, (Inf, (Node, Node, Node)))
pop_stack c@Context{dc_stack = (current_A : dcA : dcAs, current_B : dcB : dcBs, current_R : dcR : dcRs), current_level = _: lv@(_, inf) : lvs} = 
    (c{dc_stack = (trimListToSize n (current_A: dcA : dcAs), trimListToSize n (current_B : dcB : dcBs), trimListToSize n (current_R : dcR : dcRs)), current_level= lv : lvs}, (inf, (dcA, dcB, dcR)))
    where n = length $ lv : lvs -- `debug` ("n = " ++ (show $ length $ lv : lvs))

-- removes the current level and returns information about the previous level
-- todo: popping the dcs is naive currently
pop_stack' :: Context -> (Context, Inf)
pop_stack' c@Context{dc_stack = (dcAs, dcBs, dcRs), current_level = _: lv@(_, inf) : lvs} = 
    (c{dc_stack = (trimListToSize n dcAs, trimListToSize n dcBs , trimListToSize n dcRs ), current_level= lv : lvs}, inf)
    where n = length $ lv : lvs

trimListToSize :: Int -> [a] -> [a]
trimListToSize n xs
  | n < 0     = xs -- Or error, depending on desired behavior for negative n
  | length xs <= n = xs
  | otherwise = drop (length xs - n) xs -- `debug` ("dropping to length: " ++ show n ++ " from length " ++ show (length xs))

func_tail :: Context -> Context
func_tail c@Context{dc_stack = (dcA : dcAs, dcB : dcBs, dcR : dcRs), current_level = lv@(_, inf) : lvs} = 
    c{dc_stack = (dcAs, dcBs, dcRs), current_level=lvs}

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
            else (if (m == "pos child") || (m == "neg child") then node 
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