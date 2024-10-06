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



module MDDmanipulation where
-- todo-future : explore {-# UNPACK #-} !Int
--SPECIALIZE pragma
import MDD hiding (debug)
import Debug.Trace (trace)
import DrawMDD
import Data.Kind

import GHC.IO (unsafePerformIO)



-- todo parser from debug show output to DD
-- todo add levels to the hashing
-- todo add dereferencing in the nodelookup

-- -- create stack also for function calls: only mixed and absorb can be added
-- -- add additional context types: mixed and absorb

-- -- | This module describes functions that manipulate MDDs.



type DdF4 :: Inf -> Constraint
type Dd1 :: Inf -> Constraint

supply_dds :: DdManipulation -> Context -> NodeId -> NodeId -> (Context, NodeId)
supply_dds f c a b = f c a b (getDd c a) (getDd c b)

intersection :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
intersection c a b = intersection'  c a b
    -- `debug` ("intersection: \n" ++ show_dd settings c a ++ " \n; "  ++ show_dd settings c b)
intersection' :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
intersection' c a_id b_id a (Leaf False) = (c, b_id)
intersection' c a_id b_id (Leaf False) b = (c, a_id)
intersection' c a_id b_id a (Leaf True) = insert c a
intersection' c a_id b_id (Leaf True) b = insert c b
intersection' c a_id b_id a b = intersectionMain c a_id b_id
union :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
union c a b = union' c a b
    -- `debug` ("union: " ++ show c ++ " ; " ++ show_dd settings c a ++ " ; "  ++ show_dd settings c b)
union' :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
union' c a_id b_id a (Leaf True) = (c, b_id)
union' c a_id b_id (Leaf True) b = (c, a_id)
union' c a_id b_id a (Leaf False) = insert c a
union' c a_id b_id (Leaf False) b = insert c b
union' c a_id b_id a b = unionMain c a_id b_id

negation' :: (Context, NodeId) -> (Context, NodeId)
negation' (c, node_id) = negation'' c node_id (getDd c node_id)

negation_ :: Context -> NodeId -> (Context, NodeId)
negation_ c node_id = negation'' c node_id (getDd c node_id)

negation'' :: Context -> NodeId -> Dd -> (Context, NodeId)
negation'' c node_id dd  = let r = negation c node_id dd in r
    -- `debug` (colorize "green" "negation : \n" ++ "  ->   " ++ show_dd settings c node_id ++
    --         "\n  =>   " ++ show_dd settings (fst r) (snd r)  ++ "\n") -- "\n -> \n" )

negation :: Context -> NodeId -> Dd -> (Context, NodeId)
negation c node_id d@(Node position pos_child neg_child)  = withCache_ c node_id $ let
    (c1, posR) = negation_ c pos_child  --`debug` ("negation pos child: " ++ show_dd settings c pos_child ++ " , " ++ " -> " ++ show (getDd c pos_child) )
    (c2, negR) = negation_ c1 neg_child  --`debug` ("negation neg child: " ++ show_dd settings c neg_child ++ " , " ++ "-> " ++ show (getDd c' neg_child))
    in insert c2 $ Node position posR negR -- `debug` (" inserted: " ++ show (insert c'' $ Node position posR negR))
negation c node_id d@(InfNodes position dc n1 n0 p1 p0) = withCache_ c  node_id $ let
    (c1, r_dc) = negation_ c dc
    (c2, r_n) = negation_ c1 n1
    (c3, r_p) = negation_ c2 n0
        in insert c3 $ InfNodes position r_dc r_n r_p
negation c node_id d@(EndInfNode a) = withCache_ c  node_id $ let
    (c1, result) = negation2 c a (getDd c a) --`debug` ("negation endinf child: " ++ show_dd settings c a )
    in insert c1 $ EndInfNode result
negation c _ (Leaf b) = (c, leaf $ not b) --`debug` ("returning : " ++ show (c, leaf $ not b))


applyElimRule_arg :: Context -> Inf -> Dd -> (Context, NodeId)
applyElimRule_arg c Dc d = applyElimRule @Dc c d
applyElimRule_arg c Neg d = applyElimRule @Neg c d
applyElimRule_arg c Pos d = applyElimRule @Pos c d


continue_outer t c a_id b_id a b = continue_outer' t c a_id b_id a b --`debug` ("continue outer: \n a: " ++ show_dd settings c a_id ++ "\n b: " ++ show_dd settings c b_id)

continue_outer' :: (Inf, FType) -> Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
continue_outer' t c = case t of
    (Dc, Inter) -> intersectionLocal @Dc c
    (Neg, Inter) -> intersectionLocal @Neg c
    (Pos, Inter) -> intersectionLocal @Pos c

    (Dc, Union) -> unionLocal @Dc c
    (Neg, Union) -> unionLocal @Neg c
    (Pos, Union) -> unionLocal @Pos c

    (Dc, Absorb) -> absorb @Dc c
    (Neg, Absorb) -> absorb @Neg c
    (Pos, Absorb) -> absorb @Pos c

    (_, _) -> error (show t ++ ", " ++ show c ++ ", ")

addInfNode :: Context -> Int -> Inf -> NodeId -> (Context, NodeId)
addInfNode c n inf conseq  =
        case inf of -- only for Dc we need to check the b, since after a hole we interpret the following sub domains in substance (1-set)
            Dc -> insert c' $ InfNodes n dd l0 l1 l0 l1
            Neg -> insert c' $ InfNodes n l0 dd l1 l0 l1
            Pos -> insert c' $ InfNodes n l0 l0 l1 dd l1
        where
            (c', dd) = insert c $ EndInfNode conseq

-- intersectionInferA :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
-- intersectionInferA Context{func_stack = []} _ _ _ _ = error "empty context"
-- intersectionInferA  _ _ _ _ (Leaf _) = error "Leaf in A"
-- intersectionInferA  _ _ _ _ (EndInfNode _) = error "EndNode in A"
-- intersectionInferA  _ _ _ _ (Node _ _ _) = error "Node in A"

-- intersectionInferA c a_id b_id a b = debug_manipulation (intersectionInferA' c a_id b_id a b) "intersection" "intersectionInferA" c a_id b_id
-- intersectionInferA' :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
-- intersectionInferA' c'@Context{func_stack = ((inf, _) : _)} a_id' b_id a' b@(InfNodes positionB dcB n1B n0B p1B p0B) = undefined
--         where
--             (c, a_id) = insert c' $ EndInfNode a_id'
--             a = getDd c a_id
--             dcB_dd = getDd c dcB
--             n1B_dd = getDd c n1B
--             n0B_dd = getDd c n0B
--             p1B_dd = getDd c p1B
--             p0B_dd = getDd c p0B

-- intersectionInferA' _ _ _ _ _ = undefined

-- intersectionInferB :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
-- intersectionInferB Context{func_stack = []} _ _ _ _ = error "empty context"
-- intersectionInferB _ _ _ (Leaf _) _ = error "Leaf in A"
-- intersectionInferB _ _ _ (EndInfNode _) _ = error "EndNode in A"
-- intersectionInferB _ _ _ (Node _ _ _) _ = error "Node in A"

-- intersectionInferB c a_id b_id a b =  debug_manipulation (intersectionInferB' c a_id b_id a b) "intersection" "intersectionInferB" c a_id b_id
-- intersectionInferB' :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
-- intersectionInferB' c'@Context{func_stack = ((inf, _) : _)} a_id b_id' a@(InfNodes positionA dcA n1A n0A p1A p0A) b' = undefined
--         where
--             (c, b_id) = insert c' $ EndInfNode b_id'
--             b = getDd c b_id
--             dcA_dd = getDd c' dcA
--             n1A_dd = getDd c' n1A
--             n0A_dd = getDd c' n0A
--             p1A_dd = getDd c' p1A
--             p0A_dd = getDd c' p0A
-- intersectionInferB' _ _ _ _ _ = undefined


intersectionMain :: Context -> NodeId -> NodeId -> (Context, NodeId)
intersectionMain c a b = debug_manipulation (intersectionMain' c a b (getDd c a) (getDd c b))
    "intersection" "intersectionMain" c a b
intersectionMain' :: DdManipulation
intersectionMain'  c@Context{} !a_id !b_id a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B)
    | positionA == positionB =
        let
            (c1, dcR) = intersectionLocal @Dc c dcA dcB (getDd c dcA)  (getDd c dcB)
            (c2, nR) = intersectionLocal @Neg c dcA dcB (getDd c dcA)  (getDd c dcB)
            (c3, pR) = intersectionLocal @Pos c dcA dcB (getDd c dcA)  (getDd c dcB)
        in insert c3 $ InfNodes positionA dcR nR pR
    | positionA > positionB = withCache c (a_id, b_id, "intersection") $ intersectionInferA c a_id b_id a b `debug` "interA"
    | positionA < positionB = withCache c (a_id, b_id, "intersection") $ intersectionInferB c a_id b_id a b `debug` "interB"-- replace all the A stuf with (dc: a, neg: 0, neg0: (1,0), pos: (1,0), pos0: (1,0))
intersectionMain' c a_id b_id a b = error (show_dd settings c a_id ++ ", " ++ show_dd settings c b_id ++ ", "++ show c)

-- unionInferA :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
-- unionInferA Context{func_stack = []} _ _ _ _ = error "empty context"
-- unionInferA  _ _ _ _ (Leaf _) = error "Leaf in A"
-- unionInferA  _ _ _ _ (EndInfNode _) = error "EndNode in A"
-- unionInferA  _ _ _ _ (Node _ _ _) = error "Node in A"

-- unionInferA c a_id b_id a b =  debug_manipulation (unionInferA' c a_id b_id a b) "union" "unionInferA" c a_id b_id   -- ++ " = " ++ show (unionInferA' c a_id b_id a b ))
-- unionInferA' :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
-- unionInferA' c'@Context{func_stack = ((inf, _) : _)} a_id' b_id a' b@(InfNodes positionB dcB n1B n0B p1B p0B) = undefined
--         where
--             (c, a_id) = insert c' $ EndInfNode a_id'
--             a = getDd c a_id
--             dcB_dd = getDd c dcB
--             n1B_dd = getDd c n1B
--             n0B_dd = getDd c n0B
--             p1B_dd = getDd c p1B
--             p0B_dd = getDd c p0B

-- unionInferA' _ _ _ _ _ = undefined


-- unionInferB :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
-- unionInferB Context{func_stack = []} _ _ _ _ = error "empty context"
-- unionInferB _ _ _ (Leaf _) _ = error "Leaf in A"
-- unionInferB _ _ _ (EndInfNode _) _ = error "EndNode in A"
-- unionInferB _ _ _ (Node _ _ _) _ = error "Node in A"

-- unionInferB c a_id b_id a b =  debug_manipulation (unionInferB' c a_id b_id a b) "union" "unionInferB" c a_id b_id
-- unionInferB' :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
-- unionInferB' c'@Context{func_stack = ((inf, _) : _)} a_id b_id' a@(InfNodes positionA dcA n1A n0A p1A p0A) b' = undefined

--         where
--             (c, b_id) = insert c' $ EndInfNode b_id'
--             b = getDd c b_id
--             dcA_dd = getDd c dcA
--             n1A_dd = getDd c n1A
--             n0A_dd = getDd c n0A
--             p1A_dd = getDd c p1A
--             p0A_dd = getDd c p0A

-- unionInferB' _ _ _ _ _ = undefined

unionMain :: Context -> NodeId -> NodeId -> (Context, NodeId)
-- -- exclusive points (0's / holes) under union are filled unless they are present in both A and B (so only an intersection between them needs to be done)
-- -- inclusive point (1's ) under union are intersected with the opposite infinite subset (dc) before they are added together
unionMain c !a_id !b_id = debug_manipulation (unionMain' c a_id b_id (getDd c a_id) (getDd c b_id))
    "union" "unionMain" c a_id b_id
unionMain' :: Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
unionMain' c a_id b_id a@(InfNodes positionA dcA n1A n0A p1A p0A)  b@(InfNodes positionB dcB n1B n0B p1B p0B)
    | positionA == positionB =  undefined -- let
    --     (c1, dcR) = unionLocal @Dc c dcA dcB (getDd c dcA)  (getDd c dcB)
    -- in insert c9 $ InfNodes positionA dcR n1R n0R p1R p0R
    | positionA > positionB = withCache c (a_id, b_id, "union") $ unionInferA c a_id b_id a b --`debug` ("unionA: " ++ (show_dd settings c a_id) ++ "\n" ++ (show_dd settings c b_id))
    | positionA < positionB = withCache c (a_id, b_id, "union") $ unionInferB c a_id b_id a b -- replace all the A stuf with (dc: a, neg: 0, neg0: 1, pos: 0, pos0: 1)
unionMain' c a_id b_id a b = error (show a ++ ", " ++ show_dd settings c b_id ++ ", "++ show c)


-- -- captures the general patterns for the functions
class Dd1 a where
    intersectionLocal' :: DdManipulation
    unionLocal' :: DdManipulation
    absorb' :: DdManipulation
    apply :: FType -> Context -> NodeId -> NodeId -> String -> DdManipulation -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
    apply2 :: FType -> Context -> NodeId -> NodeId -> String -> DdManipulation -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)



instance (DdF4 a) => Dd1 a where
    -- | take cache keys, manipulation function and its arguments, gives its result back with insertion in nodelookup map, func cache and elim rule
    apply operator c a_key b_key f_key f a_id b_id a b = let (c', r) = f c{func_stack = (to_constr @a, operator) : func_stack c} a_id b_id a b in withCache c' (a_key, b_key, f_key) $ applyInfElimRule @a c' $ getDd c' r --`debug` "apply" -- `debug` ("apply"  ++ (show_dd settings c a_id) ++ "\n" ++ (show_dd settings c b_id) ++ " ==> \n" ++ (show_dd settings c' r))
    apply2 operator c a_key b_key f_key f a_id b_id a b = let (c', r) = f c{func_stack = (to_constr @a, operator)  : func_stack c} a_id b_id a b in withCache c' (a_key, b_key, f_key) $ applyInfElimRule2 @a c' $ getDd c' r -- `debug` ("apply2222222222222222222222222222222222"  ++ (show_dd settings c a_id) ++ "\n" ++ (show_dd settings c b_id) ++ " ==> \n" ++ (show_dd settings c' r))
    intersectionLocal' c a_id b_id a@(Leaf True) b@InfNodes{} = insert c $ EndInfNode b_id
    intersectionLocal' c a_id b_id a@(Leaf True) (EndInfNode (0,0)) = (c, (0,0))
    intersectionLocal' c a_id b_id a@(Leaf True) (EndInfNode (1,0)) = (c, (1,0))
    intersectionLocal' c a_id b_id a@(Leaf True) b = (c, b_id) --`debug` ("returning" ++ show_dd settings c b_id_id)
    intersectionLocal' c@(Context{func_stack = (f:fs)}) a_id b_id a@(Leaf False) b@(EndInfNode childB ) = withCache c (a_id, b_id, "intersectionLocal") $ intersectionLocal_arg f c{func_stack = fs} a_id childB a (getDd c childB)

    intersectionLocal' c a_id b_id a@(Leaf False) (EndInfNode (0,0)) = (c, (0,0))  --`debug` ("returning" ++ show a_id)-- dc case for leafs
    intersectionLocal' c a_id b_id a@(Leaf False) (EndInfNode (1,0)) = (c, (0,0))  --`debug` ("returning" ++ show a_id)-- dc case for leafs
    intersectionLocal' c a_id b_id a@(Leaf False) b@(Leaf _) = (c, (0,0))  --`debug` ("returning" ++ show a_id)-- dc case for leafs

    intersectionLocal' c a_id b_id a@(Leaf False) b@(InfNodes {}) =  apply @a Inter c a_id b_id "intersectionLocal" (intersectionInferA_ @a) a_id b_id a b -- leaf with node or end infnode
    intersectionLocal' c a_id b_id a@(Leaf False) b = inferNodeA @a (intersectionLocal @a) c  a_id b_id a b -- leaf with node or end infnode

    intersectionLocal' c a_id b_id a@InfNodes{} b@(Leaf True) = insert c $ EndInfNode a_id
    intersectionLocal' c a_id b_id (EndInfNode (0,0)) b@(Leaf True) = (,) c (0,0)
    intersectionLocal' c a_id b_id (EndInfNode (1,0)) b@(Leaf True) = (,) c (1,0)
    intersectionLocal' c a_id b_id a b@(Leaf True) = (,) c a_id
    intersectionLocal' c@(Context{func_stack = (f:fs)}) a_id b_id a@(EndInfNode childA ) b@(Leaf False) = apply @a Inter c{func_stack = fs} a_id b_id "intersectionLocal" (intersectionLocal_arg f) childA b_id (getDd c childA) b

    intersectionLocal' c a_id b_id a@(InfNodes {}) b@(Leaf False) = apply @a Inter c a_id b_id "intersectionLocal" (intersectionInferB_ @a) a_id b_id a b -- leaf with node or end infnode
    intersectionLocal' c a_id b_id a b@(Leaf False) = inferNodeB @a (intersectionLocal @a) c a_id b_id a b -- leaf with node or end infnode

    -- infer node at DdF4, and here the shared abstrations
    intersectionLocal' c a_id b_id a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
        -- Match
        | positionA == positionB =
            let (c', pos_result) = supply_dds (intersectionLocal @a) c pos_childA pos_childB
                (c'', neg_result) = supply_dds (intersectionLocal @a) c' neg_childA neg_childB
            in  withCache c (a_id, b_id, "intersection") $ applyElimRule @a c'' (Node positionA pos_result neg_result)
        -- Mismatch, but with a inference we ontinue recursion with the earliest (thus lowest valued) node.
        | positionA < positionB = inferNodeB @a (intersectionLocal @a) c a_id b_id a b
        | positionA > positionB = inferNodeA @a (intersectionLocal @a) c a_id b_id a b

    -- go one recursive layer deeper !
    intersectionLocal' c a_id b_id a@(InfNodes positionA _ _ _ _ _) b@(Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB =  inferNodeA @a (intersectionLocal @a) c  a_id b_id a b -- infer node A
        | positionA < positionB = apply @a Inter c a_id b_id "intersection" (intersectionInferB_ @a) a_id b_id a b -- infer infnode B and start intersection inside it
    intersectionLocal' c a_id b_id a@(Node positionA pos_childA neg_childA) b@(InfNodes positionB _ _ _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB =  apply @a Inter c a_id b_id "intersection" (intersectionInferA_ @a) a_id b_id a b
        | positionA < positionB =  inferNodeB @a (intersectionLocal @a) c  a_id b_id a b
    intersectionLocal'  c a_id b_id a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _)
        | positionA == positionB =  apply @a Inter c a_id b_id "intersection" (intersection) a_id b_id a b --`debug5` ("infinf: " ++ show a ++ show b ++ "\n"++ show_dd settings c a_id ++ show_dd settings c b_id) -- start intersection and push local-intersection to the context
        | positionA < positionB =  apply @a Inter c a_id b_id "intersection" (intersectionInferB_ @a) a_id b_id a b -- infer infnode B
        | positionA > positionB =  apply @a Inter c a_id b_id "intersection" (intersectionInferA_ @a) a_id b_id a b -- infer infnode A
    intersectionLocal' c a_id b_id a@(InfNodes positionA _ _ _ _ _) b@(EndInfNode _) =  apply @a Inter c a_id b_id "intersection" (intersectionInferB_ @a) a_id b_id a b
    intersectionLocal' c a_id b_id a@(EndInfNode _) b@(InfNodes positionB _ _ _ _ _) =  apply @a Inter c a_id b_id "intersection" (intersectionInferA_ @a) a_id b_id a b

    -- continue local traversal
    intersectionLocal' c a_id b_id a@(Node positionA pos_childA neg_childA) b@(EndInfNode childB) = inferNodeB @a (intersectionLocal @a) c a_id b_id a b
    intersectionLocal' c a_id b_id a@(EndInfNode childA) b@(Node positionB pos_childB neg_childB) = inferNodeA @a (intersectionLocal @a) c a_id b_id a b
    -- continue previous super domain traversal
    intersectionLocal' c@(Context{func_stack = (f:fs)}) a_id b_id a@(EndInfNode childA)  b@(EndInfNode childB) = withCache c (a_id, b_id, "intersection") $ (continue_outer f c{func_stack = fs} childA childB (getDd c childA) (getDd c childB)) --`debug` ("endinfendinf interLocqal : " ++ "show (continue_outer f c{func_stack=fs} childA childB)" ++ " \n : " ++ show childA ++ " , " ++ show childB)
    intersectionLocal' c@(Context{func_stack = []}) a_id b_id a@(EndInfNode childA)  b@(EndInfNode childB) = error "should not have empty context stack"-- applyInfElimRule @a c $ intersection  Context{func_stack = []} childA childB


    intersectionLocal' c a_id b_id a b = error ("how did we get here? " ++  show c ++ show a ++ "  -  " ++ show_dd settings c b_id)

    unionLocal' c a_id b_id a@(Leaf False) b@(InfNodes {}) = insert c $ EndInfNode b_id --`debug` "insert in leaf false kk"
    unionLocal' c a_id b_id a@(Leaf False) (EndInfNode (0,0)) = (,) c (0,0)
    unionLocal' c a_id b_id a@(Leaf False) (EndInfNode (1,0)) = (,) c (1,0)
    unionLocal' c a_id b_id a@(Leaf False) b = (,) c b_id  --findme --  fix below - add endinfnode?
    unionLocal' c@(Context{func_stack = (f:fs)}) a_id b_id a@(Leaf True) b@(EndInfNode childB ) = withCache c (a_id, b_id, "union") $ unionLocal_arg f c{func_stack = fs} a_id childB a (getDd c childB) --`debug` ("endif a = true, f_stack = " ++ show f ++ "," ++ show fs ++ " a: " ++ show a ++ " b: " ++ show childB)
    unionLocal' c a_id b_id a@(Leaf True) (EndInfNode (0,0)) = (,) c (1,0)
    unionLocal' c a_id b_id a@(Leaf True) (EndInfNode (1,0)) = (,) c (1,0)
    unionLocal' c a_id b_id a@(Leaf True) b@(Leaf _) = (,) c (1,0)
    unionLocal' c a_id b_id a@(Leaf True) b@(InfNodes {}) =  apply @a Union c a_id b_id "union" (unionInferA_ @a) a_id b_id a b
    unionLocal' c a_id b_id a@(Leaf True) b = inferNodeA @a (unionLocal @a) c a_id b_id a b -- leaf with node or end infnode

    unionLocal' c a_id b_id a@(InfNodes {}) b@(Leaf False) = insert c $ EndInfNode a_id --`debug` ("insert in leaf false kk" ++ show_dd settings c a_id ++ "\n" ++ show a)
    unionLocal' c a_id b_id (EndInfNode (0,0)) b@(Leaf False) = (,) c (0,0)
    unionLocal' c a_id b_id (EndInfNode (1,0)) b@(Leaf False) = (,) c (1,0)
    unionLocal' c a_id b_id a b@(Leaf False) = (,) c a_id
    unionLocal' c@(Context{func_stack = (f:fs)}) a_id b_id a@(EndInfNode childA ) b@(Leaf True) = withCache c (a_id, b_id, "union") $ unionLocal_arg f c{func_stack = fs} childA b_id (getDd c childA) b --`debug` ("endif b = true, f_stakc = " ++ show f ++ "," ++ show fs ++ " a: " ++ show childA ++ " b: "  ++ show_dd settings c b_id)

    unionLocal' c a_id b_id a@(InfNodes {}) b@(Leaf True) = apply @a Union c a_id b_id "union" (unionInferB_ @a) a_id b_id a b
    unionLocal' c a_id b_id a b@(Leaf True) = inferNodeB @a (unionLocal @a) c a_id b_id a b -- leaf with node or end infnode


    unionLocal' c a_id b_id a@(Node positionA pos_childA neg_childA)  b@(Node positionB pos_childB neg_childB)
        -- no mismatch, only the appropriate elim rule is applied
        | positionA == positionB =
            let (c', pos_result) = supply_dds (unionLocal @a) c pos_childA pos_childB
                (c'', neg_result) = supply_dds (unionLocal @a) c' neg_childA neg_childB
            in (withCache c (a_id, b_id, "union") $ applyElimRule @a c'' (Node positionA pos_result neg_result)) `debug` "eeeuhm, normal? unionLocal?"
        | positionA < positionB = inferNodeB @a (unionLocal @a) c a_id b_id a b
        | positionA > positionB = inferNodeA @a (unionLocal @a) c a_id b_id a b

    unionLocal' c a_id b_id a@(InfNodes positionA _ _ _ _ _)  b@(Node positionB pos_childB neg_childB)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes"
        | positionA > positionB = inferNodeA @a (unionLocal @a) c a_id b_id a b
        | positionA < positionB = apply @a Union c a_id b_id "union" (unionInferB_ @a) a_id b_id a b -- infer infnode for A

    unionLocal' c a_id b_id a@(Node positionA pos_childA neg_childA)  b@(InfNodes positionB _ _ _ _ _)
        | positionA == positionB = error "undefined, multiple options possible for interpreting node in a context to sub nodes" -- a possible option: (InfNodes (dcA .*. pos_childB) (n1A .*. pos_childB) (n0A .*. pos_childB) (p1A .*. pos_childB) (p0A .*. pos_childB))
        | positionA < positionB =  inferNodeB @a (unionLocal @a) c a_id b_id a b
        | positionA > positionB =  apply @a Union c a_id b_id "union" (unionInferA_ @a) a_id b_id a b -- infer infnode for B

    unionLocal' c a_id b_id a@(InfNodes positionA _ _ _ _ _)  b@(InfNodes positionB _ _ _ _ _)
        | positionA == positionB = apply @a Union c{func_stack = (to_constr @a, Union) : func_stack c} a_id b_id "union" union a_id b_id a b `debug` "eeeuhm, normal? unionLocal?"
        | positionA < positionB =  apply @a Union c a_id b_id "union" (unionInferB_ @a) a_id b_id a b `debug` "eeeuhm, normal? unionLocal?" -- infer infnode A
        | positionA > positionB =  apply @a Union c a_id b_id "union" (unionInferA_ @a) a_id b_id a b `debug` "eeeuhm, normal? unionLocal?"-- infer infnode B

    unionLocal' c a_id b_id a@(InfNodes {}) b@(EndInfNode _) =  apply @a Union c a_id b_id "union" (unionInferB_ @a) a_id b_id a b `debug` "eeeuhm, normal? unionLocal?"
    unionLocal' c a_id b_id a@(EndInfNode _) b@(InfNodes {}) =  apply @a Union c a_id b_id "union" (unionInferA_ @a) a_id b_id a b `debug` "eeeuhm, normal? unionLocal?"

    -- continue local traversal
    unionLocal' c a_id b_id a@(Node positionA pos_childA neg_childA) b@(EndInfNode childB) = inferNodeB @a (unionLocal @a) c a_id b_id a b `debug` "eeeuhm, normal? unionLocal?"
    unionLocal' c a_id b_id a@(EndInfNode childA) b@(Node positionB pos_childB neg_childB) = inferNodeA @a (unionLocal @a) c a_id b_id a b `debug` "eeeuhm, normal? unionLocal?"

--     -- continue previous super domain traversal
    unionLocal' c@(Context{func_stack = (f:fs)}) a_id b_id a@(EndInfNode childA)  b@(EndInfNode childB) = withCache c (a_id, b_id, "union") $ continue_outer f c{func_stack = fs} childA childB (getDd c childA) (getDd c childB) `debug` "eeeuhm, normal? unionLocal?"  --`debug` ("endinf endinf union local, childA = " ++ show childA  ++ " \n \t childB = " ++ show childB )
    unionLocal' c@(Context{func_stack = []}) a_id b_id a@(EndInfNode childA)  b@(EndInfNode childB) = error "should not have empty context stack"  -- applyInfElimRule @a c $ union  Context{func_stack = []} childA childB
    unionLocal' c a_id b_id a b = error (show c ++ show a ++ show_dd settings c b_id)


    --todo add endinfnode (0,0) /(1,0) removal on leaf cases
    absorb' c a_id b_id a@(Leaf _) dc = if a == dc then (c, false @a) else (c, a_id)
    -- absorb' c a_id b_id a@(EndInfNode _) dc@(Node positionD pos_childD neg_childD)  = inferNodeA @a (absorb @a) c a_id b_id a dc
    absorb' c a_id b_id a@(EndInfNode a_child) dc@(Leaf _)  = if (getDd c a_child) == dc then (c, false @a) else (c, a_id)
    absorb' c a_id b_id a@(InfNodes {}) dc@(Leaf _)  = (c, a_id)
    absorb' c a_id b_id a@(Node positionA pos_childA neg_childA) dc@(EndInfNode _)  = --infere Dc node
        let (c', pos_result) = absorb @a c pos_childA b_id (getDd c pos_childA) dc
            (c'', neg_result) = absorb @a c' neg_childA b_id (getDd c neg_childA) dc
        in withCache c (a_id, b_id, "absorb") $ applyElimRule @a c'' (Node positionA pos_result neg_result)
    absorb' c a_id b_id a@(EndInfNode a') dc@(EndInfNode dc') = if a' == dc' then (c, false @a) else (c, a_id)
    absorb' c a_id b_id a@(Node positionA pos_childA neg_childA) dc@(Leaf _) =
        let (c', pos_result) = absorb @a c pos_childA b_id (getDd c pos_childA) dc
            (c'', neg_result) = absorb @a c' neg_childA b_id (getDd c neg_childA) dc
        in withCache c (a_id, b_id, "absorb") $ applyElimRule @a c'' (Node positionA pos_result neg_result)

    absorb' c a_id b_id a@(Node positionA pos_childA neg_childA)  dc@(Node positionD pos_childD neg_childD)
        -- No mismatch
        | positionA == positionD =
            let (c', pos_result) = absorb @a c pos_childA pos_childD (getDd c pos_childA) (getDd c pos_childD)
                (c'', neg_result) = absorb @a c' neg_childA neg_childD (getDd c neg_childA) (getDd c neg_childD)
            in withCache c (a_id, b_id, "absorb") $ applyElimRule @a c'' (Node positionA pos_result neg_result)

        -- Mismatch
        | positionA > positionD = inferNodeA @a (absorb @a) c a_id b_id a dc
        | positionA < positionD =
            let (c', pos_result) = absorb @a c pos_childA b_id (getDd c pos_childA) dc
                (c'', neg_result) = absorb @a c' neg_childA b_id (getDd c neg_childA) dc
            in withCache c (a_id, b_id, "absorb") $ applyElimRule @a c'' (Node positionA pos_result neg_result)

    absorb' c a_id b_id a@(InfNodes {}) b@(InfNodes {}) = case to_constr @a of
        Dc -> error "absorb with a dc as first argument should not be possible"
        Neg -> f True
        Pos -> f True
        where
            f b' = apply @a Absorb c a_id b_id "absorb" (t_and_rMain b') a_id b_id a b

    absorb' c a_id b_id a@(InfNodes positionA dcA n1A n0A p1A p0A) dc@(Node positionD pos_childD neg_childD)
        | positionA > positionD = inferNodeA @a (absorb @a) c a_id b_id a dc
        | positionA < positionD = case to_constr @a of
            Dc -> error "absorb with a dc as first argument should not be possible"
            Neg -> f True
            Pos -> f True
        | otherwise = undefined
            where
                f b' = apply @Dc Absorb c a_id b_id "absorb" (t_and_rInferB b') a_id b_id a dc
    -- add posB == posA, then we consider node to be AllNegs -> [1]
    absorb' c a_id b_id a@(Node positionA pos_childA neg_childA) dc@(InfNodes positionD dcA n1A n0A p1A p0A)
        | positionA > positionD =  case to_constr @a of
                Dc -> error "absorb with a dc as first argument should not be possible"
                Neg -> f True
                Pos -> f True
        | positionA < positionD =
            let (c', pos_result) = absorb @a c pos_childA b_id (getDd c pos_childA) dc
                (c'', neg_result) = absorb @a c' pos_childA b_id (getDd c neg_childA) dc
            in withCache c (a_id, b_id, "absorb") $ applyElimRule @a c'' (Node positionD pos_result neg_result)
        | otherwise = undefined
            where
                f b' = apply @a Absorb c a_id b_id "absorb" (t_and_rInferA b') a_id b_id a dc

    absorb' c a_id b_id a b = error $ "absorb , " ++ "a = " ++ show a ++ "b = " ++ show_dd settings c b_id


absorb_or_remove :: Context -> Bool
absorb_or_remove c@(Context {func_stack = ((_, f) : cs)})
  | f == Absorb = True
  | f == Remove = False
  | otherwise = absorb_or_remove c{func_stack = cs}
absorb_or_remove c@(Context{func_stack = []}) = error "no absorb or remove in current stack"
-- holds the debug and class specific functions
class DdF4 a where
    to_constr :: Inf
    applyElimRule :: Context -> Dd -> (Context, NodeId)
    intersectionLocal :: DdManipulation
    unionLocal :: DdManipulation
    absorb :: DdManipulation

    false :: NodeId
    true :: NodeId
    negate_maybe :: Context -> NodeId -> Dd -> (Context, NodeId)
    applyInfElimRule :: Context -> Dd -> (Context, NodeId)
    applyInfElimRule2 :: Context -> Dd -> (Context, NodeId)
    intersectionInferA_ :: DdManipulation
    intersectionInferB_ :: DdManipulation
    unionInferA_ :: DdManipulation
    unionInferB_ :: DdManipulation
    inferNodeA :: DdManipulation -> Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)
    inferNodeB :: DdManipulation -> Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)

type DdManipulation = Context -> NodeId -> NodeId -> Dd -> Dd -> (Context, NodeId)

instance DdF4 Dc where
    to_constr = Dc
    applyInfElimRule c (Leaf b) = (c, leaf b)
    applyInfElimRule c d = let (c', r) = applyElimRule @Dc c d in case getDd c' r of

        x@(InfNodes {}) -> insert c' $ EndInfNode r
        x -> (c', r)
    applyInfElimRule2 c (Leaf b) = (c, leaf b)
    applyInfElimRule2 c (EndInfNode (0,0)) = (c, (0,0))
    applyInfElimRule2 c (EndInfNode (1,0)) = (c, (1,0))
    applyInfElimRule2 c (EndInfNode child) = (c, child)
    applyInfElimRule2 c d = applyElimRule @Dc c d
    applyElimRule c d@(Node _ posC negC) = if posC == negC then (c, posC) else insert c d
    applyElimRule c d@(InfNodes pos dcR n1R n0R p1R p0R) =
        if (n1R, n0R, p1R, p0R) == ((0,0), (1,0), (0,0), (1,0)) then
                        (case getDd c dcR of
                            (EndInfNode x) -> (c, x)
                            (Leaf False) -> (c, (0,0))
                            (Leaf True) -> (c, (1,0))
                            _ -> insert c $ InfNodes pos dcR n1R n0R p1R p0R)
                        else insert c $ InfNodes pos dcR n1R n0R p1R p0R
    applyElimRule c d = insert c d-- (EndInfNode _) = error "cannot end on end infnodlet c = lastN' (len positionA) c ine"
    false = (-1,-1) --hack to not be equal to any leaf
    true = (-1,-1)
    negate_maybe c d_id _ = (c, d_id)
    intersectionInferB_ c a_id b_id a@(InfNodes positionA _ _ _ _ _) b = let (c', r) = intersectionInferB c{func_stack = ((Dc, Inter): func_stack c)} a_id b_id a b in ( c', r) --`debug` "adding"
    intersectionInferB_ _ _ _ _ _ = undefined
    intersectionInferA_ c a_id b_id a b@(InfNodes positionB _ _ _ _ _) = let (c', r) = intersectionInferA c{func_stack = ((Dc, Inter): func_stack c)} a_id b_id a b in ( c', r) --`debug` "adding"
    intersectionInferA_ _ _ _ _ _ = undefined
    unionInferB_ c a_id b_id a@(InfNodes positionA _ _ _ _ _) b = let (c', r) = unionInferB c{func_stack=((Dc, Union): func_stack c)} a_id b_id a b in ( c', r) --`debug` "adding"
    unionInferB_ _ _ _ _ _ = undefined
    unionInferA_ c a_id b_id a b@(InfNodes positionB _ _ _ _ _) = let (c', r) = unionInferA c{func_stack=((Dc, Union): func_stack c)} a_id b_id a b in ( c', r) --`debug` "adding"
    unionInferA_ c a_id b_id _ _ = error $ "-------------" ++ show_dd settings c a_id ++ "\n ==" ++ show_dd settings c b_id ++ ""
    intersectionLocal c a_id b_id a b = if (getDd c a_id == a) && (getDd c b_id == b)
        then  debug_manipulation (intersectionLocal' @Dc c a_id b_id a b)
            "intersection" "intersectionLocal Dc" c a_id b_id --"\n result: \n" ++ showTree c' (getDd c' r))
        else error "a and b are not equal"
    -- comparing nodes, allowed mis-matches based on each inference rule
    unionLocal c a_id b_id a b = if (getDd c a_id == a) && (getDd c b_id == b)
        then debug_manipulation (unionLocal' @Dc c a_id b_id a b)
            "union" "unionLocal Dc" c a_id b_id --"\n result: \n" ++ showTree c' (getDd c' r))
        else error "a and b are not equal"

    absorb = error "mixedintersection only with finite kinds"

    inferNodeA f c a_id b_id a b@(Node positionB pos_childB neg_childB) =
        let (c', pos_result) = supply_dds f c a_id pos_childB
            (c'', neg_result) = supply_dds f c' a_id neg_childB
        in applyElimRule @Dc c'' (Node positionB pos_result neg_result)
    inferNodeA _ c a_id b_id a b = error ("inferNode : " ++ show c ++ ", " ++ show a ++ ", " ++ show_dd settings c b_id)

    inferNodeB f c a_id b_id a@(Node positionA pos_childA neg_childA) b =
        let (c', pos_result) = supply_dds f c pos_childA b_id
            (c'', neg_result) = supply_dds f c' neg_childA b_id
        in applyElimRule @Dc c'' (Node positionA pos_result neg_result)
    inferNodeB f c a_id b_id a b = undefined `debug` ("infernodeB dc ; " ++ show c ++ "\n \t a: " ++ show a ++ " \n \t b: " ++ show_dd settings c b_id)


instance DdF4 Neg where
    to_constr = Neg
    applyInfElimRule c (Leaf b) = (c, leaf b)
    applyInfElimRule c d = let (c', r) = applyElimRule @Neg c d in insert c' $ EndInfNode r

    applyElimRule c d@(Node _ posC negC) = if posC == (0,0) then (c, negC) else insert c d
    applyElimRule c d@(InfNodes pos dcR n1R n0R p1R p0R) =
        if (dcR, n0R, p1R, p0R) == ((0,0), (1,0), (0,0), (1,0)) then
                        (case getDd c n1R of
                            (EndInfNode x) -> (c, x)
                            (Leaf False) -> (c, (0,0))
                            (Leaf True) -> (c, (1,0))
                            _ -> insert c $ InfNodes pos dcR n1R n0R p1R p0R)
                        else insert c $ InfNodes pos dcR n1R n0R p1R p0R
    applyElimRule c d = insert c d

    false = (0,0)
    true = (1,0)
    negate_maybe c d_id _ = (c, d_id)

    intersectionInferB_ c a_id b_id a@(InfNodes positionA _ _ _ _ _) b = let (c', r) = intersectionInferB c{func_stack=((Neg, Inter): func_stack c)} a_id b_id a b in ( c', r)
    intersectionInferB_ _ _ _ _ _ = undefined
    intersectionInferA_ c a_id b_id a b@(InfNodes positionB _ _ _ _ _) = let (c', r) = intersectionInferA c{func_stack=((Neg, Inter): func_stack c)} a_id b_id a b in ( c', r)
    intersectionInferA_ _ _ _ _ _ = undefined
    unionInferB_ c a_id b_id a@(InfNodes positionA _ _ _ _ _) b = let (c', r) = unionInferB c{func_stack=((Neg, Union): func_stack c)} a_id b_id a b in ( c', r)
    unionInferB_ _ _ _ _ _ = undefined
    unionInferA_ c a_id b_id a b@(InfNodes positionB _ _ _ _ _) = let (c', r) = unionInferA c{func_stack=((Neg, Union): func_stack c)} a_id b_id a b in ( c', r)
    unionInferA_ _ _ _ _ _ = undefined


    intersectionLocal c a_id b_id a b = debug_manipulation (intersectionLocal' @Neg c a_id b_id a b)
        "intersection" "intersectionLocal neg" c a_id b_id

    unionLocal c a_id b_id a b = if (getDd c a_id == a) && (getDd c b_id == b)
        then  debug_manipulation (unionLocal' @Neg c a_id b_id a b)
            "union" "unionLocal neg" c a_id b_id
        else error ("id and dd are not equal, \n a_id: " ++ show (getDd c a_id) ++ "\n a: " ++ show a ++ "\n b_id: " ++ show (getDd c b_id) ++ " \n b: " ++ show b )
    absorb c a_id b_id a b = if (getDd c a_id == a) && (getDd c b_id == b)
        then debug_manipulation (absorb' @Neg c a_id b_id a b)
            "absorb" "absorb neg" c a_id b_id
        else error ("id and dd are not equal, \n a_id: " ++ show (getDd c a_id) ++ "\n a: " ++ show a ++ "\n b_id: " ++ show (getDd c b_id) ++ " \n b: " ++ show b )

    inferNodeA f c a_id b_id a  b@(Node positionB pos_childB neg_childB) = if (getDd c a_id == a) && (getDd c b_id == b)
        then
            let (c', r) = f c a_id b_id (Node positionB (0,0) a_id) b in applyElimRule @Neg c' (getDd c' r)
        else error ("id and dd are not equal, \n a_id: " ++ show (getDd c a_id) ++ "\n a: " ++ show a ++ "\n b_id: " ++ show (getDd c b_id) ++ " \n b: " ++ show b )
    inferNodeA f c a_id b_id  a b = undefined `debug` ("inferNodeA ; c= " ++ (show c) ++ " a= " ++ (show a) ++ " b= " ++ (show_dd settings c b_id))


    inferNodeB f c a_id b_id a@(Node positionA pos_childA neg_childA) b =if (getDd c a_id == a) && (getDd c b_id == b)
        then
            let (c', r) = f c a_id b_id a (Node positionA (0,0) b_id) in applyElimRule @Neg c' $ getDd c' r
        else error ("id and dd are not equal, \n a_id: " ++ show (getDd c a_id) ++ "\n a: " ++ show a ++ "\n b_id: " ++ show (getDd c b_id) ++ " \n b: " ++ show b )
    inferNodeB _ _ a_id b_id  _ _ = undefined


instance DdF4 Pos where
    to_constr = Pos
    applyInfElimRule c (Leaf b) = (c, leaf b)
    applyInfElimRule c d = let (c', r) = applyElimRule @Pos c d in insert c' $ EndInfNode r

    applyElimRule c d@(Node _ posC negC) = if negC == (0,0) then (c, posC) else insert c d
    applyElimRule c d@(InfNodes pos dcR n1R n0R p1R p0R) =
        if (n1R, n0R, dcR, p0R) == ((0,0), (1,0), (0,0), (1,0)) then
            (case getDd c p1R of
                (EndInfNode x) -> (c, x)
                (Leaf False) -> (c, (0,0))
                (Leaf True) -> (c, (1,0))
                _ -> insert c $ InfNodes pos dcR n1R n0R p1R p0R)
        else insert c $ InfNodes pos dcR n1R n0R p1R p0R
    applyElimRule c d = insert c d

    false = (0,0)
    true = (1,0)
    negate_maybe c d_id _ = (c, d_id)


    intersectionInferB_ c a_id b_id a@(InfNodes positionA _ _ _ _ _) b = let (c', r) = intersectionInferB c{func_stack=((Pos, Inter): func_stack c)} a_id b_id a b in ( c', r)
    intersectionInferB_ _ _ _ _ _ = undefined
    intersectionInferA_ c a_id b_id a b@(InfNodes positionB _ _ _ _ _) = let (c', r) = intersectionInferA c{func_stack=((Pos, Inter): func_stack c)} a_id b_id a b in ( c', r)
    intersectionInferA_ _ _ _ _ _ = undefined
    unionInferB_ c a_id b_id a@(InfNodes positionA _ _ _ _ _) b = let (c', r) = unionInferB c{func_stack=(Pos, Union): func_stack c} a_id b_id a b in ( c', r)
    unionInferB_ _ _ _ _ _ = undefined
    unionInferA_ c a_id b_id a b@(InfNodes positionB _ _ _ _ _) = let (c', r) = unionInferA c{func_stack=(Pos, Union): func_stack c} a_id b_id a b in ( c', r)
    unionInferA_ _ _ _ _ _ = undefined
    intersectionLocal c a_id b_id a b = debug_manipulation (intersectionLocal' @Pos c a_id b_id a b)
        "intersection" "intersectionLocal pos: " c a_id b_id

    unionLocal c a_id b_id a b = debug_manipulation (unionLocal' @Pos c a_id b_id a b)
        "union" "unionLocal pos" c a_id b_id

    absorb c a_id b_id a b = debug_manipulation (absorb' @Pos c a_id b_id a b)
        "absorb" "absorb pos" c a_id b_id

    inferNodeA f c a_id b_id a b@(Node positionB pos_childB neg_childB) =
        let (c', r) = f c a_id b_id (Node positionB a_id (0,0)) b in applyElimRule @Pos c' $ getDd c' r
    inferNodeA _ c a_id b_id a b = error ("pos" ++ show c ++ show a ++ show_dd settings c b_id )
    inferNodeB f c a_id b_id a@(Node positionA pos_childA neg_childA) b =
        let (c', r) = f c a_id b_id a (Node positionA b_id (0,0)) in applyElimRule @Pos c' $ getDd c' r
    inferNodeB _ c a_id b_id a b = error "infernodeB" -- c a_id b_id




debugFlag = True
debugFlag2 = True

force_eval_debug :: c -> String -> c
force_eval_debug f s = unsafePerformIO $ do
    !x <- return f
    print s
    return x

debug :: c -> String -> c
debug f s = if debugFlag then trace s f else f

debug3 :: c -> [String] -> c
debug3 f s = trace (format' s) f

debug2 :: a -> String -> a
debug2 f s = if debugFlag2 then trace (colorize "red" s) f else f

debug4 :: a -> String -> a
debug4 f s = if True then trace (colorize "green" s) f else f

-- debug5 :: a -> String -> a
-- debug5 f s = if True then trace (colorize "red" s) f else f
