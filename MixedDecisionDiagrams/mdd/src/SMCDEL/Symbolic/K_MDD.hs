{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables, TupleSections #-}

module SMCDEL.Symbolic.K_MDD where

import Data.Bifunctor (bimap)
import Data.Tagged
import Data.List ((\\), intercalate, sort)
import qualified Data.Map.Strict as M
import Data.Map.Strict ((!))

import SMCDEL.Internal.Help (apply, lfp, powerset)
import SMCDEL.Internal.TexDisplay
import SMCDEL.Language hiding (ite)
import SMCDEL.Symbolic.S5_MDD (KnState, texMdd, getSupport) -- Reusing some types and functions

import MDD hiding (Neg)
import MDDi hiding (Form, Impl, PrpF, Bot, Top)

-- Vocabulary Manipulation (doubled vocabulary for relations)
mvP, cpP :: Prp -> Prp
mvP (P n) = P (2*n)      -- p in the 'model view'
cpP (P n) = P ((2*n) + 1) -- p in the 'copied view'

unmvcpP :: Prp -> Prp
unmvcpP (P m) | even m    = P $ m `div` 2
              | otherwise = P $ (m-1) `div` 2

mv, cp :: [Prp] -> [Prp]
mv = map mvP
cp = map cpP

-- Type alias for a relational MDD
type RelMDD = Tagged Dubbel (Context, Node)
data Dubbel -- Phantom type for tagging

-- Belief Structure Definition
data BelStruct = BlS Context
                     [Prp]              -- vocabulary
                     Node               -- state law
                     (M.Map Agent RelMDD) -- observation laws
                     deriving (Show)

type BelScene = (BelStruct, KnState)
type MultipointedBelScene = (BelStruct, Node)

instance HasVocab BelStruct where
  vocabOf (BlS _ voc _ _) = voc

instance HasAgents BelStruct where
  agentsOf (BlS _ _ _ obdds) = M.keys obdds

instance Pointed BelStruct KnState
instance Pointed BelStruct Node


-- Helper to create an MDD for a single state (conjunction of literals)
boolMddOutOf :: Context -> [Prp] -> [Prp] -> (Context, Node)
boolMddOutOf c ps qs =
  let
    true_props = map (\(P n) -> path c (P'' [n])) ps
    false_props = map (\(P n) -> (-.) (path c (P'' [n]))) (qs \\ ps)
  in conSet (true_props ++ false_props)

-- Relational MDD Manipulation
cpMdd :: Context -> [Prp] -> Node -> RelMDD
cpMdd c vocab n =
    let relabeling = map (bimap ((\(P i) -> [i]) . mvP) ((\(P i) -> [i]) . cpP)) vocab
    in Tagged $ relabelWith relabeling (c, n)

mvMdd :: Context -> [Prp] -> Node -> RelMDD
mvMdd c vocab n =
    let relabeling = map (bimap ((\(P i) -> [i])) ((\(P i) -> [i]) . mvP)) vocab
    in Tagged $ relabelWith relabeling (c, n)

unmvMdd :: Context -> [Prp] -> RelMDD -> (Context, Node)
unmvMdd c vocab tagged_node =
    let (ctx, node) = untag tagged_node
        relabeling = map (bimap ((\(P i) -> [i]) . mvP) ((\(P i) -> [i]))) vocab
    in relabelWith relabeling (ctx, node)

-- Main translation function from Formula to MDD
mddOf :: BelStruct -> Form -> (Context, Node)
mddOf (BlS c _ _ _)   Top           = (c, top)
mddOf (BlS c _ _ _)   Bot           = (c, bot)
mddOf (BlS c _ _ _)   (PrpF (P n))  = path c (P'' [n])
mddOf bls (Neg form)    = (-.) (mddOf bls form)
mddOf bls (Conj forms)  = conSet $ map (mddOf bls) forms
mddOf bls (Disj forms)  = disSet $ map (mddOf bls) forms
mddOf bls (Xor  forms)  = xorSet $ map (mddOf bls) forms
mddOf bls (Impl f g)    = mddOf bls f .->. mddOf bls g
mddOf bls (Equi f g)    = mddOf bls f .<->. mddOf bls g
mddOf bls (Forall ps f) = forallSet (map (\(P n) -> [n]) ps) (mddOf bls f)
mddOf bls (Exists ps f) = existSet (map (\(P n) -> [n]) ps) (mddOf bls f)

mddOf bls@(BlS c allprops lawmdd obdds) (K i form) =
  let
    (c_law, law_cp) = untag $ cpMdd c allprops lawmdd
    (c_form, form_cp) = untag $ cpMdd c_law allprops (snd $ mddOf bls form)
    (c_omega, omega_i) = untag $ obdds ! i
    c_merged = unionContext c_form c_omega

    -- psi .->. (omega .->. phi) == (psi .*. omega) .->. phi
    (c_imp1, imp1) = (c_merged, law_cp) .->. ((c_merged, omega_i) .->. (c_merged, form_cp))
    ps' = map ((\(P n) -> [n]) . cpP) allprops
    (c_forall, forall_res) = forallSet ps' (c_imp1, imp1)
  in unmvMdd c_forall allprops (Tagged (c_forall, forall_res))

mddOf bls@(BlS c allprops lawmdd obdds) (Kw i form) =
  let
      (c1, k_form) = mddOf bls (K i form)
      (c2, k_neg_form) = mddOf bls (K i (Neg form))
  in (c1, k_form) .+. (c2, k_neg_form)

mddOf bls@(BlS c voc lawmdd obdds) (Ck ags form) =
  let
    initial_guess = (c, top)
    ps' = map ((\(P n) -> [n]) . cpP) voc

    -- Relations for all agents in the group
    agent_rels = map (\agent -> snd . untag $ obdds ! agent) ags
    (c_rels, rels_disj) = disSet (map (c,) agent_rels)

    lambda z =
        let
            (c_form, form_mdd) = mddOf bls form
            (c_z, z_mdd) = z
            (c_conj, conj_mdd) = (c_form, form_mdd) .*. (c_z, z_mdd)

            (c_law_cp, law_cp) = untag $ cpMdd c_conj voc lawmdd
            (c_conj_cp, conj_cp) = untag $ cpMdd c_law_cp voc conj_mdd

            c_merged = unionContext c_conj_cp c_rels

            (c_imp, imp_res) = (c_merged, law_cp) .->. ((c_merged, rels_disj) .->. (c_merged, conj_cp))
            (c_forall, forall_res) = forallSet ps' (c_imp, imp_res)
        in unmvMdd c_forall voc (Tagged (c_forall, forall_res))

    gfp op g = if snd g == snd (op g) then g else gfp op (op g)
  in gfp lambda initial_guess

mddOf bls (Ckw ags form) =
    let (c1, ck_form) = mddOf bls (Ck ags form)
        (c2, ck_neg_form) = mddOf bls (Ck ags (Neg form))
    in (c1, ck_form) .+. (c2, ck_neg_form)

mddOf _ (PubAnnounce _ _) = error "PubAnnounce not implemented for K_MDD"
mddOf _ (Announce _ _ _) = error "Announce not implemented for K_MDD"
mddOf _ (Dia _ _) = error "Dynamic operators not implemented for K_MDD"


-- Semantics
validViaMdd :: BelStruct -> Form -> Bool
validViaMdd bls@(BlS c _ lawmdd _) f =
    let (c_law, law_node) = (c, lawmdd)
        (c_f, f_node) = mddOf bls f
    in snd ((c_law, law_node) .->. (c_f, f_node)) == top

evalViaMdd :: BelScene -> Form -> Bool
evalViaMdd (bls@(BlS c allprops _ _), s) f =
    let (c_f, f_node) = mddOf bls f
        assignments = [(fromEnum p, p `elem` s) | p <- allprops]
        (c_final, final_node) = foldl (\(ctx, node) (var, val) -> restrict [var] val (ctx, node)) (c_f, f_node) assignments
    in case snd final_node of
        Leaf True -> True
        _         -> False

instance Semantics BelStruct where
  isTrue = validViaMdd

instance Semantics BelScene where
  isTrue = evalViaMdd

-- Update Logic
instance Update BelStruct Form where
  checks = []
  unsafeUpdate bls@(BlS c props lawmdd obs) psi =
    let (c_new, law_new) = (c, lawmdd) .*. mddOf bls psi
    in BlS c_new props law_new obs

instance Update BelScene Form where
  unsafeUpdate (kns,s) psi = (unsafeUpdate kns psi,s)

pubAnnounce :: BelStruct -> Form -> BelStruct
pubAnnounce bls@(BlS c props lawmdd obs) f =
  let (c_new, law_new) = (c, lawmdd) .*. mddOf bls f
  in BlS c_new props law_new obs

announce :: BelStruct -> [Agent] -> Form -> BelStruct
announce bls@(BlS c props lawmdd obdds) ags psi =
  let
    proppsi@(P k) = freshp props
    newprops  = sort $ proppsi : props
    (c1, psi_mdd) = mddOf bls psi
    (c2, k_mdd) = path c1 (P'' [k])

    (c_equiv, equiv_mdd) = (c2, k_mdd) .<->. (c1, psi_mdd)
    (c_law, law_node) = (unionContext c c_equiv, lawmdd)
    (c_new_law, new_law_mdd) = (c_law, law_node) .*. (c_equiv, equiv_mdd)

    newobdds  = M.mapWithKey (newOfor c_new_law newprops k) obdds
    newOfor ctx voc p_k i oi
      | i `elem` ags = let
          (c_mv, mv_k) = untag $ mvMdd ctx voc (snd k_mdd)
          (c_cp, cp_k) = untag $ cpMdd c_mv voc (snd k_mdd)
          (c_eq, eq_k) = (c_cp, mv_k) .<->. (c_cp, cp_k)
          in Tagged $ oi .*. (Tagged (c_eq, eq_k))
      | otherwise = let
          (c_cp, cp_k) = untag $ cpMdd ctx voc (snd k_mdd)
          (c_neg, neg_k) = (-.) (c_cp, cp_k)
          in Tagged $ oi .*. (Tagged (c_neg, neg_k))

  in BlS c_new_law newprops new_law_mdd newobdds

-- Visualization
texRelMDD :: RelMDD -> String
texRelMDD tagged_node =
  let (c,n) = untag tagged_node
  in texMdd (c,n) -- Simplified for now

ddprefix, ddsuffix :: String
ddprefix = "\\begin{array}{l} \\scalebox{0.3}{"
ddsuffix = "} \\end{array} \n"

instance TexAble BelStruct where
  tex (BlS c props lawmdd obdds) = concat
    [ " \\left( \n"
    , tex props, ", "
    , ddprefix, texMdd (c, lawmdd), ddsuffix
    , ", "
    , intercalate ", " obddstrings
    , " \\right) \n"
    ] where
        obddstrings = map (bddstring . (fst &&& (texRelMDD . snd))) (M.toList obdds)
        bddstring (i,os) = "\\Omega_{\\text{" ++ i ++ "}} = " ++ ddprefix ++ os ++ ddsuffix

instance TexAble BelScene where
  tex (bls, state) = concat
    [ " \\left( \n", tex bls, ", ", tex state, " \\right) \n" ]
