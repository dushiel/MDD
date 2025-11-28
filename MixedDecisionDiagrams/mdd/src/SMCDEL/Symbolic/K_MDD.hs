{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables, TupleSections #-}

module SMCDEL.Symbolic.K_MDD where

import Data.Bifunctor (bimap)
import Data.Tagged
import Data.List ((\\), intercalate, sort)
import qualified Data.Map.Strict as M
import Data.Map.Strict ((!))
import Debug.Trace (trace)

import SMCDEL.Internal.Help (apply, lfp, powerset)
import SMCDEL.Internal.TexDisplay
import Internal.Language hiding (ite)
import SMCDEL.Symbolic.S5_MDD (KnState)

import MDD hiding (Neg)
import MDDi hiding (Form, Impl, PrpF, Bot, Top)
import DrawMDD

-- =============================================================================
-- * Phase 1: Relational Infrastructure
-- =============================================================================

mvP, cpP :: Prp -> Prp
mvP (P (Ll ((_, inf):xs) i)) = P (Ll ((1, inf):xs) i)
mvP p = error $ "mvP failed: Unexpected Prp structure: " ++ show p

cpP (P (Ll ((_, inf):xs) i)) = P (Ll ((2, inf):xs) i)
cpP p = error $ "cpP failed: Unexpected Prp structure: " ++ show p

unmvcpP :: Prp -> Prp
unmvcpP (P (Ll ((_, inf):xs) i)) = P (Ll ((0, inf):xs) i)
unmvcpP p = error $ "unmvcpP failed: Unexpected Prp structure: " ++ show p

mv, cp :: [Prp] -> [Prp]
mv = map mvP
cp = map cpP

data Dubbel
type RelMDD = Tagged Dubbel (Context, Node)

-- | Shifts a standard MDD (domain 0) to the Copy/Target domain (domain 2)
cpMdd :: [Prp] -> (Context, Node) -> RelMDD
cpMdd vocab (c, n) =
    let relabeling = map (\p -> (toOrdinal p, toOrdinal (cpP p))) vocab
    in Tagged $ relabelWith relabeling (c, n)

-- | Shifts a standard MDD (domain 0) to the Model/Source domain (domain 1)
mvMdd :: [Prp] -> (Context, Node) -> RelMDD
mvMdd vocab (c, n) =
    let relabeling = map (\p -> (toOrdinal p, toOrdinal (mvP p))) vocab
    in Tagged $ relabelWith relabeling (c, n)

-- | Shifts a Relational MDD (domains 1) back to standard domain (0)
unmvMdd :: [Prp] -> RelMDD -> (Context, Node)
unmvMdd vocab tagged_node =
    let (ctx, node) = untag tagged_node
        relabelingMv = map (\p -> (toOrdinal (mvP p), toOrdinal p)) vocab
    in relabelWith relabelingMv (ctx, node)

-- | Shifts a Relational MDD (domains 2) back to standard domain (0)
uncpMdd :: [Prp] -> RelMDD -> (Context, Node)
uncpMdd vocab tagged_node =
    let (ctx, node) = untag tagged_node
        relabelingCp = map (\p -> (toOrdinal (cpP p), toOrdinal p)) vocab
    in relabelWith relabelingCp (ctx, node)

-- =============================================================================
-- * Belief Structures
-- =============================================================================

-- Removed explicit Context field. It is now implicit in MDD and RelMDD.
data BelStruct = BlS [Prp]              -- vocabulary
                     MDD                -- state law (on standard vars)
                     (M.Map Agent RelMDD) -- observation laws
                     deriving (Show)

type BelScene = (BelStruct, KnState)
type MultipointedBelScene = (BelStruct, Node)

instance HasVocab BelStruct where
  vocabOf (BlS voc _ _) = voc

instance HasAgents BelStruct where
  agentsOf (BlS _ _ omdds) = M.keys omdds

instance Pointed BelStruct KnState
instance Pointed BelStruct Node

-- =============================================================================
-- * Main Translation (Formula -> MDD)
-- =============================================================================

mddOf :: BelStruct -> Form -> (Context, Node)
mddOf _   Top           = top
mddOf _   Bot           = bot
mddOf _   (PrpF (P n))  = var' n
mddOf bls (Neg form)    = (-.) (mddOf bls form)
mddOf bls (Conj forms)  = conSet $ map (mddOf bls) forms
mddOf bls (Disj forms)  = disSet $ map (mddOf bls) forms
mddOf bls (Xor  forms)  = xorSet $ map (mddOf bls) forms
mddOf bls (Impl f g)    = mddOf bls f .->. mddOf bls g
mddOf bls (Equi f g)    = mddOf bls f .<->. mddOf bls g
mddOf bls (Forall ps f) = forallSet (map toOrdinal ps) (mddOf bls f)
mddOf bls (Exists ps f) = existSet (map toOrdinal ps) (mddOf bls f)

mddOf bls@(BlS allprops lawmdd omdds) (K i form) =
  let
    -- 1. Shift Law to Target (cp)
    law_cp = untag $ cpMdd allprops lawmdd


    -- 2. Shift Formula to Target (cp)
    form_node = mddOf bls form
    form_cp = untag $ cpMdd allprops form_node

    -- 3. Get Relation
    omega_i = untag $ omdds ! i

    -- 5. Implication Chain: Law(t) -> (Rel(s,t) -> Phi(t))
    imp_res = law_cp .->. (omega_i .->. form_cp)

    -- 6. Quantify over Target variables (cp)
    ps_target = map toOrdinal (cp allprops)
    forall_res = forallSet ps_target imp_res

  in
    -- 7. Map Source variables (mv) back to Standard variables
    (unmvMdd allprops (Tagged forall_res))

mddOf bls (Kw i form) =
  let
      k_form = mddOf bls (K i form)
      -- k_neg_form = mddOf bls (K i (Neg form))
  in k_form -- .+. k_neg_form

mddOf bls@(BlS voc lawmdd omdds) (Ck ags form) =
  let
    initial_guess = top
    ps_target = map toOrdinal (cp voc)

    agent_rels = map (\agent -> untag $ omdds ! agent) ags
    rels_disj = disSet agent_rels -- Union of relations

    lambda z =
        let
            -- Calculate phi AND Z
            form_mdd = mddOf bls form
            z_mdd = z
            conj_mdd = form_mdd .*. z_mdd

            -- Shift (phi AND Z) to Target (cp)
            conj_cp = untag $ cpMdd voc conj_mdd

            -- Shift Law to Target (cp)
            law_cp = untag $ cpMdd voc lawmdd

            -- Compute K_G (phi AND Z): Law(t) -> (R_G(s,t) -> (phi(t) AND Z(t)))
            imp_res = law_cp .->. (rels_disj .->. conj_cp)

            -- Quantify out target
            forall_res = forallSet ps_target imp_res

            -- Shift result back to standard
            res_mdd = unmvMdd voc (Tagged forall_res)
        in res_mdd

    -- Iterate until convergence
    gfp op g =
        let next = op g
        in if snd g == snd next then g else gfp op next

  in gfp lambda top

mddOf bls (Ckw ags form) =
    let ck_form = mddOf bls (Ck ags form)
        ck_neg_form = mddOf bls (Ck ags (Neg form))
    in ck_form .+. ck_neg_form

mddOf bls@(BlS props _ _) (Announce ags f g) =
  let
    domain = case props of
                (P (Ll d _):_) -> d
                [] -> [(0, Dc1)]
    p_k = freshp props domain
    k_pos = toOrdinal p_k
    bls' = announce bls ags f
  in
    mddOf bls f .->. restrict k_pos True (mddOf bls' g)

mddOf bls@(BlS props _ _) (AnnounceW ags f g) =
  let
    domain = case props of
                (P (Ll d _):_) -> d
                [] -> [(0, Dc1)]
    p_k = freshp props domain
    k_pos = toOrdinal p_k

    lhs = mddOf bls f
    rhs_true = restrict k_pos True (mddOf (announce bls ags f) g)
    rhs_false = restrict k_pos True (mddOf (announce bls ags (Neg f)) g)
  in
    ite (mddOf bls f) rhs_true rhs_false

mddOf _ (Dia _ _) = error "Dynamic operators not yet implemented for K_MDD"

mddOf bls (PubAnnounce form1 form2) =
    mddOf bls form1 .->. mddOf (bls `update` form1) form2

mddOf bls (PubAnnounceW form1 form2) =
    ite (mddOf bls form1)
        (mddOf (pubAnnounce bls form1) form2)
        (mddOf (pubAnnounce bls (Neg form1)) form2)

-- =============================================================================
-- * Semantics and Updates
-- =============================================================================

validViaMdd :: BelStruct -> Form -> Bool
validViaMdd bls@(BlS _ lawmdd _) f =
    let f_node = mddOf bls f
    in snd (lawmdd .->. f_node) == top'

evalViaMdd :: BelScene -> Form -> Bool
evalViaMdd (bls@(BlS _ lawmdd _), s) f =
    let
        -- 1. Compute MDD for formula
        f_node = mddOf bls f

        -- 2. State 's' is the actual world MDD
        check_node = s .->. f_node
    in
        trace ("evalvia mdd: checking state : " ++ show_dd settings (fst s) (snd s)
            ++ "\n against law: " ++  show_dd settings (fst lawmdd) (snd lawmdd)
            ) (snd check_node == top')

instance Semantics BelStruct where
  isTrue = validViaMdd

instance Semantics BelScene where
  isTrue = evalViaMdd

pubAnnounce :: BelStruct -> Form -> BelStruct
pubAnnounce bls f = update bls f

instance Update BelStruct Form where
  checks = [] -- unpointed structures can be updated with anything
  unsafeUpdate bls@(BlS props lawmdd obs) psi =
    let
        law_new = lawmdd .*. mddOf bls psi
    in
        BlS props law_new obs

instance Update BelScene Form where
  unsafeUpdate (kns,s) psi = (unsafeUpdate kns psi, s)

getLevelL :: Prp -> LevelL
getLevelL (P l) = l

announce :: BelStruct -> [Agent] -> Form -> BelStruct
announce bls@(BlS props lawmdd omdds) ags psi =
  let
    -- 1. Generate fresh proposition k
    domain = case props of
                (P (Ll d _):_) -> d
                [] -> [(0, Dc1)]
    p_k = (freshp props domain)
    k_level = getLevelL p_k
    k_mdd = var' k_level

    -- 2. Update Properties
    newprops = p_k : props

    -- 3. Update State Law: law AND (k -> psi)
    psi_mdd = mddOf bls psi
    newlaw = lawmdd .*. (k_mdd .->. psi_mdd)

    -- 4. Update Relations
    -- Agents in ags distinguish k (mv_k <-> cp_k)
    -- Agents not in ags do not see k (cp_k is false)
    mv_k = var' (getLevelL $ mvP p_k)
    cp_k = var' (getLevelL $ cpP p_k)

    newOfor i rel_tagged =
        let rel = untag rel_tagged
        in if i `elem` ags
           then Tagged $ rel .*. (mv_k .<->. cp_k)
           else Tagged $ rel .*. ((-.) cp_k)

    newomdds = M.mapWithKey newOfor omdds

  in --trace ("\n private announce to : " ++ (show ags) ++ "\n for formula: " ++ show psi ++ "\n newlaw: " ++ show_dd settings (fst newlaw) (snd newlaw) ++ "\n added freshp : " ++ show p_k ++ "\n knowledge laws: \n " ++ intercalate "\n , " (map (\(agent, rel) -> "Agent " ++ agent ++ " : " ++ show_dd settings (fst $ untag rel ) (snd $ untag rel )) (M.toList newomdds)) ++ " \n " )
  (BlS newprops newlaw newomdds)