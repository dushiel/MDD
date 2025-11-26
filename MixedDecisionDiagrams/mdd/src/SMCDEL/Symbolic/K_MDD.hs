{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables, TupleSections #-}

module SMCDEL.Symbolic.K_MDD where

import Data.Bifunctor (bimap)
import Data.Tagged
import Data.List ((\\), intercalate, sort)
import qualified Data.Map.Strict as M
import Data.Map.Strict ((!))

import SMCDEL.Internal.Help (apply, lfp, powerset)
import SMCDEL.Internal.TexDisplay
import Internal.Language hiding (ite)
import SMCDEL.Symbolic.S5_MDD (KnState, texMdd) -- Reusing some types and functions

import MDD hiding (Neg)
import MDDi hiding (Form, Impl, PrpF, Bot, Top)

-- =============================================================================
-- * Phase 1: Relational Infrastructure
-- =============================================================================

-- | Phase 1: Variable Transformation
-- Standard variables: domain 0 (e.g., [(0, Dc1)] i)
-- Source variables (mv): domain 1 (e.g., [(1, Dc1)] i)
-- Target variables (cp): domain 2 (e.g., [(2, Dc1)] i)

mvP, cpP :: Prp -> Prp
mvP (P (Ll ((_, inf):xs) i)) = P (Ll ((1, inf):xs) i)
mvP p = error $ "mvP failed: Unexpected Prp structure: " ++ show p

cpP (P (Ll ((_, inf):xs) i)) = P (Ll ((2, inf):xs) i)
cpP p = error $ "cpP failed: Unexpected Prp structure: " ++ show p

-- | Helper to map back to standard vocabulary
unmvcpP :: Prp -> Prp
unmvcpP (P (Ll ((_, inf):xs) i)) = P (Ll ((0, inf):xs) i)
unmvcpP p = error $ "unmvcpP failed: Unexpected Prp structure: " ++ show p

mv, cp :: [Prp] -> [Prp]
mv = map mvP
cp = map cpP

-- | Phantom type for tagging Relational MDDs
data Dubbel
type RelMDD = Tagged Dubbel (Context, Node)

-- | Relational MDD Manipulation
-- Shifts a standard MDD (domain 0) to the Copy/Target domain (domain 2)
cpMdd :: Context -> [Prp] -> Node -> RelMDD
cpMdd c vocab n =
    let
        -- Create mapping from [0, i] to [2, i]
        relabeling = map (\p -> (toOrdinal p, toOrdinal (cpP p))) vocab
    in Tagged $ relabelWith relabeling (c, n)

-- Shifts a standard MDD (domain 0) to the Model/Source domain (domain 1)
mvMdd :: Context -> [Prp] -> Node -> RelMDD
mvMdd c vocab n =
    let
        -- Create mapping from [0, i] to [1, i]
        relabeling = map (\p -> (toOrdinal p, toOrdinal (mvP p))) vocab
    in Tagged $ relabelWith relabeling (c, n)

-- Shifts a Relational MDD (domains 1 or 2) back to standard domain (0)
unmvMdd :: Context -> [Prp] -> RelMDD -> (Context, Node)
unmvMdd c vocab tagged_node =
    let (ctx, node) = untag tagged_node
        -- Map Source (1) -> Standard (0)
        relabelingMv = map (\p -> (toOrdinal (mvP p), toOrdinal p)) vocab
        -- Map Target (2) -> Standard (0)
        relabelingCp = map (\p -> (toOrdinal (cpP p), toOrdinal p)) vocab

        -- Combine mappings. Order matters less here as domains 1 and 2 are disjoint.
        relabeling = relabelingMv ++ relabelingCp
    in relabelWith relabeling (ctx, node)


-- =============================================================================
-- * Belief Structures
-- =============================================================================

data BelStruct = BlS Context
                     [Prp]              -- vocabulary
                     MDD                -- state law (on standard vars)
                     (M.Map Agent RelMDD) -- observation laws (relations on mv/cp vars)
                     deriving (Show)

type BelScene = (BelStruct, KnState)
type MultipointedBelScene = (BelStruct, Node)

instance HasVocab BelStruct where
  vocabOf (BlS _ voc _ _) = voc

instance HasAgents BelStruct where
  agentsOf (BlS _ _ _ obdds) = M.keys obdds

instance Pointed BelStruct KnState
instance Pointed BelStruct Node

-- =============================================================================
-- * Main Translation (Formula -> MDD)
-- =============================================================================

mddOf :: BelStruct -> Form -> (Context, Node)
mddOf (BlS c _ _ _)   Top           = (c, top)
mddOf (BlS c _ _ _)   Bot           = (c, bot)
mddOf (BlS c _ _ _)   (PrpF (P n))  = path c (P'' [n]) -- Assumes P'' handles the domain correctly or P n is standard
mddOf bls (Neg form)    = (-.) (mddOf bls form)
mddOf bls (Conj forms)  = conSet $ map (mddOf bls) forms
mddOf bls (Disj forms)  = disSet $ map (mddOf bls) forms
mddOf bls (Xor  forms)  = xorSet $ map (mddOf bls) forms
mddOf bls (Impl f g)    = mddOf bls f .->. mddOf bls g
mddOf bls (Equi f g)    = mddOf bls f .<->. mddOf bls g
mddOf bls (Forall ps f) = forallSet (map toOrdinal ps) (mddOf bls f)
mddOf bls (Exists ps f) = existSet (map toOrdinal ps) (mddOf bls f)

-- Knowledge Operator: K_i phi
-- Logic: forall t . (StateLaw(t) -> (Relation_i(s, t) -> phi(t)))
mddOf bls@(BlS c allprops lawmdd obdds) (K i form) =
  let
    -- 1. Shift Law to Target (cp)
    (c_law, law_cp) = untag $ cpMdd c allprops lawmdd

    -- 2. Shift Formula to Target (cp)
    (c_form, form_node) = mddOf bls form
    (c_form_cp, form_cp) = untag $ cpMdd c_form allprops form_node

    -- 3. Get Relation (already on mv/cp)
    (c_omega, omega_i) = untag $ obdds ! i

    -- 4. Union contexts
    c_merged = unionContext c_law (unionContext c_form_cp c_omega)

    -- 5. Implication Chain: Law(t) -> (Rel(s,t) -> Phi(t))
    -- Note: .->. handles context union internally, but we use c_merged for safety
    (c_imp, imp_res) = (c_merged, law_cp) .->. ((c_merged, omega_i) .->. (c_merged, form_cp))

    -- 6. Quantify over Target variables (cp) to leave only Source variables (mv)
    ps_target = map toOrdinal (cp allprops)
    (c_forall, forall_res) = forallSet ps_target (c_imp, imp_res)

  in
    -- 7. Map Source variables (mv) back to Standard variables
    unmvMdd c_forall allprops (Tagged (c_forall, forall_res))

-- Knowing Whether: Kw_i phi = K_i phi OR K_i (NOT phi)
mddOf bls (Kw i form) =
  let
      (c1, k_form) = mddOf bls (K i form)
      (c2, k_neg_form) = mddOf bls (K i (Neg form))
  in (c1, k_form) .+. (c2, k_neg_form)

-- Common Knowledge: Ck_G phi
-- Fixed point of: E_G (phi AND Z)
mddOf bls@(BlS c voc lawmdd obdds) (Ck ags form) =
  let
    initial_guess = (c, top)
    ps_target = map toOrdinal (cp voc)

    -- Relations for all agents in the group, combined into one access relation
    -- E_G Z iff forall i in G, K_i Z.
    -- Or simpler: Union of relations R_G = Union(R_i).
    -- Then C_G phi = forall t . (R_G*(s,t) -> phi(t)).
    -- Here we use the iterative approach on the formula.

    -- Pre-calculate relations disjunction (Anyone in G considers possible...)
    -- Actually for "Everyone Knows", we need Intersection of Knowledge,
    -- which corresponds to Union of Relations in the reachability sense?
    -- "Everyone knows phi" = K_1 phi AND K_2 phi ...
    -- In fixed point: Z = phi AND K_1 Z AND K_2 Z ...

    -- Optimization: Pre-compute the union of relations R_G = U_{i in ags} R_i
    -- Then K_G Z = [R_G] Z
    agent_rels = map (\agent -> snd . untag $ obdds ! agent) ags
    (c_rels, rels_disj) = disSet (map (c,) agent_rels) -- Union of relations

    lambda z =
        let
            -- Calculate phi AND Z
            (c_form, form_mdd) = mddOf bls form
            (c_z, z_mdd) = z
            (c_conj, conj_mdd) = (c_form, form_mdd) .*. (c_z, z_mdd)

            -- Shift (phi AND Z) to Target (cp)
            (c_conj_cp, conj_cp) = untag $ cpMdd (unionContext c_conj c_z) voc conj_mdd

            -- Shift Law to Target (cp)
            (c_law_cp, law_cp) = untag $ cpMdd c_conj_cp voc lawmdd

            c_merged = unionContext c_law_cp c_rels

            -- Compute K_G (phi AND Z): Law(t) -> (R_G(s,t) -> (phi(t) AND Z(t)))
            (c_imp, imp_res) = (c_merged, law_cp) .->. ((c_merged, rels_disj) .->. (c_merged, conj_cp))

            -- Quantify out target
            (c_forall, forall_res) = forallSet ps_target (c_imp, imp_res)

            -- Shift result back to standard
            (c_res, res_mdd) = unmvMdd c_forall voc (Tagged (c_forall, forall_res))
        in (c_res, res_mdd)

    -- Iterate until convergence
    gfp op g =
        let next = op g
        in if snd g == snd next then g else gfp op next

  in gfp lambda initial_guess

mddOf bls (Ckw ags form) =
    let (c1, ck_form) = mddOf bls (Ck ags form)
        (c2, ck_neg_form) = mddOf bls (Ck ags (Neg form))
    in (c1, ck_form) .+. (c2, ck_neg_form)

mddOf _ (Announce _ _ _) = error "Private Announce not yet implemented for K_MDD"
mddOf _ (Dia _ _) = error "Dynamic operators not yet implemented for K_MDD"


-- =============================================================================
-- * Semantics and Updates
-- =============================================================================

validViaMdd :: BelStruct -> Form -> Bool
validViaMdd bls@(BlS c _ lawmdd _) f =
    let (c_law, law_node) = (c, lawmdd)
        (c_f, f_node) = mddOf bls f
    in snd ((c_law, law_node) .->. (c_f, f_node)) == top'

-- | Evaluate if a formula is true in a specific scene (Pointed Model)
evalViaMdd :: BelScene -> Form -> Bool
evalViaMdd (bls@(BlS c allprops _ _), s) f =
    let
        -- 1. Compute MDD for formula
        (c_f, f_node) = mddOf bls f

        -- 2. "Read" the actual state 's' (which is an MDD path) to determine the valuation
        -- We assume 's' is a single path MDD representing the actual world.
        -- We can intersect the formula with 's'. If result is 's', then True.
        -- Or simpler: Restrict the formula MDD by the literals in 's'.

        -- However, 'restrict' takes a Position and Bool.
        -- We need to extract the valuation from 's'.
        -- Since extracting from MDD 's' is complex without a helper,
        -- we can just check if (s -> f) is True (Top).
        -- Since s is a single point, if s implies f, then f is true at s.

        (c_s, s_node) = (c, s)
        (c_check, check_node) = (c_s, s_node) .->. (c_f, f_node)
    in
        snd check_node == top'

instance Semantics BelStruct where
  isTrue = validViaMdd

instance Semantics BelScene where
  isTrue = evalViaMdd

-- | Public Announcement: Updates Law and preserves Relations (implicitly)
-- [!psi] -> NewLaw = OldLaw AND mdd(psi)
pubAnnounce :: BelStruct -> Form -> BelStruct
pubAnnounce bls@(BlS c props lawmdd obs) f =
  let (c_new, law_new) = (c, lawmdd) .*. mddOf bls f
  in BlS c_new props law_new obs

-- | Public Announcement Logic for MDD
mddOf bls (PubAnnounce form1 form2) =
    mddOf bls form1 .->. mddOf (pubAnnounce bls form1) form2

mddOf bls (PubAnnounceW form1 form2) =
    ite (mddOf bls form1)
        (mddOf (pubAnnounce bls form1) form2)
        (mddOf (pubAnnounce bls (Neg form1)) form2)

-- Update Logic Instances
instance Update BelStruct Form where
  checks = []
  unsafeUpdate bls psi = pubAnnounce bls psi

instance Update BelScene Form where
  unsafeUpdate (kns,s) psi = (unsafeUpdate kns psi, s)

-- Placeholder for Private Announcement (Phase 4)
announce :: BelStruct -> [Agent] -> Form -> BelStruct
announce bls@(BlS c props lawmdd obdds) ags psi = error "Private Announcement not implemented"