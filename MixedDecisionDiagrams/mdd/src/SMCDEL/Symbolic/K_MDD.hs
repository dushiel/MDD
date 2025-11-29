{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables, TupleSections #-}

module SMCDEL.Symbolic.K_MDD where

import Data.Bifunctor (bimap)
import Data.Tagged
import Data.List ((\\), intercalate, sort, nub)
import qualified Data.Map.Strict as M
import Data.Map.Strict ((!))
import Debug.Trace (trace)

import SMCDEL.Internal.Help (apply, lfp, powerset)
import SMCDEL.Internal.TexDisplay
import Internal.Language hiding (ite)
import SMCDEL.Symbolic.S5_MDD (KnState, boolMddOf)

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
  agentsOf (BlS _ _ obdds) = M.keys obdds

instance Pointed BelStruct KnState
instance Pointed BelStruct Node

-- =============================================================================
-- * Transformers and Events
-- =============================================================================

data Transformer = Trf
  [Prp]                 -- addprops (new event variables)
  Form                  -- event law (precondition on new vars + interaction)
  (M.Map Prp Form)      -- changelaw (assignments: p := psi)
  (M.Map Agent RelMDD)  -- eventObs (observations of the event)
  deriving (Show)

instance HasAgents Transformer where
  agentsOf (Trf _ _ _ obdds) = M.keys obdds

-- An Event is a Transformer plus a Formula describing which event(s) actually happened.
type Event = (Transformer, Form)

instance HasPrecondition Transformer where
  preOf _ = Top

instance HasPrecondition Event where
  preOf (Trf addprops addlaw _ _, facts) =
      -- Simplistic precondition check: Exists addprops (facts AND addlaw)
      -- This ignores the state-dependent parts for now, simpler than BDD.
      Exists addprops (Conj [facts, addlaw])

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

mddOf bls@(BlS allprops lawmdd obdds) (K i form) =
  let
    -- 1. Shift Law to Target (cp)
    law_cp = untag $ cpMdd allprops lawmdd

    -- 2. Shift Formula to Target (cp)
    form_node = mddOf bls form
    form_cp = untag $ cpMdd allprops form_node

    -- 3. Get Relation
    omega_i = untag $ obdds ! i

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
      k_neg_form = mddOf bls (K i (Neg form))
  in k_form .+. k_neg_form

mddOf bls@(BlS voc lawmdd obdds) (Ck ags form) =
  let
    initial_guess = top
    ps_target = map toOrdinal (cp voc)

    agent_rels = map (\agent -> untag $ obdds ! agent) ags
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

    gfp op g =
        let next = op g
        in if snd g == snd next then g else gfp op next

  in gfp lambda top

mddOf bls (Ckw ags form) =
    let ck_form = mddOf bls (Ck ags form)
        ck_neg_form = mddOf bls (Ck ags (Neg form))
    in ck_form .+. ck_neg_form

-- Private Announcement (Legacy implementation using structural update helper)
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
        f_node = mddOf bls f
        check_node = s .->. f_node
    in
        snd check_node == top'

instance Semantics BelStruct where
  isTrue = validViaMdd

instance Semantics BelScene where
  isTrue = evalViaMdd

pubAnnounce :: BelStruct -> Form -> BelStruct
pubAnnounce bls f = update bls f

instance Update BelStruct Form where
  checks = []
  unsafeUpdate bls@(BlS props lawmdd obs) psi =
    let
        law_new = lawmdd .*. mddOf bls psi
    in
        BlS props law_new obs

instance Update BelScene Form where
  unsafeUpdate (kns,s) psi = (unsafeUpdate kns psi, s)


-- =============================================================================
-- * Event / Transformer Update Logic
-- =============================================================================

getLevelL :: Prp -> LevelL
getLevelL (P l) = l

-- | Shift the Action Model variables so they don't collide with the Belief Structure
shiftPrepare :: BelStruct -> Transformer -> (Transformer, [(Prp, Prp)])
shiftPrepare (BlS props _ _) (Trf addprops addlaw changelaw eventObs) =
  let
      -- Domain extraction for fresh generation
      domain = case props of
                  (P (Ll d _):_) -> d
                  [] -> [(0, Dc1)]

      -- Generate fresh props mapping
      -- We need 'n' fresh props where n = length addprops
      genFresh [] _ acc = acc
      genFresh (p:ps) used acc =
          let newP = freshp used domain
          in genFresh ps (newP:used) ((p,newP):acc)

      shiftRel = reverse $ genFresh addprops props []
      shiftAddProps = map snd shiftRel

      -- Relabel components
      addlawShifted = replPsInF shiftRel addlaw

      -- For changelaw: keys are existing props (no shift needed),
      -- values might refer to addprops (shift needed)
      changelawShifted = M.map (replPsInF shiftRel) changelaw

      -- For eventObs: The relations need to be shifted.
      -- RelMDD contains Context+Node. We must relabel the Node.
      -- The shiftRel maps P -> P'. We need ordinals.
      shiftRelOrd = map (\(p,q) -> (toOrdinal p, toOrdinal q)) shiftRel

      -- We also need to account for MV/CP shifts in relations if addprops are used in relations?
      -- The relations in eventObs are usually over (mv addprops) and (cp addprops).
      -- So we must shift mv->mv' and cp->cp'.
      shiftRelMV = map (\(p,q) -> (toOrdinal (mvP p), toOrdinal (mvP q))) shiftRel
      shiftRelCP = map (\(p,q) -> (toOrdinal (cpP p), toOrdinal (cpP q))) shiftRel
      fullShiftRelOrd = shiftRelMV ++ shiftRelCP

      eventObsShifted = M.map (\tagged ->
          let (c, n) = untag tagged
          in Tagged (relabelWith fullShiftRelOrd (c,n))) eventObs

  in (Trf shiftAddProps addlawShifted changelawShifted eventObsShifted, shiftRel)

instance Update BelScene Event where
  unsafeUpdate (bls@(BlS props lawmdd obs), s) (trf, eventFacts) =
      let
          -- 1. Shift the Transformer to avoid collisions
          (Trf addprops addlaw changelaw eventObs, shiftRel) = shiftPrepare bls trf

          -- Shift the event facts form to match the shifted addprops
          eventFactsShifted = replPsInF shiftRel eventFacts

          -- 2. Handle Assignments (Copying Logic)
          -- Identify which propositions are changing
          changeprops = M.keys changelaw

          -- Generate Copy Props (to hold old values)
          domain = case props of
            (P (Ll d _):_) -> d
            [] -> [(0, Dc1)]

          -- We need fresh props that are NOT in props AND NOT in addprops
          genCopies [] _ acc = acc
          genCopies (p:ps) used acc =
               let newP = freshp used domain
               in genCopies ps (newP:used) ((p,newP):acc)

          copyRel = reverse $ genCopies changeprops (props ++ addprops) []
          copyChangeProps = map snd copyRel

          -- Mapping for MDD Relabeling (p -> p_copy)
          copyRelOrd = map (\(p,q) -> (toOrdinal p, toOrdinal q)) copyRel

          -- 3. Construct New Law
          -- (a) Shift Old Law: Relabel occurrences of changeprops to their copies
          -- So law(p) becomes law(p_copy).
          law_shifted = relabelWith copyRelOrd lawmdd

          -- (b) Event Law: mddOf the shifted addlaw
          -- Note: mddOf requires a BelStruct. We construct a temporary one
          -- containing all necessary vars to parse the formula.
          tempBls = BlS (props ++ addprops ++ copyChangeProps) top M.empty
          law_event = mddOf tempBls addlaw

          -- (c) Assignment Laws: p <-> psi(p_copy)
          -- For each p in changelaw, p takes the value of psi.
          -- psi is evaluated in the old state, so we must relabel psi's vars to copies.
          assign_laws = map (\(p, psi) ->
              let
                  p_node = var' (getLevelL p)
                  psi_node = mddOf tempBls psi -- psi might use props or addprops
                  psi_shifted = relabelWith copyRelOrd psi_node -- shift psi to use copies
              in
                  p_node .<->. psi_shifted
            ) (M.toList changelaw)

          newLawNode = conSet (law_shifted : law_event : assign_laws)

          -- 4. Construct New Relations
          -- Agents distinguish 'addprops' via eventObs.
          -- Agents distinguish 'changeprops' (p) via their old relations on 'copyChangeProps' (p_copy).
          -- We need to shift the old relations: mv(p) -> mv(p_copy), cp(p) -> cp(p_copy)

          copyRelMV = map (\(p,q) -> (toOrdinal (mvP p), toOrdinal (mvP q))) copyRel
          copyRelCP = map (\(p,q) -> (toOrdinal (cpP p), toOrdinal (cpP q))) copyRel
          fullCopyRelOrd = copyRelMV ++ copyRelCP

          newOfor i rel_tagged =
              let
                  -- Old relation shifted to copies
                  old = untag rel_tagged
                  relOldShifted = relabelWith fullCopyRelOrd old

                  -- Event relation (already shifted in step 1)
                  relEvent_tagged = M.findWithDefault (Tagged top) i eventObs
                  ev = untag relEvent_tagged
              in
                  Tagged (relOldShifted .*. ev)

          newObs = M.mapWithKey newOfor obs

          -- 5. Construct New State
          -- s is the old state (MDD).
          -- (a) Relabel s to copies: s(p) -> s(p_copy)
          s_copy = relabelWith copyRelOrd s

          -- (b) Intersect with assignments and event facts
          -- This effectively calculates the new values of p based on psi(p_copy) and s(p_copy)
          -- and sets addprops based on eventFacts.
          factsNode = mddOf tempBls eventFactsShifted

          newStateNode = conSet [s_copy, factsNode, conSet assign_laws]

          -- 6. Final Vocabulary
          newProps = props ++ addprops ++ copyChangeProps

      in (BlS newProps newLawNode newObs, newStateNode)


-- Simple announce wrapper (re-implemented using Transformers for consistency?
-- Or keep separate? The prompt asked for Events/Transformers logic, but legacy announce
-- is fine to keep as is for now as it's lighter).
announce :: BelStruct -> [Agent] -> Form -> BelStruct
announce bls@(BlS props lawmdd obdds) ags psi =
  let
    domain = case props of
                (P (Ll d _):_) -> d
                [] -> [(0, Dc1)]
    p_k = freshp props domain
    k_level = getLevelL p_k
    k_mdd = var' k_level

    newprops = (p_k : props)
    psi_mdd = mddOf bls psi
    newlaw = lawmdd .*. (k_mdd .->. psi_mdd)

    mv_k = var' (getLevelL $ mvP p_k)
    cp_k = var' (getLevelL $ cpP p_k)

    newOfor i rel_tagged =
        let rel = untag rel_tagged
        in if i `elem` ags
           then Tagged $ rel .*. (mv_k .<->. cp_k)
           else Tagged $ rel .*. ((-.) cp_k)

    newobdds = M.mapWithKey newOfor obdds

  in --trace ("\n private announce to : " ++ (show ags) ++ "\n for formula: " ++ show psi ++ "\n newlaw: " ++ show_dd settings (fst newlaw) (snd newlaw) ++ "\n added freshp : " ++ show p_k ++ "\n knowledge laws: \n " ++ intercalate "\n , " (map (\(agent, rel) -> "Agent " ++ agent ++ " : " ++ show_dd settings (fst $ untag rel ) (snd $ untag rel )) (M.toList newomdds)) ++ " \n " )
  (BlS newprops newlaw newobdds)
