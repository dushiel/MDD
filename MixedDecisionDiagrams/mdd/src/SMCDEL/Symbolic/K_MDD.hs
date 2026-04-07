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
import SMCDEL.Internal.Language hiding (ite)
import SMCDEL.Symbolic.S5_MDD (KnState, boolMddOf)

import MDD.Types hiding (Neg)
import MDD.Extra.Interface
import MDD.Extra.Draw (settings, show_dd, show_node, show_mdd)

-- * refactored with AI

-- | Standard domain (0, 0) for state law propositions
standardDomain :: [(Int, InfL)]
standardDomain = [(0, Dc1), (1, Dc1)]

-- | Standard domain (0, 1) for event variables in transformers
eventFactsDomain :: [(Int, InfL)]
eventFactsDomain = [(0, Dc1), (0, Dc1)]

-- | Event facts domain with Neg1 inner context, for constraining which events have occurred
eventFactsDomainNeg :: [(Int, InfL)]
eventFactsDomainNeg = [(0, Dc1), (0, Neg1)]

-- | Index agent domain for observables
agentDomain :: [(Int, InfL)]
agentDomain = [(1, Dc1)]

-- | Model/Source domain (2, .. ) for observables (mv relations)
-- (2, 0) for mv standard props, (2, 1) for mv eventfacts / variables
mvDomain :: [(Int, InfL)]
mvDomain = [(2, Dc1)]

-- | Copy/Target domain (3, .. ) for observables (cp relations)
-- (3, 0) for cp standard props, (3, 1) for cp eventfacts / variables
cpDomain :: [(Int, InfL)]
cpDomain = [(3, Dc1)]


data Dubbel
type RelMDD = Tagged Dubbel MDD

data BelStruct = BlS [Prp]              -- vocabulary
                     MDD                -- state law (on standard vars)
                     (M.Map Agent Int, RelMDD) -- observation laws
                     deriving (Show)

type BelScene = (BelStruct, KnState)
type MultipointedBelScene = (BelStruct, Node)

instance HasVocab BelStruct where
  vocabOf (BlS voc _ _) = voc

instance HasAgents BelStruct where
  agentsOf (BlS _ _ (obdds, _)) = M.keys obdds

instance Pointed BelStruct KnState
instance Pointed BelStruct Node

data Transformer = Trf
  [Prp]                 -- addprops (new event variables)
  Form                  -- event law (precondition on new vars + interaction)
  (M.Map Prp Form)      -- changelaw (assignments: p := psi)
  (M.Map Agent Int, RelMDD)  -- eventObs (observations of the event)
  deriving (Show)

instance HasAgents Transformer where
  agentsOf (Trf _ _ _ (obdds, _)) = M.keys obdds

-- An Event is a Transformer plus a Formula describing which event(s) actually happened.
type Event = (Transformer, Form)

instance HasPrecondition Transformer where
  preOf _ = Top

instance HasPrecondition Event where
  preOf (Trf addprops addlaw _ _, facts) =
      -- Simplistic precondition check: Exists addprops (facts AND addlaw)
      -- This ignores the state-dependent parts for now.. todo?
      Exists addprops (Conj [facts, addlaw])


mddOf :: BelStruct -> Form -> MDD
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

mddOf bls@(BlS allprops lawmdd (ags, obdds)) (K i form) =
  let
    print_debug = False
    debugTrace msg val = if print_debug then trace msg val else val

    -- 1. Shift Law to Target (cp)
    law_cp = untag $ cpMdd allprops lawmdd

    -- 2. Shift Formula to Target (cp)
    form_node = mddOf bls form
    form_cp = untag $ cpMdd allprops form_node

    -- 3. Get Relation
    omega_i = restrict (agentPos (ags ! i)) True (untag obdds)

    -- 5. Implication Chain: Law(t) -> (Rel(s,t) -> Phi(t))
    imp_res = law_cp .->. (omega_i .->. form_cp)

    -- 6. Quantify over Target variables (cp)
    ps_target = map toOrdinal (cp allprops)
    forall_res = forallSet ps_target imp_res

    -- 7. Map Source variables (mv) back to Standard variables
    res = unmvMdd allprops (Tagged forall_res)

  in res
    -- debugTrace ("\n=== K Operator Debugging ===" ++
    --            "\nAgent: " ++ show i ++
    --            "\nFormula: " ++ show form ++
    --            "\nAll props: " ++ show allprops ++
    --            "\n\n--- 1. Law (cp) ---" ++
    --            "\nLaw (original): " ++ show_mdd lawmdd ++
    --            "\nLaw (shifted): " ++ show_mdd law_cp ++
    --            "\n\n--- 2. Formula (cp) ---" ++
    --            "\nFormula Node: " ++ show_mdd form_node ++
    --            "\nFormula (shifted): " ++ show_mdd form_cp ++
    --            "\n\n--- 3. Relation ---" ++
    --            "\nOmega_i: " ++ show_mdd omega_i ++
    --            "\n\n--- 5. Implication Chain ---" ++
    --            "\nImp Res: " ++ show_mdd imp_res ++
    --            "\n\n--- 6. Quantify Target ---" ++
    --            "\nTarget Props: " ++ show ps_target ++
    --            "\nForall Res: " ++ show_mdd forall_res ++
    --            "\n\n--- 7. Final Result ---" ++
    --            "\nFinal Result: " ++ show_mdd res ++ "\n")


mddOf bls (Kw i form) =
  let
      k_form = mddOf bls (K i form)
      k_neg_form = mddOf bls (K i (Neg form))
  in k_form .+. k_neg_form

mddOf bls@(BlS voc lawmdd (ags, obdds)) (Ck target_ags form) =
  let
    initial_guess = top
    ps_target = map toOrdinal (cp voc)

    agent_rels = map (\agent -> restrict (agentPos (ags ! agent)) True (untag obdds)) target_ags
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
        in if g == next then g else gfp op next

  in gfp lambda top

mddOf bls (Ckw ags form) =
    let ck_form = mddOf bls (Ck ags form)
        ck_neg_form = mddOf bls (Ck ags (Neg form))
    in ck_form .+. ck_neg_form

mddOf bls@(BlS props _ _) (Announce ags f g) =
  let
    domain = case props of
                (P (Ll d _):_) -> d
                [] -> standardDomain
    p_k = freshp props domain
    k_pos = toOrdinal p_k
    bls' = announce bls ags f
  in
    mddOf bls f .->. restrict k_pos True (mddOf bls' g)

mddOf bls@(BlS props _ _) (AnnounceW ags f g) =
  let
    domain = case props of
                (P (Ll d _):_) -> d
                [] -> standardDomain
    p_k = freshp props domain
    k_pos = toOrdinal p_k
  in
    ite (mddOf bls f)
        (restrict k_pos True (mddOf (announce bls ags f) g))
        (restrict k_pos True (mddOf (announce bls ags (Neg f)) g))

mddOf bls (PubAnnounce form1 form2) =
    mddOf bls form1 .->. mddOf (bls `update` form1) form2

mddOf bls (PubAnnounceW form1 form2) =
    ite (mddOf bls form1)
        (mddOf (bls `update` form1) form2)
        (mddOf (bls `update` Neg form1) form2)

mddOf _ (Dia _ _) = error "Dynamic operators not yet implemented for K_MDD"


validViaMdd :: BelStruct -> Form -> Bool
validViaMdd bls@(BlS _ lawmdd _) f =
    let f_node = mddOf bls f
    in (lawmdd .->. f_node) == top

evalViaMdd :: BelScene -> Form -> Bool
evalViaMdd (bls@(BlS _ lawmdd _), s) f =
    let (nl, node) = unMDD s
        traceMsg = "" -- "\n \n   evaluating state s : " ++ show_dd settings nl node ++ "\n   on formula : " ++ show f
    in
    trace traceMsg (let
        f_node = mddOf bls f
        check_node = s .->. f_node
    in
        check_node == top)

instance Semantics BelStruct where
  isTrue = validViaMdd

instance Semantics BelScene where
  isTrue = evalViaMdd


instance Update BelStruct Form where
  checks = []
  unsafeUpdate bls@(BlS props lawmdd obs) psi =
    let
        law_new = lawmdd .*. mddOf bls psi
    in
        BlS props law_new obs

instance Update BelScene Form where
  unsafeUpdate (kns,s) psi = (unsafeUpdate kns psi, s)

instance Update BelScene Event where
  unsafeUpdate (bls@(BlS props lawmdd (blsAgs, blsObs)), s) (trf, eventFacts) =
      let
          print_debug = False
          debugTrace msg val = if print_debug then trace msg val else val

          -- 1. Extract Transformer components (addprops are in eventFactsDomain (0,0), distinct from state vars (0,1))
          (Trf addprops addlaw changelaw (trfAgs, trfObs)) = trf

          -- 2. Handle Assignments (Copying Logic)
          -- Identify which propositions are changing
          changeprops = M.keys changelaw

          -- Generate Copy Props (to hold old values)
          domain = case props of
            (P (Ll d _):_) -> d
            [] -> standardDomain

          -- We need fresh props that are NOT in props
          genCopies [] _ acc = acc
          genCopies (p:ps) used acc =
               let newP = freshp used domain
               in genCopies ps (newP:used) ((p,newP):acc)

          copyRel = reverse $ genCopies changeprops props []
          copyChangeProps = map snd copyRel

          -- Mapping for MDD Relabeling (p -> p_copy)
          copyRelOrd = map (\(p,q) -> (toOrdinal p, toOrdinal q)) copyRel

          -- 3. Construct New Law
          -- (a) Shift Old Law: Relabel occurrences of changeprops to their copies
          -- So law(p) becomes law(p_copy).
          law_shifted =
            existSet (map toOrdinal eventFactsProps)
            (relabelWith copyRelOrd lawmdd)

          -- (b) Event Law
          law_event = boolMddOf addlaw

          -- (c) Assignment Laws: p <-> psi(p_copy)
          -- For each p in changelaw, p takes the value of psi.
          -- psi is evaluated in the old state, so we must relabel psi's vars to copies.
          assign_laws = map (\(p, psi) ->
              let
                  p_node = var' (getLevelL p)
                  psi_node = boolMddOf psi
                  psi_shifted = relabelWith copyRelOrd psi_node -- shift psi to use copies
              in
                  p_node .<->. psi_shifted
            ) (M.toList changelaw)

          newLawNode' = conSet (law_shifted : law_event : assign_laws)
          newLawNode = newLawNode'
              -- debugTrace ("\n=== STEP 1: Prepare Transformer ===" ++
                    --  "\nOriginal props: " ++ show props ++
                    --  "\nAddprops: " ++ show addprops ++
                    --  "\nAddlaw: " ++ show addlaw ++
                    --  "\nChangelaw: " ++ show changelaw ++
                    --  "\nEvent facts: " ++ show eventFacts ++
                    --  "\n\n=== STEP 2: Handle Assignments ===" ++
                    --  "\nChange props: " ++ show changeprops ++
                    --  "\nCopy relation: " ++ show copyRel ++
                    --  "\nCopy change props: " ++ show copyChangeProps ++
                    --  "\nCopy relabeling (ordinals): " ++ show copyRelOrd ++
                    --  "\n\n=== STEP 3a: Shift Old Law ===" ++
                    --  "\nOriginal law: " ++ show_mdd  lawmdd ++
                    --  "\nShifted law: " ++ show_mdd  law_shifted ++
                    --  "\n\n=== STEP 3b: Event Law ===" ++
                    --  "\nTemp vocabulary: " ++ show (props ++ addprops ++ copyChangeProps) ++
                    --  "\nEvent law formula: " ++ show addlaw ++
                    --  "\nEvent law MDD: " ++ show_mdd law_event ++
                    --  "\n\n=== STEP 3c: Assignment Laws ===" ++
                    --  "\nNumber of assignments: " ++ show (length assign_laws) ++
                    --  "\nAssignment laws MDDs:\n" ++
                    --  intercalate "\n" (map (\(i, al) -> "  Assignment " ++ show i ++ ": " ++
                    --    (show_mdd al))
                    --    (zip [1..] assign_laws)) ++
                    --  "\n\n=== STEP 3: Final New Law ===" ++
                    --  "\nNew law node: " ++ show_mdd newLawNode' ++ "\n")


          -- 4. Construct New Relations
          -- Agents distinguish 'addprops' via eventObs.
          -- Agents distinguish 'changeprops' (p) via their old relations on 'copyChangeProps' (p_copy).
          -- shift the old relations: mv(p) -> mv(p_copy), cp(p) -> cp(p_copy)

          copyRelMV = map (\(p,q) -> (toOrdinal (mvP p), toOrdinal (mvP q))) copyRel
          copyRelCP = map (\(p,q) -> (toOrdinal (cpP p), toOrdinal (cpP q))) copyRel
          fullCopyRelOrd = copyRelMV ++ copyRelCP

          updateRel agent =
              let
                  i = blsAgs ! agent

                  -- Old relation shifted
                  oldRel = restrict (agentPos i) True (untag blsObs)
                  relOldShifted = relabelWith fullCopyRelOrd oldRel
                  evRel = restrict (agentPos i) True (untag trfObs)

                  newRel = relOldShifted .*. evRel

                  aVar = agentVar i

              in aVar .->. newRel
                -- debugTrace ("\n--- updateRel for Agent: " ++ show agent ++
                --                  " (index: " ++ show i ++ ") ---" ++
                --                  "\nAgent position: " ++ show (agentPos i) ++
                --                  "\n\nOld relation (before shifting): " ++ show_mdd oldRel ++
                --                  "\nFull copy relabeling: " ++ show fullCopyRelOrd ++
                --                  "\nOld relation (after shifting): " ++ show_mdd relOldShifted ++
                --                  "\n\nEvent relation: " ++ show_mdd evRel ++
                --                  "\n\nCombined new relation (old .*. event): " ++ show_mdd newRel ++
                --                  "\nAgent variable: " ++ show_mdd aVar ++
                --                  "\nFinal result (aVar .->. newRel): " ++ show_mdd (aVar .->. newRel) ++ "\n")


          newRelMDD = conSet (map updateRel (M.keys blsAgs))
          newObs = (blsAgs, Tagged newRelMDD)
            -- debugTrace ("\n=== STEP 4: Construct New Relations ===" ++
            --          "\nCopy relabeling MV: " ++ show copyRelMV ++
            --          "\nCopy relabeling CP: " ++ show copyRelCP ++
            --          "\nFull copy relabeling: " ++ show fullCopyRelOrd ++
            --          "\nNew observations (combined): " ++
            --            (show_mdd newRelMDD))


          -- 5. Construct New State
          -- s is the old state (MDD).

          -- (a) Relabel s to copies: s(p) -> s(p_copy)
          -- Quantify out the originals (the new state can be either true or neg evaluations in this step)
          r = relabelWith copyRelOrd s
          eventFactsProps = propsInForm eventFacts
          propsToQuantify = changeprops ++ eventFactsProps
          r' = existSet (map toOrdinal propsToQuantify) r
          s_copy = r'
            -- debugTrace ("\n=== STEP 5: Construct New State ===" ++
            -- "\nOriginal state s: " ++ show_mdd s ++
            -- "\n\n=== STEP 5a: Relabel State to Copies ===" ++
            -- "\nRelabeling with: " ++ show copyRelOrd ++
            -- "\nBefore quantification (r): " ++ show_mdd r ++
            -- "\nQuantifying out: " ++ show (map toOrdinal propsToQuantify) ++
            -- "\nAfter quantification (r'): " ++ show_mdd r' ++ "\n")


          -- (b) Intersect with assignments and event facts
          -- This effectively calculates the new values of p based on psi(p_copy) and s(p_copy)
          -- and sets addprops based on eventFacts.
          factsNode = boolMddOf eventFacts

          assign_laws_conj = conSet assign_laws

          newStateNode = (conSet [s_copy, factsNode, assign_laws_conj])
            -- debugTrace ("\n=== STEP 5b: Event Facts Node ===" ++
            --          "\nEvent facts formula: " ++ show eventFacts ++
            --          "\nFacts node: " ++ show_mdd factsNode ++
            --          "\n\nAssignment laws conjunction: " ++
            --          show_mdd assign_laws_conj ++
            --          "\n\n=== STEP 5: Final New State ===" ++
            --          "\nComponents:\n  s_copy: " ++ show_mdd s_copy ++
            --          "\n  factsNode: " ++ show_mdd factsNode ++
            --          "\n  assign_laws_conj: " ++ show_mdd assign_laws_conj ++
            --          "\nFinal new state: " ++ show_mdd (conSet [s_copy, factsNode, assign_laws_conj]) ++ "\n")


          -- 6. Final Vocabulary
          newProps = (props ++ addprops ++ copyChangeProps)
            -- debugTrace ("\n=== STEP 6: Final Vocabulary ===" ++
            --          "\nOriginal props: " ++ show props ++
            --          "\nAdded props: " ++ show addprops ++
            --          "\nCopy change props: " ++ show copyChangeProps ++
            --          "\nFinal new props: " ++ show (props ++ addprops ++ copyChangeProps) ++ "\n")


      in (BlS newProps newLawNode newObs, newStateNode)


getLevelL :: Prp -> LevelL
getLevelL (P l) = l

agentPos :: Int -> Position
agentPos i = toOrdinal (intToPrp agentDomain i)

agentVar :: Int -> MDD
agentVar i = var' (Ll agentDomain i)

joinRelations :: [(Agent, Int, RelMDD)] -> (M.Map Agent Int, RelMDD)
joinRelations rels =
  let
    agentMap = M.fromList (map (\(agent, i, _) -> (agent, i)) rels)

    -- Combine relations: (AgentVar_i -> R_i)
    combine (agent, i, rel) =
        let aVar = agentVar i
            r = untag rel
        in aVar .->. r

    combinedRel = conSet (map combine rels)
  in (agentMap, Tagged combinedRel)

mvP, cpP :: Prp -> Prp
mvP (P (Ll ((_, inf):xs) i)) =
    let (mvDomainNum, _) = head mvDomain
    in P (Ll ((mvDomainNum, inf):xs) i)
mvP p = error $ "mvP failed: Unexpected Prp structure: " ++ show p

cpP (P (Ll ((_, inf):xs) i)) =
    let (cpDomainNum, _) = head cpDomain
    in P (Ll ((cpDomainNum, inf):xs) i)
cpP p = error $ "cpP failed: Unexpected Prp structure: " ++ show p

unmvcpP :: Prp -> Prp
unmvcpP (P (Ll ((_, inf):xs) i)) =
    let (standardDomainNum, _) = head standardDomain
    in P (Ll ((standardDomainNum, inf):xs) i)
unmvcpP p = error $ "unmvcpP failed: Unexpected Prp structure: " ++ show p

mv, cp :: [Prp] -> [Prp]
mv = map mvP
cp = map cpP

-- | Shifts a standard MDD (domain 0) to the Copy/Target domain (domain 2)
cpMdd :: [Prp] -> MDD -> RelMDD
cpMdd vocab mdd =
    let relabeling = map (\p -> (toOrdinal p, toOrdinal (cpP p))) vocab
    in Tagged $ relabelWith relabeling mdd

-- | Shifts a standard MDD (domain 0) to the Model/Source domain (domain 1)
mvMdd :: [Prp] -> MDD -> RelMDD
mvMdd vocab mdd =
    let relabeling = map (\p -> (toOrdinal p, toOrdinal (mvP p))) vocab
    in Tagged $ relabelWith relabeling mdd

-- | Shifts a Relational MDD (domains 1) back to standard domain (0)
unmvMdd :: [Prp] -> RelMDD -> MDD
unmvMdd vocab tagged_node =
    let mdd = untag tagged_node
        relabelingMv = map (\p -> (toOrdinal (mvP p), toOrdinal p)) vocab
    in relabelWith relabelingMv mdd

-- | Shifts a Relational MDD (domains 2) back to standard domain (0)
uncpMdd :: [Prp] -> RelMDD -> MDD
uncpMdd vocab tagged_node =
    let mdd = untag tagged_node
        relabelingCp = map (\p -> (toOrdinal (cpP p), toOrdinal p)) vocab
    in relabelWith relabelingCp mdd

totalRelMdd :: RelMDD
totalRelMdd = Tagged top

-- Helper for Identity Relation (Distinguishes p)
-- Relation: mv(p) <-> cp(p)
allsameMdd :: [Prp] -> RelMDD
allsameMdd ps =
    let
        mddList = map (\p ->
            let
                mv_node = boolMddOf (PrpF $ mvP p)
                cp_node = boolMddOf (PrpF $ cpP p)
            in mv_node .<->. cp_node
            ) ps
    in Tagged (conSet mddList)

-- Helper for Copy Relation (Copies p's value)
cpRelMdd :: [Prp] -> Form -> RelMDD
cpRelMdd vocab f =
    let
        node = boolMddOf f
        rel = untag $ cpMdd vocab node
    in Tagged rel

announce :: BelStruct -> [Agent] -> Form -> BelStruct
announce bls@(BlS props lawmdd (ags, obdds)) target_ags psi =
  let
    domain = case props of
                (P (Ll d _):_) -> d
                [] -> standardDomain
    p_k = freshp props domain
    k_level = getLevelL p_k
    k_mdd = var' k_level

    newprops = (p_k : props)
    psi_mdd = mddOf bls psi
    newlaw = lawmdd .*. (k_mdd .->. psi_mdd)

    mv_k = var' (getLevelL $ mvP p_k)
    cp_k = var' (getLevelL $ cpP p_k)

    updateRel i =
        let
            oldRel = restrict (agentPos (ags ! i)) True (untag obdds)
            newRel = if i `elem` target_ags
                     then oldRel .*. (mv_k .<->. cp_k)
                     else oldRel .*. ((-.) cp_k)
            aVar = agentVar (ags ! i)
        in aVar .->. newRel

    newRelMdd = conSet (map updateRel (M.keys ags))

  in BlS newprops newlaw (ags, Tagged newRelMdd)
