{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables, TupleSections #-}

module SMCDEL.Symbolic.S5_MDD where

import Data.List ((\\), intercalate, nub)
import Data.Map (Map)
import qualified Data.Map as Map

import SMCDEL.Internal.Help (apply, powerset)
import Internal.Language hiding (ite)
import SMCDEL.Internal.TexDisplay

import MDD.Types hiding (Neg)
import MDD.Interface
import MDD.Draw (settings, show_dd)
import Debug.Trace (trace, traceShow)

-- | Knowledge structures using a Mixed Decision Diagram.
data KnowStruct =
  KnS [Prp] MDD [(Agent,[Prp])]
  deriving (Show)

-- | A state is represented in a single Neg1 or Pos1 MDD path
-- For now there is no specific type contrain for this
type KnState = MDD
type KnowScene = (KnowStruct, KnState)

instance HasAgents KnowStruct where
  agentsOf (KnS _ _ obs)= map fst obs

instance HasVocab KnowStruct where
  vocabOf (KnS props _ _) = props

instance Pointed KnowStruct KnState

-- | Create an MDD from a boolean formula.
boolMddOf :: Form -> MDD
boolMddOf Top           = top
boolMddOf Bot           = bot
boolMddOf (PrpF (P n))  = var' n
boolMddOf (Neg form)    = (-.) (boolMddOf form)
boolMddOf (Conj forms)  = conSet $ map boolMddOf forms
boolMddOf (Disj forms)  = disSet $ map boolMddOf forms
boolMddOf (Xor forms)   = xorSet $ map boolMddOf forms
boolMddOf (Impl f g)    = boolMddOf f .->. boolMddOf g
boolMddOf (Equi f g)    = boolMddOf f .<->. boolMddOf g
boolMddOf (Forall ps f) = forallSet (map toOrdinal ps) (boolMddOf f)
boolMddOf (Exists ps f) = existSet (map toOrdinal ps) (boolMddOf f)
boolMddOf  f            = error $ "boolMddOf failed: Not a boolean formula:" ++ show f

-- | Create an MDD from a general S5 formula.
mddOf :: KnowStruct -> Form -> MDD
mddOf kns Top           = top
mddOf kns Bot           = bot
mddOf kns (PrpF (P n))  = var' n
mddOf kns (Neg form)    = (-.) $ mddOf kns form
mddOf kns (Conj forms)  = conSet $ map (mddOf kns) forms
mddOf kns (Disj forms)  = disSet $ map (mddOf kns) forms
mddOf kns (Xor  forms)  = xorSet $ map (mddOf kns) forms
mddOf kns (Impl f g)    = mddOf kns f .->. mddOf kns g
mddOf kns (Equi f g)    = mddOf kns f .<->. mddOf kns g
mddOf kns (Forall ps f) = forallSet (map toOrdinal ps) (mddOf kns f)
mddOf kns (Exists ps f) = existSet (map toOrdinal ps) (mddOf kns f)

-- Knowledge Operator: Agent i knows phi if phi is true in all worlds considered possible by i.
-- In S5, this means phi must be true regardless of the values of variables i cannot observe.
-- Implemented as universal quantification over unobservable variables on (Law -> Phi).
mddOf kns@(KnS allprops lawmdd obs) (K i form) =
  forallSet (map toOrdinal otherps) (lawmdd .->. mddOf kns form)
  where
    otherps = allprops \\ apply obs i

-- Knowing Whether: K i phi or K i (not phi)
mddOf kns@(KnS allprops lawmdd obs) (Kw i form) =
  -- trace ("K" ++ show i ++ " cannot observe : " ++ show otherps ++
        -- "for restrict false \n" ++
        -- "\n " ++ show_dd settings c d ++
        -- "\n for restrict true " ++ show ( form) ++
        -- "\n " ++ show_dd settings c2 d2 ++
        -- "\n  of formula "  ++
        -- "\n " ++ show_dd settings c3 d3)
  disSet [ forallSet otherps (lawmdd .->. mddOf kns f) | f <- [form, Neg form] ]
  where
    otherps = map toOrdinal $ allprops \\ apply obs i
    -- (c, d) = (restrict (head otherps) False (lawmdd .->. mddOf kns form))
    -- (c2, d2) = (restrict (head otherps) True (lawmdd .->. mddOf kns form))
    -- (c3, d3) = lawmdd .->. mddOf kns ( form)

-- Common Knowledge: Greatest Fixed Point of Everyone Knows.
-- Z = Phi AND E_G Z
mddOf kns@(KnS allprops lawmdd obs) (Ck ags form) =
  let
    initial_guess = top
    -- E_G Z = AND_{i in ags} K_i Z
    -- K_i Z = forall unobs. (law -> Z)
    operator z = conSet (mddOf kns form : [ forallSet (map toOrdinal (otherps i)) (lawmdd .->. z) | i <- ags ])
    otherps i = allprops \\ apply obs i

    -- Fixed point iteration
    gfp op g =
        let next = op g
        in if g == next then g else gfp op next
  in gfp operator initial_guess

mddOf kns (Ckw ags form) = mddOf kns (Ck ags form) .+. mddOf kns (Ck ags (Neg form))

-- Announcement: Private announcement to group 'ags'
mddOf kns@(KnS props _ _) (Announce ags form1 form2) =
  let
      form1_mdd = mddOf kns form1
      kns' = announce kns ags form1
      form2_mdd = mddOf kns' form2
      -- Fix: Use a valid default domain for fresh proposition
      domain = case props of
                  (P (Ll d _):_) -> d
                  [] -> [(0, Dc1)]
      p = toOrdinal $ freshp props domain
  in form1_mdd .->. restrict p True form2_mdd

-- Announcement Whether
mddOf kns@(KnS props _ _) (AnnounceW ags form1 form2) =
  let
      form1_mdd = mddOf kns form1
      form2a_mdd = mddOf (announce kns ags form1) form2
      form2b_mdd = mddOf (announce kns ags (Neg form1)) form2
      -- Fix: Use a valid default domain for fresh proposition
      domain = case props of
                  (P (Ll d _):_) -> d
                  [] -> [(0, Dc1)]
      p = toOrdinal $ freshp props domain
  in ite form1_mdd (restrict p True form2a_mdd) (restrict p False form2b_mdd)

-- Public Announcement: [!phi] psi
-- psi is evaluated in the restricted model where phi is true.
mddOf kns (PubAnnounce form1 form2) = mddOf kns form1 .->. mddOf (pubAnnounce kns form1) form2

-- Public Announcement Whether
mddOf kns (PubAnnounceW form1 form2) = trace ("PubannounceW, form1: " ++ show form1 ++ " \n , form2: " ++ show form2) (
    ite (mddOf kns form1) (mddOf (pubAnnounce kns form1) form2) (mddOf (pubAnnounce kns (Neg form1)) form2))

mddOf _ (Dia _ _) = error "Dynamic operators are not implemented in S5_MDD."


-- | Publicly announces a formula, updating the knowledge structure.
-- The law is restricted by the announcement.
pubAnnounce :: KnowStruct -> Form -> KnowStruct
pubAnnounce kns@(KnS props lawmdd obs) psi = KnS props (lawmdd .*. mddOf kns psi) obs

-- | Announces a formula to a group of agents.
announce :: KnowStruct -> [Agent] -> Form -> KnowStruct
announce kns@(KnS props lawmdd obs) ags psi =
  let
    -- Fix: Use a valid default domain for fresh proposition
    domain = case props of
                (P (Ll d _):_) -> d
                [] -> [(0, Dc1)]
    proppsi@(P k) = freshp props domain
    newprops = proppsi:props
    psi_mdd = mddOf kns psi
    k_mdd = var' k
    equiv_mdd = k_mdd .<->. psi_mdd
    law_new = lawmdd .*. equiv_mdd
    newobs = [(i, apply obs i ++ [proppsi | i `elem` ags]) | i <- map fst obs]
  in KnS newprops law_new newobs

-- | Evaluate a formula in a given state (scene).
-- A formula is true in a pointed model (M, s) if the formula holds at s.
-- For MDD S5 knowstructs, this means that the Neg1 state 's' should imply the statelaw.
evalViaMdd :: KnowScene -> Form -> Bool
evalViaMdd (kns@(KnS allprops lawmdd _), s) f =
    let
      stateValid = (s .->. lawmdd) == top
      formValid = (s .->. mddOf kns f) == top
    in if not stateValid
       then error ("evalViaMdd: State " ++ show s ++ " is not consistent with the Law.")
       else formValid

-- | Check if a formula is valid in a knowledge structure.
-- Validity means: Law -> Form is a tautology (Top).
validViaMdd :: KnowStruct -> Form -> Bool
validViaMdd kns@(KnS _ lawmdd _) f = (lawmdd .->. (mddOf kns f)) == top

instance Semantics KnowScene where
  isTrue = evalViaMdd

instance Semantics KnowStruct where
  isTrue = validViaMdd

-- | Instance for updating unpointed structures (just restrictions/announcements)
instance Update KnowStruct Form where
  checks = [ ] -- unpointed structures can be updated with anything
  unsafeUpdate kns psi = (pubAnnounce kns psi)

-- | Instance for updating pointed scenes (KnS + State)
instance Update KnowScene Form where
  -- check if the update formula is true in the current state
  checks = [ preCheck ]
  -- update the structure, keep the state same
  unsafeUpdate (kns, s) psi = (unsafeUpdate kns psi, s)

-- * Visualisation functions

-- -- Assuming the existence of these functions from the prompt.
-- -- These are placeholders as we can't execute IO for file generation here.
-- texMdd :: (Context, Node) -> String
-- texMdd (c, n) = unsafePerformIO $ do
--     -- In a real scenario, this would generate a file and return the LaTeX string
--     -- For now, we return a placeholder.
--     -- (success, message, imageFilePath) <- generateGraphImage c n True True Map.empty
--     -- when success $ putStrLn $ "Image file: " ++ imageFilePath
--     -- return $ "\\includegraphics{" ++ imageFilePath ++ "}"
--     return $ "[Graphical Representation of MDD: " ++ show (fst n) ++ "]"

-- instance TexAble KnowStruct where
--   tex (KnS props lawbdd obs) = concat
--     [ " \\left( \n"
--     , tex props ++ ", "
--     , " \\begin{array}{l} \\scalebox{0.4}{"
--     , texMdd lawbdd
--     , "} \\end{array}\n "
--     , ", \\begin{array}{l}\n"
--     , intercalate " \\\\\n " (map (\(_,os) -> tex os) obs)
--     , "\\end{array}\n"
--     , " \\right)" ]

-- instance TexAble KnowScene where
--   tex (kns, state) = tex kns ++ " , " ++ tex state

-- giveMddTex :: (Context, Node) -> String
-- giveMddTex (c, n) = concat
--   [
--     " \\begin{array}{l} \\scalebox{0.4}{"
--     , texMdd (c, n)
--     , "} \\end{array}\n "]