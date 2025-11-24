{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables, TupleSections #-}

module SMCDEL.Symbolic.S5_MDD where

import Data.List ((\\), intercalate, nub)
import Data.Map (Map)
import qualified Data.Map as Map

import SMCDEL.Internal.Help (apply, powerset)
import Internal.Language hiding (ite)
import SMCDEL.Internal.TexDisplay

-- Assuming Path constructor is P'' to avoid conflicts as per user note.
import MDD hiding (Neg)
import MDDi hiding (Form, Impl, PrpF, Bot, Top)
import SupportMDD (allVars)
import Bool_MDD (ddOf')
import DotDD (generateGraphImage, createDotGraph) -- For Tex rendering
import System.IO.Unsafe (unsafePerformIO)
import Control.Monad (when)


-- | Knowledge structures using a Mixed Decision Diagram.
data KnowStruct =
  KnS [Prp] MDD [(Agent,[Prp])]
  deriving (Show)

type KnState = [Prp]
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
-- Corrected to use P'' for path construction
mddOf kns (PrpF (P n))  = var' n
mddOf kns (Neg form)    = (-.) $ mddOf kns form
mddOf kns (Conj forms)  = conSet $ map (mddOf kns) forms
mddOf kns (Disj forms)  = disSet $ map (mddOf kns) forms
mddOf kns (Xor  forms)  = xorSet $ map (mddOf kns) forms
mddOf kns (Impl f g)    = mddOf kns f .->. mddOf kns g
mddOf kns (Equi f g)    = mddOf kns f .<->. mddOf kns g
-- Corrected lambda to use the Prp constructor 'P'
mddOf kns (Forall ps f) = forallSet (map toOrdinal ps) (mddOf kns f)
mddOf kns (Exists ps f) = existSet (map toOrdinal ps) (mddOf kns f)
mddOf kns@(KnS allprops lawmdd obs) (K i form) =
  forallSet (map toOrdinal otherps) (lawmdd .->. mddOf kns form)
  where
    otherps = allprops \\ apply obs i
mddOf kns@(KnS allprops lawmdd obs) (Kw i form) =
  disSet [ forallSet (map toOrdinal otherps) (lawmdd .->. mddOf kns f) | f <- [form, Neg form] ]
  where
    otherps = allprops \\ apply obs i
mddOf kns@(KnS allprops lawmdd obs) (Ck ags form) =
  let
    initial_guess = top
    operator z = conSet (mddOf kns form : [ forallSet (map toOrdinal (otherps i)) (lawmdd .->. z) | i <- ags ])
    otherps i = allprops \\ apply obs i
    gfp op g = if snd g == snd (op g) then g else gfp op (op g)
  in gfp operator initial_guess
-- Corrected to use the .+. operator for proper context handling
mddOf kns (Ckw ags form) = mddOf kns (Ck ags form) .+. mddOf kns (Ck ags (Neg form))
mddOf kns@(KnS props _ _) (Announce ags form1 form2) =
  let
      form1_mdd = mddOf kns form1
      kns' = announce kns ags form1
      form2_mdd = mddOf kns' form2
      p = toOrdinal $ freshp props
  in form1_mdd .->. restrict p True form2_mdd
mddOf kns@(KnS props _ _) (AnnounceW ags form1 form2) =
  let
      form1_mdd = mddOf kns form1
      form2a_mdd = mddOf (announce kns ags form1) form2
      form2b_mdd = mddOf (announce kns ags (Neg form1)) form2
      p = toOrdinal $ freshp props
  in ite form1_mdd (restrict p True form2a_mdd) (restrict p False form2b_mdd)
mddOf kns (PubAnnounce form1 form2) =
    mddOf kns form1 .->. mddOf (pubAnnounce kns form1) form2
mddOf kns (PubAnnounceW form1 form2) =
    ite (mddOf kns form1) (mddOf (pubAnnounce kns form1) form2) (mddOf (pubAnnounce kns (Neg form1)) form2)
mddOf _ (Dia _ _) = error "Dynamic operators are not implemented in S5_MDD."


-- | Publicly announces a formula, updating the knowledge structure.
pubAnnounce :: KnowStruct -> Form -> KnowStruct
pubAnnounce kns@(KnS props lawmdd obs) psi = KnS props (lawmdd .*. mddOf kns psi) obs

-- | Announces a formula to a group of agents.
-- Corrected to handle contexts properly throughout the function.
announce :: KnowStruct -> [Agent] -> Form -> KnowStruct
announce kns@(KnS props lawmdd obs) ags psi =
  let
    proppsi@(P k) = freshp props
    newprops = proppsi:props
    psi_mdd = mddOf kns psi
    k_mdd = var' k
    equiv_mdd = k_mdd .<->. psi_mdd
    law_new = lawmdd .*. equiv_mdd
    newobs = [(i, apply obs i ++ [proppsi | i `elem` ags]) | i <- map fst obs]
  in KnS newprops law_new newobs

-- | Evaluates an MDD against a variable assignment.
mddEval :: MDD -> (Position -> Bool) -> Bool
mddEval n f =
    let vars = allVars n
        assignment = map (\v -> (v, f v)) vars
        result_node = foldl (\node (var, val) -> restrict var val node) n assignment
    in case snd $ snd result_node of
        Leaf True -> True
        _ -> False

-- -- | Returns all satisfying assignments for a given MDD.
-- -- todo! work with Level
-- statesOf :: KnowStruct -> [KnState]
-- statesOf (KnS allprops lawmdd _) =
--     map (map P . map fst . filter snd) (findModels [] lawmdd)
--   where
--     findModels :: Context -> [(Level, Bool)] -> Node -> [[(Level, Bool)]]
--     findModels path (ctx, (nodeId, dd)) = case dd of
--         Leaf True ->
--             let
--                 allPropInts = map fromEnum allprops
--                 assigned = map fst path
--                 unassigned = allPropInts \\ assigned
--             in map (\subset -> path ++ subset) (powerset (map (,True) unassigned))
--         Leaf False -> []
--         Unknown -> []
--         Node var posId negId ->
--             findModels ctx ((var, True):path) (getNode ctx posId) ++
--             findModels ctx ((var, False):path) (getNode ctx negId)
--         InfNodes {} -> error "InfNodes not supported in statesOf for S5 models"
--         EndInfNode childId -> findModels ctx path (getNode ctx childId)


-- | Evaluate a formula in a given state (scene).
evalViaMdd :: KnowScene -> Form -> Bool
evalViaMdd (kns@(KnS allprops _ _), s) f =
    let result_mdd = mddOf kns f
        assignments = [(fromEnum p, p `elem` s) | p <- allprops]
        final_node = foldl (\(ctx, node) (var, val) -> restrict [var] val (ctx, node)) result_mdd assignments
    in case snd final_node of
        top'  -> True
        _     -> False

-- | Check if a formula is valid in a knowledge structure.
validViaMdd :: KnowStruct -> Form -> Bool
validViaMdd kns@(KnS _ lawmdd _) f = (snd $ lawmdd .->. (mddOf kns f)) == top'

-- -- | Find all states where a formula is true.
-- whereViaMdd :: KnowStruct -> Form -> [KnState]
-- whereViaMdd kns f = statesOf (kns `update` f)


instance Semantics KnowScene where
  isTrue = evalViaMdd

instance Semantics KnowStruct where
  isTrue = validViaMdd

instance Update KnowStruct Form where
  checks = [ ] -- unpointed structures can be updated with anything
  unsafeUpdate kns@(KnS props lawmdd obs) psi = KnS props (lawmdd .*. mddOf kns psi) obs


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