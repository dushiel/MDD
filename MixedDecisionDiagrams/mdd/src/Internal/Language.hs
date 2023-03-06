module Internal.Language where

import Data.List (nub,intercalate,(\\))
import MDD
-- import Test.QuickCheck

--newtype AgAgent = Ag Agent deriving (Eq,Ord,Show)
newtype Prp = P Ordinal deriving (Eq,Ord,Show)
type Agent = String
--newtype Group = Group [Agent] deriving (Eq,Ord,Show)

ite :: Form -> Form -> Form -> Form
ite f g h = Conj [f `Impl` g, Neg f `Impl` h]

toOrdinal :: Prp -> Ordinal
toOrdinal (P i) = i

data Form
  = Top                         -- ^ True Constant
  | Bot                         -- ^ False Constant
  | PrpF Prp                    -- ^ Atomic Proposition
  | B Form                      -- ^ Infinite paths context
  | O1I1 Form                   -- ^ Finite paths context
  | O1I0 Form                   -- ^ Finite paths context with complemented input
  | O0I1 Form                   -- ^ Finite paths context with complemented output
  | O0I0 Form                   -- ^ Finite paths context with complemented input and output
  | Neg Form                    -- ^ Negation
  | Conj [Form]                 -- ^ Conjunction
  | Disj [Form]                 -- ^ Disjunction
  | Xor [Form]                  -- ^ n-ary X-OR
  | Impl Form Form              -- ^ Implication
  | Equi Form Form              -- ^ Bi-Implication
  | Forall [Prp] Form           -- ^ Boolean Universal Quantification
  | Exists [Prp] Form           -- ^ Boolean Existential Quantification
  | K Agent Form                -- ^ Knowing that
  | Ck [Agent] Form             -- ^ Common knowing that
  | Kw Agent Form               -- ^ Knowing whether
  | Ckw [Agent] Form            -- ^ Common knowing whether
  -- | PubAnnounce Form Form       -- ^ Public announcement that
  -- | PubAnnounceW Form Form      -- ^ Public announcement whether
  -- | Announce [Agent] Form Form  -- ^ (Semi-)Private announcement that
  -- | AnnounceW [Agent] Form Form -- ^ (Semi-)Private announcement whether
  deriving (Eq,Ord,Show)

class Semantics a where
  isTrue :: a -> Form -> Bool

(|=) :: Semantics a => a -> Form -> Bool
(|=) = isTrue

showSet :: Show a => [a] -> String
showSet xs = intercalate "," (map show xs)

-- | Pretty print a formula, possibly with a translation for atoms:
ppForm :: Form -> String
ppForm = ppFormWith (\(P n) -> show n)

ppFormWith :: (Prp -> String)-> Form -> String
ppFormWith _     Top           = "T"
ppFormWith _     Bot           = "F"
ppFormWith trans (PrpF p)      = trans p
ppFormWith trans (B f)         = "(B :: " ++ ppFormWith trans f ++ " )"
ppFormWith trans (O1I1 f)      = "(O1I1 :: " ++ ppFormWith trans f ++ " )"
ppFormWith trans (O1I0 f)      = "(O1I1 :: " ++ ppFormWith trans f ++ " )"
ppFormWith trans (O0I1 f)      = "(O1I1 :: " ++ ppFormWith trans f ++ " )"
ppFormWith trans (O0I0 f)      = "(O1I1 :: " ++ ppFormWith trans f ++ " )"
ppFormWith trans (Neg f)       = "~" ++ ppFormWith trans f
ppFormWith trans (Conj fs)     = "(" ++ intercalate " & " (map (ppFormWith trans) fs) ++ ")"
ppFormWith trans (Disj fs)     = "(" ++ intercalate " | " (map (ppFormWith trans) fs) ++ ")"
ppFormWith trans (Xor fs)      = "XOR{" ++ showSet (map (ppFormWith trans) fs) ++ "}"
ppFormWith trans (Impl f g)    = "(" ++ ppFormWith trans f ++ "->" ++ ppFormWith trans g ++ ")"
ppFormWith trans (Equi f g)    = ppFormWith trans f ++ "=" ++ ppFormWith trans g
ppFormWith trans (Forall ps f) = "Forall {" ++ showSet ps ++ "}: " ++ ppFormWith trans f
ppFormWith trans (Exists ps f) = "Exists {" ++ showSet ps ++ "}: " ++ ppFormWith trans f
ppFormWith trans (K i f)       = "K " ++ i ++ " " ++ ppFormWith trans f
ppFormWith trans (Ck is f)     = "Ck " ++ showSet is ++ " " ++ ppFormWith trans f
ppFormWith trans (Kw i f)      = "Kw " ++ i ++ " " ++ ppFormWith trans f
ppFormWith trans (Ckw is f)    = "Ckw " ++ showSet is ++ " " ++ ppFormWith trans f
-- ppFormWith trans (PubAnnounce f g)  = "[! " ++ ppFormWith trans f ++ "] " ++ ppFormWith trans g
-- ppFormWith trans (PubAnnounceW f g) = "[?! " ++ ppFormWith trans f ++ "] " ++ ppFormWith trans g
-- ppFormWith trans (Announce is f g)  = "[" ++ intercalate ", " is ++ " ! " ++ ppFormWith trans f ++ "]" ++ ppFormWith trans g
-- ppFormWith trans (AnnounceW is f g) = "[" ++ intercalate ", " is ++ " ?! " ++ ppFormWith trans f ++ "]" ++ ppFormWith trans g
-- ppFormWith trans (Dia (Dyn s _) f)  = "<" ++ s ++ ">" ++ ppFormWith trans f

substit :: Prp -> Form -> Form -> Form
substit _ _   Top           = Top
substit _ _   Bot           = Bot
substit q psi (PrpF p)      = if p==q then psi else PrpF p
substit q psi (Neg form)    = Neg (substit q psi form)
substit q psi (Conj forms)  = Conj (map (substit q psi) forms)
substit q psi (Disj forms)  = Disj (map (substit q psi) forms)
substit q psi (Xor  forms)  = Xor  (map (substit q psi) forms)
substit q psi (Impl f g)    = Impl (substit q psi f) (substit q psi g)
substit q psi (Equi f g)    = Equi (substit q psi f) (substit q psi g)
substit q psi (Forall ps f) = if q `elem` ps
  then error ("substit failed: Substituens "++ show q ++ " in 'Forall " ++ show ps ++ " " ++ show f)
  else Forall ps (substit q psi f)
substit q psi (Exists ps f) = if q `elem` ps
  then error ("substit failed: Substituens " ++ show q ++ " in 'Exists " ++ show ps ++ " " ++ show f)
  else Exists ps (substit q psi f)
substit q psi (K  i f)     = K  i (substit q psi f)
substit q psi (Kw i f)     = Kw i (substit q psi f)
substit q psi (Ck ags f)   = Ck ags (substit q psi f)
substit q psi (Ckw ags f)  = Ckw ags (substit q psi f)
-- substit q psi (PubAnnounce f g)   = PubAnnounce (substit q psi f) (substit q psi g)
-- substit q psi (PubAnnounceW f g)  = PubAnnounceW (substit q psi f) (substit q psi g)
-- substit q psi (Announce ags f g)  = Announce ags (substit q psi f) (substit q psi g)
-- substit q psi (AnnounceW ags f g) = AnnounceW ags (substit q psi f) (substit q psi g)
-- substit _ _   (Dia _ _)           = undefined -- TODO needs substit in dynop! Dia dynop (substit q psi f)

substitSet :: [(Prp,Form)] -> Form -> Form
substitSet []             f = f
substitSet ((q,psi):rest) f = substitSet rest (substit q psi f)

substitOutOf :: [Prp] -> [Prp] -> Form -> Form
substitOutOf truths allps = substitSet [(p, if p `elem` truths then Top else Bot) | p <- allps]


booloutofForm :: [Prp] -> [Prp] -> Form
booloutofForm ps qs = Conj $ [ PrpF p | p <- ps ] ++ [ Neg $ PrpF r | r <- qs \\ ps ]



defaultVocabulary :: [Prp]
defaultVocabulary = map (P . Order . \x -> [x]) [0..4]

-- instance Arbitrary Prp where
--   arbitrary = elements defaultVocabulary
