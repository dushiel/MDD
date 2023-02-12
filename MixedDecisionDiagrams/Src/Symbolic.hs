module MixedDecisionDiagrams.Src.Symbolic where

{-# LANGUAGE ViewPatterns #-}

import MixedDecisionDiagrams.Src.MDDi
import MixedDecisionDiagrams.Src.DrawMDD
import MixedDecisionDiagrams.Src.MDD
import MixedDecisionDiagrams.Src.Internal.Language
import Data.Maybe (fromMaybe)
import Data.List

defaultT :: a -> Maybe a -> a
defaultT = fromMaybe

-- for much faster path building, especially for ZDDs
-- seperate per kind, per class, the base propositions in current Form level
extractPropPerClassSublists :: [Form] -> ([(Ordinal, [Int])], [Form])
extractPropPerClassSublists = undefined

applSet :: (Dd Ordinal -> Dd Ordinal -> Dd Ordinal) -> [Dd Ordinal] -> Dd Ordinal
applSet f [] = top
applSet f (n:ns) = foldl' f n ns


exists n z = (.+.) (r0 z n) (r1 z n)
forAll n z = (.*.) (r0 z n) (r1 z n)

existsSet [] z = z
existsSet [n] z = exists n z
existsSet (n:ns) z = (.*.) (r0 (existsSet ns z) n) (r1 (existsSet ns z) n)
forAllSet [] z = z
forAllSet [n] z = forAll n z
forAllSet (n:ns) z = (.+.) (r0 (forAllSet ns z) n) (r1 (forAllSet ns z) n)




-- MDD Construction from Logic formulas
ddOf :: Inf -> Form -> Dd Ordinal
ddOf c Top           = top
ddOf c Bot           = bot
ddOf c (PrpF (P n))  = makeNode n c
ddOf c (Neg form)    = (-.) $ ddOf c form

-- pattern match on atleast more than 1 component
ddOf c (Conj form@(n:ns))  = let (r, s) = extractPropPerClassSublists form in
     applSet (.*.) $ map (\x -> uncurry path x c) r ++ [ddOf c (Conj s)]
ddOf c (Disj form@(n:ns))  = let (r, s) = extractPropPerClassSublists form in
     applSet (.+.) $ map (\x -> uncurry path x c) r ++ [ddOf c (Conj s)]

-- otherwise:
ddOf c (Conj forms)  = applSet (.*.) $ map (ddOf c) forms
ddOf c (Disj forms)  = applSet (.+.) $ map (ddOf c) forms
-- ddOf c (Xor forms)   = xorSet $ map ddOf forms
ddOf c (Impl f g)    = (.->.) (ddOf c f) (ddOf c g)
ddOf c (Equi f g)    = (.<->.) (ddOf c f) (ddOf c g)

ddOf c (Forall ps f) = forAllSet (map toOrdinal ps) (ddOf c f)
ddOf c (Exists ps f) = existsSet (map toOrdinal ps) (ddOf c f)
ddOf _   f             = error $ "ddOf failed: Not a boolean formula:" ++ show f

{-}
ddOf c (K i form) =
  forallSet mgr otherps (imp mgr lawbdd (ddOf kns form)) where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i --what does this do?
ddOf c (Kw i form) =
  disSet mgr [ forallSet mgr otherps (imp mgr lawbdd (ddOf kns f)) | f <- [form, Neg form] ] where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i
ddOf c (Ck ags form) = gfp mgr lambda where
  lambda z = conSet mgr $ ddOf kns form : [ forallSet mgr (otherps i) (imp mgr lawbdd z) | i <- ags ]
  otherps i = map (\(P n) -> n) $ allprops \\ apply obs i
ddOf c (Ckw ags form) = dis mgr (ddOf kns (Ck ags form)) (ddOf kns (Ck ags (Neg form)))
ddOf c (Announce ags form1 form2) =
  imp mgr (ddOf kns form1) (restrict mgr bdd2 (k,True)) where
    bdd2  = ddOf (announce kns ags form1) form2
    (P k) = freshp props
ddOf c (AnnounceW ags form1 form2) =
  ifthenelse mgr (ddOf kns form1) bdd2a bdd2b where
    bdd2a = restrict mgr (ddOf (announce kns ags form1) form2) (k,True)
    bdd2b = restrict mgr (ddOf (announce kns ags form1) form2) (k,False)
    (P k) = freshp props
ddOf c (PubAnnounce form1 form2) = imp mgr (ddOf kns form1) newform2 where
    newform2 = ddOf (pubAnnounce kns form1) form2
ddOf c (PubAnnounceW form1 form2) =
  ifthenelse mgr (ddOf kns form1) newform2a newform2b where
    newform2a = ddOf (pubAnnounce kns form1) form2
    newform2b = ddOf (pubAnnounce kns (Neg form1)) form2-}
