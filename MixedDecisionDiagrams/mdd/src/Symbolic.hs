module Symbolic where

{-# LANGUAGE ViewPatterns #-}

import MDDi
import DrawMDD
import MDD
import Internal.Language
import Data.Maybe (fromMaybe)
import Data.List
import qualified Data.Map.Strict as Map

defaultT :: a -> Maybe a -> a
defaultT = fromMaybe

-- for much faster path building, especially for ZDDs
-- seperate per kind, per class / infinite subdomain, the base propositions in current Form level
extractPropPerClassSublists :: [Form] -> ([(Ordinal, [Int])], [Form])
extractPropPerClassSublists (PrpF (P n)) = undefined
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
boolDdOf :: Inf -> Form -> Dd Ordinal
boolDdOf c Top           = top
boolDdOf c Bot           = bot
boolDdOf c (PrpF (P n))  = makeNode n c
boolDdOf c (Neg form)    = (-.) $ boolDdOf c form

-- pattern match on atleast more than 1 component
boolDdOf c (Conj form@(n:ns))  = let (r, s) = extractPropPerClassSublists form in
     applSet (.*.) $ map (\x -> uncurry path x c) r ++ [boolDdOf c (Conj s)]
boolDdOf c (Disj form@(n:ns))  = let (r, s) = extractPropPerClassSublists form in
     applSet (.+.) $ map (\x -> uncurry path x c) r ++ [boolDdOf c (Conj s)]

-- otherwise:
boolDdOf c (Conj forms)  = applSet (.*.) $ map (boolDdOf c) forms
boolDdOf c (Disj forms)  = applSet (.+.) $ map (boolDdOf c) forms
-- ddOf c (Xor forms)   = xorSet $ map ddOf forms
boolDdOf c (Impl f g)    = (.->.) (boolDdOf c f) (boolDdOf c g)
boolDdOf c (Equi f g)    = (.<->.) (boolDdOf c f) (boolDdOf c g)

boolDdOf c (Forall ps f) = forAllSet (map toOrdinal ps) (boolDdOf c f)
boolDdOf c (Exists ps f) = existsSet (map toOrdinal ps) (boolDdOf c f)


-- MDD Construction from Logic formulas, a map from labels (e.g. agentlabels) to ordinal is included.
-- todo make this map to a typed ordinal instead, for using inference rules (other than Dc) on the class level.
ddOf :: Map.Map k a -> Inf -> Form -> Dd Ordinal
ddOf m c Top           = top
ddOf m c Bot           = bot
ddOf m c (PrpF (P n))  = makeNode n c
ddOf m c (Neg form)    = (-.) $ ddOf m c form

-- pattern match on atleast more than 1 component
ddOf m c (Conj form@(n:ns))  = let (r, s) = extractPropPerClassSublists form in
     applSet (.*.) $ map (\x -> uncurry path x c) r ++ [ddOf m c (Conj s)]
ddOf m c (Disj form@(n:ns))  = let (r, s) = extractPropPerClassSublists form in
     applSet (.+.) $ map (\x -> uncurry path x c) r ++ [ddOf m c (Conj s)]

-- otherwise:
ddOf m c (Conj forms)  = applSet (.*.) $ map (ddOf m c) forms
ddOf m c (Disj forms)  = applSet (.+.) $ map (ddOf m c) forms
-- ddOf c (Xor forms)   = xorSet $ map ddOf forms
ddOf m c (Impl f g)    = (.->.) (ddOf m c f) (ddOf m c g)
ddOf m c (Equi f g)    = (.<->.) (ddOf m c f) (ddOf m c g)

ddOf m c (Forall ps f) = forAllSet (map toOrdinal ps) (ddOf m c f)
ddOf m c (Exists ps f) = existsSet (map toOrdinal ps) (ddOf m c f)


ddOf m c (K i form) =
  forallSet otherps ((.->.) lawbdd (ddOf m c form)) where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i -- [a,..]

-- can we remove common know if we can use gfp?
-- ideally there should be no transitive relation
-- agent -> (CommonKnow ^ Observableprops) ->  (commonKnow ^ incommingObservables)

ddOf m@(map("ObservableProperties") map("CommonKnow") map("incommingObservables")) c (K i form) = unmvDd allprops result
  where
  result = forallSet ps' <$> ((.->.) <$> cpDd allprops lawdd <*> ((.->.) <$> omegai <*> cpDd allprops (ddOf bls form)))
  -- forall incomingObservables: comknow as incomming -> omegai -> (ddOf Form) as incomming
  lawdd = map("CommonKnow")
  ps'    = map fromEnum $ cp allprops -- map("incommingObservables")
  -- todo forall for an infinite domain: add (^) all consequences, by using restrictSet with ranges
  -- restrictGen is used for
  -- forallGen
  omegai = rSet $ map ! "Agents" -- restrict to (Neg1 : agent_i) -- requires restrict Law

ddOf m c (Kw i form) =
  disSet [ forallSet otherps ((.->.) lawbdd (ddOf m c f)) | f <- [form, Neg form] ] where
    otherps = map (\(P n) -> n) $ allprops \\ apply obs i

ddOf _ _  f             = error $ "ddOf failed: Not a boolean formula:" ++ show f

--ddOf c (Ck ags form) = gfp mgr lambda where
--  lambda z = conSet mgr $ ddOf kns form : [ forallSet mgr (otherps i) (imp mgr lawbdd z) | i <- ags ]
--  otherps i = map (\(P n) -> n) $ allprops \\ apply obs i
--ddOf c (Ckw ags form) = dis mgr (ddOf kns (Ck ags form)) (ddOf kns (Ck ags (Neg form)))
{-}
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
