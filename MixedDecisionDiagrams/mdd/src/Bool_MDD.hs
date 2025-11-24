
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Move brackets to avoid $" #-}
{-# HLINT ignore "Eta reduce" #-}
module Bool_MDD where

import MDDi ( top, bot, neg, con, dis, var, var', MDD )
import MDD ( Context, LevelL, makeNode, unionContext )

data Form
    = Top
    | Bot
    | Negate Form
    | And Form Form
    | Or Form Form
    | PrpF LevelL
    | Var MDD
    | Impl Form Form
    | ImplR Form Form
    -- | F Form

ddOf :: Context -> Form -> MDD
ddOf _ Top = top
ddOf _ Bot = bot
-- ddOf c Unknown = (c, unk)
ddOf c (Negate a) =
                let
                    (c1, r1) = ddOf c a
                in neg c1 r1
ddOf c (And a b) =
                let
                    (c1, r1) = ddOf c a
                    (c2, r2) = ddOf c1 b
                in con c2 r1 r2
ddOf c (Or a b) =
                let
                    (c1, r1) = ddOf c a
                    (c2, r2) = ddOf c1 b
                in dis c2 r1 r2
ddOf c (Impl a b) = ddOf c $ Or (Negate a) b
ddOf c (ImplR a b) = ddOf c $ Or a (Negate b)
ddOf c (PrpF l) = makeNode c l
ddOf c (Var (_, d)) = (c, d)

ddOf' :: Form -> MDD
ddOf' Top = top
ddOf' Bot = bot
ddOf' (Negate a) =
                let
                    (c1, r1) = ddOf' a
                in neg c1 r1
ddOf' (And a b) =
                let
                    (c1, r1) = ddOf' a
                    (c2, r2) = ddOf' b
                in con (unionContext c1 c2) r1 r2
ddOf' (Or a b) =
                let
                    (c1, r1) = ddOf' a
                    (c2, r2) = ddOf' b
                in dis (unionContext c1 c2) r1 r2
ddOf' (Impl a b) = ddOf' $ Or (Negate a) b
ddOf' (ImplR a b) = ddOf' $ Or a (Negate b)
ddOf' (PrpF l) = var' l
ddOf' (Var (c, d)) = (c, d)