{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Move brackets to avoid $" #-}
{-# HLINT ignore "Eta reduce" #-}
module MDD.Bool where

import MDD.Interface ( top, bot, (-.), (.*.), (.+.), var, var', top_n, bot_n, unk_n )
import MDD.Types ( NodeLookup, LevelL, Node, MDD )
import MDD.Manager ( unionNodeLookup )
import MDD.Construction ( makeNode )

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

-- | Updated ddOf to work with the new (NodeLookup, Node) structure
ddOf :: NodeLookup -> Form -> MDD
ddOf nl Top = (nl, top_n)
ddOf nl Bot = (nl, bot_n)
-- ddOf c Unknown = (c, unk)
ddOf nl (Negate a) =
                let
                    (nl1, r1) = ddOf nl a
                in (-.) (nl1, r1)
ddOf nl (And a b) =
                let
                    (nl1, r1) = ddOf nl a
                    (nl2, r2) = ddOf nl1 b
                in (nl1, r1) .*. (nl2, r2)
ddOf nl (Or a b) =
                let
                    (nl1, r1) = ddOf nl a
                    (nl2, r2) = ddOf nl1 b
                in (nl1, r1) .+. (nl2, r2)
ddOf nl (Impl a b) = ddOf nl $ Or (Negate a) b
ddOf nl (ImplR a b) = ddOf nl $ Or a (Negate b)
ddOf nl (PrpF l) = makeNode nl l
ddOf nl (Var (nl_v, d_v)) = (unionNodeLookup nl nl_v, d_v)

-- | Updated ddOf' for self-contained form conversion
ddOf' :: Form -> MDD
ddOf' Top = top
ddOf' Bot = bot
ddOf' (Negate a) =
                let
                    (nl1, r1) = ddOf' a
                in (-.) (nl1, r1)
ddOf' (And a b) =
                let
                    (nl1, r1) = ddOf' a
                    (nl2, r2) = ddOf' b
                in (nl1, r1) .*. (nl2, r2)
ddOf' (Or a b) =
                let
                    (nl1, r1) = ddOf' a
                    (nl2, r2) = ddOf' b
                in (nl1, r1) .+. (nl2, r2)
ddOf' (Impl a b) = ddOf' $ Or (Negate a) b
ddOf' (ImplR a b) = ddOf' $ Or a (Negate b)
ddOf' (PrpF l) = var' l
ddOf' (Var (nl, d)) = (nl, d)