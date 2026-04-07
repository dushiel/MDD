{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Move brackets to avoid $" #-}
{-# HLINT ignore "Eta reduce" #-}
module SMCDEL.Symbolic.Bool where

import MDD.Extra.Interface ( top, bot, (-.), (.*.), (.+.), var, var', top_n, bot_n, unk_n )
import MDD.Types ( NodeLookup, LevelL, Node, MDD(..) )
import MDD.NodeLookup ( unionNodeLookup )
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

-- | ddOf for (NodeLookup, Node) chaining
ddOf :: NodeLookup -> Form -> MDD
ddOf nl Top = MDD (nl, top_n)
ddOf nl Bot = MDD (nl, bot_n)
-- ddOf nl Unknown = (nl, unk)
ddOf nl (Negate a) = (-.) (ddOf nl a)
ddOf nl (And a b) = (ddOf nl a) .*. (ddOf nl b)
ddOf nl (Or a b) = (ddOf nl a) .+. (ddOf nl b)
ddOf nl (Impl a b) = ddOf nl $ Or (Negate a) b
ddOf nl (ImplR a b) = ddOf nl $ Or a (Negate b)
ddOf nl (PrpF l) = makeNode nl l
ddOf nl (Var (MDD (nl_v, d_v))) = MDD (unionNodeLookup nl nl_v, d_v)

-- | ddOf where a nodelookup still needs to be initialised
ddOf' :: Form -> MDD
ddOf' Top = top
ddOf' Bot = bot
ddOf' (Negate a) = (-.) (ddOf' a)
ddOf' (And a b) = (ddOf' a) .*. (ddOf' b)
ddOf' (Or a b) = (ddOf' a) .+. (ddOf' b)
ddOf' (Impl a b) = ddOf' $ Or (Negate a) b
ddOf' (ImplR a b) = ddOf' $ Or a (Negate b)
ddOf' (PrpF l) = var' l
ddOf' (Var m) = m