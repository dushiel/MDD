{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module MDD.Test.Fixtures where

import MDD.Types
import MDD.Extra.Interface
import MDD.Construction (path, add_path)
import SMCDEL.Symbolic.Bool ()

-- Variable naming conventions:
--   dc, n, p        = Dc1, Neg1, Pos1 context (background = False)
--   dc', n', p'     = Dc0, Neg0, Pos0 context (background = True)
--   suffix number    = node position(s) within the class
--   underscore       = different class id (e.g. dc_2 = class 2, dc__2 = class 3)
--   doubled prefix   = nested domain (e.g. dcdc2 = Dc1 inside Dc1)

-- ============================================================
-- Single-level variables: class 1, Dc context
-- ============================================================

dc     = path                      (P' [(1, Dc1, P'' [0])])
dc'    = add_path dc               (P' [(1, Dc0, P'' [0])])
n      = add_path dc'              (P' [(1, Neg1, P'' [0])])
n'     = add_path n                (P' [(1, Neg0, P'' [0])])
p      = add_path n'               (P' [(1, Pos1, P'' [0])])
p'     = add_path p                (P' [(1, Pos0, P'' [0])])

dc1    = add_path p'               (P' [(1, Dc1, P'' [1])])
dc2    = add_path dc1              (P' [(1, Dc1, P'' [2])])
dc23   = add_path dc2              (P' [(1, Dc1, P'' [2, 3])])
dc'2   = add_path dc23             (P' [(1, Dc1, P'' [-2])])
dc3    = add_path dc'2             (P' [(1, Dc1, P'' [3])])
dc4    = add_path dc3              (P' [(1, Dc1, P'' [4])])

-- ============================================================
-- Single-level variables: classes 2 and 3, Dc context
-- ============================================================

dc_2   = add_path dc4              (P' [(2, Dc1, P'' [2])])
dc_3   = add_path dc_2             (P' [(2, Dc1, P'' [3])])
dc__2  = add_path dc_3             (P' [(3, Dc1, P'' [2])])

-- ============================================================
-- Single-level variables: Neg1 context
-- ============================================================

n2     = add_path dc__2            (P' [(1, Neg1, P'' [2])])
n3     = add_path n2               (P' [(1, Neg1, P'' [3])])
n23    = add_path n3               (P' [(1, Neg1, P'' [2,3])])
n_2    = add_path n23              (P' [(2, Neg1, P'' [2])])
n__2   = add_path n_2              (P' [(3, Neg1, P'' [2])])
n__3   = add_path n__2             (P' [(3, Neg1, P'' [3])])

-- ============================================================
-- Single-level variables: Neg0 context
-- ============================================================

n'2    = add_path n__3             (P' [(1, Neg0, P'' [2])])
n'3    = add_path n'2              (P' [(1, Neg0, P'' [3])])
n'23   = add_path n'3              (P' [(1, Neg0, P'' [2,3])])
n'_2   = add_path n'23             (P' [(2, Neg0, P'' [2])])
n'_3   = add_path n'_2             (P' [(2, Neg0, P'' [3])])
n'__2  = add_path n'_3             (P' [(3, Neg0, P'' [2])])
n'__3  = add_path n'__2            (P' [(3, Neg0, P'' [3])])

-- ============================================================
-- Single-level variables: Pos1 context
-- ============================================================

p2     = add_path n'__3            (P' [(1, Pos1, P'' [-2])])
p3     = add_path p2               (P' [(1, Pos1, P'' [-3])])
p23    = add_path p3               (P' [(1, Pos1, P'' [-2,-3])])
p_2    = add_path p23              (P' [(2, Pos1, P'' [-2])])
p__2   = add_path p_2              (P' [(3, Pos1, P'' [-2])])

-- ============================================================
-- Single-level variables: Pos0 context
-- ============================================================

p'2    = add_path p__2             (P' [(1, Pos0, P'' [-2])])
p'3    = add_path p'2              (P' [(1, Pos0, P'' [-3])])
p'_2   = add_path p'3              (P' [(2, Pos0, P'' [-2])])
p'__2  = add_path p'_2             (P' [(3, Pos0, P'' [-2])])

-- ============================================================
-- Nested domains: Dc inside Dc
-- ============================================================

dcdc2  = add_path p'__2            (P' [(1, Dc1, P' [(1, Dc1, P'' [2])])])
dcdc3  = add_path dcdc2            (P' [(1, Dc1, P' [(1, Dc1, P'' [3])])])
dcdc'2 = add_path dcdc3            (P' [(1, Dc1, P' [(1, Dc1, P'' [-2])])])
dcdc'3 = add_path dcdc'2           (P' [(1, Dc1, P' [(1, Dc1, P'' [-3])])])

-- ============================================================
-- Nested domains: Pos inside Pos
-- ============================================================

pp2    = add_path dcdc'3           (P' [(1, Pos1, P' [(1, Pos1, P'' [-2])])])
pp3    = add_path pp2              (P' [(1, Pos1, P' [(1, Pos1, P'' [-3])])])
pp'2   = add_path pp3              (P' [(1, Pos1, P' [(1, Pos0, P'' [-2])])])
pp'3   = add_path pp'2             (P' [(1, Pos1, P' [(1, Pos0, P'' [-3])])])

-- ============================================================
-- Nested domains: Neg inside Neg
-- ============================================================

nn2    = add_path pp'3             (P' [(1, Neg1, P' [(1, Neg1, P'' [2])])])
nn3    = add_path nn2              (P' [(1, Neg1, P' [(1, Neg1, P'' [3])])])
nn'2   = add_path nn3              (P' [(1, Neg1, P' [(1, Neg0, P'' [2])])])
nn'3   = add_path nn'2             (P' [(1, Neg1, P' [(1, Neg0, P'' [3])])])

-- ============================================================
-- Mixed nested domains: different inference types at each level
-- ============================================================

dcn1   = add_path nn'3             (P' [(1, Dc1, P' [(1, Neg1, P'' [1])])])
dcn'1  = add_path dcn1             (P' [(1, Dc1, P' [(1, Neg0, P'' [1])])])
dcn23  = add_path dcn'1            (P' [(1, Dc1, P' [(1, Neg1, P'' [2,3])])])
dcn'23 = add_path dcn23            (P' [(1, Dc1, P' [(1, Neg0, P'' [2,3])])])

dcp1   = add_path dcn'23           (P' [(1, Dc1, P' [(1, Pos1, P'' [-1])])])
dcp'1  = add_path dcp1             (P' [(1, Dc1, P' [(1, Pos0, P'' [-1])])])
dcp23  = add_path dcp'1            (P' [(1, Dc1, P' [(1, Pos1, P'' [-2,-3])])])

nn1    = add_path dcp23            (P' [(1, Neg1, P' [(1, Neg1, P'' [1])])])
n_n1   = add_path nn1              (P' [(1, Neg1, P' [(2, Neg1, P'' [1])])])
n_n2   = add_path n_n1             (P' [(1, Neg1, P' [(2, Neg1, P'' [2])])])
n'n'1  = add_path n_n2             (P' [(1, Neg0, P' [(1, Neg0, P'' [1])])])
n'n1   = add_path n'n'1            (P' [(1, Neg0, P' [(1, Neg1, P'' [1])])])
n'n2   = add_path n'n1             (P' [(1, Neg0, P' [(1, Neg1, P'' [2])])])
n'_n1  = add_path n'n2             (P' [(1, Neg0, P' [(2, Neg1, P'' [1])])])
n'_n2  = add_path n'_n1            (P' [(1, Neg0, P' [(2, Neg1, P'' [2])])])
nn'1   = add_path n'_n2            (P' [(1, Neg1, P' [(1, Neg0, P'' [1])])])
nn     = add_path nn'1             (P' [(1, Neg1, P' [(1, Neg1, P'' [0])])])
n'n    = add_path nn               (P' [(1, Neg0, P' [(1, Neg1, P'' [0])])])
nn'    = add_path n'n              (P' [(1, Neg1, P' [(1, Neg0, P'' [0])])])

pp1    = add_path nn'              (P' [(1, Pos1, P' [(1, Pos1, P'' [-1])])])
p_p1   = add_path pp1              (P' [(1, Pos1, P' [(2, Pos1, P'' [-1])])])
p_p2   = add_path p_p1             (P' [(1, Pos1, P' [(2, Pos1, P'' [-2])])])
p'p'1  = add_path p_p2             (P' [(1, Pos0, P' [(1, Pos0, P'' [-1])])])
p'p'2  = add_path p'p'1            (P' [(1, Pos0, P' [(1, Pos0, P'' [-2])])])
p'p1   = add_path p'p'2            (P' [(1, Pos0, P' [(1, Pos1, P'' [-1])])])
p'p2   = add_path p'p1             (P' [(1, Pos0, P' [(1, Pos1, P'' [-2])])])
p'_p1  = add_path p'p2             (P' [(1, Pos0, P' [(2, Pos1, P'' [-1])])])
p'_p2  = add_path p'_p1            (P' [(1, Pos0, P' [(2, Pos1, P'' [-2])])])
pp'1   = add_path p'_p2            (P' [(1, Pos1, P' [(1, Pos0, P'' [-1])])])
p'p'12 = add_path pp'1             (P' [(1, Pos1, P' [(1, Pos0, P'' [-1, -2])])])

ndc    = add_path p'p'12           (P' [(1, Neg1, P' [(1, Dc1, P'' [0])])])
n'dc'  = add_path ndc              (P' [(1, Neg0, P' [(1, Dc0, P'' [0])])])

-- ============================================================
-- Single-level variables: Dc0 context (background = True)
-- ============================================================

dc0_1  = add_path n'dc'            (P' [(1, Dc0, P'' [1])])
dc0_2  = add_path dc0_1            (P' [(1, Dc0, P'' [2])])
dc0_3  = add_path dc0_2            (P' [(1, Dc0, P'' [3])])
dc0__2 = add_path dc0_3            (P' [(2, Dc0, P'' [2])])

-- ============================================================
-- Context-switching fixtures:
-- Terms that use different inference contexts for the same class.
-- This models the "bounding" pattern from MDDmodelling.md §9.
-- ============================================================

-- A Dc1 content term: sub-class 1 of class 1, with variable 2
-- "I specify sub-class 1 but don't care about other sub-classes"
cs_dc_sub1 = add_path dc0__2
    (P' [(1, Dc1, P' [(1, Dc1, P'' [2])])])

-- A Dc1 content term: sub-class 2 of class 1, with variable 3
cs_dc_sub2 = add_path cs_dc_sub1
    (P' [(1, Dc1, P' [(2, Dc1, P'' [3])])])

-- A Neg1 bounding term: class 1 bounded to sub-classes {1, 2} only
-- "Only sub-classes 1 and 2 exist; all others are absent"
cs_neg_bound12 = add_path cs_dc_sub2
    (P' [(1, Neg1, P' [(1, Dc1, P'' [0]), (2, Dc1, P'' [0])])])

-- A Neg1 bounding term: class 1 bounded to sub-class {1} only
cs_neg_bound1 = add_path cs_neg_bound12
    (P' [(1, Neg1, P' [(1, Dc1, P'' [0])])])

-- A Neg1 bounding term: class 1 bounded to sub-classes {1, 2, 3}
cs_neg_bound123 = add_path cs_neg_bound1
    (P' [(1, Neg1, P' [(1, Dc1, P'' [0]), (2, Dc1, P'' [0]), (3, Dc1, P'' [0])])])

-- A Dc1 content term: sub-class 3 of class 1, with variable 4
cs_dc_sub3 = add_path cs_neg_bound123
    (P' [(1, Dc1, P' [(3, Dc1, P'' [4])])])

-- ============================================================
-- 4-level deep nesting: Dc -> Dc -> Dc -> Dc (homogeneous)
-- ============================================================

dddd2  = add_path cs_dc_sub3
    (P' [(1, Dc1, P' [(1, Dc1, P' [(1, Dc1, P' [(1, Dc1, P'' [2])])])])])
dddd3  = add_path dddd2
    (P' [(1, Dc1, P' [(1, Dc1, P' [(1, Dc1, P' [(1, Dc1, P'' [3])])])])])
dddd'2 = add_path dddd3
    (P' [(1, Dc1, P' [(1, Dc1, P' [(1, Dc1, P' [(1, Dc1, P'' [-2])])])])])

-- ============================================================
-- 4-level deep nesting: Dc -> Neg -> Pos -> Dc (mixed at every level)
-- ============================================================

dnpd2  = add_path dddd'2
    (P' [(1, Dc1, P' [(1, Neg1, P' [(1, Pos1, P' [(1, Dc1, P'' [2])])])])])
dnpd3  = add_path dnpd2
    (P' [(1, Dc1, P' [(1, Neg1, P' [(1, Pos1, P' [(1, Dc1, P'' [3])])])])])
dnpd'2 = add_path dnpd3
    (P' [(1, Dc1, P' [(1, Neg1, P' [(1, Pos1, P' [(1, Dc1, P'' [-2])])])])])

-- ============================================================
-- 4-level deep nesting: Neg -> Dc -> Neg -> Dc (alternating)
-- ============================================================

ndnd2  = add_path dnpd'2
    (P' [(1, Neg1, P' [(1, Dc1, P' [(1, Neg1, P' [(1, Dc1, P'' [2])])])])])
ndnd3  = add_path ndnd2
    (P' [(1, Neg1, P' [(1, Dc1, P' [(1, Neg1, P' [(1, Dc1, P'' [3])])])])])

-- ============================================================
-- The shared test context (NodeLookup) containing all variables
-- ============================================================

(t_c, _) = unMDD ndnd3

-- ============================================================
-- Advanced operations context
-- ============================================================

(t_c_adv, node_and_34) = let
    m1 = dc3
    m2 = add_path m1 (P' [(1, Dc1, P'' [4])])
    in (fst $ unMDD m2, m1 .*. m2)
