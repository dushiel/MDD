# Inference Contexts and Tautologies: How Class Domains Break Classical Logic Symmetries

This document explains how the MDD inference contexts (Dc, Neg, Pos) and their background suffixes (1/0) create a richer logical landscape where many classical Boolean tautologies no longer hold universally. It then performs a gap analysis of the current test suite against this landscape.

This file is made with help of AI.


## 1. The Starting Point: Classical Boolean Algebra

In a standard BDD, every variable lives in a single flat namespace under a single inference rule (don't-care elimination). All the classical Boolean algebra laws hold unconditionally:

| Law | Formula |
|-----|---------|
| Complement | x AND (NOT x) == Bot; x OR (NOT x) == Top |
| Idempotence | x AND x == x; x OR x == x |
| Commutativity | x OP y == y OP x |
| Associativity | (x OP y) OP z == x OP (y OP z) |
| Distributivity | x AND (y OR z) == (x AND y) OR (x AND z) |
| Absorption | x AND (x OR y) == x |
| De Morgan | NOT (x AND y) == (NOT x) OR (NOT y) |
| Double negation | NOT (NOT x) == x |
| Identity | x AND Top == x; x OR Bot == x |
| Annihilation | x AND Bot == Bot; x OR Top == Top |

These laws hold because every variable is independent: the truth value of variable `a` says nothing about the truth value of variable `b`. The variables are "orthogonal" -- they live in separate dimensions of a product space.


## 2. What MDDs Change: Variables Are No Longer Independent

In an MDD, variables are grouped into **class domains** via ClassNode. Each class domain has an **inference context** (Dc, Neg, or Pos) that determines what happens to variables that are *not explicitly mentioned* in a term. This creates implicit constraints between variables in the same class, breaking the independence assumption.

### 2.1 The Three Inference Contexts

**Dc (Don't-Care)**: An unmentioned variable is inferred as "don't care" -- it has no influence. A Dc-context term is a **partial specification** that accepts any value for positions it doesn't constrain. This is the classical BDD behavior.

**Neg (Negative-literal)**: An unmentioned variable is inferred as **negatively evaluated** (absent/false). A Neg-context term is a **complete specification** -- it names exactly which items are present, and everything else is absent. This is like a regex character class `[abc]`: only what you list matches.

**Pos (Positive-literal)**: An unmentioned variable is inferred as **positively evaluated** (present/true). A Pos-context term specifies **exceptions** -- everything is present except what you explicitly exclude. This is like a negated character class `[^abc]`.

### 2.2 The Background Suffix (1 vs 0)

The suffix determines the **default leaf value** for the background (the dc branch of the ClassNode):

- **Dc1 / Neg1 / Pos1**: Background defaults to `False` (leaf 0). The term describes a region carved out of an otherwise-false space.
- **Dc0 / Neg0 / Pos0**: Background defaults to `True` (leaf 1). The term describes exceptions carved out of an otherwise-true space.

The 1/0 suffix is a construction-time parameter. At the graph level, the difference manifests as the dc branch of the ClassNode pointing to `Leaf False` vs `Leaf True`. This affects how `Unknown` nodes resolve during traversal and how the `absorb` function determines redundancy.

### 2.3 The Key Insight: Same Variable, Different Context = Different Semantics

Consider variable 2 in class 1. The MDD `n2` (Neg1 context) and the MDD `dc2` (Dc1 context) both "talk about" position 2 in class 1. But they carry different implicit information:

- `dc2` says: "position 2 is positively evaluated; I have no opinion about any other position."
- `n2` says: "position 2 is positively evaluated; every other position in this class is absent."

This difference is invisible when you look at a single term, but it becomes visible when you combine terms.


## 3. Which Tautologies Break and Why

### 3.1 Tautologies That Always Hold (Context-Independent)

These laws hold regardless of inference context because they involve the *same* terms on both sides, so the implicit constraints are consistent:

| Law | Why it holds |
|-----|-------------|
| **Idempotence**: x AND x == x | Same implicit constraints on both sides. |
| **Double negation**: NOT (NOT x) == x | Negation inverts the graph; doing it twice restores it. |
| **Complement**: x AND (NOT x) == Bot; x OR (NOT x) == Top | NOT x is the exact complement within the same context. |
| **Commutativity**: x OP y == y OP x | Operand order doesn't affect the result. |
| **Identity**: x AND Top == x; x OR Bot == x | Top/Bot are context-free constants. |
| **Annihilation**: x AND Bot == Bot; x OR Top == Top | Same. |
| **De Morgan**: NOT (x AND y) == (NOT x) OR (NOT y) | Holds because negation is well-defined and distributes correctly through the graph traversal. |

These hold for *all* contexts (Dc, Neg, Pos, nested, mixed) because they are structural properties of the graph operations, not dependent on the background semantics.

### 3.2 Tautologies That Break Under Neg/Pos Context

The critical failures occur when you combine terms that **implicitly disagree** about unmentioned variables.

#### The "Independent Variables" Assumption Fails

In classical logic: if `a` and `b` are independent variables, then `a AND b` is satisfiable (not Bot).

In Neg context: `n2 AND n3 == Bot`. Why? `n2` says "position 2 is present, everything else is absent" -- so position 3 is absent. `n3` says "position 3 is present, everything else is absent" -- so position 2 is absent. They contradict each other.

In Pos context: `p2 AND p3 == Bot`. Similarly, `p2` says "exclude position 2 from the all-present set" and `p3` says "exclude position 3." These are different exclusion sets and cannot coexist (each one demands the other's excluded item be present).

In Dc context: `dc2 AND dc3` is satisfiable (not Bot). Each term is a partial specification that doesn't constrain the other's position.

**This is the fundamental asymmetry**: Dc variables are independent; Neg and Pos variables within the same class are implicitly coupled.

#### Absorption Law Asymmetry

In classical logic: `(a AND b) OR b == b` always holds (absorption).

In Neg context: `(n2 AND n3) OR n3 == n3` still holds, but for a different reason than in classical logic. Since `n2 AND n3 == Bot` (as shown above), this reduces to `Bot OR n3 == n3`. The absorption law "works" but only because the intersection is already empty.

The absorption law holds structurally in all contexts, but the *reason* it holds differs:
- In Dc: `dc2 AND dc3` is a genuine conjunction (both constraints active). `(dc2 AND dc3) OR dc3 == dc3` because `dc2 AND dc3` is a subset of `dc3`.
- In Neg: `n2 AND n3 == Bot`, so `(n2 AND n3) OR n3 == Bot OR n3 == n3`. The "absorption" is trivial.

#### Distributivity Holds But Produces Different Results

`x AND (y OR z) == (x AND y) OR (x AND z)` holds in all contexts. But the *value* of each side depends on context:

- Dc: `dc2 AND (dc3 OR dc1)` is a non-trivial conjunction.
- Neg: `n2 AND (n3 OR n1)` -- since `n2 AND n3 == Bot` and `n2 AND n1 == Bot` (different items in same Neg class), this equals `Bot OR Bot == Bot`.

The law holds, but in Neg context it often reduces to a trivial equality `Bot == Bot`.

### 3.3 Cross-Context Interactions

When terms from **different contexts** are combined, the result depends on the dominance relationship:

| Combination | AND behavior | OR behavior |
|-------------|-------------|------------|
| Dc AND Neg | Dc acts as wildcard; result follows Neg constraints. `dc2 AND n2 == n2` (Dc doesn't add restrictions). | Dc subsumes Neg. `dc2 OR n2 == dc2` (Dc is more permissive). |
| Dc AND Pos | Similar: Dc accepts Pos constraints. | Dc subsumes Pos. |
| Neg AND Pos (same class) | Usually Bot (conflicting defaults). | Depends on specific variables. |
| 1-suffix AND 0-suffix (same type) | Bot (opposite backgrounds). `n2 AND n'2 == Bot`. | May produce Top. `n'2 OR n'3 == Top`. |

The 1/0 suffix interaction is particularly important: `n2` (Neg1, background=False) and `n'2` (Neg0, background=True) are **complements** -- they describe opposite regions of the same class. Their intersection is always Bot and their union is always Top.

### 3.4 Multi-Level and Nested Domain Effects

When variables live in different class levels (e.g., `n2` in class 1 vs `n_2` in class 2), they are in **different namespaces**. Variables in different classes are always independent, regardless of inference context:

- `n2 AND n_2` is satisfiable (not Bot), even though both use Neg1 context, because they are in different classes.
- `n2 AND n3 == Bot` because they are in the *same* class.

Nesting adds another dimension: `nn2` (Neg1 inside Neg1) creates a variable at position 2 inside a nested Neg class inside an outer Neg class. The outer and inner contexts can differ:
- `nn2` = Neg1 outer, Neg1 inner
- `nn'2` = Neg1 outer, Neg0 inner
- `n'n2` = Neg0 outer, Neg1 inner

These all have different semantics because the background at each level can differ.


## 4. The Symmetry Structure

The test suite should account for the following symmetry axes:

### Axis 1: Inference Type (3 values)
- Dc, Neg, Pos

### Axis 2: Background Suffix (2 values)
- 1 (background = False), 0 (background = True)

This gives 6 construction literals: Dc1, Dc0, Neg1, Neg0, Pos1, Pos0.

### Axis 3: Same-Class vs Cross-Class (2 values)
- Variables in the same class (implicit coupling under Neg/Pos)
- Variables in different classes (always independent)

### Axis 4: Nesting Depth (3+ values)
- Flat (single class level)
- 2 levels (class containing class)
- 3+ levels (deeply nested)

### Axis 5: Homogeneous vs Mixed Context (2 values)
- All variables in the same inference context
- Variables from different inference contexts combined

### Axis 6: Operation Type
- Binary: AND, OR
- Unary: NOT, restrict
- Derived: implication, biconditional, XOR, ite
- Quantification: forall, exist

### The Full Combinatorial Space

For each Boolean law, the test should ideally verify it across:
- All 6 construction literals (or at least the 3 inference types x 2 backgrounds)
- Same-class and cross-class variable pairs
- Flat and nested configurations
- Homogeneous and mixed-context combinations

Not every combination is meaningful (e.g., Dc1 vs Dc0 behave identically for many laws), but the space is large enough that systematic coverage matters.


## 5. Context-Specific Tautologies

Beyond the classical laws, MDDs have tautologies that are *specific* to certain inference contexts:

### Neg-Specific
- **Mutual exclusion**: `n_i AND n_j == Bot` for i /= j in the same class (different items in a Neg class are mutually exclusive).
- **Exhaustive union with complement**: `n'_i OR n'_j == Top` when i and j together cover all explicitly mentioned items (Neg0 variables are complements).
- **Dc subsumption**: `dc_i OR n_i == dc_i` (Dc is strictly more permissive than Neg for the same variable).

### Pos-Specific
- **Mutual exclusion**: `p_i AND p_j == Bot` for i /= j in the same class (different exclusions in a Pos class conflict).
- **Complement union**: `p'_i OR p_i == Top` (Pos0 and Pos1 for the same variable are complements).
- **Dc subsumption**: `dc'_i OR p_i == dc'_i`.

### Cross-Context
- **Dc absorbs Neg/Pos under AND**: `dc_i AND n_i == n_i` (Dc doesn't add constraints).
- **Dc subsumes Neg/Pos under OR**: `dc_i OR n_i == dc_i` (Dc is more permissive).
- **Opposite-background contradiction**: `n_i AND n'_i == Bot` (Neg1 and Neg0 for same variable are complements).

### Nested-Specific
- **Inner context independence**: Variables at different nesting levels are independent regardless of inference type.
- **Context collapse**: When inner Neg items combine exhaustively, the result collapses to the outer Dc wildcard (e.g., `nn'2 OR nn'3 == ndc`).


## 6. Gap Analysis of Current Test Suite

### 6.0 Test Suite Overview

The Tasty test suite (`test/Main.hs`) contains ~543 test cases across 8 modules:

| Module | ~# tests | Focus |
|--------|----------|-------|
| Construction | 22 | `path`, `add_path`, `makeNode`, `levelLtoPath` |
| BinaryOps | 127 | AND/OR across contexts, multi-level, 3-level, context switching, tautologies |
| NestedDomains | 135 | Nested Dc/Neg/Pos, algebraic laws on nested vars, cross-context dc_stack, absorb catchup |
| UnaryOps | 37 | Negation, restrict (Dc/Neg/Pos), Shannon expansion |
| Interface | 36 | Constants, ite, xor, implication, biconditional, conSet/disSet/xorSet |
| Quantification | 43 | forall/exist/forallSet/existSet in Dc, Neg, Pos, cross-class |
| Relabeling | 7 | relabelWith: simple, overlapping, cross-domain |
| Properties | 136 | Exhaustive algebraic laws for Dc1, Neg1, Pos1, Dc0 (same-class + cross-class) |

Fixtures are defined in `MDD.Test.Fixtures` and build a shared `NodeLookup` (`t_c`) containing variables across all 6 construction literals (Dc1, Dc0, Neg1, Neg0, Pos1, Pos0), multiple class IDs (1, 2, 3), and nested domains (Dc-in-Dc, Neg-in-Neg, Pos-in-Pos, Dc-with-Neg, Dc-with-Pos). Context-switching fixtures model the "bounding" pattern from MDDmodelling.md.

### 6.1 Coverage Matrix

The table below maps which combinations of (inference context x operation x structural level) are tested. YES means at least one test exists; a dash means no test exists.

#### Binary Operations (AND/OR)

| Context pair | Same-class flat | Cross-class flat | 2-level | 3-level | Nested (2-deep) |
|---|---|---|---|---|---|
| Dc1 x Dc1 | YES | YES | YES | - | YES |
| Dc0 x Dc0 | YES | YES | - | - | - |
| Neg1 x Neg1 | YES | YES | YES | YES | YES |
| Neg0 x Neg0 | - | - | YES | YES | - |
| Pos1 x Pos1 | YES | YES | YES | YES | YES |
| Pos0 x Pos0 | - | - | YES | YES | - |
| Dc1 x Dc0 | YES | YES | - | - | - |
| Dc1 x Neg1 | YES | - | - | - | YES |
| Dc1 x Pos1 | YES | - | - | - | - |
| Dc1 x Neg0 | YES | - | - | - | - |
| Dc1 x Pos0 | YES | - | - | - | - |
| Neg1 x Neg0 | YES | - | - | - | YES |
| Pos1 x Pos0 | YES | - | - | - | YES |
| Neg1 x Pos1 | YES | - | - | YES (mixed) | - |
| Neg0 x Pos0 | - | - | - | YES (mixed) | - |
| Neg1 x Pos0 | - | - | - | YES (mixed) | - |
| Neg0 x Pos1 | - | - | - | YES (mixed) | - |

#### Unary Operations

| Operation | Dc1 | Dc0 | Neg1 | Neg0 | Pos1 | Pos0 | Nested |
|---|---|---|---|---|---|---|---|
| NOT (double negation) | YES | YES | YES | - | YES | - | YES (Dc, Neg) |
| NOT (De Morgan) | YES | YES | YES | - | YES | - | YES (Dc, Neg, Pos, mixed) |
| restrict | YES | - | YES | - | YES | - | - |
| Shannon expansion | YES | - | YES | - | YES | - | - |

#### Algebraic Properties (Properties.hs)

| Law | Dc1 | Dc0 | Neg1 (same + cross) | Neg0 | Pos1 (same + cross) | Pos0 | Cross-context |
|---|---|---|---|---|---|---|---|
| Identity | YES | YES | YES | - | YES | - | - |
| Annihilation | YES | YES | YES | - | YES | - | - |
| Idempotence | YES | YES | YES (+ multi-item) | - | YES (+ multi-item) | - | - |
| Complement | YES | YES | YES | - | YES | - | - |
| Commutativity | YES | YES | YES (same + cross) | - | YES (same + cross) | - | - |
| Associativity | YES | YES | YES (same + cross) | - | YES (same + cross) | - | - |
| Distributivity | YES | YES | YES (same + cross) | - | YES (same + cross) | - | - |
| Absorption | YES | YES | YES (same + cross) | - | YES (same + cross) | - | - |
| De Morgan | YES | YES | YES (same + cross) | - | YES (same + cross) | - | - |
| Double negation | YES | YES | YES (+ multi-item) | - | YES (+ multi-item) | - | - |

#### Nested Algebraic Properties (NestedDomains.hs)

| Law | Dc-in-Dc | Neg-in-Neg (same) | Neg-in-Neg (cross) | Pos-in-Pos (same) | Pos-in-Pos (cross) | Mixed (Dc/Neg) |
|---|---|---|---|---|---|---|
| Associativity | YES | YES | YES | YES | YES | YES |
| Distributivity | YES | YES | YES | YES | YES | YES |
| Absorption | YES | YES | YES | YES | YES | YES |
| De Morgan | YES | YES | YES | YES | YES | YES |
| Complement/Identity | - | - | - | - | - | YES |

#### Context-Specific Tautologies (BinaryOps.hs)

| Tautology | Neg | Pos | Cross-context |
|---|---|---|---|
| Mutual exclusion (same-class) | YES (+ multi-item) | YES (+ multi-item) | - |
| Exhaustive complement (0-suffix) | YES | YES | - |
| 1/0 suffix complement | YES | YES | - |
| Cross-class independence | YES | YES | - |
| Dc absorbs Neg/Pos under AND | - | - | YES |
| Dc subsumes Neg/Pos under OR | - | - | YES |
| Neg AND Pos conflict | - | - | YES |

#### Context Switching (BinaryOps.hs)

| Pattern | Tested |
|---|---|
| Dc content AND Neg bound (non-bot) | YES |
| Result implies content | YES |
| Result more restrictive than bound | YES |
| Two contents AND bound | YES |
| Content outside bound gives bot | YES |
| Wider bound accepts more | YES |
| Commutativity with context switch | YES |
| Bound idempotence | YES |
| Narrower bound more restrictive | YES |
| Wider bound subsumes narrower | YES |
| Associativity with context switch | YES |

#### Quantification

| Operation | Dc1 | Neg1 | Pos1 | Nested | Cross-class |
|---|---|---|---|---|---|
| forall | YES | YES | YES | - | YES |
| exist | YES | YES | YES | - | YES |
| forallSet | YES | YES | YES | - | - |
| existSet | YES | YES | YES | - | - |
| trivial (top/bot) | YES | YES | - | - | - |

#### Derived Operators

| Operator | Dc1 | Neg1 | Pos1 | Neg0 | Pos0 | Cross-context |
|---|---|---|---|---|---|---|
| ite | YES | - | - | - | - | - |
| xor | YES | - | - | - | - | - |
| implication | YES | - | - | - | - | - |
| biconditional | YES | - | - | - | - | - |

### 6.2 Identified Gaps

#### Gap A: No Neg0 or Pos0 algebraic properties

Properties.hs covers Dc1, Dc0, Neg1, and Pos1 but has no Neg0 or Pos0 sections. While Neg0/Pos0 variables appear in BinaryOps.hs (multi-level, tautologies) and NestedDomains.hs, the systematic algebraic law verification (identity, annihilation, idempotence, complement, etc.) is missing for these contexts. Neg0 and Pos0 have inverted backgrounds and should behave as complements of Neg1/Pos1 respectively.

#### Gap B: Derived operators only tested in Dc1 context

ite, xor, implication, and biconditional in Interface.hs are tested exclusively with Dc1 variables. Their behavior with Neg/Pos variables (where implicit background changes semantics) is untested. Since these are defined in terms of AND/OR/NOT which are well-tested in all contexts, this is lower risk but still a coverage gap.

#### Gap C: No cross-context algebraic property tests

Properties.hs tests each context in isolation. There are no algebraic law tests that mix contexts as operands (e.g., distributivity with one Dc1 operand and one Neg1 operand). BinaryOps.hs tests cross-context tautologies and context switching, but not the full set of algebraic laws across context boundaries.

**Needed**: Cross-context variants of at least distributivity, absorption, and De Morgan where operands come from different inference contexts (e.g., `dc2 AND (n2 OR n3) == (dc2 AND n2) OR (dc2 AND n3)`).

#### Gap D: No 4-level deep nesting tests

The deepest nesting tested is 3 levels (in `threeLevelOps` and `threeLevelMixed` in BinaryOps.hs). No tests exercise 4-level deep class hierarchies. Deeper nesting stresses the dc_stack management, Unknown resolution cascading, and absorb position catchup at multiple levels simultaneously.

**Needed**: 4-level fixtures (e.g., `P' [(1, Dc1, P' [(1, Neg1, P' [(1, Pos1, P' [(1, Dc1, P'' [2])])])])]`) and algebraic law tests at that depth. This would catch bugs in dc_stack synchronization that only manifest with deeper cascading.

#### Gap E: No cross-context tests at nested/multi-level depth

Cross-context interactions (Dc absorbs Neg, Dc subsumes Pos, Neg-Pos conflict) are tested only at the flat single-level. The same interactions at 2-level or nested depth are untested. For example: a Dc1 variable in class 1 combined with a Neg1 variable in a nested sub-class of class 1.

**Needed**: Cross-context tautologies (absorption, subsumption, conflict) verified at 2-level and nested depths.

#### Gap F: Negation not tested for Neg0, Pos0, or nested Pos

Double negation is tested for Dc1, Dc0, Neg1, Pos1, and nested Dc/Neg. Missing: Neg0, Pos0, nested Pos, and mixed-context nested variables. De Morgan is similarly missing for Neg0 and Pos0.

#### Gap G: No quantification over nested variables

All quantification tests use flat (single-level) variables. Quantifying over a variable inside a nested class hierarchy (e.g., `forall [1, 1, 2] nn2`) is untested. This would exercise restrict's behavior when the target variable is behind multiple ClassNode layers.

#### Gap H: No restrict or Shannon expansion on nested variables

Restrict and Shannon expansion are tested for flat Dc, Neg, and Pos variables. No tests verify restrict behavior when the target variable is inside a nested domain. The dc_stack interaction during restrict at nested depth is a potential bug surface.

#### Gap I: No Neg0/Pos0 flat same-class tests

For Neg0 and Pos0, there are no flat same-class intersection/union tests (e.g., `n'2 AND n'3` in the same class at the flat level). The multi-level and tautology tests cover some of this indirectly, but basic single-level algebraic behavior is not verified.

#### Gap J: No tests for the "wildcard" construction pattern

The `P'' [0]` in Dc1 context (the "Top trick") is used in fixtures but never explicitly tested. A test should verify that `path (P' [(1, Dc1, P'' [0])])` produces an MDD equivalent to Top within that class scope.

### 6.3 Priority Ranking

| Priority | Gap | Rationale |
|----------|-----|-----------|
| **High** | Gap C (cross-context algebraic properties) | Cross-context is a core MDD differentiator. Algebraic laws across context boundaries exercise the most complex traversal paths. Should be added soon. |
| **High** | Gap D (Explicit Depth-Gap Tests) | Deeper nesting and asymmetric depth operations stress dc_stack cascading and EndClassNode stacking. Bugs here cause level violations that are subtle and hard to catch without explicit structural tests. Should be added soon. |
| **High** | Gap E (cross-context at nested depth) | Combines the two hardest dimensions (cross-context + nesting). Most likely to reveal dc_stack synchronization bugs. |
| **Medium** | Gap A (Neg0/Pos0 algebraic properties) | Systematic verification of inverted-background contexts. Lower risk since the graph operations are context-agnostic, but worth having for completeness. |
| **Medium** | Gap G (quantification over nested vars) | Quantification depends on restrict, which is untested at nested depth. |
| **Medium** | Gap H (restrict/Shannon on nested vars) | Foundation for nested quantification; exercises dc_stack during restrict. |
| **Medium** | Gap B (derived operators in Neg/Pos) | Lower risk since ite/xor/implication/biconditional are defined via AND/OR/NOT. |
| **Low** | Gap F (negation completeness) | Partially covered; remaining cases (Neg0, Pos0, nested Pos) are symmetric to tested ones. |
| **Low** | Gap I (Neg0/Pos0 flat same-class) | Partially covered at multi-level; flat case is simpler. |
| **Low** | Gap J (wildcard construction) | Construction is well-exercised indirectly; explicit test is for documentation. |

### 6.4 Test Suite Organization: Planned Changes

#### Trivial test separation

Many test cases in the suite are **trivial** in the sense that they verify basic properties that are structurally guaranteed or reduce to simple constant propagation (e.g., `x AND top == x`, `x OR bot == x`, `bot AND x == bot`, `NOT top == bot`, `forall v top == top`). These tests are valuable for regression and documentation but add runtime overhead when iterating on non-trivial bugs.

**Plan**: Separate trivial tests so they are not run by default. They should only execute when a `--full` flag (or similar) is passed. This keeps the default test run focused on the non-trivial cases that exercise real traversal, dc_stack synchronization, absorb, and cross-context interactions.

Candidates for "trivial" classification:
- **Constants**: `top AND bot == bot`, `top OR bot == top`, `top AND top == top`, `bot OR bot == bot`
- **Identity/Annihilation with constants**: `x AND top == x`, `x OR bot == x`, `x AND bot == bot`, `x OR top == top` (for all contexts)
- **Trivial quantification**: `forall v top == top`, `forall v bot == bot`, `exist v top == top`, `exist v bot == bot`, `forallSet [] x == x`, `existSet [] x == x`
- **Trivial restrict**: `restrict on top == top`, `restrict on bot == bot`
- **Self-operations**: `x AND x == x`, `x OR x == x` (idempotence with identical operands)

Non-trivial tests that should always run include: cross-context operations, nested domain algebraic laws, context switching, distributivity, absorption, De Morgan, Shannon expansion, multi-level operations, and any test involving compound expressions.

#### Implementation approach

Tasty supports test filtering via `--pattern` on the command line. The recommended approach:

1. Wrap trivial tests in a `testGroup "Trivial"` sub-group within each module.
2. By default, use `--pattern '!Trivial'` (or equivalent) to exclude them.
3. With `--full`, run `defaultMain` without the pattern filter.

Alternatively, use `adjustOption` in `Main.hs` to set a default pattern that excludes trivial tests, overridable by command-line arguments. This avoids needing a custom `--full` flag and works with Tasty's existing infrastructure.

#### Next priorities for new test cases

1. **Cross-context algebraic properties** (Gap C): Add a `testGroup "Cross-context"` section to Properties.hs with distributivity, absorption, and De Morgan tests mixing Dc1/Neg1, Dc1/Pos1, and Neg1/Pos1 operands.
2. **Explicit Depth-Gap Tests** (Gap D): Add asymmetric depth operations tests to NestedDomains.hs. Focus on explicitly checking the string representation (`show_mdd`) to verify that the correct number of `EndClassNode`s (`<>`) are stacked when combining nodes at different depths.
3. **Cross-context at nested depth** (Gap E): Add tests combining cross-context tautologies with 2-level and nested structures.


## 7. Relationship to ZDD (Cube) Algebra

### 7.1 What ZDDs Are

A Zero-suppressed Decision Diagram (ZDD), introduced by Minato (1993), is a BDD variant that uses a different elimination rule: **a node is eliminated when its positive edge leads to the zero terminal**. This means an absent variable is inferred as negatively evaluated (not in the set). ZDDs represent *families of sets* -- collections of subsets drawn from a universe of items.

The ZDD elimination rule is exactly the **Neg inference rule** in MDD terminology. A ZDD is, in essence, a decision diagram where every variable lives under Neg inference globally.

### 7.2 The Correspondence

| ZDD concept | MDD equivalent | Notes |
|-------------|---------------|-------|
| ZDD elimination rule | Neg inference | Node eliminated when pos-edge -> 0 terminal |
| BDD elimination rule | Dc inference | Node eliminated when both edges lead to same child |
| No ZDD equivalent | Pos inference | MDD-specific: absent = positively evaluated |
| Cube `{a, b}` | `n_a AND n_b` in same Neg class | Both items present, all others absent |
| Family union | `.+.` (OR) | Union of set families |
| Family intersection | `.*. ` (AND) | Intersection of set families |
| Family difference `P - Q` | `p .*. (-.) q` | Sets in P but not in Q |
| Complement `U - P` | Requires defining U explicitly | ZDDs have no native NOT; MDDs do via Neg0 |
| `Subset1(P, var)` | `restrict pos True` | Cofactor: sets containing var |
| `Subset0(P, var)` | `restrict pos False` | Cofactor: sets not containing var |
| `Change(P, var)` | No direct equivalent | Toggle membership of var in all sets |
| `Count(P)` | No direct equivalent | Number of sets in family |

### 7.3 Key Algebraic Differences

**ZDD family algebra** operates on *families of sets* (sets of sets). The operations are:

- **Union** (`P ∪ Q`): family containing all sets from P or Q.
- **Intersection** (`P ∩ Q`): family containing sets in both P and Q.
- **Difference** (`P \ Q`): family containing sets in P but not Q.
- **Join** (`P ⊔ Q`): `{a ∪ b | a ∈ P, b ∈ Q}` -- pairwise union of sets.
- **Meet** (`P ⊓ Q`): `{a ∩ b | a ∈ P, b ∈ Q}` -- pairwise intersection.

In MDD Neg context, the AND/OR operators correspond to family intersection/union at the *Boolean function* level, not the family-of-sets level. The distinction matters:

- ZDD `Intsec({a}, {b})` = `{}` (empty family, because no set is in both `{{a}}` and `{{b}}`).
- MDD `n_a AND n_b` = Bot (same result, different framing: the Boolean functions are contradictory).

The algebraic identities are the same, but the interpretation differs. ZDD algebra talks about "which sets are in the family"; MDD Neg-context algebra talks about "which variable assignments satisfy the formula." For single-element families (single cubes), these coincide.

**What MDDs add that ZDDs lack:**

1. **Dc inference (wildcard/don't-care)**: ZDDs have no native way to say "I don't care about variable x." To express this in a ZDD, you must enumerate both the x-present and x-absent variants -- exponential blowup for many don't-care variables. MDDs handle this natively via Dc context.

2. **Pos inference (complement sets)**: ZDDs have no native complement. `NOT P` requires computing `U \ P` where U is the explicit universal set. MDDs represent "everything except these" directly via Pos context.

3. **Mixed inference in one diagram**: A ZDD uses Neg inference globally. An MDD can use Dc for one class (container/namespace), Neg for another (item selection), and Pos for a third (exclusion list), all in the same canonical graph.

4. **Hierarchical nesting**: ZDD variables are flat. MDD variables are organized into nested class hierarchies, enabling structured multi-domain modelling.

### 7.4 Known ZDD Identities as MDD Neg-Context Tests

The following are standard ZDD family-algebra identities (from Knuth, TAOCP Vol 4, and Minato's original papers). Each translates directly into an MDD Neg-context test. The "MDD form" column shows how the identity would be expressed using MDD Neg-context variables.

#### Family Union / Intersection (correspond to MDD OR / AND)

| # | ZDD Identity | MDD Neg-context form | Currently tested? |
|---|-------------|---------------------|-------------------|
| Z1 | `P ∪ {} = P` | `n_i OR Bot == n_i` | YES (Neg1 identity in Properties.hs) |
| Z2 | `P ∪ P = P` | `n_i OR n_i == n_i` | YES (Neg1 idempotence in Properties.hs) |
| Z3 | `P ∪ Q = Q ∪ P` | `n_i OR n_j == n_j OR n_i` | YES (Neg1 commutativity in Properties.hs) |
| Z4 | `P ∩ {} = {}` | `n_i AND Bot == Bot` | YES (Neg1 annihilation in Properties.hs) |
| Z5 | `P ∩ P = P` | `n_i AND n_i == n_i` | YES (Neg1 idempotence in Properties.hs) |
| Z6 | `P ∩ Q = Q ∩ P` | `n_i AND n_j == n_j AND n_i` | YES (Neg1 commutativity in Properties.hs) |
| Z7 | `P \ {} = P` | `n_i AND (NOT Bot) == n_i` | YES (follows from Neg1 identity: n_i AND top == n_i) |
| Z8 | `{} \ P = {}` | `Bot AND (NOT n_i) == Bot` | YES (annihilation) |
| Z9 | `P \ P = {}` | `n_i AND (NOT n_i) == Bot` | YES (Neg1 complement in Properties.hs) |

#### Mutual Exclusion (Neg-specific, no BDD analogue)

| # | ZDD Identity | MDD Neg-context form | Currently tested? |
|---|-------------|---------------------|-------------------|
| Z10 | `{a} ∩ {b} = {}` for a /= b | `n_i AND n_j == Bot` (same class, i /= j) | YES (negSpecificTautologies in BinaryOps.hs) |
| Z11 | `{a} ∩ {a,b} = {}` | `n_i AND n_ij == Bot` | YES (n2 AND n23 == Bot in negSpecificTautologies) |
| Z12 | `{a,b} ∩ {a,b} = {a,b}` | `n_ij AND n_ij == n_ij` | YES (Neg1 idempotence for n23 in Properties.hs) |

These hold because in Neg context, each term specifies a *complete* selection: `n2` means "exactly item 2 is present." Two terms with different selections are disjoint.

#### Cofactor / Restriction Identities

| # | ZDD Identity | MDD Neg-context form | Currently tested? |
|---|-------------|---------------------|-------------------|
| Z13 | `Subset1(P, v) ∪ Subset0(P, v) = P` | `restrict v True p OR restrict v False p == p` | YES (Shannon expansion in UnaryOps.hs for Dc, Neg, Pos, simple and compound) |
| Z14 | `Subset1({}, v) = {}` | `restrict v True Bot == Bot` | YES (restrict on bot in UnaryOps.hs) |
| Z15 | `Subset0({}, v) = {}` | `restrict v False Bot == Bot` | YES (follows from restrict on bot) |
| Z16 | `Subset1(P, v) ∩ Subset0(P, v) = {}` | `restrict v True p AND restrict v False p == Bot` | YES (tested for Dc and Neg in UnaryOps.hs) |

The Shannon expansion (Z13) is particularly important: it says that restricting a variable to True and to False, then OR'ing the results, recovers the original. This should hold in all contexts.

#### Complement / Difference Identities

| # | ZDD Identity | MDD Neg-context form | Currently tested? |
|---|-------------|---------------------|-------------------|
| Z17 | `(U \ P) ∪ P = U` | `(NOT n_i) OR n_i == Top` | YES (Neg1 complement in Properties.hs) |
| Z18 | `(U \ P) ∩ P = {}` | `(NOT n_i) AND n_i == Bot` | YES (Neg1 complement in Properties.hs) |
| Z19 | `U \ (U \ P) = P` | `NOT (NOT n_i) == n_i` | YES (Neg1 double negation in Properties.hs) |

Note: In ZDDs, complement requires an explicit universal set U. In MDDs, negation (`-. `) is a native operation that works in all contexts, so Z17 and Z18 translate directly.

#### Distributivity

| # | ZDD Identity | MDD Neg-context form | Currently tested? |
|---|-------------|---------------------|-------------------|
| Z20 | `P ∩ (Q ∪ R) = (P ∩ Q) ∪ (P ∩ R)` | `n_i AND (n_j OR n_k) == (n_i AND n_j) OR (n_i AND n_k)` | YES (Neg1 distributivity in Properties.hs, same-class + cross-class) |
| Z21 | `P ∪ (Q ∩ R) = (P ∪ Q) ∩ (P ∪ R)` | `n_i OR (n_j AND n_k) == (n_i OR n_j) AND (n_i OR n_k)` | YES (Neg1 distributivity in Properties.hs, same-class + cross-class) |

In Neg context with same-class variables, Z20 often reduces to `Bot == Bot` (since `n_i AND n_j == Bot` for i /= j). This is still a valid test -- it verifies the trivial case. For cross-class Neg variables (e.g., `n2` in class 1 and `n_2` in class 2), the distributivity is non-trivial and worth testing.

#### Absorption

| # | ZDD Identity | MDD Neg-context form | Currently tested? |
|---|-------------|---------------------|-------------------|
| Z22 | `P ∩ (P ∪ Q) = P` | `n_i AND (n_i OR n_j) == n_i` | YES (Neg1 absorption in Properties.hs, same-class + cross-class) |
| Z23 | `P ∪ (P ∩ Q) = P` | `n_i OR (n_i AND n_j) == n_i` | YES (Neg1 absorption in Properties.hs, same-class + cross-class) |

#### De Morgan (requires complement)

| # | ZDD Identity | MDD Neg-context form | Currently tested? |
|---|-------------|---------------------|-------------------|
| Z24 | `U \ (P ∩ Q) = (U \ P) ∪ (U \ Q)` | `NOT (n_i AND n_j) == (NOT n_i) OR (NOT n_j)` | YES (Neg1 De Morgan in Properties.hs, same-class + cross-class) |
| Z25 | `U \ (P ∪ Q) = (U \ P) ∩ (U \ Q)` | `NOT (n_i OR n_j) == (NOT n_i) AND (NOT n_j)` | YES (Neg1 De Morgan in Properties.hs, same-class + cross-class) |

### 7.5 Pos-Context as Complement ZDD

Pos inference can be understood as "complement ZDD" -- where the elimination rule is the mirror of ZDD's. Instead of "absent = not selected" (Neg/ZDD), it's "absent = selected" (Pos). The Pos-context identities mirror the Neg-context ones with the polarity flipped:

| # | Pos-context identity | Currently tested? |
|---|---------------------|-------------------|
| P1 | `p_i AND p_j == Bot` (same class, i /= j) -- different exclusions conflict | YES (posSpecificTautologies in BinaryOps.hs) |
| P2 | `p_i AND p_i == p_i` (idempotent) | YES (Pos1 idempotence in Properties.hs) |
| P3 | `p'_i OR p_i == Top` (complement) | YES (posSpecificTautologies in BinaryOps.hs) |
| P4 | `NOT (NOT p_i) == p_i` (double negation) | YES (Pos1 double negation in Properties.hs) |
| P5 | `p_i OR Bot == p_i` (identity) | YES (Pos1 identity in Properties.hs) |
| P6 | `p_i AND Top == p_i` (identity) | YES (Pos1 identity in Properties.hs) |
| P7 | `p_i AND (p_i OR p_j) == p_i` (absorption) | YES (Pos1 absorption in Properties.hs) |
| P8 | `NOT (p_i AND p_j) == (NOT p_i) OR (NOT p_j)` (De Morgan) | YES (Pos1 De Morgan in Properties.hs) |
| P9 | `NOT (p_i OR p_j) == (NOT p_i) AND (NOT p_j)` (De Morgan) | YES (Pos1 De Morgan in Properties.hs) |
| P10 | `p_i AND (p_j OR p_k) == (p_i AND p_j) OR (p_i AND p_k)` (distributivity) | YES (Pos1 distributivity in Properties.hs) |
| P11 | `restrict v True p OR restrict v False p == p` (Shannon expansion) | YES (Shannon on p2 and compound Pos in UnaryOps.hs) |

### 7.6 Summary: ZDD-Derived Test Coverage

All ZDD-derived identities listed in Sections 7.4 and 7.5 are now covered by the test suite:

| Category | Status | Test location |
|----------|--------|---------------|
| Basic algebra (identity, idempotence, complement) in Neg | ALL COVERED | Properties.hs (Neg1 context) |
| Basic algebra in Pos | ALL COVERED | Properties.hs (Pos1 context) |
| Shannon expansion (restrict round-trip) | ALL COVERED | UnaryOps.hs (Dc, Neg, Pos, simple + compound) |
| Distributivity in Neg/Pos | ALL COVERED | Properties.hs (same-class + cross-class) |
| Absorption in Neg/Pos | ALL COVERED | Properties.hs (same-class + cross-class) |
| De Morgan in Neg/Pos | ALL COVERED | Properties.hs (same-class + cross-class) |
| Mutual exclusion (Neg/Pos-specific) | ALL COVERED | BinaryOps.hs (negSpecificTautologies, posSpecificTautologies) |
| Multi-item cube identities | ALL COVERED | Properties.hs (n23/p23 idempotence) |
| Cofactor / restriction | ALL COVERED | UnaryOps.hs (restrictNegTests, restrictPosTests) |
| Complement / difference | ALL COVERED | Properties.hs (Neg1/Pos1 complement laws) |

The original 23 missing ZDD-derived tests have all been implemented. The remaining gaps (Section 6.2) are in areas that go beyond classical ZDD algebra: cross-context interactions, deep nesting (4+ levels), and nested quantification/restrict.
