# Modelling with MDDs: Inference Contexts and Class Hierarchy Design

This document explains how to choose between Dc, Neg, and Pos inference contexts when designing class hierarchies for MDD-based models. It covers the behavioral differences, draws analogies to regex/pattern matching, and provides practical guidelines.

This file is made with help of AI.


## 1. Dc vs Neg/Pos: Behavioral Differences

A ClassNode has three outgoing branches — Dc, Pos, and Neg (in that slot order) — each representing a different **inference and elimination rule** for the variables within that class. When constructing a path, the `InfL` suffix (`Dc1`, `Neg1`, `Pos1`, etc.) determines which branch the path is placed on and what the "background" default is.

### Dc (Don't-Care)

- **Elimination rule**: A variable is eliminated when its positive and negative evaluations lead to the same child. In other words, if a variable "doesn't matter" for the outcome, it is removed.
- **Background default**: The Dc branch *is* the background. Variables not explicitly mentioned are assumed to have no influence — they are "don't care".
- **Effect when combining**: A term constructed under Dc context acts as a **wildcard** for any variables it does not explicitly constrain. When AND'd with another term, it **accepts** whatever the other term says about those variables.

### Neg (Negative-literal)

- **Elimination rule**: A variable is eliminated when its positive evaluation leads to Unknown (i.e., only the negative evaluation is a valid path). The inferred default for an absent variable is that it is **negatively evaluated** (not present / not selected).
- **Background default (`Neg1`)**: Unknown resolves to **False/0**. This means every variable in this class is assumed to be *absent* unless explicitly included.
- **Effect when combining**: A term constructed under Neg context is **restrictive** — it specifies exactly which values are present. When AND'd with another term that mentions *different* values in the same Neg class, the Neg context rejects those values (they weren't in its explicit set), producing **Bot** (contradiction).

### Pos (Positive-literal)

- **Elimination rule**: A variable is eliminated when its negative evaluation leads to Unknown (i.e., only the positive evaluation is a valid path). The inferred default for an absent variable is that it is **positively evaluated** (present / selected).
- **Background default (`Pos1`)**: Unknown resolves to **True/1**. This means every variable in this class is assumed to be *present* unless explicitly excluded.
- **Effect when combining**: A Pos context term assumes everything is included by default. It is used to describe exceptions — "everything except these".

For a formal analysis of how these behavioral differences affect Boolean algebra laws, see [inference_contexts_and_tautologies.md](inference_contexts_and_tautologies.md) §2–3.


## 2. Variable Independence and Implicit Coupling

In a standard BDD, all variables are independent: the truth value of variable `a` says nothing about variable `b`. They live in separate dimensions of a product space, and all classical Boolean algebra laws hold unconditionally.

MDDs break this independence assumption. The inference context of a class determines whether its variables are independent or implicitly coupled.

### The Fundamental Asymmetry

**Dc variables are independent.** A Dc-context term is a partial specification — it constrains only the variables it mentions and is silent about everything else. Two Dc terms that mention different variables can always be AND'd together without contradiction:

- `dc2` says: "position 2 is positively evaluated; I have no opinion about any other position."
- `dc3` says: "position 3 is positively evaluated; I have no opinion about any other position."
- `dc2 AND dc3` is satisfiable — both constraints coexist.

**Neg and Pos variables in the same class are coupled.** A Neg-context term is a complete specification — it names exactly which items are present, and everything else is absent. Two Neg terms that name different items contradict each other:

- `n2` says: "position 2 is present; every other position in this class is absent."
- `n3` says: "position 3 is present; every other position in this class is absent."
- `n2 AND n3 == Bot` — `n2` demands position 3 be absent, but `n3` demands it be present.

The same applies to Pos: `p2 AND p3 == Bot` because each exclusion demands the other's excluded item be present.

### Cross-Class Independence

Variables in **different classes** are always independent, regardless of inference context. The class hierarchy creates separate namespaces:

- `n2` in class 1 and `n_2` in class 2 are in different namespaces.
- `n2 AND n_2` is satisfiable (not Bot), even though both use Neg1 context.
- `n2 AND n3 == Bot` because they are in the *same* class.

This is a key design principle: the coupling is *intra-class*, never *inter-class*. See [inference_contexts_and_tautologies.md](inference_contexts_and_tautologies.md) §3 for a complete analysis of how this coupling affects Boolean algebra laws.


## 3. Intuition: What Happens to Things You Don't Mention

The essential difference between Dc, Neg, and Pos is what they assume about variables that are **not explicitly mentioned** in a term. This maps onto the well-known distinction between open-world and closed-world reasoning:

| MDD Context | Assumption about unmentioned variables | Analogy |
|---|---|---|
| **Dc** | No opinion — unknown / don't care | **Open-world**: absence of information is not information about absence. |
| **Neg** | Assumed false / absent | **Closed-world**: if it's not stated, it's not true. |
| **Pos** | Assumed true / present | **Closed-world complement**: if it's not excluded, it's included. |

In database terms: Dc is like a query that returns rows matching a partial condition (unmentioned columns are unconstrained). Neg is like a complete record — every field has a value, and unmentioned fields default to "no". Pos is like a record where every field defaults to "yes" and you list the exceptions.

### Example: the guest list

Consider a party with potential guests {Alice, Bob, Carol, Dave}.

- **Dc**: "Alice is invited." — Says nothing about Bob, Carol, or Dave. They might come, they might not. This term is compatible with any information about the others.
- **Neg**: "Alice is invited." — This is the *complete* guest list. Bob, Carol, and Dave are not invited. If someone else says "Bob is invited" (also Neg), the two lists contradict — `Alice AND Bob == Bot`.
- **Pos**: "Alice is excluded." — Everyone *except* Alice is invited. Bob, Carol, and Dave are all coming.

The key consequence for combining terms (§2): two Dc terms about different guests can always be AND'd ("Alice is invited" AND "Bob is invited" = both are invited). Two Neg terms about different guests cannot ("only Alice" AND "only Bob" = contradiction).

### Example: items vs properties

The choice between Dc and Neg often reflects whether you are modelling **items** (members of a set) or **properties** (attributes of a state).

**Item selection (Neg is natural):** A robot's gripper holds objects from a set {wrench, bolt, washer}. A term "the gripper holds the wrench" naturally uses Neg — the gripper holds exactly the wrench, and implicitly *not* the bolt, *not* the washer. This is how ZDDs/cubes represent set families: each term is a complete specification of which items are present.

**Property description (Dc is natural):** The same robot has observable properties: {is-moving, is-gripping, battery-low}. A sensor reading "is-moving = true" naturally uses Dc — it tells you about movement but says nothing about whether the robot is gripping or whether the battery is low. Those properties are unknown, not false. A second sensor reading "battery-low = true" can be AND'd with the first without contradiction, because Dc terms about different properties are independent.

If you mistakenly used Neg for the property class, then "is-moving = true" would imply "is-gripping = false" and "battery-low = false" — the sensor reading would carry information it doesn't actually have. Conversely, if you used Dc for the item class, then "holds wrench" would leave the status of bolt and washer unknown rather than absent, which misrepresents the physical constraint that the gripper has a definite contents.

**Note on finite vs infinite domains:** When the domain of variables is finite, both items and properties *can* be modelled with either Dc or Neg/Pos — the choice is one of convenience and semantic fit, not necessity. With a finite item set you could enumerate all properties explicitly under Dc; with finite properties you could list them exhaustively under Neg. But when the domain is infinite (or open-ended), the right inference type matters: Dc naturally handles an unbounded property space (new properties can appear without invalidating existing terms), while Neg naturally handles selection from an unbounded item universe (unmentioned items are absent by default, no enumeration required).


## 4. Neg1 for Instances, Dc1 for Attributes

The key design principle:

> **Use Neg1 for leaf-level discrete choices (selecting instances from a domain).**
> **Use Dc1 for container classes whose sub-classes will be combined (AND'd) together.**

### Neg1: "Pick one from the set" (instances / items / enumeration)

Neg1 is the natural choice when a class represents a **discrete selection** — exactly one value from a finite domain. The Neg background ensures that all other values in the domain are implicitly *not selected*.

Examples:
- A **color** attribute: pick one color from {red, blue, green, ...}
- A **shape** attribute: pick one shape from {round, square, bear-like, ...}
- A **symbol** in a word: pick one character from the alphabet
- An **action** choice: pick one action from {eat, fight, pray, ...}

In all these cases, the class represents a single slot that holds exactly one value. There is no need to combine multiple independent selections within the same class — you are picking an *instance*.

### Dc1: "This is a container with independent sub-parts" (attributes / structure)

Dc1 is the natural choice when a class is a **structural container** — it groups sub-classes that each describe a different aspect, and those aspects will be independently specified and then combined.

Examples:
- A **visual object** has both a shape and a color → the object class is Dc1 so that `shape = bear-like` and `color = brown` can be AND'd together without conflict.
- A **sentence** has multiple word positions → the sentence class is Dc1 so that `word_at 1 "bear"` and `word_at 2 "brown"` can be AND'd together.
- A **scene** has both visual input and language rules → the top-level grouping is Dc1.

The Dc context acts as a wildcard: "I don't constrain the other sub-classes, so they can be filled in by other terms."

### Pos1: "Everything except these" (exclusion lists)

Pos1 is the mirror of Neg1. Where Neg1 assumes every value is *absent* unless explicitly included, Pos1 assumes every value is *present* unless explicitly excluded. This is useful when you want to describe a set by its exceptions rather than its members.

Example: from a domain of agents `{alice, bob, carol, dave}`, select everyone except Carol:

```haskell
-- Neg1 approach: explicitly list the included agents
P' [(agentClass, Neg1, P' [ (alice, Dc1, P'' [0])
                           , (bob,   Dc1, P'' [0])
                           , (dave,  Dc1, P'' [0]) ])]

-- Pos1 approach: only list the excluded agent
P' [(agentClass, Pos1, P' [ (carol, Dc1, P'' [0]) ])]
```

Both produce the same semantics, but Pos1 is more concise when the exclusion set is small relative to the domain. In practice, Neg1 is far more common because most modelling tasks select a small number of items from a large domain. Note that Pos variables in the same class are coupled just like Neg variables: `p_i AND p_j == Bot` for different exclusions in the same class, because different exclusion sets conflict. See [inference_contexts_and_tautologies.md](inference_contexts_and_tautologies.md) §7.5 for the full set of Pos-context algebraic identities.


## 5. Designing Class Hierarchies

### The Decision Rule

For each class in your hierarchy, ask:

> **"Will multiple terms that each specify different sub-classes of this class be AND'd together?"**

- **Yes** → Use **Dc1**. The class is a container/namespace. Its sub-classes are independent attributes.
- **No** → Use **Neg1** (or Pos1). The class is a leaf-level discrete choice. Exactly one value is selected.

### Worked Example: The Bears Model

The bear encounter rhyme model ([Examples.Bears](mdc:src/Examples/Bears.hs)) uses three top-level classes:

```
[1]       Visual Input    (Dc1)    — container for observed objects
  [1,i]   Object i        (Dc1)    — container for shape + color
    [1,i,1] Shape          (Neg1)  — pick one shape
    [1,i,2] Color          (Neg1)  — pick one color
[2]       Sentences       (Dc1)    — container for word positions
  [2,i]   Word i          (Dc1)    — container for symbol positions (AND'd with other words)
    [2,i,j] Symbol j      (Neg1)   — pick one symbol at position j
[3]       Actions         (Neg1)   — pick one action
```

Walking through the reasoning:

1. **Visual Input `[1]`** → `Dc1`. Multiple objects could be observed simultaneously. Object 1 and Object 2 would be AND'd together. Even with a single object, the class is a structural container.

2. **Object `[1,i]`** → `Dc1`. Each object has both a shape and a color, specified independently:
   `shape 1 ["bear-like"] .*. color 1 ["brown"]`
   Shape is sub-class `[1,i,1]` and color is `[1,i,2]`. These must combine, so the object class is Dc1.

3. **Sentences `[2]`** → `Dc1`. A sentence is built by AND'ing words at different positions:
   `word_at 1 "bear" .*. word_at 2 "brown" .*. word_at 3 "then" .*. ...`
   Each `word_at` specifies a different sub-class `[2,i]`. The sentence class must be Dc1 so these can combine.

4. **Word position `[2,i]`** → `Dc1`. Each word position is a container for its symbol positions. The word positions themselves are AND'd together within the sentence (e.g. `word_at 1 "bear" .*. word_at 2 "brown"`), so they use Dc1 context. The symbols *within* a word are constructed as a single path (not AND'd separately), but the word positions need Dc1 so they don't reject each other when combined.

5. **Actions `[3]`** → `Neg1`. An agent picks *one* action. No sub-classes to combine. The Neg1 context means that if no action is explicitly selected, the set is empty — no valid action exists.

The leaf-level classes (Shape, Color, Symbol) all use `Neg1` — they are discrete selections where you pick exactly one value from the domain.

### Common Pitfall

If you use Neg1 for a container class, AND'ing two terms that each specify *different* sub-classes will produce **Bot**. This is because Neg1 treats unmentioned sub-classes as "absent/rejected", so term A rejects the sub-classes mentioned by term B, and vice versa.

**Fix**: Change the container class to Dc1. The Dc context treats unmentioned sub-classes as "don't care", allowing them to be filled in by other terms during combination.

### Rule of Thumb

Think of your class hierarchy as a tree:
- **Internal nodes** (classes that branch into sub-classes) → **Dc1**
- **Leaf nodes** (classes that hold a single discrete value) → **Neg1**

This mirrors the distinction between a *record type* (struct with fields — Dc1) and an *enum type* (one-of-many — Neg1) in programming languages.

### Nested Context Semantics

When classes are nested, the **outer context** determines how the class itself interacts with its siblings, while the **inner context** determines how items within the class interact with each other. These are independent choices.

Consider a variable at position 2 inside a nested class. The notation `nn2` means Neg1 outer, Neg1 inner; `n'n2` means Neg0 outer, Neg1 inner; `nn'2` means Neg1 outer, Neg0 inner. Each has different semantics because the background at each level can differ.

**Variables at different nesting levels are always independent**, regardless of inference type. A variable in the outer class and a variable in the inner class live in different namespaces — they can always be AND'd without contradiction, even if both use Neg context.

When designing nested hierarchies:

- The **outer context** answers: "How does this class relate to its sibling classes?" If sibling classes will be AND'd together, the parent should use Dc1. If the class represents a discrete choice among siblings, the parent should use Neg1.
- The **inner context** answers: "How do items within this class relate to each other?" If items are independent attributes, use Dc1. If items are mutually exclusive selections, use Neg1.

In the Bears model, the nesting follows this pattern:
- Visual Input (Dc1 outer) → Object (Dc1 inner): objects are independent containers, and their attributes are independent.
- Object (Dc1 outer) → Shape (Neg1 inner): shape is one attribute slot, and you pick exactly one shape.

See [inference_contexts_and_tautologies.md](inference_contexts_and_tautologies.md) §3.4 for the formal analysis of multi-level and nested domain effects.


## 6. The MDD Modelling Design Space

When designing an MDD model, each class involves a choice along several axes. Understanding this design space helps ensure systematic coverage and avoid blind spots.

### Axis 1: Inference Type (3 values)

Dc, Neg, or Pos — determines the elimination rule and implicit default for unmentioned variables.

### Axis 2: Background Suffix (2 values)

1-suffix (background = False) or 0-suffix (background = True) — determines the default leaf value. Together with Axis 1, this gives 6 construction literals: `Dc1`, `Dc0`, `Neg1`, `Neg0`, `Pos1`, `Pos0`.

### Axis 3: Same-Class vs Cross-Class

Variables in the **same class** are subject to implicit coupling under Neg/Pos (see §2). Variables in **different classes** are always independent. This distinction is critical when deciding whether two terms can be AND'd.

### Axis 4: Nesting Depth

- **Flat** (single class level): the simplest case.
- **2 levels** (class containing class): outer and inner contexts can differ.
- **3+ levels** (deeply nested): each level adds an independent context choice.

### Axis 5: Homogeneous vs Mixed Context

- **Homogeneous**: all terms use the same inference context for a given class.
- **Mixed**: different terms use different contexts for the same class (e.g., context switching in §9). Mixed contexts follow the dominance rules in §10.

### Using the Design Space

For each class in your model, you are choosing a point in this space. The axes interact:

- A Dc1 container (Axis 1) with independent sub-classes (Axis 3: cross-class) at 2 nesting levels (Axis 4) is the standard structural pattern.
- A Neg1 leaf (Axis 1) with same-class mutual exclusion (Axis 3) at flat depth (Axis 4) is the standard enumeration pattern.
- A mixed-context bounding term (Axis 5) that switches a Dc1 container to Neg1 (Axis 1) is the context-switching pattern from §9.

See [inference_contexts_and_tautologies.md](inference_contexts_and_tautologies.md) §4 for the full combinatorial analysis of this design space, including its implications for testing.


## 7. Path Construction Reference

The top level of every valid MDD is implicitly in `Dc1` context. Paths are built with two constructors from `MDD.Types`:

```haskell
data Path
  = P'' [Int]                      -- Terminal: variable positions within the current class
  | P' [(Int, InfL, Path)]         -- Class prefix: (class_id, inference_type, nested_path)
```

`InfL` is one of `Dc1`, `Dc0`, `Neg1`, `Neg0`, `Pos1`, `Pos0`. The `1`/`0` suffix determines the default leaf value used for the background during construction: with `Dc1`/`Neg1`/`Pos1` the constructor sets the background leaf to `False` (0), while with `Dc0`/`Neg0`/`Pos0` it sets the background leaf to `True` (1).

### The Background Suffix: 1 vs 0

The suffix controls the **default truth value** for the dc branch of the ClassNode, which determines what `Unknown` nodes resolve to during traversal and how the `absorb` function determines redundancy.

- **1-suffix** (`Dc1`, `Neg1`, `Pos1`): Background defaults to `False` (leaf 0). The term describes a region carved out of an otherwise-false space. This is the common case — you are specifying what *is* true.
- **0-suffix** (`Dc0`, `Neg0`, `Pos0`): Background defaults to `True` (leaf 1). The term describes exceptions carved out of an otherwise-true space. This is used when you want to specify what *is not* true.

The 1-suffix and 0-suffix for the same inference type and variable are **complements**: their AND is always Bot and their OR is always Top. For example, `n2` (Neg1) and `n'2` (Neg0) for the same variable describe opposite regions of the same class.

In practice, 1-suffix variants (`Dc1`, `Neg1`, `Pos1`) are far more common. The 0-suffix variants are useful for:
- Expressing "everything in this class is true except ..." (Neg0 as an alternative to Pos1 with different graph structure).
- Constructing complements without using the negation operator.

See [inference_contexts_and_tautologies.md](inference_contexts_and_tautologies.md) §2.2 for the full semantic analysis of 1/0 suffix interactions.

### Reading a Path

Each `(class_id, InfL, Path)` tuple opens a ClassNode at `class_id`, places the nested `Path` on the branch determined by `InfL`, and closes the class (EndClassNode) when the nested path terminates. Sibling tuples in the same `P'` list are sibling sub-classes at the same hierarchy level.

### Worked Example

Goal: a `Dc1` top-level class (class 0) containing a `Neg1` sub-class (class 1) with four `Dc1` children — three wildcards and one with variable 5 positively evaluated.

```haskell
P' [( 0, Dc1,                       -- open class 0 on Dc branch
      P' [( 1, Neg1,                 -- open class 1 on Neg branch (bg = False)
            P' [ (0, Dc1, P'' [0])   -- sub-class 0: wildcard (Top)
               , (1, Dc1, P'' [0])   -- sub-class 1: wildcard (Top)
               , (2, Dc1, P'' [0])   -- sub-class 2: wildcard (Top)
               , (3, Dc1, P'' [5])   -- sub-class 3: variable 5 = True
               ]
          )]
   )]
```

Key conventions:
- `P'' [0]` inside `Dc1` produces an EndClassNode (wildcard / Top for that sub-domain — see §8).
- `P'' [5]` creates a standard node at position 5 with a positive evaluation.
- `P'' [-5]` would create a node at position 5 with a negative evaluation.
- `path` / `var` from `MDD.Extra.Interface` turn a `Path` into an `MDD`.
- `add_path` from `MDD.Construction` adds a `Path` to an existing `MDD` without going through a binary operation, which can be useful for incrementally building up an MDD.


## 8. Wildcards: Expressing "Don't Care" with `Dc1` and `P'' [0]`

When building paths, you sometimes need to express "any value is acceptable here" — a wildcard. The MDD mechanism for this is `Dc1` context combined with `P'' [0]` (the "Top trick").

### The `P'' [0]` Convention

In `MDD.Construction`, a `P'' [0]` terminal inside a `Dc1` context is treated specially: instead of creating a node at position 0, it produces an `EndClassNode` that immediately closes the class — effectively saying "this entire sub-class is unconstrained." The result is equivalent to Top within that class scope.

### Wildcard at Different Levels

Wildcards can be applied at any level of the hierarchy:

**Wildcard symbol** (any character at a position within a word):
```haskell
-- In wordPath, '*' at symbol position j means "any symbol here"
symbolEntry j '*' = (j, Dc1, P'' [0])   -- instead of (j, Neg1, P'' [symbol_id])
```

**Wildcard word** (any word at a position within a sentence):
```haskell
-- In word_at, "*" means "any word at this position"
word_at pos "*" = var $ sentence_label $ P' [(pos, Dc1, P'' [0])]
```

**Wildcard class** (any value in an entire class):
```haskell
-- Top: unconstrained across all classes
var (P'' [0])
```

### When to Use Wildcards

Wildcards are useful when a term should **partially constrain** a structure — specifying some positions while leaving others open. For example, the sentence `["bear", "brown", "*", "*"]` constrains words 1 and 2 but accepts any words at positions 3 and 4. This is essential for:

- **Partial matching**: Scene rules that map visual input to only the first two words of a sentence, leaving the rest unconstrained.
- **Bridge rules**: Implications that only care about one position (e.g. "if word 4 is X, then action X"), using wildcards for all other positions.


## 9. Bounding Open-Ended Structures with Context Switching

When a container class (Dc1) has a variable number of sub-classes — like a sentence with an arbitrary number of word positions — you need a way to **close off** the structure and say "no more sub-classes beyond this point."

### The End-of-Sentence Pattern

The Bears model demonstrates this with `end_of_sentence`:

```haskell
end_of_sentence :: Int -> MDD
end_of_sentence n = var $
    P' [(2, Neg1, P' [(j, Dc1, P'' [0]) | j <- [1..n]])]
```

This switches the sentence class `[2]` from its usual `Dc1` context to `Neg1` context. Under `Neg1`, any word position **not** explicitly listed is inferred as absent (rejected). The positions `1..n` are listed with `Dc1` + `P'' [0]` (wildcard), meaning "these positions exist but I don't constrain their content." Any position beyond `n` is implicitly absent.

### Why Context Switching Works

The key insight is that a single class can appear under **different inference contexts in different terms**, and these are combined during AND:

- `word_at 1 "bear"` places word 1 under `Dc1` context (don't care about other positions).
- `end_of_sentence 4` places the sentence under `Neg1` context (reject positions beyond 4).

When AND'd together, the `Dc1` terms fill in specific word content, while the `Neg1` term bounds the sentence length. The result is a fully specified sentence: exactly 4 words with specific content, and nothing beyond.

### General Pattern

To bound a variable-length Dc1 container to exactly `n` sub-classes:

1. Create a `Neg1` term for the container class.
2. List positions `1..n` with `Dc1` + `P'' [0]` (wildcard) as content.
3. AND this bounding term with the content terms.

The `Neg1` context rejects any sub-class not in the explicit list, effectively closing the container. This pattern relies on the cross-context dominance rules described in §10. See also [inference_contexts_and_tautologies.md](inference_contexts_and_tautologies.md) §6.2 Gap 9 for a discussion of testing this pattern.


## 10. Cross-Context Interaction Rules

When terms constructed under different inference contexts are combined, the result follows predictable dominance rules. Understanding these rules is essential for patterns like context switching (§9) and bridge rules (§11).

### Dominance Table

| Combination | AND behavior | OR behavior |
|---|---|---|
| **Dc AND Neg** | Dc acts as wildcard; result follows Neg constraints. `dc_i AND n_i == n_i`. | Dc subsumes Neg. `dc_i OR n_i == dc_i`. |
| **Dc AND Pos** | Dc accepts Pos constraints. `dc_i AND p_i == p_i`. | Dc subsumes Pos. `dc_i OR p_i == dc_i`. |
| **Neg AND Pos** (same class) | Usually Bot — conflicting defaults (Neg assumes absent, Pos assumes present). | Depends on specific variables. |
| **1-suffix AND 0-suffix** (same type) | Always Bot — opposite backgrounds. `n_i AND n'_i == Bot`. | May produce Top. `n'_i OR n'_j == Top`. |

### The General Principle

Under AND, **the more restrictive context dominates**. Dc is the least restrictive (it constrains nothing it doesn't mention), so it defers to Neg or Pos. Neg and Pos are both maximally restrictive (they constrain *every* variable in the class), so combining them usually produces a contradiction.

Under OR, **the more permissive context subsumes**. Dc is the most permissive, so `dc_i OR n_i == dc_i` — the Dc term already includes everything the Neg term describes and more.

### Cross-Context Pitfalls

- **Neg AND Pos in the same class**: Avoid this unless you specifically want Bot. Neg assumes unmentioned items are absent; Pos assumes they are present. These defaults contradict.
- **Mixing 1-suffix and 0-suffix for the same variable**: This always produces Bot under AND (they are complements). Under OR it produces Top. This can be useful for constructing tautologies but is usually a modelling error.

See [inference_contexts_and_tautologies.md](inference_contexts_and_tautologies.md) §3.3 for the full cross-context interaction analysis, including nested and multi-level cases.


## 11. Bridge Rules: Connecting Classes with Implications

Different classes in an MDD model are structurally independent — they live in separate branches of the hierarchy. To create **semantic connections** between classes, you use implication rules.

### The Word-to-Action Bridge

In the Bears model, the 4th word of a sentence determines which action is activated. This connection is expressed as a bridge rule:

```haskell
word4_to_action :: MDD
word4_to_action = conSet
  [ sentence ["*", "*", "*", x] .->. action x
  | x <- Map.keys actions
  ]
```

For each known action word `x`, this creates an implication: "if the 4th word of the sentence is `x`, then action `x` is activated." The conjunction of all these implications means every action word maps to exactly its corresponding action.

### How Bridge Rules Work

A bridge rule has the form: `(constraint in class A) .->. (constraint in class B)`

The implication `.->.` is defined as `a .->. b = (-.) a .+. b`, which means "either the condition is false, or the consequence holds." When AND'd with other knowledge:

- If the condition in class A is satisfied, the consequence in class B is enforced.
- If the condition in class A is not satisfied, the implication is trivially true and doesn't constrain class B.

### Design Pattern

To connect a value in one class to a value in another:

1. **Enumerate** all possible mappings (e.g. each action word maps to its action).
2. For each mapping, create an **implication** from the source class constraint to the target class constraint.
3. Use **wildcards** for positions in the source that are irrelevant to the mapping.
4. Take the **conjunction** of all implications.

The target class should typically use `Neg1` context so that if no source value matches (e.g. no single action word is determined), the target set is empty — a safe default that prevents spurious activations.
