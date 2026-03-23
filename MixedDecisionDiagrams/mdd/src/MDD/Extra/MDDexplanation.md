Mixed Decision Diagrams (MDD) Project Documentation

The project provide a MDD library, which is set up to represent logic statements and thereby be able to model all kinds of systems that can be described with at least first order logic.
The core extensions of this project over a classic BDD library is:
- functionality for modelling variable domains / classes has been added.
- the mixing of elimination rules with paths representing areas in continuous domains (with DC inference) and discrete domains (with Pos or Neg inference) within a single, canonical graph structure.
These features allows for modelling second-order-logic-like statements.

This file is made with help of AI.

# Executive Summary & Theoretical Relation

## The MDD Concept

A Mixed Decision Diagram (MDD) is an extension of traditional Binary Decision Diagrams (BDDs) designed to model complex domains where continuous regions and discrete exceptions coexist. Unlike standard BDDs that strictly branch on a finite number of boolean variables, MDDs uses ClassNode and EndClassNode to represent the opening and closing of a class domain in the current path - and Branch Types to represent different inference and elimination rules.

## Hierarchical Variable Classes

Variable classes in MDDs are managed through **ClassNode**, which create hierarchical domains that can be nested to arbitrary depth. Each ClassNode acts as a prefix that establishes a class context, and variables within that context are scoped to that class. This hierarchical structure enables the representation of complex multi-layered variable dependencies where "normal" nodes (standard BDD-style branching nodes) reside within specific class-indexed environments.

### Understanding the Hierarchy

A **ClassNode** is a special node type that opens a class domain.

When you traverse through a ClassNode, you enter a new class context. Variables encountered after entering this context belong to that class. If you encounter another ClassNode while already in a class, you enter a nested sub-class, creating a hierarchy.

### Path Representation

The hierarchy is represented using the `Path` data structure during construction:

```haskell
data Path = P'' [Int]                    -- Terminal: variable positions
          | P' [(Int, InfL, Path)]       -- Class prefix: (class_id, inference_type, nested_path)
```

- `P'' [Int]` represents a terminal path with variable positions
- `P' [(Int, InfL, Path)]` represents a class prefix, where each element is `(class_id, inference_type, nested_path)`

The nested `Path` inside `P'` allows for arbitrary nesting depth.

### Class Prefixes and Variable Identity

The key insight is that **the full path through the class hierarchy determines variable identity**. Two variables with the same local position but different class prefixes are completely different variables:

- `[ClassNode 1, ClassNode 3, variable 5]` represents a different variable than
- `[ClassNode 2, ClassNode 3, variable 5]`

Even though both end with "variable 5" and both pass through "ClassNode 3", the different outer class (1 vs 2) makes them distinct.

### EndClassNode: Closing a Class

When traversing through the hierarchy, an **EndClassNode** marks the end of the current class context and returns to the parent class. For example:

- Current position: `[Dc 1, Neg 3, Neg 4]` (in class 1, sub-class 3, variable 4)
- Encounter EndClassNode
- New position: `[Dc 1, Neg 4]` (back in class 1, now at variable 4)

This allows the MDD to efficiently represent cases where a sub-class is "closed" and we return to the parent class context.

### Practical Benefits

The hierarchical class system enables:

1. **Namespace Separation**: Different semantic domains (words, shapes, feelings) can use the same local variable indices without conflict
2. **Scalable Modeling**: New classes can be added without affecting existing variable indices
3. **Efficient Representation**: Related variables can share class contexts, reducing redundancy
4. **Complex Domain Modeling**: Supports second-order-logic-like statements where variables range over different domains

### Construction Process

When constructing an MDD from a `Path`, the `path'` function in `Construction.hs` recursively processes the hierarchy:

1. For each `(class_id, inference_type, nested_path)` in `P'`:
   - Create an `ClassNode` node with the appropriate inference type
   - Recursively process the nested path to create the child structure
   - The nested path may itself contain more `P'` structures, creating deeper nesting

2. For terminal `P'' [Int]`:
   - Create standard `Node` structures for each variable position
   - These nodes are scoped to the current class context established by the ClassNode above them

This recursive construction naturally builds the hierarchical structure, with each level of nesting corresponding to a deeper class level in the MDD graph.

## Inference & Elimination Rules

A ClassNode has three types of outgoing edges, one branch for each inference / elimination rule that applies for traversal during that (sub)class:

DC (Don't Care / Continuous): Used in a branch representing a continuous area. This serves as the "default"  evaluation for a specific variable class, as dont-care inference is usually assumed in logic (if there is no information about a varrible, its variable evaluation has no influence on any path evaluation in the diagram).
The dc stands for dont-care literal inference/elimination rule, which means that on that branch the nodes from which the positive evaluation and negative evaluation lead to the same child node / subgraph, are eliminated and inferred during traversal / interpretation.

Dc inference is often used as default when taking variables to be acting as properties / atribute-labels (of a state or object). e.g. colors, is-it-raining, is-sally-present

The pos stands for the positive literal inference/elimination rule, which means that on that branch the nodes which only have their positive evaluation as a valid path (i.e. their negative evaluation leads to Uknown) are eliminated and inferred during traversal / interpretation.
The neg stands for the negative literal inference/elimination rule, which means that on that branch the nodes which only have their positive evaluation as a valid path (i.e. their positive evaluation leads to Uknown) are eliminated and inferred during traversal / interpretation.

Pos and Neg inference are usually the default when describing item sets / objects. The class variable then represents all posible items and the positive evaluations are the items that are present. e.g. from all agents, take Alice and Bob (Neg inference for all other agents). Or take all agents except for Carrol (Pos inference for all agents except Carrol).




# Architectural Design

The Context Manager

The Context (defined in `MDD.Traversal.Context`) is the central state manager for all MDD operations. It contains:

NodeLookup: A HashMap (NodeId to entries) storing all unique nodes.

Cache: A memoization table for binary operations (like union or intersection) to prevent redundant computations.

dc_stack: A specialized structure ([Node], [Node], [Node]) representing dcA, dcB, and dcR. This tracks the hierarchy of continuous branches as the algorithm descends into sub-classes.

Usually MDDs are represented by a tuple of a root NodeId and a Context manager object containing the nodelookup. For combining 2 MDD's with a binary operator, first the Contexts are combined (by merging the nodelookups of the Contexts, and reinitializing the cache and dc_stack) before running the traversal function which computes the resulting MDD. There are also versions of the cache and dc_stack for unary functions. Context conversion helpers (`binaryToUnaryContext` and `unaryToBinaryContext`) allow switching between binary and unary contexts, used by the `absorb` function which runs as a unary operation within a binary traversal.

Node Representation (Dd Data Type)

The project represents logic through several node constructors:

Leaf Bool: Terminal / leaf evaluations ($0$ or $1$).

Unknown: A lazy leaf value that triggers a lookup in the corresponding dc branch of the current or previous layer.

Node Int NodeId NodeId: A standard branching node (Variable local position, branch following a positive evaluation of the variable, branch following a negative evaluation of the variable).

ClassNode Int NodeId NodeId NodeId: A class-defining node containing branches for Dc, Pos, and Neg (in that order).

EndClassNode NodeId: A marker that signals the end of the current class context and moves the path resolution one layer up the hierarchy.


# Core Algorithms

The dc_stack and Unknown Resolution

The dc_stack is essential for resolving the mixing of the diagram during traversal.

dcR: The resulting continuous branch for the current ClassNode layer. It is used primarily by the absorb function to check, after finalizing a new branch in the traversal function of a operator on MDDs, if a branch evaluates to the same result as the continuous area of the same (or previous) layer(s), allowing for its elimination.

dcA & dcB: When an Unknown leaf is encountered during a binary operation, the algorithm cascades through these lists to find the actual evaluation in the continuous area of the same (or previous) layer(s).

Traversal and "Catch-up"

In `MDD.Traversal.Support`, the `traverse_dc` function synchronizes the traversal of the main MDD with the continuous (background) branches in the dc_stack.
If a branch in the main MDD skips a variable (due to an elimination rule), the catchup logic ensures the dc components do not "lag behind." It uses the specific inference rule of the current type (e.g., Dc, Pos, or Neg) to infer the missing nodes dynamically. The shared `traverse_dc_generic` and `move_dc` functions (in `MDD.Traversal.Stack`) are used by both binary and unary traversal modules.

Redundancy Elimination (absorb)

To maintain a canonical and minimal graph, the absorb function checks, given a node, all its subgraph outcomes against its corresponding (of the same class layer) continuous area (dcR). If a discrete branch’s evaluation matches the continuous background, the branch is redundant and is "absorbed" (eliminated), resulting in a maximally reduced graph.

Pathing and Static Translation

- Construction: A variable's full identity is determined by its class prefix and its local position. The class prefix is a list of `(class_id, InfL)` pairs, where `InfL` is one of the 6 inference literals: `Dc1`, `Dc0`, `Neg1`, `Neg0`, `Pos1`, `Pos0`. During construction, the `1`/`0` suffix determines the default leaf value for the background: `Dc1`/`Neg1`/`Pos1` set the background to `False` (paths end in 0), while `Dc0`/`Neg0`/`Pos0` set the background to `True` (paths end in 1). This is represented in the MDD by setting the dc branch of the ClassNode for that (sub)domain to the corresponding leaf evaluation. A path like `Ll [(1, Neg1), (2, Dc1)] 5` describes a variable at local position 5, inside class 2 (Dc context, background=False), inside class 1 (Neg context, background=False).

- Paths: Node addresses are relative to the path taken from the root node through the ClassNode hierarchy (and which branch types were taken), e.g., `[Dc 1, Neg 2, Pos 5]`. The top level of a valid MDD is always in Dc context, so paths are represented in the style of `L [(1, Neg), (2, Pos)] 5`.

- Current level: The level is derived by stripping the inference information from the class prefix: `[1, 2, 5]`.

- Static Mapping: While manipulation occurs with relative positions to allow for dynamic variable insertion, a static translation is provided for visualization. This assigns a fixed global order to all declared variables for consistent Graphviz rendering.


1. Codebase Mapping (After Refactor)

The refactored codebase is organized into focused modules with clear responsibilities:

**Core Type Definitions** (`MDD.Types`)
- `MDD`: Newtype wrapper `newtype MDD = MDD { unMDD :: (NodeLookup, Node) }`
- `Dd`: Core decision diagram data structure (Node, ClassNode, EndClassNode, Leaf, Unknown)
- `Inf`: Inference types (Dc, Neg, Pos)
- `NodeId`, `Node`, `NodeLookup`: Node identification and storage
- `Level`, `Level'`, `Position`: Path and level representations
- `Path`, `LevelL`, `InfL`: Construction-time path representations

**Context Management** (`MDD.Traversal.Context`)
- `BiOpContext`: Context for binary operations (union, intersection)
  - Contains: `bin_nodelookup`, `bin_cache`, `bin_dc_stack`, `bin_current_level`
- `UnOpContext`: Context for unary operations (negation)
  - Contains: `un_nodelookup`, `un_cache`, `un_dc_stack`, `un_current_level`
- `DrawOperatorContext`: Context for visualization
  - Contains: `draw_nodelookup`, `draw_cache`
- `HasNodeLookup`: Typeclass for unified access to NodeLookup across context types
- Initialization functions: `init_binary_context`, `init_unary_context`, `init_draw_context`
- Context conversion: `binaryToUnaryContext` and `unaryToBinaryContext` for switching between binary and unary contexts (used by `absorb`)

**Node Management** (`MDD.NodeLookup`)
- `init_lookup`: Initial NodeLookup with standard leaf nodes
- `insert_id`: Core insertion logic into NodeLookup
- `unionNodeLookup`: Merges two NodeLookups, summing reference counts
- `Hashable` instance for `Dd` for canonical representation

**Traversal Operations** (`MDD.Traversal.Binary`, `MDD.Traversal.Unary`, `MDD.Traversal.Support`, `MDD.Traversal.Stack`)
- Binary operations: `apply` (union, intersection, etc.) in `MDD.Traversal.Binary`
- Unary operations: `negation`, `restrict_node_set` in `MDD.Traversal.Unary`. Unary traversal follows the same structural pattern as binary (dc_stack synchronization, inference rules, absorb) but operates on a single MDD with a simpler context (`UnOpContext`).
- Support functions: Inference rules (`DdF3` typeclass), elimination rules, and `absorb` in `MDD.Traversal.Support`
- Stack management: `MDD.Traversal.Stack` provides dc_stack manipulation functions, `move_dc` (shared helper to step into sub-branches), and `traverse_dc_generic` (shared dc traversal synchronization, used by both binary and unary modules)
- Both operation modules use operation-specific contexts and caching

**Construction** (`MDD.Construction`)
- `path`: Creates MDD from Path description
- `makeNode`: Creates MDD from LevelL
- `add_path`: Adds a path to existing MDD

**Public Interface** (`MDD.Extra.Interface`)
- Constants: `top`, `bot`, `unk`
- Operators: `(-.)`, `(.*.)`, `(.+.)`, `(.->.)`, `(.<->.)`
- Helpers: `var`, `var'`, `ite`, `xor`, `restrict`
- Set operations: `conSet`, `disSet`, `xorSet`
- Quantification: `forall`, `exist`, `forallSet`, `existSet`
- Utilities: `relabelWith`, `substitSimul`

**Visualization** (`MDD.Extra.Draw`, `MDD.Extra.Dot`)
- `settings`: Configuration for debugging display
- `show_dd`, `show_node`, `show_mdd`: String representation of MDD nodes
- `drawTree3`: Graph generation and rendering utilities in terminal
- `generateGraphImage`: Generate Graphviz dot and SVG files from MDD
- `generateAndShow`, `generateAndShow_c`, `generateAndShow_h`, `generateAndShow_ch`, `generateAndShow_cn`: Convenience functions for visualization
**Static Translation** (`MDD.Extra.Static`)
- `to_static_form`: Converts MDD to static form for visualization
- `StaticNodeLookup`, `NodeStatic`: Static representation types

**Formula-based Construction** (`SMCDEL.Symbolic.Bool`)
- `Form`: Algebraic data type for logical formulas (`Top`, `Bot`, `Negate`, `And`, `Or`, `Impl`, `PrpF`, `Var`)
- `ddOf`: Translates a `Form` into an `MDD`, threading a shared `NodeLookup`. `PrpF` creates a variable from a `LevelL`, `Var` embeds an existing `MDD`, and the logical connectives map to the corresponding MDD operators.
- `ddOf'`: Convenience variant that initializes a fresh `NodeLookup`.

**SMCDEL Integration**
- `SMCDEL.Symbolic.K_MDD`: Kripke-style knowledge structures using MDD
  - `BelStruct`: Belief structures with MDD state laws
  - `RelMDD`: Tagged MDD for relational operations
  - `mddOf`: Formula to MDD translation for epistemic logic
- `SMCDEL.Symbolic.S5_MDD`: S5 knowledge structures
  - `KnowStruct`: Knowledge structures with MDD laws
  - `boolMddOf`: Boolean formula to MDD translation
  - `mddOf`: Epistemic formula to MDD translation



# Questions and answers:


1. The dc_stack structure: In `MDD.Traversal.Context`, dc_stack is defined as ([Node], [Node], [Node]). Is it used to track the hierarchy of ClassNode as you descend into sub-classes?
1. the dc_stack structure is used to track the hierarchy of ClassNode as you descend into sub-classes. It represents dcA, dcB and dcR respectively. dcR is the resulting continuous dc branch of the current ClassNode context / subgraph. See in calculating the of the current ClassNode, in applyInf, that first the dcR is calculated, then the neg and pos components.


dcR is mainly used for checking whether the final result needs to be absorbed.

dcA and dcB are the dc components of the input arguments when calling applyInf, and are mainly used when replacing an encountered Unknown leaf branch with a evaluation of the previous layer.

As a previous layer of the dc's can also evaluate to Unkown, all previous layers are tracked along and Unknown evaluations can be resolved by cascading along the list. The latest encountered dc branches are in the first position of the stack.



1. Does EndClassNode act as a pointer back to a specific class level?
1. For a path containing variable evaluations, EndClassNode indicates the end of the current class, going back a hierarchical level up to the previous ClassNode class variable.

An example will make this clearer:

current position of a traversal in a MDD graph [dc 1, neg 3, neg 4]. If the next node is a 5 then the next position would be [dc 1, neg 3, neg 5]. If first a EndClassNode is encountered and then a node with position 5 then the position would be [dc 1, neg 5].


1. how does parsing paths to nodes in MDD.hs use ints to determine what kind of literal / evaluation the node represents?
2. 0 in parsing paths for node initialization is taken as trick to represent Top (in Dc1) or Bot (in Dc0). a negative number in parsing paths for node initialization is taken to be a negative evaluation of the variable (should the pos / neg not already be able to indicate this? maybe we can fix this later).



# future addons:

- add colorized drawtree setting
- add better equality check for eq instance of MDD
- double check whether elim rules are applied to path constructurs eventhough the parse input gets eliminated (e.g. -1 in neg1)
- clean up type signatures
- cull the unknowns out of the dc_stack
- more efficient ifte implementation
- write about why absorb does not need the other inference cases?
- dc catchup?
- tests for returning to ZDD inference, catchup in
- more efficient pop stack
- naive relabel (just change the numbers, do have to reindex in hashmap after traversal)

- fun parser
- hashing with level


- nasty bug:
```dcA_leaf_cases c s a@(a_id, Leaf _) b@(b_id, ClassNode{}) = withCache c (a, b, s ++ "Dc") $
        applyInfA @Dc c s a b -- todo: by going in here we are "forgetting" we are processing a Dc at the moment, so when we pop back we need to continue with interDc```

- other potential bugs:
- does dc stack traversal handle endClassNode (catchup) correctly? do they have their own stack?