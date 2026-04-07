Mixed Decision Diagrams (MDD) Project Documentation

This document describes the design and implementation of a Mixed Decision Diagram (MDD) project. The core innovation of this project is the unification of continuous and discrete set modeling within a single, canonical graph structure.


1. Executive Summary & Theoretical Relation

The MDD Concept

A Mixed Decision Diagram (MDD) is an extension of traditional Binary Decision Diagrams (BDDs) designed to model complex domains where continuous regions and discrete exceptions coexist. Unlike standard BDDs that strictly branch on boolean variables, MDDs use a sophisticated hierarchy of Infnodes and Branch Types to represent different inference and elimination rules.

Inference & Elimination Rules

The MDD structure utilizes three primary types of branches, grouped by five  semantic roles:

DC (Don't Care / Continuous): Used in a branch representing a continuous area. This serves as the "default"  evaluation for a specific variable class, as dont-care inference is usually assumed in logic (if there is no information about a varrible, its variable evaluation has no influence on any path evaluation in the diagram).

 (neg1, pos1): These branches represent a finite set of exceptions to an area that would otherwise evaluate to $0$ (False).

(neg0, pos0): These branches represent a finite set of exceptions to an area that would otherwise evaluate to $1$ (True).

neg1 and neg0 branches can represented in a single branch (type).
pos1 and pos0 can represented in a single branch (type). 

The dc stands for dont-care literal inference/elimination rule, which means that on that branch the nodes from which the positive evaluation and negative evaluation lead to the same child node / subgraph, are eliminated and inferred during traversal / interpretation.
The pos stands for the positive literal inference/elimination rule, which means that on that branch the nodes which only have their positive evaluation as a valid path (i.e. their negative evaluation leads to Uknown) are eliminated and inferred during traversal / interpretation.
The neg stands for the negative literal inference/elimination rule, which means that on that branch the nodes which only have their positive evaluation as a valid path (i.e. their positive evaluation leads to Uknown) are eliminated and inferred during traversal / interpretation.

Hierarchical Variable Classes

Variable classes are managed through Infnodes. Each Infnode acts as a prefix, allowing for complex combinations:

An Infnode prefix of [Infnode 1, Infnode 3] followed by variable nodes represents a different class than [Infnode 2, Infnode 3].

This structure enables the representation of multi-layered variable dependencies where "normal" nodes reside within specific class-indexed environments.


2. Architectural Design

The Context Manager

The Context (defined in MDD.hs) is the central state manager for all MDD operations. It contains:

NodeLookup: A HashMap (NodeId to entries) storing all unique nodes.

Cache: A memoization table for binary operations (like union or intersection) to prevent redundant computations.

dc_stack: A specialized structure ([Node], [Node], [Node]) representing dcA, dcB, and dcR. This tracks the hierarchy of continuous branches as the algorithm descends into sub-classes.

Usually MDDs are represented by a tuple of a root NodeId and a Context manager object containing the nodelookup. For combining 2 MDD’s with a binary operator, first the Contexts are combined (by merging the nodelookups of the Contexts, and reinitializing the cache and dc_stack) before running the traversal function which computes the resulting MDD. There are also versions of the cache and dc_stack for unary functions. 

Node Representation (Dd Data Type)

The project represents logic through several node constructors:

Leaf Bool: Terminal / leaf evaluations ($0$ or $1$).

Unknown: A lazy leaf value that triggers a lookup in the corresponding dc branch of the current or previous layer.

Node Int NodeId NodeId: A standard branching node (Variable local position, branch following a positive evaluation of the variable, branch following a negative evaluation of the variable).

InfNodes Int NodeId NodeId NodeId: A class-defining node containing branches for Dc, Neg, and Pos.

EndInfNode NodeId: A marker that signals the end of the current class context and moves the path resolution one layer up the hierarchy.


3. Core Algorithms

The dc_stack and Unknown Resolution

The dc_stack is essential for resolving the mixing of the diagram during traversal.

dcR: The resulting continuous branch for the current Infnode layer. It is used primarily by the absorb function to check, after finalizing a new branch in the traversal function of a operator on MDDs, if a branch evaluates to the same result as the continuous area of the same (or previous) layer(s), allowing for its elimination.

dcA & dcB: When an Unknown leaf is encountered during a binary operation, the algorithm cascades through these lists to find the actual evaluation in the continuous area of the same (or previous) layer(s).

Traversal and "Catch-up"

In SODDmanipulation.hs, the traverse_dc function synchronizes the traversal of the main MDD with the continuous branches in the dc_stack.
If a branch in the main MDD skips a variable (due to an elimination rule), the catchup logic ensures the dc components do not "lag behind." It uses the specific inference rule of the current type (e.g., Dc, Pos, or Neg) to infer the missing nodes dynamically.

Redundancy Elimination (absorb)

To maintain a canonical and minimal graph, the absorb function checks, given a node, all its subgraph outcomes against its corresponding (of the same class layer) continuous area (dcR). If a discrete branch’s evaluation matches the continuous background, the branch is redundant and is "absorbed" (eliminated), resulting in a maximally reduced graph.

Pathing and Static Translation

- Parsing: During parsing a variable is identified by its 5 semantic roles, thus the input to a construct a node is a path like [1 Neg1, 2 Pos0, 5], this indicates whether the “background” dc (the continuous area in which the path represents an exception) at that level should be True/1 (for neg0, pos0) or False/0 (for neg1, pos1). 

- Paths: Node addresses/ids are relative to the path taken from the root node through the class/infnodes (and which branch types were taken), e.g., [Dc 1, Neg 2, Pos 5]. The top level of a valid MDD is always in Dc context, thus currently the paths are represented in the style of[1 Neg, 2 Pos, 5].

- Levels: The (vertical) level is derived by stripping the class information: [1, 2, 1, 5].

- Static Mapping: While manipulation occurs with relative positions to allow for dynamic variable insertion, a static translation is provided for visualization. This assigns a fixed global order to all declared variables for consistent Graphviz rendering.


4. Codebase Mapping (After Refactor)

The refactored codebase is organized into focused modules with clear responsibilities:

**Core Type Definitions** (`MDD.Types`)
- `MDD`: Newtype wrapper `newtype MDD = MDD { unMDD :: (NodeLookup, Node) }`
- `Dd`: Core decision diagram data structure (Node, InfNodes, EndInfNode, Leaf, Unknown)
- `Inf`: Inference types (Dc, Neg, Pos)
- `NodeId`, `Node`, `NodeLookup`: Node identification and storage
- `Level`, `Level'`, `Position`: Path and level representations
- `Path`, `LevelL`, `InfL`: Construction-time path representations

**Context Management** (`MDD.Context`)
- `BiOpContext`: Context for binary operations (union, intersection)
  - Contains: `bin_nodelookup`, `bin_cache`, `bin_dc_stack`, `bin_current_level`
- `UnOpContext`: Context for unary operations (negation)
  - Contains: `un_nodelookup`, `un_cache`, `un_dc_stack`, `un_current_level`
- `DrawOperatorContext`: Context for visualization
  - Contains: `draw_nodelookup`, `draw_cache`
- `HasNodeLookup`: Typeclass for unified access to NodeLookup across context types
- Initialization functions: `init_binary_context`, `init_unary_context`, `init_draw_context`

**Node Management** (`MDD.Manager`)
- `init_lookup`: Initial NodeLookup with standard leaf nodes
- `insert_id`: Core insertion logic into NodeLookup
- `unionNodeLookup`: Merges two NodeLookups, summing reference counts
- `Hashable` instance for `Dd` for canonical representation

**Operations** (`MDD.Ops.Binary`, `MDD.Ops.Unary`)
- Binary operations: `apply` (union, intersection, etc.)
- Unary operations: `negation`, `restrict_node_set`
- Both modules use operation-specific contexts and caching

**Construction** (`MDD.Construction`)
- `path`: Creates MDD from Path description
- `makeNode`: Creates MDD from LevelL
- `add_path`: Adds a path to existing MDD

**Public Interface** (`MDD.Interface`)
- Constants: `top`, `bot`, `unk`
- Operators: `(-.)`, `(.*.)`, `(.+.)`, `(.->.)`, `(.<->.)`
- Helpers: `var`, `var'`, `ite`, `xor`, `restrict`
- Set operations: `conSet`, `disSet`, `xorSet`
- Quantification: `forall`, `exist`, `forallSet`, `existSet`
- Utilities: `relabelWith`, `substitSimul`

**Visualization** (`MDD.Draw`)
- `settings`: Configuration for display
- `show_dd`: String representation of MDD nodes
- Graph generation and rendering utilities
- debugging code

**Static Translation** (`MDD.Static`)
- `to_static_form`: Converts MDD to static form for visualization
- `StaticNodeLookup`, `NodeStatic`: Static representation types

**SMCDEL Integration**
- `SMCDEL.Symbolic.K_MDD`: Kripke-style knowledge structures using MDD
  - `BelStruct`: Belief structures with MDD state laws
  - `RelMDD`: Tagged MDD for relational operations
  - `mddOf`: Formula to MDD translation for epistemic logic
- `SMCDEL.Symbolic.S5_MDD`: S5 knowledge structures
  - `KnowStruct`: Knowledge structures with MDD laws
  - `boolMddOf`: Boolean formula to MDD translation
  - `mddOf`: Epistemic formula to MDD translation



1. Questions and answers:


1. The dc_stack structure: In MDD.hs, dc_stack is defined as ([Node], [Node], [Node]). Is it used to track the hierarchy of Infnodes as you descend into sub-classes?
1. the dc_stack structure is used to track the hierarchy of Infnodes as you descend into sub-classes. It represents dcA, dcB and dcR respectively. dcR is the resulting continuous dc branch of the current infnode context / subgraph. See in calculating the of the current InfNode, in applyinf, that first the dcR is calculated, then the neg and pos components.


dcR is mainly used for checking whether the final result needs to be absorbed.

dcA and dcB are the dc components of the input arguments when calling applyinf, and are mainly used when replacing an encountered Unknown leaf branch with a evaluation of the previous layer.

As a previous layer of the dc's can also evaluate to Unkown, all previous layers are tracked along and Unknown evaluations can be resolved by cascading along the list. The latest encountered dc branches are in the first position of the stack.



1. Does EndInfNode act as a pointer back to a specific class level?
1. For a path containing variable evaluations, EndInfNode indicates the end of the current class, going back a hierachical level up to the previous InfNode class variable.

An example will make this clearer:

current position of a traversal in a MDD graph [dc 1, neg 3, neg 4]. If the next node is a 5 then the next position would be [dc 1, neg 3, neg 5]. If first a endinfnode is encountered and then a node with position 5 then the position would be [dc 1, neg 5].


2. parsing paths to nodes in MDD.hs use weird int comparison tricks?
2. 0 in parsing paths for node initialization is taken as trick to represent Top (in Dc1) or Bot (in Dc0). a negative number in parsing paths for node initialization is taken to be a negative evaluation of the variable (should the pos / neg not already be able to indicate this? maybe we can fix this later).





to build the project use "cabal build" in the project home folder.



future addons:
- fix absorb for unary stuff
- refactor elimrules

- add colorized drawtree setting
- add better equality check for eq instance of MDD
- double check whether elim rules are applied to path constructurs eventhough the parse input gets eliminated (e.g. -1 in neg1)
- clean up type signatures