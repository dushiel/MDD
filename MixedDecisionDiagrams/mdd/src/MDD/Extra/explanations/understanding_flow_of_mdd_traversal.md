# Understanding the Flow of MDD Traversal

## 1. High-Level Architecture

An MDD is `(NodeLookup, Node)` where:
- `NodeLookup` is a global hash-map of all unique nodes (keyed by `HashedId`)
- `Node = (NodeId, Dd)` is a pointer + the node data

The five `Dd` constructors:
| Constructor | Meaning |
|---|---|
| `Leaf Bool` | Terminal: True (1) or False (0) |
| `Unknown` | Lazy terminal — resolves by looking up the dc branch of the current/parent class layer |
| `Node Int NodeId NodeId` | Standard BDD branching node: (variable position, pos-child, neg-child) |
| `ClassNode Int NodeId NodeId NodeId` | Class-opening node: (class position, dc-branch, pos-branch, neg-branch) |
| `EndClassNode NodeId` | Class-closing marker: returns to parent class context |

All `Dd` nodes (except `Unknown`) have a deterministic position assigned by `nodePosition` in `MDD.Types`. `Node` and `ClassNode` use their integer position. `EndClassNode` uses `endClassPos` (which is `maxBound - 1`), and `Leaf` uses `leafPos` (which is `maxBound`), effectively placing them at "infinity" relative to standard nodes within a local domain. `Unknown` nodes cannot be positioned and must be resolved before structural comparison.

## 2. Binary Operations (e.g. Intersection `.*. `)

```haskell
(.*.) :: MDD -> MDD -> MDD
(.*.) (MDD (la, a)) (MDD (lb, b)) =
    let ctx = init_binary_context (unionNodeLookup la lb)
        (ctx', r) = apply modeDc ctx "inter" (fst a) (fst b)
    in MDD (getLookup ctx', r)
```

Key points:
- The two NodeLookups are merged first (`unionNodeLookup`)
- A fresh `BiOpContext` is created with an initial dc_stack of `([Unknown], [Unknown], [Unknown])`, this is an ephemeral context - existing only for the duration of the binary operation resolution.
- The recursive `apply` is called — it is a depth-first simultaneous traversal of the two input graphs / MDDs - where the top-level always starts with the `modeDc` (don't-care) traversal mode.
- The `TraversalMode` record (e.g., `modeDc`, `modeNeg`, `modePos`) dictates the inference and elimination rules for the local subbranches.

## 3. The traversal function: `apply` / `applyClass`

`apply` is the main binary operation entry point. It uses `withCache` for memoization, then dispatches based on the node types of A and B. The cache key is `(NodeId A, NodeId B, dc_stack state)` — the dc_stack is included because the same node pair can produce different results depending on the class hierarchy context (which ClassNode layers are currently active). The cache is a two-level map: function name (e.g. `"inter"`, `"union"`) → `(NodeId, NodeId, dc_stack)` → result NodeId.

The behaviour of the function is dependent on the current nodes of its input MDDs and the active `TraversalMode`:
- **Both `Node`**: Compares `nodePosition`s. If equal, recurses into children. If asymmetrical, infers the missing node (via `tmInferNodeA`/`tmInferNodeB` from the `TraversalMode`).
- **Both `ClassNode`**: Delegates to `applyClass` (which handles the dc_stack push/pop and recurses into dc/neg/pos branches).
- **Both `EndClassNode`**: Both sides exit their class simultaneously. The `endclass_case` function pops the inference type stack to determine which parent `TraversalMode` context to continue in.
- **Both Leaf**: Handled by `leaf_cases`, which determines the resulting leaf value (boolean operation between the two input leaves, based on whether union or intersection is applied) and is the end of the recursive traversal.
- **Unknown cases**: `Unknown` nodes are resolved by popping from the dc_stack and delegating back to `apply`, utilizing `DcSourced` compound modes to ensure correct inheritance of `Dc` behaviors.

Asymmetrical cases are resolved based on the position of the nodes and the local context determining the inference / elimination rules. Simultaneous traversal happens in such a manner that both branches should always be in the same local context, so they are constantly caught up to each other.

### `applyClass` — entering a class

MDDs are called Mixed Decision Diagrams because they have multiple mixed inference / elimination rules applied to branches that exist parallel to each other. Mixing them comes with special rules handled by `applyClass`:

```
applyClass tm c s a@(ClassNode positionA dcA pA nA) b@(ClassNode positionB dcB pB nB):
  1. traverse_dc "class dc" → sync dc_stack for dc branch
  2. add_to_stack (position, Dc) (Unknown, Unknown, Unknown)
  3. (c1, dcR) = apply modeDc c s_dc dcA dcB
  4. add_to_stack (position, tmToInf tm) (dcA, dcB, dcR)
  5. (c2, nR) = apply (tmNegClassInf tm) c1 s_n nA nB
  6. add_to_stack (position, tmToInf tm) (dcA, dcB, dcR)
  7. (c3, pR) = apply (tmPosClassInf tm) c2 s_p pA pB
  8. pop_stack, absorb, makeClassNode
```

Because there can be multiple nested classes, there can be multiple dcR / dcA / dcB 's on the stack as traversal progresses through the multiple classes.

The `reset_stack_bin` call between steps restores the dc_stack to its state before the `applyClass` call, so each branch computation starts from the correct baseline.

It is important that the resulting dc branch is calculated before the pos / neg branches - since the pos / neg branches are absorbed in the resulting dc branch (dcR) of this class. Where a pos / neg branch is absorbed, an Unknown node is left in its place. The absorb mechanism is further explained in section 7.

## 4. Structural ordering within a class layer

Within any single class layer (the content between entering a `ClassNode` and reaching its `EndClassNode`), the Dd nodes follow a strict local depth ordering based on `nodePosition`.

`EndClassNode` has a static position of `endClassPos` (maxBound - 1), and `Leaf` has a position of `leafPos` (maxBound). This ensures they are always "deeper" than any standard `Node` or `ClassNode` in the same class layer. When the `apply` dispatcher encounters an asymmetry, the branch with the smaller `nodePosition` is "behind" and has a node inferred for it based on the active `TraversalMode`.

`Unknown` nodes cannot be compared by position and will throw an error if attempted; they must be resolved with a node from the DC stack before structural comparison.

This gives the following local chart for determining what branch needs to have a node inferred (the smaller branch infers):
rootnode/initial classnode < (class)node with position i < (class)node with position j < endclass node < boolean leaf
where i and j are ints and i < j

## 5. Inference and `tmApplyElimRule` Instances

Node elimination is the opposite of inference and is performed whenever a result "determined" in the traversal function is passed back upwards.

Standard nodes are eliminated/inferred depending on their active `TraversalMode`:
| `modeDc` | nodes with the same child |
| `modeNeg` | nodes with the pos child leading to Unknown |
| `modePos` | nodes with the neg child leading to Unknown |

`ClassNode`s are also eliminated/inferred based on the context:
| `modeDc` | `ClassNode _ (EndClassNode childnode) (0,0) (0,0)` — only dc has content |
| `modePos` | `ClassNode _ (0,0) (EndClassNode childnode) (0,0)` — only pos has content |
| `modeNeg` | `ClassNode _ (0,0) (0,0) (EndClassNode childnode)` — only neg has content |

Endclassnodes that are directly above a boolean leaf node are eliminated. When a leaf node is compared with an endclassnode, another endclassnode is inferred for the leaf node branch.

## 6. Value-Level `TraversalMode` and `bin_current_level`

The project utilizes a value-level `TraversalMode` record to dynamically manage inference and elimination contexts. 

When a branch resolves an `Unknown` node by popping from the `dc_stack`, it effectively enters a state where it acts as a `Dc` branch (since it was sourced from the continuous background), even if the overarching operation is in a `Neg` or `Pos` context. 

To handle this smoothly across nested class boundaries, the `TraversalMode` dynamically composes "Compound Modes" (e.g., combining a `Neg` context for argument A with a `DcSourced` context for argument B). The `compoundMode` function accurately merges behaviors like `tmInferNode`, `tmApplyElimRule`, and how `Unknown` returns are handled based on the source of the branches.

`bin_current_level :: (Level', Level')` records the class hierarchy path for each operand. `Level'` is a stack of `(position, inference-type)` pairs. During traversal, `add_to_stack` pushes the inference type, and `pop_stack'` pops it. `EndClassNode` resolution uses the popped `Inf` pair to dynamically reconstruct the parent `TraversalMode` (via `infToMode (pairToInf infA infB)`), seamlessly returning to the outer context.

## 7. The `absorb` Function

After computing the dc, neg, and pos branches of a result `ClassNode`, `absorb` eliminates redundancy.
It takes a (neg and pos) result branch and matches it with the local `dcR` (the result dc branch), or it takes the local dcR result branch and matches it with an outer `dcR` branch (from the dcR_stack):

- If a branch is identical to `dcR`, it is replaced with `Unknown` (since it adds no information beyond the continuous background).
- This keeps the MDD compact by avoiding explicit representation of branches that agree with the default.
- If the `dcR` also contains an Unknown node, it is resolved to a `dcR` branch higher up the hierarchical class stack.

## Absorb in depth, notes under construction

- Naive absorb minimizes the pos / neg branches of a class with respect to the class' resulting dc branch - Or a dc branch with respect to the outer dc branch.
- it should only be used after the branches have been calculated (in the resolution of applyclass).
- then does a simultaneous traversal of the about-to-be-absorbed branch and the absorbing branch recursively/depth-first past all children / edges.
- until the traversal encounters the endclass node of the local class (depth = 0) where an equality check has to be applied between the about-to-be-absorbed and absorbing branch (equal = absorb, not-equal = leave unchanged).
- if a boolean leaf node is encountered, then an endclassnode should be inferred.
- if an unknown node is encountered for pos/neg/dcR, then it is already absorbed, let it stay absorbed.
- if an unknown node is encountered for the dcR, then substitute it with the closest outer dcR from the dcR stack.

## 8. The BiOpContext and dc_stack

```haskell
data BiOpContext = BCxt {
  bin_nodelookup :: NodeLookup,
  bin_cache      :: Cache,
  bin_dc_stack   :: ([Node], [Node], [Node]),  -- (dcA, dcB, dcR)
  bin_current_level :: (Level', Level')
}
```

The `dc_stack` is a triple of stacks:
- **dcA**: The dc (continuous/background) branches of argument A at each class nesting level
- **dcB**: Same for argument B
- **dcR**: The *result* dc branch at each level — used by `absorb` to check redundancy

## The `traverse_dc` Synchronization

When the main traversal descends into a child, the dc_stack must be kept in sync. `traverse_dc` calls `traverse_dc_generic` which uses `move_dc` to step each dc-stack element into the matching child.

### `move_dc` — stepping a dc_stack element

`move_dc` pattern-matches on the dc-stack element:
- `Node` → follow pos_child or neg_child based on the move string
- `EndClassNode` → follow child for `"endclass"`
- `ClassNode` → follow dc/pos/neg child
- `Leaf` / `Unknown` → return as-is

### `traverse_dc_generic` — dispatch table

`traverse_dc_generic` pattern-matches on `(dcNode, refNode)` pairs to decide how to synchronize:

| dcNode type | refNode type | Action |
|---|---|---|
| `Node pos` | `Node idx` | If dc node (pos) is ahead of the refnode (idx): stay. If pos == idx: `move_dc`. If dcnode < refnode: `catchup` then `move_dc`. |
| `EndClassNode` | `EndClassNode` | `move_dc` (follow the EndClassNode's child) |
| anything | `Unknown` | `move_dc` on dcNode ("just move down") |
| `Unknown` | anything | Return dcNode as-is |
| anything else | anything else | Return dcNode as-is (default fallthrough) |

### `catchup` — skipping intermediate variables

The `catchup` function is inference-type-specific. 
- **`catchup @Pos`**: Repeatedly follows the **pos child** (via `move_dc`).
- **`catchup @Neg`**: Repeatedly follows the **neg child** (via `move_dc`).
- **`catchup @Dc`**: Undefined for standard nodes.

## 9. Note on unary traversal

The unary traversal module (`MDD.Traversal.Unary`) follows the same structural pattern as binary traversal — dc_stack synchronization, inference/elimination rules via `TraversalMode`, and `absorb` — but operates on a single MDD with a simpler context (`UnOpContext`). The shared helpers (`traverse_dc_generic`, `move_dc`, `catchup`) are reused directly. This document focuses on binary traversal as it is the more complex case.