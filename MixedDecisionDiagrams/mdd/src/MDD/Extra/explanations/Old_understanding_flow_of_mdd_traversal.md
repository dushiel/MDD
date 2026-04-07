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

## 2. Binary Operations (e.g. Intersection `.*. `)

```haskell
(.*.) :: MDD -> MDD -> MDD
(.*.) (MDD (la, a)) (MDD (lb, b)) =
    let ctx = init_binary_context (unionNodeLookup la lb)
        (ctx', r) = apply @Dc ctx "inter" (fst a) (fst b)
    in MDD (getLookup ctx', r)
```

Key points:
- The two NodeLookups are merged first (`unionNodeLookup`)
- A fresh `BiOpContext` is created with an initial dc_stack of `([Unknown], [Unknown], [Unknown])`, this is an ephemeral context - existing only for the duration of the binary operation resolution (explained in more depth in sections ...).
- The recursive `apply @Dc` is called — it is a depth-first simulatious traversal of the two input graphs / MDDs - where the top-level always starts in Dc (don't-care) inference context.
- The type parameter `@Dc` / `@Neg` / `@Pos` controls which `DdF3` instance is applies for inference and elimination rules the local subbranches (explained in more depth in sections ...).


## 3. The traversal function: `apply` / `applyClass`

`apply` is the main binary operation entry point. It uses `withCache` for memoization, then dispatches based on the node types of A and B. The cache key is `(NodeId A, NodeId B, dc_stack state)` — the dc_stack is included because the same node pair can produce different results depending on the class hierarchy context (which ClassNode layers are currently active). The cache is a two-level map: function name (e.g. `"inter"`, `"union"`) → `(NodeId, NodeId, dc_stack)` → result NodeId.

The behaviour of the function is dependent on the current nodes of its input MDDs:
- **Both `Node`**: Compares positions and either infers the missing node (via `inferNodeA`/`inferNodeB`) or recurses into children
- **Both `ClassNode`**: Delegates to `applyClass` (which handles the dc_stack push/pop and recurses into dc/neg/pos branches)
- **Both `EndClassNode`**: Both sides exit their class simultaneously. The `endclass_case` function pops the inference type stack to determine which parent context to continue in.
- **Both Leaf**: Handled by `leaf_cases`, which determines the resulting leaf value (boolean operation between the two input leaves, based on whether union or intersection is applied) and is the end of the recursive traversal.
- **Unknown cases**: `Unknown` nodes are resolved by popping from the dc_stack and delegates to `applyDcA'`/`applyDcB'`

Asymetrical cases are resolved based on the position of the nodes and the local context determining the inference / elimination rules. Simulatious traversal happens in such a manner that both branches should always be in the same local context, so they are constantly caught up to each other.

### `applyClass` — entering a class

MDDs are called Mixed Decision Diagrams, because they have multiple mixed inference / elimination rules applied to branches that exist parallel to each other - and have a different (albeit subtle) semantics. mixing them therefore comes with special rules, handeled by the applyclass function call:

```
applyClass c s a@(ClassNode positionA dcA pA nA) b@(ClassNode positionB dcB pB nB):
  1. traverse_dc "class dc" → sync dc_stack for dc branch
  2. add_to_stack (position, Dc) (Unknown, Unknown, Unknown)
  3. (c1, dcR) = apply @Dc dcA dcB
  4. add_to_stack (position, Neg) (dcA, dcB, dcR)
  5. (c2, nR) = apply @Neg nA nB
  6. add_to_stack (position, Pos) (dcA, dcB, dcR)
  7. (c3, pR) = apply @Pos pA pB
  8. pop_stack, absorb, makeClassNode
```

Because there can be multiple nested classes, there can multiple dcR / dcA / dcB 's on the stack as traversal progresses through the multiple classes.

The `reset_stack_bin` call between steps restores the dc_stack to its state before the `applyClass` call, so each branch computation (dc, neg, pos) starts from the same baseline.

It is important that the resulting dc branch is calculated before the pos / neg branches - since the pos / neg branch are absorbed in the resulting dc branch (dcR) of this class. Where a pos / neg branch is absorbed an Unknown node is left in its place. The absorb mechanism is further explained in section 7.



## 4. Structural ordering within a class layer

Within any single class layer (the content between entering an `ClassNode` and reaching its `EndClassNode`), the Dd nodes follow a strict (local) depth ordering - based on their position / int field.

Within a class node and its endclassnode, one can find standard nodes or more classnodes ordered by their positions. A consequence of this ordering is that `EndClassNode` is always "deeper" than any `Node` or `ClassNode` in the same class layer. When the `apply` dispatcher encounters an `EndClassNode` paired with a `Node` or `ClassNode`, it knows the `EndClassNode` side has finished its class content while the other side still has content to process. In such a case the missing node at the least further ahead position is inferred for that branch (what node is inferred depends on the multiple factors, e.g. what kind of nodes are being compared and the currently active elimination rules).

Similarly a Boolean leaf indicates the end of the entire path, which means that it is furtest ahead.
An Unknown node gets resolved with a node from the DC stack, it cannot be compared by position with another node before being substituted.

This gives the following local chart for determining what branch in a binary traversal step needs to have a node inferred (the "smaller"/less further ahead branch needs to infer its node):
rootnode/initial classnode < (class)node with position i < (class)node with position j < (local) endclass node < boolean leaf
where i and j are ints and i < j

## 5. Inference and `applyElimRule` Instances

Node elimination is the oposite of inference: and is performed whenever a result "determined" in the traversal function (is passed back upwards in the recurive call chain).

Standard nodes are eliminated/inference depending on their local inference rule (context):
| `@Dc` | nodes with the same child |
| `@Neg` | nodes with the pos child leading to Uknown |
| `@Pos` | nodes with the neg child leading to Uknown |

`ClassNode`'s are also eliminated/inference on the their local context: `ClassNode position dc pos neg`.

| `@Dc` | `ClassNode _ (EndClassNode childnode) (0,0) (0,0)` — only dc has content and immediatly exits the class |
| `@Pos` | `ClassNode _ (0,0) (EndClassNode childnode) (0,0)` — only pos has content and immediatly exits the class |
| `@Neg` | `ClassNode _ (0,0) (0,0) (EndClassNode childnode)` — only neg has content and immediatly exits the class |

Also any endclassnodes that are directly above a boolean leaf node are eliminated. Again, the dual is that, when a leaf node is compared with an endclassnode an other endclassnode is inferred for the leaf node branch.
Thus when encountering a leaf bool in traversal, there are as many endclassnodes eliminated/inferred to exit all current active classes before the leaf bool node is "reached". Endclassnode elimination is a general elimination rule applied to all kinds of branches.

* todo: endclassnodes leading to Unknown nodes should not be eliminated, as their resolution is local context dependent. Double check whether the code adheres to this.

Note: In most call sites the eliminationrule always aligns with the context — if you're in a Neg context, you wrap as Neg and eliminate as Neg. But in the `applyDcA'`/`applyDcB'` functions, they diverge: the operand that came from a dc_stack pop should be **wrapped as Dc** (it lives in a dc slot), but the **result** should be eliminated using the outer context's rule (e.g. Neg, if we're inside a Neg branch).

This is currently sub-optimal characteristic of the code - and should be cleaned up in a future refactor.


## 6. `bin_current_level` — tracking the class prefix

`bin_current_level :: (Level', Level')` records the class hierarchy path for each operand. `Level'` is `[(Int, Inf)]` — a stack of `(position, inference-type)` pairs representing the nesting of class layers from innermost (head) to outermost (tail). It starts as `([(0, Dc)], [(0, Dc)])` — both operands begin at the root Dc context.

Positions within a class layer are **local**: a `Node` at position 3 inside a sub-class at position 1 is stored simply as position 3, not as a compound `[1,3]`. The `current_level` stack provides the prefix needed to reconstruct the full position vector when required (e.g. for visualization using `to_static_form`).

During traversal, `add_to_stack` pushes a new `(position, Inf)` entry onto both level stacks when entering a sub-class, and `pop_stack'` pops them when exiting (when resolving endclass nodes). The `Inf` is then used to return to the same context (from the outer class) that was active before entering the nested/inner class.

### Remembering a Dc-sourced operand when the other side opens a class, with the current level stack

Sometimes binary traversal runs under `applyDcA'` or `applyDcB'`: one argument is treated as coming from a dc (continuous) slot - after `Unknown` is resolved by popping `dcA` / `dcB` from the `dc_stack`. That branch must stay in Dc type when inferring missing nodes, while the result and the other non-dc branch of the step may still be eliminated with the current context rule (`@Neg`, `@Pos`, …).

When in this applyDc(A/B) traversal, if a `ClassNode` is encountered and traversed into, the traversal enters a new local context - but should still remember it is in partial Dc context on the current level.

When entering a encountered class while also a class node should be inferred for one of the two branches, the functions `applyClassAAs @Dc @a` (A is the dc-sourced side) and `applyClassBAs @Dc @a` (B is the dc-sourced side) are used; the plain `applyClassA` / `applyClassB` variants use `inferClassNode @a` when both operands share the same inference role.

When exiting a class and returning to a partial Dc traversal, `pop_stack'` provides the pair `(infA, infB)` from `bin_current_level` and continues with `apply`, `applyDcA`, or `applyDcB` so the combination matches how each side entered that class layer (e.g. `(Dc, Neg) -> applyDcA @Neg`).

- Todo, explain the logic/reasoning when both sides have an Uknown node resolved (they are now both in "Dc" mode - and their resolution is handeled according to a special logic.)

## 7. The `absorb` Function

After computing the dc, neg, and pos branches of a result `ClassNode`, `absorb` eliminates redundancy.
It takes a (neg, and pos) result branch and matches it with the the local `dcR` (the result dc branch), or it takes the local dcR result branch and matches it with an outer (when dealing with nested classes) `dcR` branch (from the dcR_stack) :

- If a branch is identical to `dcR`, it is replaced with `Unknown` (since it adds no information beyond the continuous background)
- This keeps the MDD compact by avoiding explicit representation of branches that agree with the default
- If the `dcR` also contains an Unknown node, it is resolved to a `dcR` branch higher up the hierachical class stack. (taken from the dcr-stack, that are all traversed along as well)

The dc_stack tracks the continuous background at each nesting level. When `Unknown` is encountered during traversal, it is resolved by popping from the appropriate dc_stack (dcA or dcB), effectively substituting the "don't care" background for the lazy placeholder.

## Absorb in depth, notes under construction

- Naive absorb minimizes the pos / neg branches of a class with respect to the class' resulting dc branch - Or a dc branch with respect to the outer dc branch.
- it should only be used after the branches have been calculated (in the resolution of applyclass).
- then does a simulatuous traversal of the about-to-be-absorbed branch and the absorbing branch (pos/neg with the local dcR, or local dcR with outer dcR), recursively/depth-first past all children / edges
- until the traversal encouters the endclass node of the local class (depth = 0) where an equality check has to be applied between the about-to-be-absorbed and absorbing branch (equal = absorb, not-equal = leave unchanged).
- if a boolean leaf node is encountered, then an endclassnode should be inferred
- if an unknown node is encountered for pos/neg/dcR, then it is already absorbed, let it stay absorbed
- if an unknown node is encountered for the dcR, then substitute it with the closest outer dcR from the dcR stack
- if it enters a new class an alternative traversal function is called (depth+1), that only does simultanuous traversal without absorbtion - until the same class level is arrived at again (depth = 0) and the absorbtion continues as above. this means that the current_level of when the absorb is used should be passed along (with the naiveTraverse context). Since naiveTraverse can also encounter class nodes and go deeper it is not garanteed that when it encounters endclassnodes that it can pop back to naiveAbsorbtion.
- inference and elimination runs as usual during naiveTraverse according to the structural ordering mentioned in section 4.
- the dcR stack is kept up-to-date during naiveAbsorb and naiveTraverse for the outerclass layers (for when encountering Uknowns on the dcR branch).
- since the absorbing branch is always of the Dc type, we can sometime apply the optimization that we do not have to infer a node for it but can immediatly continue traversal on the cild node of the about-to-be-absorbed branch with the unchanged absorbing branch. this would have the same outcome as first inferring a node and then removing it again by traversing to both child nodes of the about-to-be-absorbed and absorbing branches.


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

When the main traversal descends into a child (pos or neg branch of a `Node`), the dc_stack must be kept in sync (such that Unknown nodes can be resolved at any point of the traversal). `traverse_dc` calls `traverse_dc_generic` which uses `move_dc` to step each dc-stack element into the matching child.

traverse_dc_generic handles inference for syncronizing the traversal for the branches on the dc_stack. They are all in the dc inference / elimination rule context. Even if at every step the dc_stack is syncronized with the least "far"/"ahead" node of the input graphs, this can still mean that the branches on the dc_step need multiple node traversal steps to catch up. For this the catch up function is used.

### `move_dc` — stepping a dc_stack element

`move_dc` pattern-matches on the dc-stack element:
- `Node` → follow pos_child or neg_child based on the move string (`"pos child"` / `"neg child"`)
- `EndClassNode` → follow child for `"endclass"`; for `"pos child"`/`"neg child"`/`"class *"` → return node as-is (stay put)
- `ClassNode` → follow dc/pos/neg child for `"class dc"`/`"class pos"`/`"class neg"`
- `Leaf` / `Unknown` → return as-is

Each node type only handles its own set of moves. `Node` handles variable-level moves; `ClassNode` handles class-level moves. Cross-type moves (e.g. `"neg child"` on an `ClassNode`) are undefined.

* this design is a little bit clunky and open to be refactored in the future.

### `traverse_dc_generic` — dispatch table

`move_dc`  = with the current move already applied for traversal on the input mdds

`traverse_dc_generic` pattern-matches on `(dcNode, refNode)` pairs to decide how to synchronize:

| dcNode type | refNode type | Action |
|---|---|---|
| `Node pos` | `Node idx` | If dc node (pos) is ahead of the refnode (idx): stay. If pos == idx: `move_dc`. If dcnode < refnode: `catchup` then `move_dc`. |

| `EndClassNode` | `EndClassNode` | `move_dc` (follow the EndClassNode's child) |

*todo: figure out: the reasoningbehind: (ClassNode handled separately)
| `ClassNode pos` | `ClassNode idx` | If pos > idx: stay. If pos == idx: `move_dc`. If pos < idx: stay (ClassNode handled separately). |

*todo: figur out: can this even happen?
| `Node` | `Leaf` | `catchup` to terminal (-1) then `move_dc` |

*todo: figure out: shouldnt it catchup to endclass node, not terminal?
| `Node` | `EndClassNode` | `catchup` to terminal (-1) then `move_dc` |


| anything | `Unknown` | `move_dc` on dcNode ("just move down") |

| `Unknown` | anything | Return dcNode as-is (dcnode being Unknown gives a fallthrough to a outerlevel dc branch when resolved) |

* what is anything else?
| anything else | anything else | Return dcNode as-is (default fallthrough) |

* todo: throw error
Cross-type pairs like `(Node, ClassNode)` or `(ClassNode, Node)` fall through to the default, which returns the dc_stack element unchanged.

* todo: this still needs a critical analysis to see whether the logic makes sense and covers all possible cases.

### `catchup` — skipping intermediate variables

The `catchup` function is inference-type-specific. The reference node is ahead by passing multiple eliminated nodes which are not eliminated in the dc node. The path that the dc branch should take is thus dependend on the context (inference/elimnination rule) of the reference node.

- **`catchup @Pos`**: Repeatedly follows the **pos child** (via `move_dc`) until the dc_stack element's position catches up to the target position.
- **`catchup @Neg`**: Repeatedly follows the **neg child** (via `move_dc`) until caught up.
- **`catchup @Dc`**: Undefined for standard nodes.
* todo: Dc might be a dificult if the dcnode is branching (when it is a node or classnode) - throw an error in this case? Somehow i think that this case might not be possible to occur. I should figure this out



If the dc_stack element is an `ClassNode`, `catchup` returns it unchanged (is this correct? should this be possible?). ClassNode in the dc_stack are assumed to be handled separately by the `applyClass` logic.


## 9. Note on unary traversal

The unary traversal module (`MDD.Traversal.Unary`) follows the same structural pattern as binary traversal — dc_stack synchronization, inference/elimination rules via `DdF3`, and `absorb` — but operates on a single MDD with a simpler context (`UnOpContext`). The shared helpers (`traverse_dc_generic`, `move_dc`, `catchup`) are reused directly. This document focuses on binary traversal as it is the more complex case; unary traversal is the simpler analogue and does not require separate in-depth documentation.

The restrict_node_set function in Unary.hs demonstrates the pattern:

**traverse_dc_unary** is called before every recursive descent (pos child, neg child, class dc/neg/pos, endclass)

**add_to_stack_** is called when entering a ClassNode, pushing (position, Dc/Neg/Pos) and the dc/dcR pair

**pop_stack_** is called when exiting via EndClassNode, yielding the outer Inf to dispatch with

**reset_stack_un** restores dc_stack state between sibling branches (dc, neg, pos)
