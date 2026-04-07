MDD is a Mixed Decision Diagram Library.

In the current form (under construction) it is set up to be used via ghci.

Build the project: `cabal build`

Start the interactive terminal: `cabal repl lib:mdd`

run:

`import MDD.Construction `

`example_simple_mdd = path (P'' [2,-3]))`

To visualize a mdd in the terminal in a tree like manner run:

`import MDD.Extra.Draw`

`draw_tree3 example_simple_mdd`

this should look like:

```
drawTree3 $ example_simple_mdd

(2) #3349223725899013879:0
 ├─╴(3) #-4820568095391887338:0
 ¦   ├─╴[0]
 ¦   └ ╴[1]
 └ ╴[0]

```

The numbers behind the hashsigns are the nodeId's, useful when branches are merged (later duplicate branches show the nodeId as child instead of repeating the duplicate branch).

A special feature of MDDs is that they enable (infinite) variable domains, or variable class, modelling. A single variable class model example:

`path (P' [(1, Dc1, P'' [2,-3])])`

```
drawTree3 $ example_mdd

<1> dc #-5063922728968097123:0
  ║
  ╚═╴(2) #3349223725899013879:0
      ├─╴(3) #-4820568095391887338:0
      ¦   ├─╴[1]
      ¦   └ ╴[0]
      └ ╴[0]
```

Construction explained further:

- `path` also initializes a clean NodeLookup table.

- `P'' [2,-3]` indicates a local subpath (inside the current domain), where a positive int constructs a positive literal for a node at that position and a negative int constructs a negative literal. 0 construcs a top/bot (depending on the domain context).

- At the top level Dc1 is set as the default variable domain context, mostly to make it an intuitive fit for logic modeling and simpel BDD translations.

- `P' [(1, Dc1, ... ), ...]` indicates the class variable domain (these can be nested/recursive or extended sideways).

e.g. for a nested/recursive class labelled 3 inside class 1:

```
example_mdd_1 = path (P' [(1, Dc1, P' [(3, Pos1, P'' [2,-3])])])
drawTree3 $ example_mdd_1

<1> dc #-5454985502812428423:0
  ║
  ╚═╴<3> dc, p #6864650091446325536:0
       ║
       ╠═╴[0]
       ╚═╴(2) #8175986100517295829:0
           ├─╴(3) #8045768184225666623:0
           ¦   ├─╴[.]
           ¦   └ ╴[1]
           └ ╴[.]
```

adding a class 2 "sideways" next to class 1 gives:

```
example_mdd_2 = path (P' [(1, Dc1, P' [(3, Pos1, P'' [2,-3])]), (2, Neg0, P'' [4])])
drawTree3 $ example_mdd_2
<1> dc
  ║
  ╚═╴<3> dc, p
       ║
       ╠═╴[0]
       ╚═╴(2)
           ├─╴(3)
           ¦   ├─╴[.]
           ¦   └ ╴<>
           ¦       ║
           ¦       ╚═╴<>
           ¦            ║
           ¦            ╚═╴<2> dc, n
           ¦                 ║
           ¦                 ╠═╴[1]
           ¦                 ╚═╴(4)
           ¦                     ├─╴[0]
           ¦                     └ ╴[.]
           └ ╴[.]
```

To explain what you see in the last graph, from top to bottom:
- domain <1> is opened with a dc edge,
- then domain <3> is opened with a dc and p / Pos edge
- dc leads to 0 leaf, p leads to the "local" 2 and -3 nodes
- the "unknown" leaf, drawn as [.], is resolved to the local dc value (for the 2 and -3 nodes this leads to [0])
- then domain <3> is closed by a signalling node drawn as <>
- then domain <1> is closed by another <>
- then domain <2> is opened with a dc and a n / Neg edge
- dc leads to 1 leaf, n leads to the "local" 4 node
- the "unknown" leaf, [.], is resolved to the local dc value (for the 4 node [1])

The domain context is one of `Dc1, Dc0, Pos1, Pos0, Neg1, Neg0`. The 1 / 0  indicates what the default leaf is for the non-specified literals/nodes and the Dc / Pos / Neg indicates what type of literal/node is eliminated/inferred. The default leaf is shown in t

for applying operators on MDDs run:
`import MDD.Extra.Interface`

Negation operator:
```
drawTree3 $ (-.) example_mdd_1

<1> dc #-143673977659937233:0
  ║
  ╚═╴<3> dc, p #-6851443654348986350:0
       ║
       ╠═╴[1]
       ╚═╴(2) #-1630582456238703257:0
           ├─╴(3) #1012014391607894026:0
           ¦   ├─╴[.]
           ¦   └ ╴[0]
           └ ╴[.]
```

Union of the two results in the less restricitve of the two:
```
drawTree3 $ example_mdd_1 .+. example_mdd_2                    )

<1> dc #2510633293275582109:0
  ║
  ╚═╴<3> dc, p #-9213335027350919961:0
       ║
       ╠═╴[0]
       ╚═╴(3) #8045768184225666623:0
           ├─╴[.]
           └ ╴[1]
```

Intersection of the two results in the more restricitve of the two:
```
drawTree3 $ example_mdd_1 .*. example_mdd_2

<1> dc #6076981842987065639:0
  ║
  ╚═╴<3> dc, p #3442502464519035208:0
       ║
       ╠═╴[0]
       ╚═╴(3) #-3416118629538443179:0
           ├─╴[.]
           └ ╴<> #-1006863587637083029:0
               ║
               ╚═╴<> #7920581874830993355:0
                    ║
                    ╚═╴<2> dc, n #-2786078858222793006:0
                         ║
                         ╠═╴[1]
                         ╚═╴(4) #-1897443590967967970:0
                             ├─╴[0]
                             └ ╴[.]
```

Note that there are bugs expected still, some discovered and not yet improved, some undiscovered.

`import MDD.Extra.Test` contains a test of everything (tautologies and handcrafted checks) that works. Calling `test` runs all tests. A more extensive test suite is on the top of my todo list.

An example of it working is modelchecking logic puzzles as modelled in SMCDEL with knowledge/belief-structs. This library contains an adapted version of SMCDELs modules.

S5 example implementation for muddychildren:
```
import SMCDEL.Examples.MuddyChildren
runMuddy 6 5
Initializing puzzle with 6 children, 5 muddy.
Round 0: Father announces 'At least one child is muddy'.
Round 1: Nobody knows. Announcing 'Nobody knows'...
Round 2: Nobody knows. Announcing 'Nobody knows'...
Round 3: Nobody knows. Announcing 'Nobody knows'...
Round 4: Nobody knows. Announcing 'Nobody knows'...
SUCCESS: In Round 5, the following children know their status:
[1,2,3,4,5]
```

K example implementation for sally-anne:
```
import SMCDEL.Examples.SallyAnne
runSallyAnne False

[0] Initial: Sally present, No marble.

[1] Action: Sally puts marble in basket.

[2] Action: Sally leaves the room.

[3] Action: Anne moves marble to box (Sally doesn't see).

[4] Action: Sally returns.

--- Final Belief Check ---
Does Anne know marble is gone?
True (Expected: True)
Does Sally know marble is gone?
False (Expected: False)
Does Sally believe marble is still in basket?
True (Expected: True)
```

Running the runSallyAnne with a True flag generates an output folder in the root directory containing dot-graph renders of the MDD's for each scene / after each update.

Notably the K_MDD.hs module has some MDD specific changes, such that it show cases some of the added capabilities of the added variable domains. The mixing nature (the additional expressivity) of the MDD is not really show-case-able, in the sense that these problems are already representable in either one of BDDs or ZDDs - instead of requiring both.

In `src\Examples\Bears.hs` you can find a "simpel" example of modelling systems where MDDs can show both their mixed nature and their ability to model infinite variable domains. I would really recommend reading this script as it doubles as a more in-depth tutorial for MDD modelling.

In `src\MDD\Extra\MDDexplanation.md` you can find a more in depth explanation of the library and its design / codebase. Note that this file is mainly constructed for AI usage, and can sometimes be jarring to read for humans. A proper human readable report of the MDD library is still on the todo list.

You can reach me at daniel2miedema@gmail.com for any questions.