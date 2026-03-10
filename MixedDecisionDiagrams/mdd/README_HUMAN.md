MDD is a Mixed Decision Diagram Library.

In the current form (under construction) it is set up to be used via ghci.

Build the project: `cabal build`

Start the interactive terminal: `cabal repl lib:mdd`

run:

`import MDD.Construction `

`dc_example = path (P' [(1, Dc1, P'' [2,-3])])`

`import MDD.Extra.Draw`

`draw_tree3 dc_example`

should look like:

```
<1> dc #-5063922728968097123:0
  ║
  ╚═╴(2) #3349223725899013879:0
      ├─╴(3) #-4820568095391887338:0
      ¦   ├─╴[1]
      ¦   └ ╴[0]
      └ ╴[0]
```

The numbers behind the hashsigns are the nodeId's, useful when branches are merged (later duplicate branches show the nodeId as child instead of repeating the duplicate branch).

path also initializes a clean NodeLookup table.

`P'' [2,-3]` indicates a local subpath (inside the current domain), where 0 : top/bot, positive int constructs a positive literal for a node at that position and a negative int constructs a negative literal.

`P' [(1, Dc1, ... )]` indicates the class variable domain (these can be nested/recursive or extended sideways).

e.g. `example_mdd_2 = path (P' [(1, Dc1, P' [(3, P'' [2,-3])]), (2, Neg0, P'' [4])])` gives:

```
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
           ¦       ╚═╴<2> dc, n
           ¦            ║
           ¦            ╠═╴[1]
           ¦            ╚═╴(4)
           ¦                ├─╴[0]
           ¦                └ ╴[.]
           └ ╴[.]
```
The domain context is one of `Dc1, Dc0, Pos1, Pos0, Neg1, Neg0`. The 1 / 0  indicates what the default leaf is for the non-specified literals/nodes and the Dc / Pos / Neg indicates what type of literal/node is eliminated/inferred.

for applying operators on MDDs run:
`import MDD.Extra.Interface`

Negation operator:
```
drawTree3 $ (-.) example_mdd

<1> dc #1173023170265034661:0
  ║
  ╚═╴(2) #1503498095392766435:0
      ├─╴(3) #1884762259972783670:0
      ¦   ├─╴[1]
      ¦   └ ╴[0]
      └ ╴[1]
```

Union of the two results in the less restricitve of the two:
```
```

Intersection of the two results in the more restricitve of the two:


Note that there are bugs expected still, some discovered and not yet improved, some undiscovered.

`import MDD.Extra.Test` contains a test of everything (tautologies and handcrafted checks) that works. Calling `test` runs all tests.

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

You can reach me at daniel2miedema@gmail.com for any questions.