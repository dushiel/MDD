Action Models, Transformers, and Updates in Symbolic DEL

This document explains the concepts of Action Models, Transformers, and the update mechanism within the context of Symbolic Dynamic Epistemic Logic (DEL) using Decision Diagrams (MDDs/BDDs).

1. Belief Structures (A Brief Overview)

A Belief Structure (or Knowledge Structure) represents the epistemic state of a group of agents. In a symbolic implementation, it consists of:

Vocabulary ($V$): The set of propositional variables used to describe the world (e.g., $p$: "It is raining").

State Law ($\theta$): A boolean formula (represented as a BDD/MDD) that defines which combinations of variables are physically possible.

Example: $\neg (p \land q)$ might mean "It cannot be raining AND sunny at the same time."

Observation Laws ($\Omega_i$): For each agent $i$, a relation describing their uncertainty.

This is a relation between a "source" world ($s$) and a "target" world ($t$).

If agent $i$ is in world $s$, they consider world $t$ possible if $(s, t) \in \Omega_i$.

Symbolically, this is represented using a doubled vocabulary: $V \cup V'$, where $V$ represents the source and $V'$ the target.

A BelScene is a pair (BeliefStructure, State), where State is a specific valuation of the variables representing the "actual world."

2. Action Models and Transformers

Just as a Kripke Model represents a static situation, an Action Model represents an event or a set of possible events. In this symbolic framework, we use a Transformer to encode action models.

A Transformer consists of:

Event Variables (addprops):

A set of fresh variables used to distinguish between different events happening in the action model.

Example: If addprops = [q], then $q=\top$ might represent "Anne moves the marble," and $q=\bot$ might represent "Nothing happens."

Event Law (addlaw):

A formula constraining the event variables and their interaction with the state.

It serves as the precondition.

Example: PrpF q $\leftrightarrow$ PrpF p means "Event $q$ can only happen if state variable $p$ is true."

Change Law (changelaw):

A map defining Ontic Changes (assignments).

Map: $p \mapsto \psi$.

Meaning: In the new world, the value of variable $p$ becomes the value of formula $\psi$ (evaluated in the old world).

Default: If a variable is not in this map, it keeps its old value ($p := p$).

Event Observations (eventObs):

Relations describing which events agents can distinguish.

Example: If Anne sees the event $q$ happen, her relation is the identity ($q \leftrightarrow q'$). If Sally doesn't see it, she might confuse $q$ with $\neg q$.

An Event is a pair (Transformer, ActualEventFormula), where the formula specifies which event actually occurred (e.g., PrpF q).

3. The Update Mechanism: instance Update BelScene Event

The update combines the current belief structure with the transformer to produce a new belief structure. This is the Product Update.

Step 3: Handle Assignments (The "Copy" Mechanism)

Goal: Preserve the "history" of variables that are about to change.

Identify Changing Variables: Let $C$ be the keys of changelaw (variables $p$ such that $p := \psi$).

Create Copies: For each $p \in C$, generate a fresh variable $p_{copy}$.

Update the Old Law:

The old state law $\theta$ was constraints on $p$.

In the new structure, $p$ will have a new value. The old constraints now apply to the history of $p$.

Action: Relabel all occurrences of $p$ in $\theta$ to $p_{copy}$.

Result: $\theta(p_{copy})$.

Step 4: Construct the New Law

The new state law is the conjunction of three parts:

The Shifted Old Law: $\theta(p_{copy})$

Preserves the logic of the previous state (stored in the copy variables).

The Event Law: mddOf(addlaw)

Enforces preconditions (e.g., "Event $q$ only happens if $p_{copy}$ was true").

The Assignment Laws: For each $p \in C$:

Construct the law: $p_{new} \leftrightarrow \psi(p_{copy})$.

Meaning: The new value of $p$ is equivalent to the result of formula $\psi$ evaluated on the old state (copies).

Example: If $p := \neg p$, the law is $p_{new} \leftrightarrow \neg p_{copy}$.

Step 5: Construct New Relations

The new observation relation for agent $i$ is the intersection of two components:


$$R_{new} = R_{old}(shifted) \cap R_{event}$$

Shifted Old Relation:

The agent's uncertainty about the previous state.

Must be shifted to copy variables: $p_{copy} \leftrightarrow p'_{copy}$.

Event Relation:

The agent's uncertainty about what just happened.

Defined over addprops (e.g., $q \leftrightarrow q'$).

-agent indexing-

the observation relation mdd can be stored in a map, one for each agent. when operating over what an agent knows, then the agent label / index is used to get the relevant obs mdd.

alternatively, however, all observable mdds can be stored in a single mdd, joined under conditionality such that a new variable domain is used to represent agents labels/indexes (e.g. $i$) where $i$ implies obs_mdd_map[$i$] . when requiring the specific obs_mdd of an agent the restrict function is used .....

The agent index is not allowed to be 0 !! this will cause a bug because 0 is a special index for top declaration in path / var.




Step 6: Construct the New State

We must calculate the specific valuation of the new "Actual World":

Start with Old State ($s$): Relabel it to copies ($s \to s_{copy}$).

Apply Assignments:

Filter the changing variables.

For each $p$, check: Does $\psi$ evaluate to True given the old state $s$ and the current event?

If yes, $p$ is True in the new state. If no, $p$ is False.

Result: A new MDD representing the single actual world.

1. Summary of Q&A

Q1: Explain addprops and "interaction".

A: addprops are variables representing the events themselves (e.g., "Action A happened" vs "Action B happened"). They do not describe the past. "Interaction" refers to the addlaw, which acts as a precondition linking the state to the event (e.g., "You can only open the door ($q$) if it is closed ($p$)").

Q2: Explain changelaw and assignments ($p := \psi$).

A: This defines ontic changes. $p$ is the variable changing, and $\psi$ is the rule calculating its new value based on the old state. It is possible to replace a state property with any logical function of the previous state (e.g., toggling a switch, or conditional updates).

Q3: Explain the observation relations in eventObs.

A: These describe uncertainty about the event.

Observer: Has an Identity relation ($q \leftrightarrow q'$). They distinguish the event perfectly.

Non-Observer (Ignorance): Has a Total relation. They don't know if $q$ or $\neg q$ happened.

False Belief (Illusion): Has a relation pointing to the wrong event (e.g., $\top \to \neg q'$). They believe nothing happened even if $q$ did happen.

Q4: Do new propositions remain in the vocabulary?

A: Yes. addprops (event vars) and copyChangeProps (history vars) stay in the vocabulary to preserve the distinction between states that are physically identical but epistemically different (e.g., "Marble gone because it moved" vs. "Marble gone because it was never there"). They can be removed later via optimization if no longer needed.

Q5: Can we simplify law_event to Top?

A: No. The addlaw (Event Law) often contains preconditions (e.g., q -> p). If we simplified it to Top, we would allow impossible actions to occur (e.g., opening an already open door). mddOf is required to enforce these constraints.

Q6: How is agent indexing used?
