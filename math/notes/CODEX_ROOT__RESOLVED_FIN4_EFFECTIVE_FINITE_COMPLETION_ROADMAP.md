# Historical resolution: effective finite completion roadmap for Fin4

## Resolution

There is a complete ordinary-mathematics answer with three source-preserving
modes:

```text
cofinalSingleton -> uniformEscape -> uniformEscape -> ...
                \
                 -> minimumReturn -> minimumReturn -> ...
```

Every hypothetical four-player positive-gap table enters the first mode on
one fixed minimum-law source chronology.  Framewise pureification and the
forced-pair construction retain fixed positive mass and gain scales, exact
post-row tails, and exact own-debt subtraction.  Finite-label stabilization
then leaves a nonnegative actual-tail excess sequence.  Either a positive
threshold occurs frequently, giving `uniformEscape`, or the excess converges
to zero, giving `minimumReturn`.

The last two singleton mode sets are exactly the terminal SCCs of this
declared completion graph, and stream shift realizes their self-transitions.
No rank transition or fairness argument is used.  Thus the Fin4 conjecture is
reduced to two exact capstones: consume uniform escape and consume minimum
return.  The detailed specification below is retained as the criterion that
the construction satisfies.

## Question

Construct a finite, source-preserving transition system which captures every
possible four-player positive-gap quitting game after the checked producer
entrance, and prove that every indefinite obstruction eventually remains in
one explicitly listed terminal component of that system.

The result need not consume those terminal components. It must reduce the
four-player uniform-equilibrium conjecture to a finite family of exact,
self-contained terminal-component questions. A direct proof or refutation of
the Fin4 conjecture is also a complete answer.

## Starting point

Let `r` be an arbitrary quitting reward table on `Fin 4`, with finite reward
bound. A hypothetical counterexample may be represented by either of the
equivalent established forms:

- no uniform-equilibrium payoff exists;
- there is one fixed positive terminal exploitability gap against every
  behavioral profile; or
- the compact terminal-semantic carrier has positive global minimum total
  debt.

The checked entrance theorem

```text
uniformPayoff_or_nonempty_finFourProducerResidual
```

in `Research/Quitting/FinFourProducerAtlas/Coverage.lean` returns either a
uniform-equilibrium payoff or one source-attached member of a finite six-tag
producer residual. Checked semantic normalization, singleton clock
compression, pure collision screening, and monodromy elimination substantially
contract this entrance classification.

That entrance atlas is not yet a finite completion roadmap. Downstream
constructions can return to earlier source types, and several current outputs
have no exhaustive outgoing dispatch. The current finite list of names is
therefore not a proof that every indefinite obstruction belongs to one of
finitely many recurrent mechanisms.

## Required finite atlas package

A successful answer must provide all of the following.

### 1. A finite mode type

Define an explicit finite type `Mode`. Every mode must have a mathematical
meaning and a source-attached packet type

```text
Packet mode reward
```

whose fields are stated completely.

Packets may contain continuous or infinite objects such as payoff vectors,
terminal laws, behavioral profiles, stopping laws, or source chronologies.
Only the number of mode tags must be finite.

No constructor may be an unnamed `other`, `unclassified`, or copy of the
entire original conjecture.

### 2. Exhaustive entrance

Prove that every Fin4 reward table with positive terminal gap produces at
least one packet in the finite mode type, using actual source data from the
same reward table.

The entrance must retain every datum later required by the transition
theorems. Selecting a semantically equivalent carrier point or an unrelated
realizing sequence is not source preservation.

### 3. Exhaustive outgoing dispatch for every mode

For every actual packet in every mode, prove one of the following outputs:

```text
Terminal
RankExit
RegularSuccessor
CertifiedCounterexample
```

Their meanings are fixed below.

`Terminal` means actual terminal approximate Nash profiles for every positive
error with one fixed limiting payoff, an actual uniform-equilibrium payoff,
or an exact positive admissible return already accepted by a checked
uniform-payoff compiler.

`RankExit` means a successor packet in the same finite atlas together with:

- a natural-valued rank defined on complete source packets;
- a strict rank decrease;
- reconstruction of every field needed to invoke the atlas again; and
- a backward compiler from the child conclusion to the parent conclusion.

`RegularSuccessor` means a successor packet in one of an explicitly listed
finite set of modes, with literal source provenance and a backward compiler.
It need not decrease a rank.

`CertifiedCounterexample` means one explicit reward table together with a
proof of one fixed positive exploitability gap against every behavioral
profile. A stationary, periodic, finite-horizon, or bounded-controller gap is
not sufficient.

The dispatch may be nonconstructive in its mathematical proof, but its list
of possible successor modes must be explicit and finite. It may not create a
new residual outside the declared mode type.

### 4. A proved finite transition graph

Define the regular mode graph by placing an edge from `a` to `b` exactly when
the exhaustive dispatch for mode `a` permits a `RegularSuccessor` in mode
`b`.

Rank exits are recorded separately because they cannot occur indefinitely.
Terminal and certified-counterexample outputs are not nonterminal graph
edges.

Prove that every regular edge is backed by an actual source-preserving packet
transition. A relation inferred only from compatible labels, carrier
membership, or semantic equality is not acceptable.

### 5. Terminal-component reduction

Compute or characterize the strongly connected components of the finite mode
graph and its finite acyclic condensation graph.

For each terminal strongly connected component `C`, define an exact
realization statement saying that one fixed Fin4 reward table with positive
global minimum debt admits an infinite source-coherent sequence of packets
whose modes remain in `C` and whose successive packets follow the declared
regular transitions.

Prove the reduction:

```text
If a Fin4 reward table has no uniform-equilibrium payoff,
then some terminal component is indefinitely realizable
on that same reward table.
```

The proof must handle arbitrary mixtures of regular and rank transitions.
Because the rank is natural-valued, rank exits cannot support an infinite
descent. Because the regular graph is finite, every remaining infinite path
eventually remains in a terminal strongly connected component.

### 6. A finite list of capstone questions

For every terminal component, state one self-contained capstone problem whose
positive resolution rules out indefinite realization of that component and
whose negative resolution gives an all-behavior positive-gap table.

Prove that solving all listed capstones positively implies the Fin4
uniform-equilibrium conjecture, while a valid negative answer to any one of
them refutes it.

This finite list is the requested effective roadmap.

## Minimum source-preservation standard

Every regular or rank successor must retain, reconstruct, or explicitly
compile all data used by its target packet, including as applicable:

- the reward table and positive-gap witness;
- the selected global minimum semantic point and total debt;
- the actual behavioral source profiles;
- complete unrestricted cap vectors;
- complete terminal laws and relevant deleted laws;
- stopping-time labels, marked dates, and shifted clocks;
- literal continuation tails;
- fixed terminal atoms and their probability floors;
- exact Nash, Bellman, or punishment-floor annotations; and
- the backward implication from a child terminal result to the parent.

The packet definitions need not all carry the same fields. They must carry
exactly what their outgoing theorems use, and no outgoing proof may recover a
missing field by an unrelated existential selection.

## Current nodes that must be represented or genuinely superseded

The answer need not use the current names, but it must account for the actual
obligations presently represented by:

- a source-attached concentrated collision packet;
- a forced-pair source and its normalized unique-all-Continue inert point;
- an actual three-role endpoint law on or above the minimum fibre;
- a one-time support handoff lacking complete atlas-source reconstruction;
- the unsaturated normalized tent-toll or fixed-cap barrier; and
- the strict-ray refinements, including positive limiting roots,
  cardinality-three binding, and full binding.

It is acceptable to prove that several of these are auxiliary refinements of
one common mode. It is also acceptable to split one of them into finitely many
new modes. In either case, coverage and every outgoing transition must be
proved.

The already impossible same-stage monodromy producer must not be reintroduced
as a live component.

## Effectiveness requirement

`Effective` means the roadmap provides finite mathematical control, not
necessarily an efficient computer program.

At minimum:

- the mode type and successor lists are finite and explicit;
- packet membership and every transition are stated by finite mathematical
  definitions or named exact predicates;
- every mode has an exhaustive theorem rather than a suggested next step;
- every terminal component has one exact realization predicate and one exact
  capstone question; and
- the global reduction to those finitely many capstones is proved.

An algorithm computing the mode and transition certificates from rational
reward data would be stronger and welcome, but is not required.

## Accepted complete answers

Any one of the following answers the question.

### A. Finite roadmap

Provide the complete finite atlas package above, including the terminal-SCC
reduction and finite capstone list.

This does not have to settle every capstone. Its progress is the theorem that
no additional recurrent obstruction can appear outside the finite list.

### B. Positive resolution

Prove that every terminal component in such a finite atlas is impossible or
has a terminal/rank consumer, thereby proving the Fin4 uniform-equilibrium
conjecture.

### C. Negative resolution

Construct one explicit Fin4 reward table and certify a fixed positive terminal
exploitability gap against every behavioral profile.

The counterexample need not be expressed in the atlas language if its
all-behavior gap proof is complete.

## What does not answer the question

The following are not complete answers:

- another finite list of current notes or packet names;
- a graph whose nodes have missing outgoing dispatches;
- a graph using proposed rather than proved source adapters;
- counting an unresolved redirect as an eliminated component;
- a finite entrance classification with no downstream closure theorem;
- one more local case split ending in a new residual;
- a one-node atlas whose packet is simply `positive-minimum Fin4 source`;
- a transition that preserves only the reward table or semantic carrier;
- a real-valued descent with no renewable finite rank;
- a supplied-object verifier whose input is not produced from arbitrary Fin4
  counterexample data;
- an SCC computation on an incomplete graph;
- a finite-state numerical experiment without exact all-behavior semantics;
  or
- a zero-minimum regression.

## Freedom of method

The atlas may use semantic debt, stopping laws, terminal atoms, exact cap
roots, response charts, constrained equilibria, occupation measures,
semialgebraic cells, topological indices, finite-memory controllers, or a new
state language.

It may discard the current atlas organization entirely, provided it proves
the finite entrance, exhaustive closure, source preservation, and terminal
component reduction above.

The proof may be ordinary mathematics first and formalized later. Claims about
existing Lean coverage, adapters, or consumers must cite their exact checked
declarations and imports.

## Lean-facing target

One possible interface is:

```text
FinFourCompletionMode
FinFourCompletionPacket
FinFourCompletionTerminal
FinFourCompletionRankExit
FinFourCompletionRegularStep
FinFourCompletionAtlas.coverage
FinFourCompletionAtlas.dispatch
FinFourCompletionAtlas.terminalComponents
FinFourCompletionAtlas.counterexample_enters_terminalComponent
```

This naming is illustrative. The mathematical package, not a particular API,
is required.
