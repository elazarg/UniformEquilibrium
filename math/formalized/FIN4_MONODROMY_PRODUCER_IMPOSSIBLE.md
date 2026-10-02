# The Fin4 same-stage monodromy producer is empty

Authors: `COMMON_HOST.md` follow-up contributor; Codex root (source audit and export assembly)

Independent reviews:

- [adversarial falsification](../feedback/COMMON_HOST__BY_ATLAS_FALSIFIER.md)
- [source and export-gate audit](../feedback/COMMON_HOST__BY_ATLAS_GATEKEEPER.md)
- [generalization and sharp-boundary audit](../feedback/COMMON_HOST__BY_STRENGTHENER.md)

## Exact statement

Let `reward` be arbitrary quitting-game reward data on `Fin 4`, let `bound` be
arbitrary, and let

```text
source : FinFourMinimumAtomProducer reward bound.
```

Then

```text
¬ Nonempty (FinFourMonodromyProducer source).
```

Consequently both refinements are empty:

```text
¬ Nonempty (FinFourCommonHostMonodromyProducer source)
¬ Nonempty (FinFourComplementaryPairMonodromyProducer source).
```

No hard-residual property, positive-minimum inequality, common-host geometry,
or complementary-pair geometry is used. The contradiction is internal to the
literal dispatched trace stored by `FinFourMonodromyProducer`.

More generally, the same conclusion holds for the corresponding same-stage
dispatched endpoint trace on any finite player type whenever the union of all
coalitions visited in its simple period has cardinality at most four. Thus the
theorem is an effective-support result, not only an ambient-`Fin 4` result.

## Conjecture-facing change

The Fin4 producer atlas treated common-host and complementary-pair monodromy as
two live leaves requiring separate nonlocal consumers. This theorem eliminates
their common parent producer. In particular, the low-tail dispatch contracts
from

```text
purified singleton
or terminal-orbit singleton
or common-host monodromy
or complementary-pair monodromy
```

to the two singleton alternatives.

This does not solve the concentrated-singleton or tail-escape obligations. It
strictly removes the entire monodromy branch from the Fin4 atlas.

## Definitions and assumptions

A trace vertex is a nonsingleton coalition in `Fin 4`. Its terminal predicate
is

```text
QuittingSameStageSingletonRoute reward profile stage source.
```

This predicate existentially chooses a player, a Boolean endpoint action, and
a singleton routed coalition whose literal stage mass is at least the source
coalition's stage mass. The chosen action is not required to be a best endpoint
or to have positive gain.

A trace edge is a nonempty

```text
QuittingSameStageEndpointEdge
  reward profile stage minimum lambda source target.
```

Such an edge toggles exactly its mover's membership, has strictly positive
literal payoff gain, and subtracts that gain exactly from the mover's terminal
semantic debt between the two literal pure-root sibling profiles.

The trace is a `DispatchedClosedSegment`: its in-period vertices are pairwise
distinct, none satisfies the terminal predicate, and every in-period successor
is a certified edge. All profiles and stage masses in the argument are the
literal profiles stored by this one trace.

## Proof

### Lemma 1: every pair vertex is terminal

Let `S` be a trace vertex with `S.card = 2`. Choose `p ∈ S`, choose the
Boolean action `false` (Continue), and put `T = S.erase p`. Then `T.card = 1`
and

```text
quittingPureEndpointRoutedCoalition S p false = T.
```

The checked pure-endpoint routing inequality says that forcing this endpoint
action does not reduce the routed stage-coalition mass. The checked
literal/canonical identity identifies that routed mass with the mass in the
literal one-date profile required by the terminal predicate. Therefore

```text
QuittingSameStageSingletonRoute reward profile stage S
```

holds. No strategic optimality or payoff sign is used.

But `DispatchedClosedSegment.offset_not_terminal` says that no in-period trace
vertex satisfies this predicate. Hence every trace vertex has cardinality
different from two.

### Lemma 2: a pair-free simple Fin4 trace has period two

Every trace vertex is nonsingleton. By Lemma 1 and the ambient cardinality
four, every vertex therefore has cardinality three or four.

Let `U` be the union of all coalitions visited in the simple period. In the
Fin4 specialization, `U ⊆ univ`, so `U.card ≤ 4`.

`QuittingSameStageEndpointEdge.target_eq_singlePlayer_toggle` says that each
edge inserts or erases exactly its mover. Adjacent cardinalities consequently
differ by one.

Assume the period is at least three. Choose a cardinality-three vertex. Such a
vertex exists: if a chosen vertex has cardinality four, either neighbor has
cardinality three. Both the predecessor and successor of a cardinality-three
vertex have cardinality two or four. Pair vertices are excluded, so both are
cardinality four. Both are subsets of `U`, and `U.card ≤ 4`; hence both equal
`U`. Thus predecessor and successor are the same trace vertex.

For cyclic period at least three, their two offsets are distinct. This
contradicts the `MinimalClosedSegment.offset_injective` field stored in the
trace. Therefore the period is at most two.

The period is positive, and period one is impossible because the in-period
edge would have identical source and target, contradicting
`QuittingSameStageEndpointEdge.source_ne_target`. Hence the period equals two.

### Lemma 3: a positive endpoint-edge trace cannot have period two

Write the two vertices as `A` and `B`, and let the two certified edges be

```text
e₀ : A → B
e₁ : B → A.
```

Let their movers be `p` and `q`. Each edge toggles precisely its mover, so

```text
A Δ B = {p}
B Δ A = {q}.
```

Symmetry of symmetric difference gives `{p} = {q}`, hence `p = q`.

Let `g₀` and `g₁` be the two literal edge gains. The edge fields give
`0 < g₀` and `0 < g₁`. After rewriting the closing endpoint by the stored
segment equality, the two exact mover-debt identities concern the same two
literal pure-root sibling profiles:

```text
d_p(B) = d_p(A) - g₀
d_p(A) = d_p(B) - g₁.
```

Substitution yields `g₀ + g₁ = 0`, contradicting positivity. Thus a
period-two trace is impossible.

Lemmas 1--3 contradict the existence of the trace field of any
`FinFourMonodromyProducer source`, proving the theorem. The common-host and
complementary-pair conclusions follow by projection to their shared
`monodromy` field.

## Probability and strategy audit

The proof is a finite contradiction inside actual same-stage profile data. It
does not serialize the trace as play, equate terminal-law mass with root
absorption, replace an actual profile by a carrier point, or restrict a
behavioral deviator. The only probability statement is the checked literal
stage-mass routing inequality used to witness the trace's own terminal
predicate.

The debt identities are full terminal-semantic debt identities already stored
by each edge. The proof does not infer them from stationary or one-stage
deviation calculations.

## Source correspondence

The relevant checked declarations are:

- `QuittingSameStageSingletonRoute`,
  `QuittingSameStageEndpointEdge`,
  `QuittingSameStageEndpointEdge.source_ne_target`, and
  `QuittingSameStageEndpointEdge.target_eq_singlePlayer_toggle` in
  `Research/Quitting/SameStageEndpointMonodromy.lean`;
- `quittingStageCoalitionMass_le_stagePureEndpointRouted` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiveWeightedCollisionTransfer.lean`;
- `quittingStageCoalitionMass_literalOneDateProfile_eq_canonical` in
  `Research/Quitting/SameStageEndpointMonodromy.lean`;
- `MinimalClosedSegment` and `DispatchedClosedSegment` in
  `MathUE/FiniteBooleanEndpointOrbit.lean`; and
- `FinFourMonodromyProducer`, its `edge`, `edge_gain_pos`, and
  `edge_mover_debt` projections in
  `Research/Quitting/FinFourProducerAtlas/Leaves.lean`.

The new content is the observation that every pair is terminal for the actual
trace predicate, followed by the Fin4 period-two reduction and the reverse-edge
debt contradiction. Existing geometry classified a surviving monodromy trace;
it did not exploit this terminal predicate to prove that the trace is empty.

## Boundary tests

1. The pair argument relies essentially on the terminal predicate allowing an
   arbitrary Boolean action. If it required the best endpoint or positive
   gain, the Continue route could not be selected without an additional sign
   hypothesis.
2. The effective-support bound four is sharp for the local interface. With
   three fixed hosts `H` and two movers `a,b`, a five-player cube has the
   pair-free common-host cycle
   `H → H+a → H+a+b → H+b → H`. Taking `a`'s payoff to be the
   XOR of `a,b` membership and `b`'s payoff to be membership equality makes
   each displayed move a strict unit improvement. This is a local-interface
   boundary example, not a positive-gap quitting-game counterexample.
3. A generic toggle cycle is not ruled out. The contradiction uses the exact
   positive mover-debt subtraction field of `QuittingSameStageEndpointEdge`.
4. Period two is special because both reverse edges necessarily have the same
   mover; no intervening different-player edge can restore that coordinate's
   debt.

## Adapter and consumer

The adapter is literal: every `FinFourMonodromyProducer source` already
contains exactly the dispatched trace used by the proof. No additional source
selection is needed.

The consumer is impossibility. Both refined monodromy leaves contain a
`FinFourMonodromyProducer source`, so they are empty. The existing low-tail
atlas dispatch may therefore delete those alternatives and retain only its two
singleton outputs.

## Lean handoff

The narrowest useful declarations are:

```lean
theorem quittingSameStageSingletonRoute_of_card_eq_two
    (source : QuittingNonsingletonCoalition (Fin 4))
    (hcard : source.1.card = 2) :
    QuittingSameStageSingletonRoute reward profile stage source

theorem FinFourMonodromyProducer.false
    (producer : FinFourMonodromyProducer source) : False

theorem not_nonempty_finFourMonodromyProducer :
    ¬ Nonempty (FinFourMonodromyProducer source)
```

A reusable finite-combinatorics lemma can state that no simple dispatched
strict-toggle closed segment exists when every pair is terminal and the union
of its visited subsets has cardinality at most four. The quitting theorem is
then its literal adapter.

The period argument can be proved directly from
`producer.trace.segment.offset_injective`, the closing equality, and finite-set
cardinality facts. The period-two contradiction should use `producer.edge 0`
and `producer.edge 1`, rewrite the second target with the segment's `closes`
field, prove mover equality from the two toggle descriptions, and finish with
the two `mover_debt` equations and `gain_pos`.

A useful downstream corollary strengthens the low-tail dispatch to the two
singleton constructors only. No new structure field should encode the desired
emptiness.

## Scope and nonclaims

This theorem does not prove a uniform-equilibrium payoff, consume a
concentrated singleton, consume quantitative tail escape, or exclude arbitrary
coalition-toggle cycles. It proves that the particular positive, exact-debt,
singleton-dispatched Fin4 monodromy object currently stored by the atlas cannot
exist.

## Formalization record

The maintained checked realization is Research-only and is reachable through
`Research/Quitting/FinFourExhaustiveProducerAtlas.lean`.

1. `Research/Quitting/FinFourProducerAtlas/MonodromyImpossible.lean` proves the
   reusable same-stage trace obstruction.  The generic declaration
   `quittingSameStageSingletonRoute_of_card_eq_two` shows, on every finite
   player type, that a cardinality-two vertex satisfies the trace's actual
   singleton-route terminal predicate by Continue-erasure and the checked
   no-loss stage-mass inequality.

   `sameStageEndpointTraceVisitedSupport` is the literal union of all
   coalitions visited at the distinct offsets of one simple period.
   `sameStageEndpointTrace_period_eq_two_of_effectiveSupport_card_le_four`
   works in an arbitrary finite ambient player type with any fixed support of
   cardinality at most four containing every visited coalition.
   `sameStageEndpointTrace_period_ne_two` uses the two reverse toggle
   descriptions, exact mover-debt subtraction, and both strictly positive
   gains to exclude period two.  Their exact union-support composition is
   `sameStageEndpointTrace_false_of_visitedSupport_card_le_four`; the more
   reusable supplied-support form is
   `sameStageEndpointTrace_false_of_effectiveSupport_card_le_four`.
2. The same module specializes the result to Fin4 through the thin theorem
   `finFourSameStageEndpointTrace_period_eq_two` and the profile-, source-, and
   minimum-independent trace theorem
   `not_nonempty_finFourSameStageEndpointClosedSegment`.
   `FinFourMonodromyProducer.false` consumes only the producer's stored
   `trace` field.  The exact source-indexed conclusions are
   `not_nonempty_finFourMonodromyProducer`,
   `not_nonempty_finFourCommonHostMonodromyProducer`, and
   `not_nonempty_finFourComplementaryPairMonodromyProducer`.  No hard-residual,
   minimum-debt, scale, gain-floor, common-host, or complementary-pair field is
   used.
3. `FinFourLowTailRow.nonempty_singleton_leaf` deletes both impossible
   monodromy alternatives from the existing four-way low-row dispatch.  The
   new four-constructor `FinFourProducerResidualWithoutMonodromy` retains the
   original minimum-singleton, purified-singleton, terminal-singleton, and
   quantitative tail-escape sources and witnesses.
   `FinFourProducerResidual.withoutMonodromy` is the lossless eliminator from
   the original six-tag residual.  The actual-data compositions
   `nonempty_finFourProducerResidualWithoutMonodromy_of_hardResidual` and
   `uniformPayoff_or_nonempty_finFourProducerResidualWithoutMonodromy` give,
   respectively, hard-residual and arbitrary bounded-reward coverage by the
   four surviving tags, preserving the existing uniform-payoff arm.
4. `Research/Quitting/FinFourExhaustiveProducerAtlas.lean` imports the no-go
   module.  `Research.lean` already imports that reader umbrella, so every
   declaration above is reachable from the maintained Research surface.

Evidence seals:

- **M:** PASS.  The pair-terminal lemma, effective-support cardinality
  argument, reverse-edge debt contradiction, and branch contraction match the
  reviewed proof and exact boundary described above.
- **L:** PASS.  The no-go module, reader atlas, and full Research umbrella
  compile.  At promotion, the named module and reader builds, Research build,
  generated axiom-audit freshness and target build, trust scan, import-graph
  check and its eleven unit tests, documentation check, proof-duplicate check,
  derivable-telescope check, and source-format checks passed.
- **A:** PASS.  Every `FinFourMonodromyProducer source` already contains the
  exact same-stage dispatched trace consumed by the no-go; no trace, source,
  minimum, or geometry is reselected.  The global four-tag theorem begins with
  arbitrary bounded Fin4 reward data and preserves every surviving source and
  witness from the checked six-tag coverage theorem.
- **C:** PASS for literal monodromy-branch deletion.  Both refined monodromy
  producers project to the impossible parent, the low-row dispatch contracts
  to its two singleton outputs, and the arbitrary-data atlas residual
  contracts to four tags.  This `C` seal is not a consumer for any surviving
  tag and is not an atlas-completion theorem.

Nonclaims:

- no uniform-equilibrium payoff is produced in the residual arm, and the Fin4
  or general finite-quitting conjecture is not proved;
- the minimum-singleton, purified-singleton, terminal-singleton, and
  quantitative tail-escape tags are not consumed here;
- the original six-tag residual and older semantic-node types remain valid
  compatibility surfaces; the theorem supplies a checked one-way contraction,
  not definitional removal or an equivalence;
- arbitrary coalition-toggle cycles are not excluded: the contradiction uses
  the exact positive mover-debt field of `QuittingSameStageEndpointEdge` and
  the singleton-route terminal predicate;
- no return, regeneration, recursive descent, backward compiler,
  near-minimality, terminal approximation, or completion closure is proved;
  and
- the five-player sharpness construction in the packet remains an ordinary
  mathematical boundary example and has not been checked in Lean.

The mathematical provenance is this packet and the independent
ATLAS_FALSIFIER, ATLAS_GATEKEEPER, and STRENGTHENER reviews linked at its head.
No external paper theorem or off-main Lean implementation is used.
