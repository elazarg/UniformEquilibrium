# Adversarial review of the monodromy no-go in `COMMON_HOST.md`

Reviewer: `ATLAS_FALSIFIER`

## Claim reviewed

The `# Followup` claims that for every Fin4 minimum-atom source,

```lean
¬ Nonempty (FinFourMonodromyProducer source)
```

and hence both its common-host and complementary-pair refinements are empty.
The proposed proof is:

1. every two-element trace vertex satisfies the stored singleton-terminal
   predicate;
2. a simple Fin4 trace containing no pair vertex has period two; and
3. a positive same-stage endpoint trace cannot have period two.

I checked the exact definitions and attempted to falsify each transition.

## Verdict

**PASS.**  The no-go is mathematically correct at the exact strength stated.
It uses the terminal predicate's actual existential quantifiers, the literal
profiles carried by the edge structure, and the minimal segment's true cyclic
injectivity.  It does not assume best-endpoint behavior in the pair-to-
singleton step and does not conflate a semantic recurrence with a behavioral
chronology.

The remaining Lean work is finite index and rewriting plumbing, not a missing
mathematical premise.  No counterexample or unresolved mathematical objection
was found.

## Declarations inspected

- `DispatchedClosedSegment` and `MinimalClosedSegment` in
  `MathUE/FiniteBooleanEndpointOrbit.lean`;
- `QuittingSameStageEndpointEdge`, `QuittingSameStageSingletonRoute`,
  `QuittingSameStageEndpointEdge.target_eq_singlePlayer_toggle`, and
  `dispatchedClosedSegment_period_ne_one` in
  `Research/Quitting/SameStageEndpointMonodromy.lean`;
- `quittingStageCoalitionMass_le_stagePureEndpointRouted` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiveWeightedCollisionTransfer.lean`;
- `quittingStageCoalitionMass_literalOneDateProfile_eq_canonical` in
  `Research/Quitting/SameStageEndpointMonodromy.lean`;
- `finFourTraceCode_injective`, `finFourTraceCode_adjacent`, and
  `finFourTraceOrderedBooleanCycle` in
  `Research/Quitting/FinFourSameStageEndpointMonodromy.lean`;
- `FinFourMonodromyProducer` in
  `Research/Quitting/FinFourProducerAtlas/Leaves.lean`.

## 1. The terminal predicate really permits the proposed pair route

For a trace state `S : QuittingNonsingletonCoalition (Fin 4)` with
`S.card=2`, choose any `p∈S`, choose `action=false`, and put

\[
 T=S\setminus\{p\}.
\]

Then `T` is a nonempty singleton and

\[
 \operatorname{quittingPureEndpointRoutedCoalition}(S,p,false)=T.
\]

The definition of `QuittingSameStageSingletonRoute` is exactly existential
in `who`, `action`, and the singleton subtype.  It does **not** require the
chosen action to equal `quittingRootBestEndpointAction`, to have positive
gain, or to be an endpoint edge.  This is the decisive quantifier check, and
the note reads it correctly.

The no-loss mass comparison also matches the literal predicate.  Apply
`quittingStageCoalitionMass_le_stagePureEndpointRouted` to the pure-root
source profile, the pair terminal, `p`, and Continue.  Its canonical target
uses `quittingStagePureEndpointBehaviorDeviation`.  Then
`quittingStageCoalitionMass_literalOneDateProfile_eq_canonical` rewrites that
target mass to the literal one-date profile occurring in
`QuittingSameStageSingletonRoute`.  Thus

\[
 \operatorname{StageMass}(S)\le \operatorname{StageMass}(T)
\]

with the exact source profile and selected date.  Zero source mass would not
invalidate the predicate, although the producer separately carries a
positive floor; no positivity is needed here.

Therefore every pair state is terminal in precisely the sense negated by
`trace.offset_not_terminal`.  Every in-period trace state has cardinality
three or four.

## 2. The Fin4 period-two conclusion is exhaustive

Every edge toggles exactly one coordinate by
`QuittingSameStageEndpointEdge.target_eq_singlePlayer_toggle`; its source and
target cardinalities differ by one.  In a cyclic trace of period at least
three, choose a three-element vertex:

- if a selected vertex is already a triple, use it;
- if it is the unique four-element coalition, either neighbor is a triple.

Both cyclic neighbors of a triple have cardinality two or four.  Pair states
are excluded, hence both neighbors are `Finset.univ`.

For period at least three the predecessor and successor offsets are distinct
in `Fin period`.  `MinimalClosedSegment.offset_injective` applies to their
states at `segment.start + offset`; the closing edge at offset `period-1` is
identified with offset zero using `segment.closes`.  It therefore forbids the
two distinct neighbor offsets from both carrying `univ`.

This checks the cyclic boundary cases that a linear predecessor/successor
argument can miss.  It also covers period three; no separate bipartiteness
argument is needed.  Hence the period is at most two.  It is positive by
`ClosedSegment.period_pos`, and period one is excluded by the already checked
`dispatchedClosedSegment_period_ne_one`, which ultimately uses the edge's
literal `source_ne_target`.  The only possibility is period two.

Equivalently, this can be formalized through the existing
`finFourTraceOrderedBooleanCycle`, whose adjacency and vertex injectivity
already incorporate the closing endpoint.  The proposed new finite lemma is
a strengthening of the current geometry classifier, not a change of state
space.

## 3. Reverse edges have the same mover

Let the two in-period vertices be `A` and `B`.  The offset-zero edge toggles
one mover `p` from `A` to `B`, and the offset-one edge toggles one mover `q`
from `B` to `A` after rewriting the closing target by
`segment.closes`.

The two alternatives in `target_eq_singlePlayer_toggle` imply in either
orientation

\[
 A\triangle B=\{p\},\qquad B\triangle A=\{q\}.
\]

Since symmetric difference is symmetric, the singleton sets coincide and
`p=q`.  The same conclusion follows by a direct membership case split: the
only coordinate on which `A` and `B` differ is unique.  There is no possibility
that two different movers realize the same reverse pair.

## 4. The debt contradiction is on literally identical endpoint profiles

For the first edge, `QuittingSameStageEndpointEdge.mover_debt` says

\[
 d_p(\sigma_B)=d_p(\sigma_A)-g_0,
 \qquad g_0>0.
\]

For the second edge it says

\[
 d_q(\sigma_{\operatorname{orbit}(start+2)})
   =d_q(\sigma_B)-g_1,
 \qquad g_1>0.
\]

Here every `sigma_S` is definitionally the same construction
`quittingLiteralPureRootCoalitionProfile reward profile stage S`, with one
common underlying `profile` and one common `stage`.  When the period is two,
`segment.closes` is an equality of the coalition subtype

\[
 \operatorname{orbit}(start+2)=\operatorname{orbit}(start)=A.
\]

Rewriting by this equality makes the second target profile literally
`sigma_A`; this is not merely equality of a selected debt number or a semantic
equivalence.  Rewriting also by `p=q` makes both edge equations concern the
same coordinate.  Substitution yields

\[
 0=g_0+g_1,
\]

contradicting strict positivity of both stored gains.

The already checked `dispatchedClosedSegment_player_circulation` provides a
more general consistency account, but it is not needed for this two-edge
contradiction.

## 5. Scope

The proof eliminates the exact `FinFourMonodromyProducer` currently defined
in `Research/Quitting/FinFourProducerAtlas/Leaves.lean`, and therefore its
common-host and complementary-pair wrappers.  It does not say that arbitrary
Boolean better-reply cycles are impossible.  Its force comes from the atlas
trace's terminal predicate: every pair vertex would already have exited to a
singleton, so a stored nonterminal cycle cannot use the pair layer.

This distinction is important.  Generic singleton-containing toggle cycles
in the full nonempty cube remain possible because their state space and
terminal dispatch are different.  The no-go applies only to the present
nonsingleton dispatched trace with `QuittingSameStageSingletonRoute` as its
terminal predicate.

## Implementation cautions, not mathematical gaps

1. In the predecessor argument, define cyclic predecessor/successor offsets
   explicitly and use `segment.closes` at the wraparound; ordinary natural
   subtraction at offset zero is unsafe.
2. In the period-two debt proof, rewrite the offset-one target coalition by
   `segment.closes` before applying the second mover-debt identity.
3. Prove reverse-mover equality from the exact toggle alternatives or a
   symmetric-difference lemma; equality of cardinality changes alone is not
   sufficient.
4. The pair-terminal adapter must end with the literal/canonical stage-mass
   identity because the route theorem's target constructor is not the one
   appearing definitionally in the terminal predicate.

These are the only repairs anticipated.  They do not alter the theorem.

## Unresolved objections

None.
