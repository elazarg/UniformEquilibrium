# Audit of the Fin4 monodromy impossibility followup

Reviewer: `CODEX_ATLAS_GATEKEEPER`

## Verdict

**PASS, export in the narrow Followup form.**  The theorem

\[
  \neg\operatorname{Nonempty}
    (\operatorname{FinFourMonodromyProducer}(\mathit{source}))
\]

is correct.  It eliminates both the common-host and complementary-pair atlas
leaves and therefore supplies acceptable answer 3 to
`FIN4_ATLAS_COMMON_HOST_MONODROMY.md` and a stronger-than-requested answer to
`FIN4_ATLAS_COMPLEMENTARY_PAIR_MONODROMY.md`.

This verdict applies only to `# Followup` in `../COMMON_HOST.md`.  The earlier
diagonal-delay argument must not be included.  The law stored by
`FinFourMinimumAtomProducer.point.2` is a terminal-outcome law, not a law of
dated stopping times.  Common deterministic delay preserves that law rather
than making it converge to an all-Never outcome.  The Followup is independent
of that failed argument.

## Exact statement checked

Let `reward` be an arbitrary quitting reward table on `Fin 4`, let `bound` be
arbitrary, and let

```lean
source : FinFourMinimumAtomProducer reward bound
```

be supplied.  Then there is no term of type

```lean
FinFourMonodromyProducer source
```

and hence no term of either wrapper type

```lean
FinFourCommonHostMonodromyProducer source
FinFourComplementaryPairMonodromyProducer source.
```

The proof actually needs only the trace stored by
`FinFourMonodromyProducer`: its state space of nonsingleton Fin4 coalitions,
its `QuittingSameStageSingletonRoute` terminal predicate, its simple closed
segment, and its positive endpoint-edge certificates.  It does not use the
hard residual, global minimum, numerical gain floor, common-host witness, or
complementary-pair witness.

## Source declarations inspected

- `QuittingSameStageSingletonRoute`,
  `QuittingSameStageEndpointEdge`,
  `QuittingSameStageEndpointEdge.source_ne_target`,
  `QuittingSameStageEndpointEdge.target_eq_singlePlayer_toggle`,
  `quittingStageCoalitionMass_le_stagePureEndpointRouted`, and
  `quittingStageCoalitionMass_literalOneDateProfile_eq_canonical` in
  `Research/Quitting/SameStageEndpointMonodromy.lean`;
- `DispatchedClosedSegment`, `MinimalClosedSegment.offset_injective`, and
  `DispatchedClosedSegment.offset_not_terminal` in
  `MathUE/FiniteBooleanEndpointOrbit.lean`;
- `OrderedBooleanCycle`, `cycleNext'`, and the Fin4 coalition coding in
  `MathUE/FinFourOrderedCoalitionCycle.lean` and
  `Research/Quitting/FinFourSameStageEndpointMonodromy.lean`;
- `FinFourMonodromyProducer`, its `trace`, and its two geometry wrappers in
  `Research/Quitting/FinFourProducerAtlas/Leaves.lean` and
  `Research/Quitting/FinFourProducerAtlas/SemanticConnections.lean`; and
- the maintained scope record in
  `formalized/SAME_STAGE_ENDPOINT_MONODROMY_REDUCTION.md`.

A narrow search found no existing theorem proving pair vertices terminal, no
pair-free period-two collapse, and no elimination theorem for
`FinFourMonodromyProducer`.

## Proof audit

### 1. Every pair vertex satisfies the actual terminal predicate

Let `S : QuittingNonsingletonCoalition (Fin 4)` have `S.1.card = 2`.
Choose `p in S.1`, take `action = false`, and put `T = S.1.erase p`.
Then `T.card = 1`, hence `T` is nonempty, and

\[
  \operatorname{quittingPureEndpointRoutedCoalition}(S,p,\mathrm{false})=T.
\]

The source is already a literal pure root with quitter set `S`.  Replacing
`p` by pure Continue at the same date gives the pure root with quitter set
`T`.  The live mass before that date is unchanged, and both corresponding
root-coalition masses equal one.  Therefore the two unconditional stage
masses are equal.  Equivalently, use
`quittingStageCoalitionMass_le_stagePureEndpointRouted` and rewrite its
canonical target with
`quittingStageCoalitionMass_literalOneDateProfile_eq_canonical`.

This constructs exactly

```lean
QuittingSameStageSingletonRoute reward profile stage S
```

because that predicate existentially permits **any** player and Boolean
action.  It does not demand `quittingRootBestEndpointAction`, positive gain,
or an endpoint-edge certificate.  This quantifier check is the decisive
point and is correct.

Consequently `trace.offset_not_terminal` excludes every pair coalition from
the stored closed segment.

### 2. The remaining simple Fin4 cycle has period two

Every trace vertex is a nonsingleton Fin4 coalition.  After pair vertices are
excluded, every vertex has cardinality three or four.  By
`target_eq_singlePlayer_toggle`, consecutive vertices differ in exactly one
membership coordinate, so their cardinalities differ by one.

There is at least one triple vertex: if a chosen vertex is `univ`, either
neighbor is a triple; otherwise it is already a triple.  At any triple
vertex, both cyclic neighbors must be four-player coalitions, because a
one-coordinate neighbor has size two or four and size two is excluded.  The
only four-player coalition is `univ`.

If the period were at least three, the predecessor and successor offsets of
that triple would be distinct.  Their vertices would both equal `univ`,
contradicting `MinimalClosedSegment.offset_injective`.  Thus the period is at
most two.  `dispatchedClosedSegment_period_ne_one` and positivity of the
period give period exactly two.

There is no cyclic-indexing gap here.  In a period at least three,
`cyclePrev i != cycleNext' i` follows from
`cycleNext'_two_step_ne`; injectivity then forbids equality of their vertices.

### 3. A positive reverse pair of endpoint edges is impossible

Let the two vertices be `A` and `B`, and let the two stored edges be

```text
e0 : A -> B
e1 : B -> A.
```

For a single-player toggle, the mover is the unique element of the symmetric
difference of source and target.  Since symmetric difference is symmetric,
the two reverse edges have the same mover `p`.  This can be proved directly
from the two erase/insert alternatives returned by
`target_eq_singlePlayer_toggle`; no payoff argument is used here.

Write `g0` and `g1` for the stored gains.  Both are strictly positive by
`gain_pos`.  The exact `mover_debt` fields give

\[
  d_p(B)=d_p(A)-g_0,
  \qquad
  d_p(A)=d_p(B)-g_1.
\]

For the second identity, rewrite the closing endpoint
`orbit (start + 2)` using `trace.segment.segment.closes`; both sibling
profiles are built from the same `profile`, `stage`, and literal coalition,
so this is equality of the actual debt expressions, not semantic
reselection.  Substitution yields `g0 + g1 = 0`, contradicting
`0 < g0` and `0 < g1`.

This disposes of the only remaining period and proves the claimed
uninhabitedness.

## Boundary and falsification checks

- **Arbitrary action is essential to Step 1.**  If the terminal predicate
  required the chosen best endpoint, a pair need not be terminal.  The actual
  predicate does not impose that restriction.
- **Fin4 is essential to Step 2.**  With five players, excluding pairs leaves
  sizes three, four, and five; larger simple toggle cycles are possible.
- **Simplicity is used.**  It is the stored `offset_injective`, not a claim
  about an arbitrary closed walk, that rules out two occurrences of `univ`
  around a triple when the period is at least three.
- **Strict gains and exact mover-debt subtraction are essential to Step 3.**
  Two zero-gain reverse toggles would not contradict the algebra.
- The common-host cycle and complementary-pair cycle displayed as boundary
  examples in the old monodromy reduction both contain pair vertices.  They
  are valid Boolean cycles but cannot be `DispatchedClosedSegment`s for this
  terminal predicate.  This is why the prior geometry theorem did not notice
  the stronger contraction.
- No temporal interpretation, unrestricted-deviation approximation, or
  Bellman chronology is used.  The contradiction is entirely between fields
  of one supplied literal trace.

## Conjecture-facing effect

The adapter is actual and already checked:

```text
FinFourMonodromyProducer source -> producer.trace.
```

The consumer is contradiction.  Therefore the two named atlas obligations
are removed rather than renamed.  The low-tail dispatch contracts to its two
singleton outcomes; the separate tail-escape and minimum-law-singleton atlas
branches remain untouched.

This is a strict boundary change and meets export gate item 4.

## Lean handoff

The narrowest implementation can use the following theorem shapes:

```lean
theorem quittingSameStageSingletonRoute_of_card_eq_two ...

theorem OrderedBooleanCycle.period_eq_two_of_no_pairVertex
    (cycle : OrderedBooleanCycle)
    (hnoPair : forall i, (coalitionSet (cycle.vertex i)).card != 2) :
    cycle.period = 2

theorem QuittingSameStageEndpointEdge.who_eq_of_reverse ...

theorem finFour_no_sameStageEndpointClosedSegment ... : False

theorem FinFourMonodromyProducer.elim
    (producer : FinFourMonodromyProducer source) : False
```

`period_eq_two_of_no_pairVertex` is clean game-independent `MathUE`
infrastructure.  The reverse-mover lemma may be stated for finite sets rather
than for quitting edges.  In the final contradiction, explicitly rewrite the
second edge's closing target by `closes` before applying `mover_debt`; this
avoids relying on arithmetic simplification of cyclic indices.

## Required export scope

Export only the Followup theorem and its atlas contraction.  Required
nonclaims:

- no all-Never successor is constructed;
- diagonal delay is not used;
- no uniform-equilibrium payoff is directly produced;
- the tail-escape and singleton atlas nodes are not consumed; and
- no analogue for five or more players is claimed.

