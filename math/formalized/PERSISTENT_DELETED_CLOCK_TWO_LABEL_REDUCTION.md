# Persistent deleted clocks reduce exactly to two divergent labels

Authors: `CODEX_CEDAR`

Independent reviews:
[Gauss](../feedback/CODEX_CEDAR__PERSISTENT_DELETED_CLOCK_CHARACTERIZATION__BY_CODEX_GAUSS.md)
and
[Noether](../feedback/CODEX_CEDAR__PERSISTENT_DELETED_CLOCK_CHARACTERIZATION__BY_CODEX_NOETHER.md)

## Exact statement

Let `I` be a finite set with at least two elements.  At every date
`t : Nat`, let players independently choose Quit under a product mixed action,
and write

```text
p(t,j) = P(player j Quits at date t).
```

For a deleted player `i`, define the one-stage opponent absorption charge and
the length-`n` deleted survival from date `m` by

```text
c(t,-i) = 1 - product_(j != i) (1-p(t,j)),
J(-i,m,n) = product_(t=m)^(m+n-1) (1-c(t,-i)).
```

Call `j` persistent when the nonnegative series `sum_t p(t,j)` diverges.  The
following are equivalent:

1. at least two distinct players are persistent;
2. for every `i`, the series `sum_t c(t,-i)` diverges;
3. for every `i,m`, `J(-i,m,n)` tends to zero as `n` tends to infinity.

These equivalent conditions imply that the joint survival product tends to
zero on every suffix.  Thus the joint-survival field is redundant once every
one-player-deleted field is known.  Joint survival by itself does not imply
the full family of deleted-player limits.

There is also a robust moving-source adapter.  Partition time into consecutive
finite blocks `B_k`, fix distinct labels `a,b`, and let `bar p` be nominal
hazards while `p` are the actual reprojected hazards.  Put

```text
H(k,j) = sum_(t in B_k) bar p(t,j),
E(k,j) = sum_(t in B_k) |p(t,j)-bar p(t,j)|.
```

If

```text
sum_k H(k,a) = sum_k H(k,b) = infinity,
sum_k E(k,a) < infinity,
sum_k E(k,b) < infinity,
```

then every joint and one-player-deleted survival tends to zero on every
suffix.  The same conclusion holds if, for one fixed `theta>0`,

```text
p(t,a) >= theta * bar p(t,a),
p(t,b) >= theta * bar p(t,b)
```

at every date, without a summable-error hypothesis.

## Conjecture-facing change

This exactly narrows the live obligation
[`questions/PERSISTENT_DELETED_CLOCKS.md`](../questions/PERSISTENT_DELETED_CLOCKS.md).
Instead of constructing separately quantified joint and deleted survival
limits, a source-matched chronology need only preserve two labelled divergent
marginal-hazard streams.  Alternating labels are allowed; the two persistent
players need not be active in the same row.

The remaining producer problem is explicit and is not solved here: actual
vanishing-debt atom/reset access must retain two distinct labels with divergent
nominal hazard through moving-source reprojection, with summable total marginal
loss or fixed-fraction retention.  The forcing, discrepancy, and small-initial-
debt fields of the chronological consumer also remain separate.

## Definitions and assumptions

The statement concerns a deterministic sequence of product mixed actions.
Randomization is independent across players within each date; no independence
across dates is required beyond multiplication of the prescribed conditional
Continue factors along the live public history.  The result is purely about
that prescribed survival law.  It does not restrict observations, agency, or
the power of unilateral behavioral deviations, and it does not by itself
assert an equilibrium.

The exact consumer fields are `joint_survival` and `opponent_survival` in
`QuittingChronologicalDebtShadowingCertificate`
(`UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean`).
Only one-player-deleted clocks are required; pair-deleted clocks are not part
of this result.

## Source correspondence

The checked declarations
`tendsto_zero_quittingOpponentSurvivalWeight_of_not_summable_charge` and
`exists_suffix_half_le_quittingOpponentSurvivalWeight_of_summable`
(`UniformEquilibrium/Quitting/Paths/OpponentClockDichotomy.lean`) give the
additive-charge/multiplicative-survival dichotomy, including isolated zero
Continue factors.  The new ordinary mathematics is the exact finite-player
reduction from all deleted opponent charges to two divergent individual
labels, plus the summable-error and fixed-fraction moving-source adapters.

The declarations `frozenRadialRepeatedRoots_jointSurvival` and
`frozenRadialRepeatedRoots_opponentSurvival`
(`UniformEquilibrium/Diagnostics/Quitting/Chronology/SourceMatchedRepeatedRootSurvival.lean`)
establish the consumer fields for one frozen periodic construction.  They do
not give the two-label characterization or transport it through a changing
carrier.

No paper result is used.

## Proof

Fix a deleted label `i`.  For every `j != i`, event inclusion and the finite
union bound give

```text
p(t,j) <= c(t,-i) <= sum_(j != i) p(t,j).             (1)
```

All terms are nonnegative and `I` is finite.  Summing (1) shows

```text
sum_t c(t,-i) < infinity
  iff
sum_t p(t,j) < infinity for every j != i.             (2)
```

Hence all deleted opponent charges diverge exactly when deleting any one
label leaves a persistent label.  For a finite set this is equivalent to the
persistent set containing at least two distinct labels.  This proves the
equivalence of items 1 and 2.

A divergent nonnegative series remains divergent after removal of a finite
prefix.  Applying
`tendsto_zero_quittingOpponentSurvivalWeight_of_not_summable_charge` at every
start date proves item 3 from item 2.  Conversely, if one deleted charge is
summable,
`exists_suffix_half_le_quittingOpponentSurvivalWeight_of_summable` supplies a
suffix on which every finite deleted survival is at least `1/2`; item 3 fails.
This also covers finitely many earlier sure-Quit factors.  Thus items 2 and 3
are equivalent.

At each date, joint Continue mass is no greater than Continue mass after
deleting any one player.  Multiplying these inequalities shows that any one
vanishing deleted survival bounds joint survival from above, proving the
joint conclusion.

For the robust adapter, the blockwise triangle inequality gives, for
`j=a,b` and every finite number of blocks,

```text
sum_actual p(t,j)
  >= sum_nominal bar p(t,j) - sum |p(t,j)-bar p(t,j)|. (3)
```

The first term on the right diverges and the second stays bounded, so both
actual marginal series diverge.  The equivalence already proved supplies all
required survival limits.  Under fixed-fraction retention, summing
`p(t,j)>=theta*bar p(t,j)` proves divergence directly.

## Boundary tests

- If `|I|=1`, deleting the unique player leaves the empty product one.  The
  cardinality hypothesis is necessary.
- A single sure-Quit date kills products crossing that date but does not kill
  every later suffix.  It contributes only finite hazard mass.
- If only one player has hazard `1/(t+2)` and all others always Continue,
  joint survival dies on every suffix, while deletion of that player leaves
  survival identically one.
- Pointwise-small reprojection error is insufficient.  Give two nominal
  anchors hazard `1/(t+2)` and set both actual hazards to zero.  Both errors
  tend to zero, but their sums diverge and both persistent streams disappear.
- The two anchors may alternate and never be active simultaneously.  The
  theorem requires cumulative labelled incidence, not pair-deleted survival.

## Adapter and consumer

For any supplied chronology whose two marginal hazard streams meet the exact
or robust hypotheses, the proof produces the literal `joint_survival` and
`opponent_survival` limits required by
`QuittingChronologicalDebtShadowingCertificate`.  This is a strict reduction
of those consumer fields; it is not an arbitrary-game source adapter.

Actual two-label production remains open.  In particular, static joint charge,
one persistent owner, two positive marginals in one isolated packet, or
pointwise reprojection errors tending to zero does not satisfy the reduction.

## Lean handoff

A narrow formalization can live near
`UniformEquilibrium/Quitting/Paths/OpponentClockDichotomy.lean` and reuse its
two named dichotomy theorems.  Suggested theorem shapes are:

1. a finite-player equivalence between nonsummability of every
   `quittingOpponentClockCharge roots i` and existence of two distinct labels
   whose scalar Quit-marginal sequences are nonsummable;
2. a corollary providing every suffixwise `quittingOpponentSurvivalWeight`
   limit and joint survival;
3. a block-indexed summable-absolute-error transport lemma, with a separate
   fixed-positive-fraction corollary.

The key elementary input is the pair of pointwise union bounds (1).  Boundary
tests should include `Fin 1`, `Fin 2`, an isolated probability-one hazard, one
harmonic owner, and two nominal harmonic owners erased by actual zero hazards.
Use the narrowest relevant imports and run the single-file Lean check plus the
project trust scan after implementation.

## Scope and nonclaims

This packet does not construct source-matched packets, prove conditioned
reprojection, retain two labels from vanishing-debt atom access, control
pair-deleted clocks, prove the other chronological-certificate fields, or
prove a uniform-equilibrium payoff.  The mathematics is independently
reviewed but is not claimed here as checked in Lean.
