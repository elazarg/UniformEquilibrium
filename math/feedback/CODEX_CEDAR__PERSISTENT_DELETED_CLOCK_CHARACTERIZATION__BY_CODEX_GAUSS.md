# Review of Persistent Deleted-Clock Characterization by `CODEX_GAUSS`

Reviewed note: [`CODEX_CEDAR__PERSISTENT_DELETED_CLOCK_CHARACTERIZATION.md`](../notes/CODEX_CEDAR__PERSISTENT_DELETED_CLOCK_CHARACTERIZATION.md).

## Claim checked

For a finite player set of cardinality at least two, Proposition 1 identifies
vanishing one-player-deleted survival on every suffix with the existence of
two distinct player labels whose cumulative marginal Quit hazards diverge.
It also makes joint survival redundant under that hypothesis.  Proposition 2
shows that two nominal divergent label streams survive source reprojection
when the two marginal error budgets are summable, or when a fixed positive
fraction of each nominal hazard is retained.

These are claims in ordinary mathematics.  I did not run Lean and assign no
`L`, `A`, or `C` seal.

## Verdict

**VALID, with two small wording/example repairs.**  The iff, suffix
quantifiers, exact deleted-clock labels, summable-error adapter, and
fixed-fraction adapter all check.  The result exactly answers the abstract
clock question in `questions/PERSISTENT_DELETED_CLOCKS.md`; it does not
construct the two persistent labels from source data or address the other
chronological-certificate fields.

The repairs are:

1. “Joint survival alone does not imply any deleted-player conclusion” should
   read “does not imply the **full family** of deleted-player conclusions.”
   For a finite player set, dying joint survival forces at least one marginal
   hazard series to diverge, hence at least one suitably chosen deleted clock
   also dies.  The note's harmonic one-owner example correctly disproves the
   required conclusion for **every** deleted label, not every individual
   deleted-clock consequence.
2. To make the pointwise-error counterexample literal for the two-anchor
   adapter, give both nominal anchors the harmonic hazard
   `1/(t+2)` and set both actual hazards to zero.  Then both nominal series
   diverge and both marginal errors tend pointwise to zero, but neither
   actual series is persistent.  The one-anchor version in the note already
   shows the analytic issue, but does not itself satisfy the two nominal
   divergence premises.

Neither repair changes a proposition.

## Independent proof of Proposition 1

Write

```text
p_t,j = P(player j Quits at t),
c_t,-i = 1 - product_(j != i)(1-p_t,j).
```

For every `j != i`, event inclusion and the finite union bound give

```text
p_t,j <= c_t,-i <= sum_(j != i) p_t,j.             (R1)
```

All terms are nonnegative and the player set is finite.  Hence

```text
sum_t c_t,-i < infinity
  iff
sum_t p_t,j < infinity for every j != i.            (R2)
```

Therefore every opponent charge is nonsummable exactly when deletion of any
one label leaves at least one persistent label.  For a finite set this is
equivalent to the persistent-label set having cardinality at least two.
This proves items 1 and 2 in both directions, including alternating labels;
the two persistent players need never be simultaneously active.

The repository's
`tendsto_zero_quittingOpponentSurvivalWeight_of_not_summable_charge`
(`UniformEquilibrium/Quitting/Paths/OpponentClockDichotomy.lean`) applies to
the exact charge `quittingRootOpponentAbsorptionMass`, which is precisely
`c_t,-i`.  Removing a finite prefix preserves nonsummability, so it supplies
the limit on every suffix.  Conversely, if the whole charge is summable,
`exists_suffix_half_le_quittingOpponentSurvivalWeight_of_summable` supplies
one suffix on which every finite deleted-survival product is at least `1/2`.
This also handles finitely many earlier sure-Quit factors and proves the exact
equivalence with item 3.

The certificate field in
`QuittingChronologicalDebtShadowingCertificate`
(`UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean`)
is written as `Math.survivalProduct` of
`quittingRootOpponentContinueMass`; the bridge
`quittingOpponentSurvivalWeight_eq_survivalProduct` identifies it with the
product used above.  Thus no joint/opponent or one-player/pair-deleted clock
has been conflated.

Finally, joint one-stage Continue mass is no larger than the corresponding
deleted-player Continue mass.  Any one of the vanishing deleted products
therefore bounds the joint product from above.  Joint survival is genuinely
redundant once the full opponent-survival field holds.

### Boundary checks

- With one player, deleting that player leaves the empty product `1` at every
  stage, so the opponent-survival field is impossible.  The cardinality
  hypothesis is necessary.
- One sure-Quit date kills only suffixes crossing that date.  Its finite
  hazard contribution is discarded by a sufficiently late suffix, exactly
  as (R2) predicts.
- With exactly one persistent owner and all other owners always continuing,
  joint survival dies on every suffix, but deleting the persistent owner
  leaves survival identically `1`.

## Independent proof of Proposition 2

For anchor `j` and the first `K` consecutive blocks, the blockwise triangle
inequality yields

```text
sum_(k<K) sum_(t in B_k) p_t,j
  >= sum_(k<K) H_k^j - sum_(k<K) E_k^j.             (R3)
```

The first right-hand term diverges and the second stays bounded under the
stated hypotheses, so the actual hazard series of each of `a,b` diverges.
Proposition 1 then gives every required deleted and joint suffix limit.  No
sign issue arises if an individual `H_k^j-E_k^j` is negative: (R3) is a
partial-sum comparison and the cumulative right side still tends to
infinity.

Under fixed-fraction retention,

```text
sum_t p_t,j >= theta * sum_t bar_p_t,j = infinity
```

for each anchor, so the same conclusion follows without an error budget.
The assumption `theta>0` is sharp in the obvious sense.

## Scope and usefulness

This is a clean formalization target because it removes a large quantified
survival field from producer design: preserving two labelled divergent
marginal streams is necessary and sufficient.  It does not make the two
streams available.  In particular, static joint charge, one persistent
label, two positive marginals in a single packet, or pointwise-small
reprojection error alone supplies no persistent two-label incidence.
