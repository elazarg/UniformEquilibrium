# Review of cumulative-charge near-return and charge-or-stall

Reviewer: `CODEX_ROOT`

Contribution: external `ChatGPT` argument supplied by the user

## Claims reviewed

1. A fixed positive lower bound on the sum of absorption charges over an
   exact punishment-floor admissible payoff near-return is sufficient for a
   uniform-equilibrium payoff; no single edge needs fixed positive charge.
2. An infinite exact admissible orbit with nonsummable absorption contains
   such cumulative-charge near-returns.
3. A summable-absorption orbit converges to a floor-safe all-Continue exact
   self-loop.
4. A nonzero payoff displacement along a summable orbit selects one payoff
   coordinate, one sign, and one terminal coalition with a quantitative
   positive cumulative probability budget.
5. Producing a source-matched restart at that port remains open.

## Verdict

**PASS after novelty and scope correction.**  The mathematical implications
above are correct.  The claimed paid summable-port restart is not proved and
must remain a named residual, not part of the theorem.

## Mathematical audit

### Whole-block absorption

For stage charges `a_k in [0,1]`,

```text
prod_k(1-a_k) * (1+sum_k a_k) <= 1.
```

Thus a block of cumulative charge `C` has absorption at least
`C/(1+C)`.  This estimate is already checked as the general product bound in
`MathUE/DivergentChargeRecurrence.lean` (including its unit-charge/one-half
corollary).

The decoded admissible path is an exact forward Bellman prefix.  Reversing
the block gives the chronological lasso used by
`ForwardBlockSingleSeam.lean`.  Its closing inequality only needs the endpoint
seam to be bounded by lasso error times whole-block weighted absorption.
Consequently a cumulative charge floor `C0>0` supplies the fixed denominator
`C0/(1+C0)`.  Choosing endpoint tolerance at that scale proves the cumulative
near-return consumer.  The stored roots at the endpoints need not recur.

### Divergent-charge recurrence

On the compact canonical payoff box, nonsummable nonnegative charge has
unbounded prefix sums.  Compact recurrence selects two ordered close payoff
visits separated by any chosen cumulative charge.  This is already checked
as `exists_close_pair_with_large_charge_gap_of_compact` in
`MathUE/DivergentChargeRecurrence.lean`.  Applying the cumulative consumer to
unit-charge returned blocks gives a uniform-equilibrium payoff even when
every individual charge tends to zero.

### Summable-port limit

The Bellman increment bound

```text
|u_(n+1)-u_n|_infty <= 2 M a_n
```

makes the values Cauchy when the absorption charges are summable.  Marginal
Quit probabilities are at most joint absorption, so the roots converge to
all Continue.  Exact Nash inequalities pass to the limit and give
`r_i({i})<=u_infty(i)`; the floor is closed.  Therefore the limiting payoff
with the all-Continue root is an exact floor-safe self-loop.

The relevant ingredients and, in the terminal-exploitability regime, this
conclusion are already checked in
`PunishmentFloorInfiniteOrbitLimit.lean`,
`Capacity/InfiniteOrbitConsequences.lean`, and
`Capacity/InfiniteOrbitLimit.lean`.

### Fixed signed terminal label

For a summable orbit, absolute convergence permits telescoping the exact
Bellman increments.  If
`s(u_infty(j)-u_0(j))>=rho>0`, then

```text
sum_(n,S) p_n(S) [s(r_j(S)-u_n(j))]_+ >= rho.
```

There are `2^|I|-1` nonempty coalitions.  Pigeonholing selects one fixed
coalition `S` with at least `rho/(2^|I|-1)` weighted positive contribution.
If payoffs and rewards are bounded by `M>0`, its cumulative probability is at
least `rho/[2M(2^|I|-1)]`.  For four players the label denominator is `15`.

This is a one-label cumulative certificate.  It is not by itself a
two-persistent-label clock, a reached restart, or a floor-admissible return.

## Probability, agency, and strategy audit

Every edge uses the literal product-root absorption probability.  Whole-block
survival is the product of its joint-Continue probabilities.  The lasso
consumer controls arbitrary unilateral behavioral deviations through exact
root Nash conditions and the punishment floor; no stationary-deviation
restriction or public randomization is introduced.  The summable-port limit
is a Bellman annotation and exact self-loop, not a claim that the original
orbit is a realized strategy payoff.

## Boundary tests

1. Charges `a_n=1/(n+2)` tend to zero but are nonsummable.  No fixed-edge
   consumer sees the tail, while the cumulative consumer does.
2. Charges `a_n=2^(-n-1)` are summable; their survival remains positive and
   the orbit belongs to the stall side.
3. Cumulative coalition mass in one fixed label does not identify a restart
   history or a second persistent player.
4. The paid-row live mass is survival to a disagreement, not exact admissible
   absorption; it cannot supply cumulative charge without a new adapter.

## Novelty audit

The contribution should not claim that the compact recurrence, product
estimate, or counterexample-orbit self-loop is new: those facts are checked.
The new boundary result is the explicit structure and consumer

```text
QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily
  -> uniform-equilibrium payoff,
```

which strictly weakens the active fixed-single-edge requirement in
`questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`.  The fixed signed terminal
label extracted from a nontrivial summable port is also not found as a
packaged declaration in the narrow source search.

## Remaining objection

There is no mathematical objection to the exported reduction.  The universal
paid producer remains open: one must connect the paid first-disagreement data
to either a divergent cumulative exact orbit or a source-matched restart at
the summable all-Continue port.
