# Player-deleted stochastic-button compression

## Concrete result

The stochastic-button reduction now survives arbitrary unilateral changes of
one player's button.

Fix a prescribed root sequence `p(t)` and a player `i`. Delete player `i` from
each row and write

```text
a_t = P(at least one opponent of i quits at row t),
O_t = product_{s < t} (1 - a_s).
```

The sequence `(a_t)` is the player-deleted opponent clock. It is unchanged if
player `i` replaces its behavior by any time-varying hazard `(r_t)`. Under
that replacement, let

```text
D_t = probability that everybody is still live before row t.
```

Then

```text
D_t = O_t * product_{s < t} (1 - r_s),
```

so in particular `D_t <= O_t`.

The Lean experiment
`QuittingStochasticButtonUnilateralCompression.lean`
proves the following exact one-row identity:

```text
CollisionMass(p(t) with i's marginal replaced by r_t)
  = (1 - r_t) * CollisionMass(p(t) with i forced to Continue)
    + r_t * a_t.                                           (1)
```

The two terms are disjoint and exhaustive:

- `i` continues and at least two opponents quit; or
- `i` quits and at least one opponent quits.

This is the strategic reason to use the player-deleted clock. The second
term contains every new collision created by the deviator, while `a_t` is
fixed before the deviation is chosen.

## Uniform diffuse bound

Fix `eta >= 0` and call a row diffuse for player `i` when `a_t <= eta`. The
deviator--opponent overlap on a finite window is

```text
sum_{t < N, a_t <= eta} D_t * r_t * a_t.
```

Lean proves

```text
sum_{t < N, a_t <= eta} D_t * r_t * a_t
  <= eta * sum_{t < N} D_t * r_t
  <= eta.                                                   (2)
```

The important measure is the deviator's own first-quit ledger
`sum D_t r_t`. It is a subprobability measure. Consequently the estimate has
no factor depending on `N`, and it holds for sure quitting, diffuse quitting,
oscillating hazards, and every other time-varying deviation.

Apply the earlier collision concentration theorem to the player-deleted
roots. Collisions internal to the opponents satisfy

```text
sum_{t < N, a_t <= eta}
  O_t * CollisionMass(opponents at t)
    <= choose(n,2) * eta.                                  (3)
```

The coefficient is intentionally inherited from the existing full-type
collision theorem; because the deleted coordinate has probability zero, the
sharper coefficient is `choose(n-1,2)`. No argument here depends on that
constant being sharp.

Combining (1)--(3) with `D_t <= O_t` gives the literal strategic collision
bound

```text
sum_{t < N, a_t <= eta}
  D_t * CollisionMass(updated row t)
    <= (choose(n,2) + 1) * eta.                             (4)
```

This is uniform over the entire unilateral hazard sequence.

## Finite certificate chosen before the deviation

Put

```text
A_N = sum_{t < N} a_t.
```

If `A_N` lies in `[L,L+1]`, retain the opponent rows with `a_t > eta`. Lean
combines the joint-clock experiment with (2)--(4) to prove

```text
eta * #{t < N : a_t > eta} <= L + 1,                       (5)

opponent-internal diffuse collision <= choose(n,2) * eta,  (6)

O_N <= exp(-L),                                            (7)

for every deviation r:
  diffuse deviator--opponent overlap <= eta,               (8)
  literal diffuse collision
    <= (choose(n,2) + 1) * eta.                            (9)
```

If the opponent clock is nonsummable, a first-crossing `N` with
`A_N in [L,L+1]` exists. The theorem
`exists_unilateral_atom_diffuse_tail_certificate_of_not_summable` chooses
this `N` and its finite large-row set using only the opponents. It then
quantifies over **all** deviation hazards. Thus neither the horizon nor the
atom classification is selected after seeing the deviation.

Because every updated survival satisfies `D_N <= O_N`, (7) also bounds the
tail under every deviation.

All printed capstones use only `propext`, `Classical.choice`, and
`Quot.sound`.

## What this actually reduces

At accuracy `eta`, and for one marked player, the chronology has three
strategic classes:

```text
1. finitely many rows with large opponent charge;
2. arbitrarily many diffuse rows whose entire multiquitter mass is O(eta)
   uniformly over every unilateral deviation;
3. an opponent-survival tail of size at most exp(-L).
```

This is a genuine finite reduction of the nonlinear coalition geometry. It
closes the counterfactual-clock gap left open by the joint-law experiment:
a deviator cannot turn infinitely many opponent-diffuse rows into a large
collision reservoir merely by choosing a large or time-dependent own
hazard.

For payoffs bounded in absolute value by `M`, deleting or consistently
reassigning the diffuse multiquitter outcomes costs at most a constant times

```text
M * (choose(n,2) + 1) * eta
```

for every unilateral hazard. The exact factor is `M` for comparison with a
zero contribution and at most `2M` when comparing two arbitrary bounded
reassignments.

## What remained after the unilateral clock estimate

The theorem does not make the full quitting game exactly finite.

After collision mass is removed, the diffuse part still carries first-order
singleton flow. Its direction—namely which opponent supplies the singleton
quit mass—may vary at infinitely many dates. A terminal-law estimate alone
does not determine the continuation value attached to those dates.

Accordingly, the remaining problem is no longer “control all unilateral
collision laws.” It is the more linear question:

```text
Can the diffuse singleton flow be replaced by a finite mesh or a finite
moment representative while preserving the Bellman continuation ledger and
the required one-sided punishment inequalities?
```

The likely equivalence is accuracy-by-accuracy, not literal exact equality:

```text
full quitting chronology
  ~= finitely many large opponent packets
     + a finite representation of diffuse singleton continuation flow
     + one exponentially small tail account.
```

E69 itself supplies the first and third pieces and makes the error from all
omitted multiquitter events uniform over deviations.  E70--E71 below resolve
the stated singleton-flow fork at the level of boundary semantics; they do not
retroactively strengthen the probability theorem proved in E69.

## The fork is now resolved

The unordered occupation-measure proposal fails.  The Lean-checked reversed
two-row example in
`QuittingSingletonOccupationOrderObstruction.lean`
has the same singleton occupation, collision, and tail ledgers in both orders,
but different stopping caps.

The correct ordered coordinate is boundary holonomy.  Every finite block,
irrespective of length, acts through exactly five real coefficients per player:
two affine prescribed coefficients and three max-affine best-response
coefficients.  The companion experiment
`QuittingHolonomyEquivalenceCompression.lean`
proves that equality of this coordinate is an exact boundary-semantic
equivalence, and that every positive resolution admits a finite codebook with
a uniform bounded-gain error estimate.

Compactness strengthens this further: the finite code centers can be chosen
from actually realized blocks, so a nonconstructive uniform row bound exists
at every fixed accuracy, even inside any source-intrinsic eligible class.  The
next target is therefore no longer a bare bounded-length theorem.  It is an
**effective, seam-compatible realization theorem**: construct a uniformly
short common root word while retaining the entry/exit Nash-debt and
punishment-floor relations to the particular surrounding strategy.  See
[`QUITTING_HOLONOMY_EQUIVALENCE_COMPRESSION.md`](QUITTING_HOLONOMY_EQUIVALENCE_COMPRESSION.md)
for the exact statement and fences.
