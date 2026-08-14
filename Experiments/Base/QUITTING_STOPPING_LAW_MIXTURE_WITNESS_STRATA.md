# Stopping-law mixtures: convex envelopes and witness strata

## Result

Complete stopping-law mixing gives a useful seam geometry, but not a globally
affine one. The exact statement is:

- every terminal-outcome mass and every player's prescribed terminal payoff
  is affine in the mixture weight;
- the payoff of every **fixed unilateral deviation** is affine;
- every other player's best-response value, being the supremum of those
  affine functions, is convex;
- semantic debt is therefore convex and lies below its endpoint chord; and
- on a stratum with one common active best-response witness, both the
  best-response value and debt are exactly affine.

There is a second exact stratum: between two points on the same global
minimum-total-debt fiber, every debt coordinate is forced to be affine.

The Lean experiment
`QuittingStoppingLawMixtureWitnessStrata.lean`
formalizes the witness-stratum statements, a quantitative approximate
version, preservation of the zero-debt face, and a literal two-player kink.

## 1. The exact convexity-defect certificate

Fix a player whose complete stopping law is mixed, a different observer, and
two endpoint strategies. Write

```text
V_s, V_t, V_lambda
```

for the observer's best-response values at the source, target, and mixed
profiles. For one fixed observer deviation `d`, write its endpoint payoffs as
`U_s(d)` and `U_t(d)`. Lean proves

```text
(1-lambda) V_s + lambda V_t - V_lambda
  <= (1-lambda) (V_s - U_s(d)) + lambda (V_t - U_t(d)).
```

The left side is nonnegative by the already-landed convexity theorem. Thus
the full sandwich is

```text
0 <= convexity defect <= weighted endpoint regret of any common witness.
```

This identifies the nonlinearity precisely. It is not an uncontrolled
failure of affinity: it is the cost of being unable to use one nearly optimal
deviation at both endpoints.

Two immediate corollaries are formalized.

1. If one deviation is optimal at both endpoints, it stays optimal on the
   whole segment, and the best-response value and semantic debt are affine.
2. If one deviation is within `epsilon_s` and `epsilon_t` of optimal at the
   endpoints, the convexity defect is at most

   ```text
   (1-lambda) epsilon_s + lambda epsilon_t.
   ```

No global best-response attainment is assumed. This matters: for a general
time-varying quitting profile, pure quit times plus `Never` generate the
best-response supremum, but that supremum need not be attained.

## 2. Zero-slack Nash faces survive exactly

There is a stronger exact-face consequence. Literal semantic debt is always
nonnegative. Convexity therefore implies:

```text
if sourceDebt(observer) = targetDebt(observer) = 0,
then mixedDebt(observer) = 0.
```

If every player has zero debt at both endpoints, every player has zero debt
throughout the stopping-law segment. Hence the exact terminal-Nash face is
convex along this legal one-player stopping-law direction.

On that common zero-debt face, the full terminal semantic pair is affine:
prescribed payoffs are affine unconditionally, and best-response values equal
the prescribed payoffs at both endpoints and throughout the segment. This is
a genuine affine chart for the terminal payoff/envelope coordinates. It does
not assert affinity of conditional live roots, marked-stage graphs, or every
component of an exact-D path anchor.

This corrects an overly pessimistic reading of the seam-compression report.
Zero-slack Nash constraints are not inherently destroyed by stopping-law
mixing. They are preserved when the proposed repair joins two points already
on the same zero-debt face and changes only one player's stopping law.

### Minimum-fiber rigidity

Zero debt is not the only exact affine face. Suppose the source globally
minimizes total semantic debt and a one-player stopping-law endpoint has the
same total debt as the source. Coordinatewise convexity puts every mixed
coordinate below its chord. If one coordinate were strictly below, summing
over the finite player set would put the mixed total strictly below the
source minimum. Lean therefore proves, for every player,

```text
mixedDebt(player)
  = (1-lambda) sourceDebt(player) + lambda endpointDebt(player).
```

This needs neither an attained common best response nor a prior witness
classification. It identifies the exact flat directions at a positive-debt
minimum: the useful reset endpoints are precisely those that stay on the
minimum-total-debt fiber. Directions with positive total excess may transfer
debt between players, but cannot by themselves form a balanced return.

## 3. A minimal genuine kink

Global affinity nevertheless fails in the smallest meaningful example.
Take two players, with mover `false` and observer `true`. Give both players
reward `1` exactly when both quit together, and reward `0` for a singleton
quit. At the source the mover quits at date `0`; at the target the mover
quits at date `1`.

Under a complete stopping-law mixture of the mover's two strategies, the
mover's stopping date is

```text
date 0 with mass 1-lambda,
date 1 with mass lambda.
```

The observer can match one date. Lean proves the exact behavioral
best-response value

```text
V(lambda) = max (1-lambda) lambda.
```

The proof covers all history-dependent observer strategies. Against the
source, an arbitrary strategy earns exactly its own stopping-law mass at date
`0`; against the target, it earns its mass at date `1`; those two masses sum
to at most one. Pure quitting at date `0` and date `1` attain the two lower
branches.

Both endpoint best-response values are `1`, but

```text
V(1/2) = 1/2 < 1
```

at the midpoint. Thus best-response switching is a real quitting-game kink,
not an artifact of the abstract supremum proof. It also shows why the
mixture can be useful for smoothing: it can strictly lower another player's
debt below the endpoint chord.

## 4. The useful equivalence-class axis

The natural classes along a mixture direction are **active-witness strata**:
two weights belong to the same exact stratum when one deviation is optimal
throughout the interval between them. On each such stratum the terminal
semantic coordinates are affine.

These classes are not finite in general. Behavioral pure-time extremality
reduces the witness family to `Option Nat`—one finite quit date plus
`Never`—but this is countable, and nonattainment can occur. Therefore a
claim of finitely many exact global cells would be false without an additional
tail hypothesis.

There are two honest finite versions.

1. **Finite block with one collapsed boundary alternative.** A block of
   length `K` has only the `K` internal pure quit dates plus the boundary
   continuation alternative. Its response envelope is a maximum of finitely
   many affine functions, hence has a finite polyhedral subdivision along a
   one-dimensional mixture segment.
2. **Approximate witness passports.** These no longer require a prior tail
   compression. For every `epsilon, delta > 0`, a uniform grid argument gives
   at most `floor(4M/delta)+2` pure dates whose affine payoff charts
   approximate the full infinite-horizon behavioral envelope everywhere on
   the segment within `epsilon+delta`. The passports can be chosen
   simultaneously for all nonmoving players.

This is the promising finite-class axis: classify a compressed block by its
active pure-time witness (or finite near-active witness set), not merely by
unordered occupation and not by a fictitious globally affine debt vector.
See
[`QUITTING_STOPPING_LAW_MIXTURE_FINITE_WITNESS_PASSPORT.md`](QUITTING_STOPPING_LAW_MIXTURE_FINITE_WITNESS_PASSPORT.md)
for the effective bounds and their exact limitations.

## 5. What this gives the fixed-neighbour problem

Stopping-law mixing now supplies three concrete repair primitives.

- It moves the complete terminal outcome law and prescribed payoff in an
  exact affine direction, with no per-date error accumulation.
- It never raises any player's debt above the endpoint chord.
- Between two zero-debt endpoints it stays on the exact zero-debt face and
  makes the terminal payoff/envelope pair affine.
- Between same-fiber endpoints at a global total-debt minimum, every debt
  coordinate is affine even without a common attained witness.

What it still does not provide automatically is a replacement of a middle
block with its original external entry and exit anchors fixed. A useful next
lemma must find two legal endpoint blocks which already share the required
external data and whose affine outcome/payoff direction has enough rank to
hit the missing seam equation. Conditional live roots and marked chronology
must either be held fixed, included in the equation system, or repaired by a
separate construction.

The sharpened next question is therefore:

```text
Inside one endpoint-conditioned minimum-debt fiber (especially the zero-debt
face), do one-player stopping-law mixture directions span the finite terminal
anchor equations needed to fit a compressed block between fixed neighbours?
```

That is a finite-dimensional rank/selection problem once a bounded block and
its finite witness atlas have been chosen. It is materially narrower than a
general seam-repair chart, and the two-player kink explains exactly where the
atlas must change charts.

One exact conditional answer is now available: if two endpoints already
share their time-zero root, terminal payoff vector, and terminal semantic-debt
vector on a global minimum-total-debt fiber, the whole stopping-law segment
preserves that terminal-semantic port literally. The zero-debt face gives the
same conclusion without a separate minimum hypothesis. This reduces the
remaining existence question to finding nontrivial same-port fibers and
bridging terminal semantic debt to the production finite exact-D costate; it
does not yet fix a complete two-ended seam. See
[`QUITTING_STOPPING_LAW_MIXTURE_FIXED_PORT.md`](QUITTING_STOPPING_LAW_MIXTURE_FIXED_PORT.md).
