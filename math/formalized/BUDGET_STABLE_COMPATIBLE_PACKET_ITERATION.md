# Budget-stable compatible packet iteration

Authors: `CODEX_EULER`

Independent review:
[`CODEX_RAMSEY` packet-level gate review](../feedback/BUDGET_STABLE_COMPATIBLE_PACKET_ITERATION__BY_CODEX_RAMSEY.md),
with the earlier
[`working-note review`](../feedback/CODEX_EULER__COMPATIBLE_PACKET_ITERATION__BY_CODEX_RAMSEY.md).

## Exact statement

Let `I` be a finite player set with at least two elements, let `r` be a finite
quitting reward table, and fix two distinct players `a,b in I`.  A product root
is a family of independent Quit/Continue distributions, one for each player.
For a root `q`, write

```text
p_i(q)=Pr_q(i Quits).
```

Let `X` be a nonempty set of reached ports.  A port may retain conditional
stopping-law provenance in addition to a semantic pair.  Give every `x in X`
a canonical annotation

```text
A(x)=(U(x),B(x))
```

and a positive local availability margin `rho(x)>0`.

For every `x in X` and every `0<h<rho(x)`, assume there exists at least one
finite packet with the following data:

1. a positive integer length `L`;
2. literal product roots `q_0,...,q_(L-1)`;
3. candidate semantic pairs `z_0,...,z_L`;
4. a literal reached successor port `y in X`;
5. exact internal Bellman equalities

   ```text
   z_s = Phi_(q_s)(z_(s+1))             (0<=s<L);
   ```

6. exact entrance anchoring `z_0=A(x)`;
7. for every player `i`, endpoint seam bounds

   ```text
   |z_L.U_i-A(y).U_i| <= omega(h),
   |z_L.U_i-A(y).U_i|+|z_L.B_i-A(y).B_i| <= omega(h);
   ```

8. two fixed-label actual hazard bounds

   ```text
   sum_(s<L) p_a(q_s) >= kappa*h,
   sum_(s<L) p_b(q_s) >= kappa*h
   ```

   for one constant `kappa>0`; and
9. the local availability-loss estimate

   ```text
   rho(y) >= rho(x)-chi(h).                         (1)
   ```

Here `omega,chi` are nonnegative functions.  It is enough that one packet at
each legal `(x,h)` satisfy all these fields; other locally available packets
may fail `(1)`.

Assume also that all displayed packet annotations have nonnegative semantic
debt and satisfy uniform prescribed-coordinate and debt bounds.  Assume the
combined declared cost

```text
Omega(h)=omega(h)+chi(h)
```

satisfies the operational small-ratio condition

```text
for every epsilon,delta>0, there exists 0<h<delta
such that Omega(h)<=epsilon*h.                       (2)
```

Finally, assume that for every `eta>0` there is a seed port `x_eta in X` whose
canonical candidate debt is coordinatewise at most `eta`.  This is an
independent input.

**Theorem.**  For every `eta>0`, one can recursively select a compatible
infinite sequence of packets such that:

1. every packet's literal successor port is exactly the entrance port of the
   next packet;
2. each player's prescribed block seams and total two-coordinate block seams
   are summable, with both total sums at most `eta`;
3. the initial candidate debt is at most `eta` in every coordinate;
4. after flattening without changing any root, the marginal Quit-hazard sums
   of both `a` and `b` diverge;
5. from every suffix, joint survival and survival after deleting any one
   player's Quit hazards tend to zero; and
6. the flattened data form a
   `QuittingSummableSeamSource r eta`, hence yield a
   `QuittingChronologicalDebtShadowingCertificate r eta`.

The theorem is a compatible-iteration compiler.  It does not produce the
local packets, their fixed labels, the seed, or estimate `(1)` from atom/reset
data.

## Conjecture-facing change

This supplies the generic compatible-iteration compiler recorded among the
answered questions in [`questions/README.md`](../questions/README.md).  It
replaces an infinite compatible block-chain input by quantitative one-step
hypotheses and an operational sublinear-cost schedule.  The scalar criterion
is an equivalence only with existence of a **positive vanishing** nonsummable
schedule whose declared cost is summable.  No necessity is claimed for
arbitrary nonvanishing iterations or for constructions whose true cost is
smaller than the declared modulus `Omega`.

The substantive local inputs are visible rather than hidden:

- exact literal/canonical anchoring at the reached source and successor;
- existence of one successor losing at most `chi(h)` of future availability;
- a seed with small candidate debt; and
- actual two-label progress at each chosen scale.

Combining a universal producer of those fields with this theorem reaches the
checked chronological consumer.  The present result alone does not prove the
finite-quitting conjecture.

## Definitions and assumptions

### Semantic and behavioral data

`Phi_q` is the one-root terminal-semantic Bellman prefix map.  Every internal
packet equality is exact.  The roots are literal product roots: players mix
independently at each live date.  Flattening concatenates the finite root words
in chronological order and introduces no public correlation or additional
observation.  At a live history players observe only that all earlier dates
survived, as in the quitting-game behavioral model.

The hazards in the theorem are the displayed marginal Quit probabilities of
the roots actually executed.  They are not frozen, nominal, or reprojected
hazards.  Consequently no global clock-transport assertion is used.

### Canonical annotation

The annotation `A(x)` must be the one used by every selected packet starting
from `x`, and the preceding endpoint seam must be measured against exactly
`A(x)`.  In a literal conditioned-source application it should be the actual
semantic pair of the reached port.  If it is artificial, a separate
actual-source-to-anchor theorem is required.  Merely having several unrelated
packet annotations at the successor does not satisfy this hypothesis.

### Availability margin

The number `rho(x)` is a one-step availability radius, not an infinite
viability certificate.  Condition `(1)` is local: at every legal state-scale
pair, at least one packet has a successor whose remaining margin loses at most
`chi(h)`.  The proof below establishes inductively that all later invocations
remain legal.

### Unilateral deviations

The selection proof does not restrict deviations or prove equilibrium
directly.  It constructs the exact input to the checked chronological
debt-shadowing consumer.  That downstream consumer uses terminal semantic
best-response caps, hence covers replacement by an arbitrary behavioral
strategy, not merely a root action, stationary clock, finite-state controller,
or one of the two persistent labels.

## Source correspondence

The exact checked downstream structures are in
`UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalSeamReduction.lean`:

- `QuittingVariableLengthSeamBlocksNat` stores positive block lengths, literal
  root arrays, candidate arrays, exact internal prefixes, nonnegative debts,
  and uniform bounds;
- `QuittingVariableLengthSeamBlocksNat.toSummableSeamSourceNat` flattens such
  blocks once prescribed and total block-seam summability, initial debt, and
  literal-root survival are proved;
- `QuittingSummableSeamSource.toChronologicalDebtShadowingCertificate` gives
  the chronological certificate; and
- `quittingGame_exists_uniformEquilibriumPayoff_of_summableSeams_all_errors`
  is the all-errors uniform-payoff consumer.

The exact clock reduction is in
`UniformEquilibrium/Quitting/Paths/PersistentDeletedClockTwoLabel.lean`:

- `hasTwoPersistentQuittingMarginals_iff_all_opponentClocks` identifies two
  divergent fixed marginal streams with divergence of every one-player-deleted
  opponent clock for a finite player set of cardinality at least two; and
- `HasTwoPersistentQuittingMarginals.survival` supplies every-suffix deleted
  survival and joint survival.

The scale selector is represented in `MathUE/SublinearCostSchedule.lean` by
`IsOperationallySublinearCost`, `exists_budgetedDivergentCostSchedule`, and
`isOperationallySublinearCost_iff_exists_vanishing_schedule`.  The local
packet data, radius-budget induction, fixed-label flattening, and certificate
assembly are represented in
`UniformEquilibrium/Quitting/Debt/Dynamic/BudgetStableCompatiblePacketIteration.lean`
by `QuittingBudgetStablePacketData`, `QuittingBudgetStablePacketSystem`, and
`QuittingBudgetStablePacketSystem.exists_chronologicalDebtShadowingCertificate_of_seed`.
No paper result is used.

## Proof

### Lemma 1: operational schedule theorem

Let `Omega:R->R` be nonnegative.  Condition `(2)` has the following two exact
consequences.

First, for every `budget,cap>0` there is a sequence `h_k` such that

```text
0<h_k<cap,                    h_k -> 0,
sum_k h_k=+infinity,          sum_k Omega(h_k)<=budget.       (4)
```

The cost series in `(4)` is summable.  Second, condition `(2)` is equivalent
to existence of at least one positive **vanishing** sequence whose scale sum
diverges and whose declared `Omega`-cost is summable.

**Proof.**  For the forward construction choose, at stage `n`, a scale below
both `cap` and `1/(n+1)` whose cost/scale ratio is at most a geometrically
decreasing fraction of `budget`.  Repeat that scale `ceil(1/h)` times.  Each
stage contributes at least one unit of scale, less than two units of scale,
and at most its assigned geometric cost budget.  Flattening the finite stages
gives `(4)`.

Conversely, let a positive vanishing sequence have divergent scale sum and
summable declared cost.  Given `epsilon,delta>0`, eventually every scale is
below `delta`.  If all sufficiently late terms had
`Omega(h_k)>epsilon*h_k`, summability of the cost tail would force summability
of the scale tail, a contradiction.  Hence condition `(2)` holds.  The
vanishing hypothesis is used here and is part of the equivalence.  QED.

### Lemma 2: legal recursive selection

Fix `eta>0` and choose a seed `x_0` with coordinatewise candidate debt at most
`eta`.  Put

```text
budget=min(eta,rho(x_0)/4),
cap=rho(x_0)/2.
```

Lemma 1 gives a schedule satisfying `(4)` with these bounds.  In particular,

```text
sum_k Omega(h_k)<=budget,       h_k<cap.             (5)
```

Suppose ports and packets have been selected through `x_k`.  From `(1)`,

```text
rho(x_k)
 >= rho(x_0)-sum_(j<k) chi(h_j)
 >= rho(x_0)-budget
 >= 3*rho(x_0)/4
 > h_k.                                             (6)
```

Thus the local packet hypothesis at `(x_k,h_k)` is legal.  Choose one packet
that also satisfies `(1)` and define `x_(k+1)` to be its literal successor.
Countable dependent choice performs this recursion.  Equation `(6)` proves
legality at every finite stage; no infinite compatible chain was assumed.
QED.

### Lemma 3: seams and fixed-label clocks

Every internal seam is zero because each packet satisfies its exact Bellman
equalities.  The only flattened seams occur at block boundaries.  At boundary
`k`, the next block starts at `A(x_(k+1))`, so the assumed endpoint estimates
give, for every player,

```text
prescribed seam <= omega(h_k),
total seam <= omega(h_k).
```

By `(5)` and `budget<=eta`, both series are summable with total at most `eta`.

Let `H_a(k)` and `H_b(k)` be the sums of the actual marginal hazards of the
two labels within block `k`.  Then

```text
sum_k H_a(k)>=kappa*sum_k h_k=+infinity,
sum_k H_b(k)>=kappa*sum_k h_k=+infinity.             (7)
```

The blocks are consecutive finite intervals and all hazards are nonnegative,
so `(7)` is exactly divergence of the two flattened marginal streams.  The
labels are distinct.  `HasTwoPersistentQuittingMarginals.survival` therefore
gives joint and every one-player-deleted survival convergence to zero from
every suffix.  QED.

### Completion

The positive lengths, roots, annotations, exact internal equalities,
nonnegative debts, and uniform bounds instantiate
`QuittingVariableLengthSeamBlocksNat`.  Lemma 3 supplies the prescribed and
total block-seam hypotheses and the two survival fields required by
`toSummableSeamSourceNat`; the seed supplies its initial-debt field.  This
produces `QuittingSummableSeamSource r eta`, and
`toChronologicalDebtShadowingCertificate` gives the stated certificate.  QED.

## Boundary tests

### Zero declared cost

If `Omega=0`, condition `(2)` holds and Lemma 1 returns schedules below every
positive cap, with divergent total scale and zero total declared cost.  This
tests that the radius induction does not assume a uniform lower bound on the
chosen scales.

### Why vanishing is part of the converse

Define a nonnegative cost by `Omega(1)=0` and `Omega(h)=h` for every positive
`h!=1`.  The constant schedule `h_k=1` has divergent scale and zero cost, but
it does not vanish.  Condition `(2)` fails, for example with
`epsilon=1/2,delta=1/2`.  Thus Lemma 1's converse cannot be extended from
vanishing schedules to arbitrary iterations.

Likewise, `Omega` is a declared upper-cost modulus.  Failure of `(2)` for a
loose declaration does not rule out another construction whose actual seams
or radius loss are smaller.  The packet asserts sufficiency of the displayed
one-step data, not global necessity.

## Adapter and consumer

The upstream adapter context is retained in
[`CONDITIONED_PACKET_REPROJECTION.md`](../notes/CONDITIONED_PACKET_REPROJECTION.md).
To use this export, such a theorem must additionally expose a positive
availability margin and prove the one-step loss estimate `(1)` for at least
one locally selectable successor.  It must also provide the same two retained
labels, actual hazard progress, exact literal source/successor anchoring, and
the seed condition.  This export supplies none of those atom/reset facts.

Once those inputs exist, the downstream path is entirely named:

```text
local reached-port packets
  -> budget-stable recursive selection (this theorem)
  -> QuittingVariableLengthSeamBlocksNat
  -> QuittingVariableLengthSeamBlocksNat.toSummableSeamSourceNat
  -> QuittingSummableSeamSource
  -> QuittingSummableSeamSource.toChronologicalDebtShadowingCertificate.
```

At every positive accuracy, the checked theorem
`quittingGame_exists_uniformEquilibriumPayoff_of_summableSeams_all_errors`
then reaches the unrestricted-behavior uniform-equilibrium-payoff endpoint.

## Lean handoff

The narrow declaration correspondence is:

1. `IsOperationallySublinearCost` is exactly condition `(2)`.
2. `exists_budgetedDivergentCostSchedule` is Lemma 1's arbitrary-budget,
   arbitrary-cap forward theorem.
3. `isOperationallySublinearCost_iff_exists_vanishing_schedule` is exactly
   the converse restricted to positive vanishing schedules with nonsummable
   scale and summable declared cost.
4. `QuittingBudgetStablePacketData` and `QuittingBudgetStablePacketSystem`
   store the one-step fields `(1)`--`(2)` without storing an infinite chain.
5. `QuittingBudgetStablePacketSystem.exists_chronologicalDebtShadowingCertificate_of_seed`
   is the packet-selection and semantic-consumer conclusion, conditional on
   the explicit seed.

Finite regression checks should keep the seed, canonical anchor, and local
radius-loss hypotheses visible rather than encoding any of them as conclusions.

## Scope and nonclaims

- The seed small-debt condition is independent and may be impossible if the
  canonical annotation is identified with an actual semantic point on a
  genuinely positive-minimum-debt carrier.
- Literal/canonical entrance and successor anchoring is a substantive local
  hypothesis.  Artificial or competing anchors require another adapter.
- The radius-loss estimate `(1)` is the local viable-set theorem; it is not
  derived from pointwise packet existence.
- No atom/reset packet, fixed atom orientation, conditioned posterior bound,
  or positive-minimum frontier adapter is produced here.
- The theorem does not assert equilibrium soundness by itself; it invokes the
  named checked semantic consumers after their exact inputs have been built.
