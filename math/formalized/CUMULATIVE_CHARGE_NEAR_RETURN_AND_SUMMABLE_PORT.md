# Cumulative-charge payoff near-returns and the summable all-Continue port

Authors: external `ChatGPT` contribution supplied by the user; export
assembly and source audit by `CODEX_ROOT`

Independent review:
[`CODEX_ROOT`](../feedback/CHATGPT_EXTERNAL__CUMULATIVE_CHARGE_OR_STALL__BY_CODEX_ROOT.md)

## Exact statement

Let `I` be a nonempty finite player set and let `r` be a finite quitting-game
reward table.  Let `R` be the exact punishment-floor-admissible charged
relation.  Its states store a bounded payoff vector and a product root; an
edge from `tail` to `current` asserts that `current` is the exact Nash--Bellman
predecessor of `tail`.  The edge charge is its literal one-stage absorption
probability.

For a finite path `P` in `R`, write

```text
C(P) = P.chargeSum,
u_start(P), u_end(P) = the endpoint payoff vectors.
```

### Theorem A: cumulative-charge near-return consumer

Assume there is `C0>0` such that for every `eta>0` there are
floor-admissible states `source_eta,target_eta` and an exact path `P_eta` from
`source_eta` to `target_eta` satisfying

```text
C0 <= C(P_eta),
|u_start(P_eta)(i)-u_end(P_eta)(i)| <= eta  for every i.
```

Then the quitting game has a uniform-equilibrium payoff against unrestricted
behavioral deviations.

Equivalently, the following proposed structure is a complete certificate:

```text
structure QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily where
  chargeFloor : Real
  chargeFloor_pos : 0 < chargeFloor
  nearReturn : forall eta>0, exists source target path,
    path.chargeSum >= chargeFloor and
    forall i, |source.payoff i-target.payoff i| <= eta
```

### Theorem B: charge-or-stall for an infinite exact orbit

Let `O` be any infinite exact punishment-floor Nash--Bellman orbit.  Let
`u_n` be its bounded payoff annotations, `x_n` its product roots, and

```text
a_n = 1-product_i Pr[x_n(i)=Continue]
```

its literal absorption charges.  Exactly one of the following analytic cases
holds.

1. `sum_n a_n` diverges.  For every `eta>0` and `C>0`, the orbit has indices
   `m<n` such that

   ```text
   |u_m(i)-u_n(i)| < eta  for every i,
   C <= sum_(k=m)^(n-1) a_k.
   ```

   Consequently the game has a uniform-equilibrium payoff by Theorem A.

2. `sum_n a_n` converges.  There is a payoff `u_infinity` such that

   ```text
   u_n -> u_infinity,
   x_n -> all-Continue,
   punishmentValue(i) <= u_infinity(i),
   r_i({i}) <= u_infinity(i)                 for every i.
   ```

   Therefore `(u_infinity,all-Continue)` is an exact floor-admissible
   Nash--Bellman self-loop.

In particular, under a terminal exploitability witness, every infinite exact
floor-admissible orbit is in the second case.  This last specialization is
already checked in the repository.

### Theorem C: a nontrivial summable port has a fixed signed terminal label

Assume the summable case of Theorem B.  Suppose rewards and orbit annotations
have absolute value at most `M>0`, and

```text
|u_infinity-u_0|_infinity >= rho > 0.
```

Let `p_n(S)` be the probability that the exact nonempty quitter coalition at
root `x_n` is `S`.  There exist a coordinate `j`, a sign
`s in {-1,+1}`, and one fixed nonempty coalition `S` such that

```text
sum_n p_n(S) * max(s*(r_j(S)-u_n(j)),0)
  >= rho/(2^|I|-1),                                    (1)
```

and hence

```text
sum_n p_n(S)
  >= rho/[2M(2^|I|-1)].                                (2)
```

For four players the label denominator in (1) is `15`.

## Conjecture-facing change

The active question
[`PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`](../questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md)
currently asks for one edge of fixed positive charge in every payoff
near-return.  Theorem A strictly weakens that obligation: a fixed lower bound
on **total path charge** is sufficient even if every individual edge charge
tends to zero.

Theorems B and C identify the only obstruction along an infinite exact
extension.  Failure to accumulate unbounded charge forces convergence to an
all-Continue floor-safe self-loop; any nontrivial payoff displacement into
that port retains one fixed coordinate, sign, and terminal label with a
quantitative cumulative probability budget.

The remaining producer is therefore narrower than the fixed-edge question:
connect the paid first-disagreement source to either

1. one exact orbit with divergent cumulative absorption; or
2. a source-matched restart at the summable all-Continue port which spends a
   fixed amount of its labelled cumulative budget or strictly decreases
   terminal semantic debt.

The second item is not proved here.

## Definitions, probability, information, and agency

Every root is a literal simultaneous product distribution.  Its charge is the
probability that at least one player Quits at that stage.  For a block with
stage charges `a_0,...,a_(N-1)`, joint survival is

```text
B(P)=product_(k<N)(1-a_k),
```

and block absorption is `1-B(P)`.

The finite path is read backwards to obtain the chronological lasso, exactly
as in the checked near-return consumer.  Exact root Nash controls both pure
actions at every stage, and punishment-floor admissibility controls a player
who changes its entire stopping strategy.  No public randomization,
stationary-deviation restriction, or observation of future roots is added.

The limit in Theorem B is a Bellman annotation and exact self-loop.  It is not
asserted to be the realized payoff of the original forward orbit.

## Source correspondence

The following ingredients are already checked.

- `Math.exists_close_pair_with_large_charge_gap_of_compact` in
  `MathUE/DivergentChargeRecurrence.lean` gives compact recurrence across an
  arbitrarily large cumulative-charge gap.
- `Math.prod_one_sub_mul_one_add_sum_range_le_one` and
  `Math.half_le_one_sub_prod_one_sub_of_one_le_sum_range` in the same file give
  the whole-block absorption denominator.
- `exists_singleSeamProjectiveLasso_of_finiteForwardPackets` in
  `UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`
  already consumes finite packets with arbitrarily large cumulative charge.
- `pathToFinitePrefix_charge` in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`
  identifies relation charge sum with decoded absorption sum.
- `QuittingPunishmentFloorInfiniteOrbit.abs_value_succ_sub_le_two_mul_absorptionMass`
  in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorInfiniteOrbitLimit.lean`
  is the value-variation bound.
- `QuittingTerminalExploitabilityWitness.infiniteOrbit_absorptionMass_summable`
  and
  `QuittingTerminalExploitabilityWitness.infiniteOrbit_exists_selfLoop_limit`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Capacity/InfiniteOrbitConsequences.lean`
  and `Capacity/InfiniteOrbitLimit.lean` prove the counterexample-side
  summability and all-Continue self-loop limit.

Those declarations already contain most of the analytic proof of Theorem B.
The new content is the cumulative near-return structure and direct consumer,
which weakens the currently exposed fixed-edge interface, together with the
fixed signed terminal-label extraction in Theorem C.  A narrow search found
no checked declaration packaging either result.  No external-paper claim is
used.

## Proof

### 1. Cumulative charge supplies a uniform block denominator

For `0<=a<=1`, `1-a<=1/(1+a)`.  Therefore

```text
B(P)
 <= 1/product_k(1+a_k)
 <= 1/(1+sum_k a_k)
 = 1/(1+C(P)).                                         (3)
```

Thus

```text
1-B(P) >= C(P)/(1+C(P)).                              (4)
```

If `C(P)>=C0>0`, the block absorption is at least

```text
alpha0=C0/(1+C0)>0.                                   (5)
```

Given a desired lasso error `epsilon>0`, invoke the assumed near-return family
at endpoint tolerance `epsilon*alpha0`.  Decode its exact path to a
punishment-floor prefix and reverse the root block.  Equation (5) gives the
weighted-absorption term required by the checked single-seam lasso
construction, while endpoint closeness pays its unique seam.  Exact Nash and
the punishment floor supply the remaining lasso fields.  The checked lasso
consumer then produces a uniform-equilibrium payoff.  This proves Theorem A.

### 2. Divergent charge forces a returned block

All orbit payoffs lie in the canonical compact reward box.  If the
nonnegative sequence `a_n` is nonsummable, its prefix sums tend to infinity.
Apply the checked compact-recurrence theorem to the payoff sequence and this
prefix clock.  For every `eta,C>0` it returns `m<n` whose payoffs are
`eta`-close and whose intervening charge is at least `C`.  The corresponding
finite orbit segment is an exact floor-admissible path.  Taking any fixed
`C0>0` and applying Theorem A gives a uniform-equilibrium payoff.

### 3. Summable charge forces the all-Continue port

The exact Bellman identity gives

```text
u_(n+1)-u_n
 = sum_(nonempty S) p_n(S)[r(S)-u_n].                 (6)
```

Hence

```text
|u_(n+1)-u_n|_infinity <= 2M a_n.                     (7)
```

Summability makes `u_n` Cauchy.  It also gives `a_n->0`.  Every marginal Quit
probability is at most `a_n`, so the roots converge to all Continue.

Eventually every player assigns positive probability to Continue.  Exact
root Nash then makes that action weakly optimal, so the pure-Quit advantage is
nonpositive.  Passing to the limit gives `r_i({i})<=u_infinity(i)`.  The
punishment-floor inequalities and reward box are closed.  At all Continue the
Bellman successor of `u_infinity` is itself, and the singleton inequalities
are exactly the Nash conditions.  This proves the self-loop assertion in
Theorem B.

### 4. A nonzero summable displacement selects one terminal label

Choose `j` and `s in {-1,+1}` such that

```text
s*(u_infinity(j)-u_0(j))>=rho.
```

Equation (7) and summability justify summing (6) absolutely.  Therefore

```text
sum_n sum_(nonempty S)
  p_n(S) s*(r_j(S)-u_n(j)) >= rho.
```

Discarding negative terms preserves the lower bound.  There are exactly
`2^|I|-1` nonempty coalitions, so one fixed `S` contributes at least the
right-hand side of (1).  Since every positive bracket is at most `2M`, (2)
follows.  This proves Theorem C.

## Boundary tests

- **Diffuse divergent charge.**  `a_n=1/(n+2)` tends to zero but is
  nonsummable.  No positive single-edge threshold survives in the tail, while
  Theorem A accepts returned blocks of fixed cumulative charge.
- **Summable stall.**  `a_n=2^(-n-1)` is summable and leaves positive
  infinite survival.  It belongs to the all-Continue-port side and cannot be
  rejected by the cumulative denominator alone.
- **One label is not two clocks.**  Theorem C may select only one coalition,
  possibly containing several players.  It does not give two persistent
  marginal hazards or a reached restart.
- **Paid live mass is different.**  A paid first-disagreement row bounds
  survival to its disagreement.  That probability is not an absorption
  charge and cannot be substituted into Theorem A without an exact
  source-matched adapter.

## Adapter and consumer

The actual-data adapter for Theorem A is an exact path in
`quittingPunishmentFloorAdmissibleChargedRelation`; its charge is already
decoded exactly by `pathToFinitePrefix_charge`.  The downstream consumer is
the existing reversed-forward single-seam projective lasso followed by
`quittingGame_exists_uniformEquilibriumPayoff_of_singleSeamProjectiveLassos`.

An infinite exact orbit supplies the path family in the nonsummable case by
compact recurrence.  In the terminal-witness regime, the checked capacity
theorems force the summable case and supply its exact all-Continue self-loop.

No adapter from a paid first-disagreement row to either orbit alternative is
claimed.

## Lean handoff

The narrow implementation should add the weaker family next to
`QuittingPositiveAdmissiblePayoffNearReturnFamily`:

```text
structure QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily

theorem exists_singleSeamProjectiveLasso_of_floorPrefix_cumulativePayoffNearReturn

theorem quittingGame_exists_uniformEquilibriumPayoff_of_admissiblePath_cumulativePayoffNearReturns

theorem QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily.exists_uniformEquilibriumPayoff
```

The proof should reuse
`prod_one_sub_mul_one_add_sum_range_le_one`,
`pathToFinitePrefix_charge`, and the low-level reversed-forward lasso
constructor.  A compatibility adapter should show that the existing
fixed-edge family implies the cumulative family.

The orbit theorem can be packaged largely by composing
`exists_close_pair_with_large_charge_gap_of_compact` with the new consumer.
The terminal-witness summable/self-loop arm should reuse the existing checked
declarations rather than duplicate their proofs.

For Theorem C, define the stage probability of one exact nonempty coalition,
prove it is bounded by stage absorption, telescope one coordinate, and use a
finite-sum pigeonhole theorem.  Audit the `M=0` boundary separately; the
positive-displacement assumption makes it impossible.

## Scope and nonclaims

This result does not prove the paid producer, a source-matched restart,
terminal semantic debt descent, or the four-player conjecture.  It does not
turn paid live mass into absorption.  It replaces the downstream fixed-edge
requirement by a strictly weaker cumulative-charge requirement and identifies
the summable all-Continue port, with one fixed signed terminal label, as the
remaining infinite-orbit obstruction.

## Checked Lean realization

The useful content is proved in Lean by the following declarations.

- Theorem A and the compatibility adapter from the older fixed-edge family:
  `cumulativeChargeRatio_le_reversedForwardWeightedAbsorption`,
  `exists_singleSeamProjectiveLasso_of_floorPrefix_cumulativePayoffNearReturn`,
  `quittingGame_exists_uniformEquilibriumPayoff_of_cumulativePayoffNearReturns`,
  and
  `QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily.ofPositiveAdmissiblePayoffNearReturnFamily`
  in
  `UniformEquilibrium/Quitting/Projective/CumulativeChargeNearReturn.lean`.
- Theorem B:
  `QuittingPunishmentFloorInfiniteOrbit.exists_uniformEquilibriumPayoff_of_not_summable_absorption`,
  `nonempty_summableChargeAllContinuePort_of_summable_absorption`, and
  `uniformPayoff_or_summableChargeAllContinuePort` in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorInfiniteOrbitChargeDichotomy.lean`.
- Theorem C:
  `QuittingPunishmentFloorInfiniteOrbit.nonempty_summableChargeSignedTerminalPort_of_displacement`
  in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorSummablePortLabel.lean`.
  Its result stores the exact sign alternative, nonempty coalition, sharp
  `2^|I|-1` contribution share, and the consequent `2M` coalition-mass bound.

Evidence seals: Theorems A--C have `M` and `L`.  The exact path/orbit inputs
give `A` at their stated source interfaces.  Theorem A and the nonsummable arm
of Theorem B have the checked all-behavior uniform-payoff consumer `C`.
The summable labelled port has no paid-source restart or debt-descent consumer,
so no such `C` is claimed for that arm.
