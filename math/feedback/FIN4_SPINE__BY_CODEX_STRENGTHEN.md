# Strengthening review of `FIN4_SPINE`

Reviewer: `CODEX_STRENGTHEN`

Target: [`gpt/FIN4_SPINE.md`](../archive/FIN4_SPINE.md)

## Verdict

The normal unique-persistent-spine theorem is correct ordinary mathematics.
The constants in the displayed proof are safe, the punishment hypothesis is
the right behavioral one, and the conclusion really is the named singleton
payoff vector, not merely target-free equilibrium existence.

I recommend a revised export, but not the current file verbatim. There are
two mandatory corrections and one substantial strengthening:

1. The target-preserving checked consumer is
   `isUniformEquilibriumPayoff_soloReward_of_approximate_caps` in
   `UniformEquilibrium/Quitting/Punishment/ApproximateCompletedCycle.lean`.
   The draft-cited
   `quittingStationarilyGeneratedApproximateEquilibria_of_approximate_solo_caps`
   forgets the payoff target and by itself yields only existence of some
   uniform-equilibrium payoff.
2. The malformed display tokens `===`, `=======`, `|...|*infty`, and
   `sum*` must be repaired before export.
3. The Fin4 conclusion should be strengthened. Two persistent labels on an
   exact canonical spine already imply a uniform-equilibrium payoff by the
   checked clock/path compiler. Consequently, on the Fin4 no-uniform branch,
   **every exact canonical spine has zero persistent labels**, equivalently
   every player's marginal Quit-hazard series is summable. The draft's
   intermediate conclusion “zero or at least two” is true but not final.

There is also a strictly stronger generic theorem. Outsider marginal
summability is a convenient sufficient condition, not the sharp stochastic
hypothesis. The proof only needs the probability of eventual absorption away
from the owner's singleton to vanish on late suffixes.

This review is ordinary mathematics and a declaration audit. It does not add
a Lean seal.

## 1. Claim audited

Let `reward` be a finite quitting table and let `(value, roots)` be a bounded
exact Nash--Bellman spine. Fix `owner`. Suppose

```text
¬ Summable (quittingMarginalQuitHazard roots owner)
∀ other, other ≠ owner ->
  Summable (quittingMarginalQuitHazard roots other)
```

and

```text
IsQuittingNormalPlayer reward owner.
```

Then

```text
(quittingGame reward).IsUniformEquilibriumPayoff none
  (quittingSoloReward reward owner).
```

The right-hand vector is exactly `reward {owner}` coordinatewise. This is the
repository-exact version of the draft's boxed theorem.

For the maintained Lean interface, “bounded exact spine” should be
`IsCanonicalExactQuittingNashBellmanSpine`. It already bounds both the reward
table and every stored value by `quittingRewardBound reward`.

## 2. Quantitative audit

Write

\[
q_{t,i}=(x_{t,i}(Q)),\qquad
a_t=\prod_{j\ne p}(1-q_{t,j}),\qquad
c_t=1-a_t,
\]

and let

\[
b_t=a_t(1-q_{t,p})
\]

be the one-stage joint all-Continue probability. In repository notation,

```text
c_t = quittingOpponentClockCharge roots p t
b_t = quittingStationaryContinueMass (roots t).
```

Let `R = quittingSoloReward reward p` and let `M` bound the reward
coordinates. Bellman evaluation gives exactly

\[
v_t-R=b_t(v_{t+1}-R)+e_t,
\]

where `e_t` is the unnormalised contribution of coalitions containing an
outsider, measured relative to `R`. Hence

\[
\lVert e_t\rVert_\infty\le 2M c_t.                 \tag{2.1}
\]

The factor `2M` is the correct uniform constant from the absolute reward
bound. It can be replaced coordinatewise by the smaller table oscillation

\[
\max_{S:\,S\setminus\{p\}\ne\varnothing}
  |r_i(S)-r_i(\{p\})|,
\]

but `2M` is the right canonical API constant.

Iterating gives

\[
v_t-R=
 \left(\prod_{u=t}^{T-1}b_u\right)(v_T-R)
 +\sum_{s=t}^{T-1}
   \left(\prod_{u=t}^{s-1}b_u\right)e_s.           \tag{2.2}
\]

Owner persistence implies every suffix product in the first term tends to
zero. Uniform boundedness of `v_T` is used only here. Thus the draft's bound

\[
\lVert v_t-R\rVert_\infty
 \le 2M\sum_{s\ge t}c_s                           \tag{2.3}
\]

is correct. It is sharper to retain the survival weights:

\[
\boxed{
\lVert v_t-R\rVert_\infty\le 2M\Lambda_t,
\qquad
\Lambda_t:=\sum_{n=0}^{\infty}
 \left(\prod_{u=t}^{t+n-1}b_u\right)c_{t+n}.}
                                                               \tag{2.4}
\]

`Lambda_t` is the probability, starting live at `t`, that the first
absorbing coalition contains someone other than `p`. It is the suffix
non-solo absorption mass. The unweighted estimate follows from

\[
\Lambda_t\le\sum_{s\ge t}c_s.
\]

### Exact relation between outsider assumptions

For a finite player set,

\[
\max_{j\ne p}q_{t,j}\le c_t\le\sum_{j\ne p}q_{t,j}.
\]

Therefore the following are equivalent:

- every outsider marginal series is summable;
- `sum_t c_t` is finite;
- `Summable (quittingOpponentClockCharge roots p)`.

This equivalence is already checked as
`summable_quittingOpponentClockCharge_iff` in
`UniformEquilibrium/Quitting/Paths/PersistentDeletedClockTwoLabel.lean`.
Using `c_t` rather than the sum `s_t` gives the exact probabilistic quantity
and the best dimension-free constant in (2.3).

Summability is nevertheless stronger than necessary. For example, at the
hazard level, `q_{t,p}` comparable to `1/t` and outsider union hazard
comparable to `1/(t log t)` gives a nonsummable outsider series but
`Lambda_t` of order `1/log t`, hence `Lambda_t -> 0`. This example only
separates the stochastic hypotheses; it is not asserted to be an exact spine
for an arbitrary reward table.

### Solo reprojection constant

For outsider `i`, force `i` to Quit and delete every outsider marginal from
the row. The two forced-Quit laws differ only if some
`j notin {p,i}` Quits. If

\[
c_{t,p,i}=1-\prod_{j\notin\{p,i\}}(1-q_{t,j}),
\]

then the sharp event coupling gives

\[
|A_{t,i}-U_i(x_t[i\leftarrow Q];v_{t+1})|
 \le 2M c_{t,p,i}\le 2M c_t.                      \tag{2.5}
\]

The draft's `2M s_t` is therefore safe but not sharp. The already checked
general perturbation theorem
`abs_quittingRootQuitPayoff_sub_le_opponentTVSum` in
`UniformEquilibrium/Quitting/Root/EndpointOpponentStability.lean` directly
recovers the draft's sum-of-marginals bound. A specialized event-coupling
lemma would recover (2.5).

Exact root Nash and Bellman evaluation then give

\[
A_{t,i}\le R_i+\lVert v_t-R\rVert_\infty+2Mc_t.
                                                               \tag{2.6}
\]

The checked identity `quittingStationaryUnilateralCap_solo_other` turns this
into the full stopping-law cap. Under the stronger hypothesis
`Lambda_t -> 0`, note that `c_t <= Lambda_t`; hence the cap error is at most
`4M Lambda_t` and still vanishes.

### Prefix/punishment constants

The remaining constants in the draft are correct:

- prescribed payoff error: `2M rho`;
- outsider environment replacement error: `2M rho`;
- outsider Nash error: `eta_t + 4M rho`;
- owner Nash error: `delta + 2M rho`.

Thus `eta_t < epsilon/3`, `delta < epsilon/3`, and
`4M rho < epsilon/3` give the displayed strict bounds. No division by the
owner hazard occurs.

## 3. Strongest clean generic statement

The unique-persistence theorem is the right simple corollary for the Fin4
question. The following is the sharper underlying theorem.

### Asymptotic singleton-concentration spine theorem

Let `(v_t,x_t)` be an exact Bellman spine with reward bound `M`. Fix `p` and
assume:

1. the joint survival product tends to zero on every suffix;
2. `Lambda_t`, the suffix probability of absorption outside `{p}`, tends to
   zero;
3. the Bellman terminal remainder is transverse, namely
   `prod_{u=t}^{T-1} b_u * ||v_T-R|| -> 0` for every `t`; and
4. `p` is punishment-normal.

Then `r({p})` is a uniform-equilibrium payoff.

For a uniformly bounded spine, item 3 follows from item 1. Items 1--2 imply
that positive owner hazards occur arbitrarily late: on a sufficiently late
suffix, absorption occurs almost surely and has positive probability of
ending at `{p}`. At those active dates (2.4)--(2.6) supply vanishing solo caps,
and the checked approximate-cap compiler applies.

Topologically, item 2 says that the suffix terminal laws converge in total
variation to the point mass on `{p}`. In repository semantics it is the
statement that the suffix `quittingNonSoloMassLimit` tends to zero. The
checked estimate
`abs_quittingTerminalPayoff_sub_soloReward_le_nonSoloMassLimit` in
`UniformEquilibrium/Quitting/Boundary/Exceptional/TailFallback.lean` is
exactly the payoff part of this formulation.

Unique persistence implies these hypotheses:

- the owner's nonsummable marginal is dominated by full absorption, so joint
  survival dies on every suffix;
- summability of `quittingOpponentClockCharge roots p` gives
  `Lambda_t <=` its remaining tail sum, which tends to zero; and
- canonical boundedness kills the terminal remainder.

This is the sharpest reward-independent probabilistic formulation. If some
off-singleton rewards happen to equal `r({p})`, even non-solo concentration
can be weakened in the payoff coordinates where those rows coincide, so no
purely probabilistic condition is literally necessary for every special
table.

## 4. Weakest roles of the other hypotheses

### Punishment normality

Only the persistent owner must be normal. No outsider normality is used. The
exact final seam is

```text
quittingPunishmentValue reward p <= quittingSoloReward reward p p.
```

Equivalently, it is enough to supply punishment profiles whose full
behavioral best-reply cap for `p` approaches `R_p` from above. The repository
definition of punishment value and
`exists_stationaryRoot_cap_lt_punishmentValue_add` provide precisely this.
No attainment of the infimum is assumed.

### Boundedness

Reward boundedness controls the coupling and target-delivery errors. It is
automatic for a finite table. Uniform boundedness of `v_t` is used only to
erase the terminal term in (2.2); it can be replaced by the transversality
condition in the strengthened theorem. For the intended Lean theorem there
is no reason to expose a second bound: `IsCanonicalExact...` supplies
`quittingRewardBound reward` for both rewards and values.

### Exact Nash

The convergence argument uses only exact Bellman evaluation. Exact root Nash
is used in the reprojection step, to bound every outsider's forced-Quit
endpoint by the current stored value. The final solo cap is behavioral, not a
stationary-deviation relaxation.

## 5. Boundary tests

### Zero persistent labels

This boundary cannot be consumed by a theorem about an arbitrary exact
spine. Every finite quitting table has the checked canonical all-Continue
phantom:

- `canonicalPhantom_isExactQuittingNashBellmanSpine`;
- `summable_quittingOpponentClockCharge_canonicalPhantom`;

both in
`UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanClockReduction.lean`.
Its marginal hazards are all zero. Thus zero persistence contains no positive
semantic information without provenance.

The phrase “zero-persistent, all-Continue-type spine” should not be read as a
classification saying every zero-persistent spine is literally constant
all-Continue. The exact conclusion is only that all marginal hazard series
are summable. The canonical phantom is the decisive regression example.

### Exactly one persistent label

The checked table in
`UniformEquilibrium/Quitting/Paths/OneOwnerPersistentLabelObstruction.lean`
has a stationary exact spine where one owner Quits surely forever and every
outsider Continues. It satisfies:

- `isCanonicalExactQuittingNashBellmanSpine_oneOwnerImmediateExit`;
- `not_hasTwoPersistentQuittingMarginals_oneOwnerReward`; and
- `zero_isUniformEquilibriumPayoff_oneOwnerHazardObstruction`.

This is fully consistent with the new theorem. The owner is
punishment-normal, and the theorem reconstructs the already available zero
uniform payoff. It confirms that the conclusion must be “uniform payoff,”
not “a second label appears on the same spine.”

### At least two persistent labels

This boundary is already positive. The exact checked chain is:

```text
HasTwoPersistentQuittingMarginals.survival
nonempty_quittingChronologicalDebtShadowingCertificate_of_exactSpine
quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors
```

in `PersistentDeletedClockTwoLabel.lean`,
`NashBellmanChronologicalForcing.lean`, and
`ChronologicalDebtShadowing.lean` respectively.

An even shorter contradiction proof uses
`hasTwoPersistentQuittingMarginals_iff_all_opponentClocks` together with
`uniformEquilibriumPayoff_or_summableClock_of_exactNashBellmanSpine`.
The summable-clock alternative is impossible when two labels are persistent,
so `value 0` is a uniform-equilibrium payoff.

## 6. Stronger Fin4 consequence

Let `reward` be a four-player table with no uniform-equilibrium payoff. The
checked theorem
`nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
produces a same-table residual whose field

```text
all_punishmentNormal : ∀ who, IsQuittingNormalPlayer reward who
```

makes every possible unique persistent owner normal.

Now fix any canonical exact spine.

- If it has at least two persistent labels, the checked two-label consumer
  gives a uniform-equilibrium payoff, contradiction.
- If it has exactly one persistent label, the theorem reviewed here gives
  its singleton row as a uniform-equilibrium payoff, contradiction.

Therefore the full conclusion is

\[
\boxed{
\neg\exists\text{ uniform-equilibrium payoff}
\quad\Longrightarrow\quad
\forall\text{ exact canonical spines }(v,x),\ \forall i,
\ \sum_t q_{t,i}<\infty.}                         \tag{6.1}
\]

Equivalently, every exact canonical spine on a hypothetical Fin4
counterexample has empty persistent set. Since the player set is finite, its
full one-stage absorption charges are also summable by the union bound (up to
the harmless possibility of finitely many sure-absorption rows when discussing
products from early starts).

This is stronger than the draft's equation (33), and stronger than excluding
only a source-selected one-persistent spine. It gives a useful global
structural necessary condition for any Fin4 counterexample.

The selector consequence can now be stated cleanly: any same-table producer
of one exact canonical spine with even one persistent marginal already
settles the game. If the label is unique, use this theorem; if not, use the
checked two-label branch.

## 7. Novelty comparison

The new content is not the punishment splice or the solo stopping-law cap;
both are checked already.

- `isUniformEquilibriumPayoff_soloReward_of_approximate_caps` is the existing
  target-preserving strategic compiler. It does not derive its cap hypotheses
  from a Nash--Bellman spine.
- `isUniformEquilibriumPayoff_soloReward_of_deletedQuitLimits` in
  `ConditionedDeletedClockSoloCompletion.lean` already packages deletion of
  vanishing outsider hazards once continuation convergence and original
  forced-Quit bounds are supplied. It substantially shortens the Lean
  handoff below.
- `NashBellmanQuitEndpointLimit.lean` controls the active quitter's own scalar
  value by opponent absorption. It does not prove vector convergence to the
  owner's singleton row and does not supply every outsider cap.
- `PersistentDeletedClockTwoLabel.lean` characterizes the two-label branch;
  it says nothing strategic about the unique-label branch.
- `OneOwnerPersistentLabelObstruction.lean` is a negative selector
  regression in a game already possessing an easy equilibrium. It does not
  subsume the normal unique-persistent positive theorem.
- `CODEX_CEDAR__ERGODIC_NASH_BELLMAN_RECURRENCE.md`, Proposition 1C, consumes
  the special recurrent case in which every outsider always Continues. The
  present theorem allows summably many outsider hazards, and the strengthened
  concentration form allows even nonsummable outsider hazards when their
  competing-risk mass tends to zero.

A narrow search found no existing export or Lean declaration asserting the
generic unique-persistent theorem or the global Fin4 all-spines summability
corollary. Subject to formalization, both are novel relative to the inspected
interfaces.

## 8. Exact Lean handoff

The draft proposes three new local adapters. Existing checked declarations
reduce the necessary work to one exact-spine wrapper plus the Fin4 corollary.

### Proposed generic theorem

Create a theorem with a name such as

```text
IsCanonicalExactQuittingNashBellmanSpine.
  isUniformEquilibriumPayoff_soloReward_of_uniquePersistent
```

with hypotheses `howner`, `hother`, and `hnormal` exactly as in Section 1.

The shortest checked route is:

1. Obtain

   ```text
   hclock : Summable (quittingOpponentClockCharge roots owner)
   ```

   from `summable_quittingOpponentClockCharge_iff` and `hother`.
2. Use `quitProbability_le_quittingRootAbsorptionMass` to show that the full
   absorption series is nonsummable from `howner`. Then use
   `tendsto_zero_quittingJointSurvivalWeight_of_not_summable_absorption` on
   every suffix.
3. Identify every stored Bellman value with the literal suffix terminal
   value by
   `eq_quittingRootSequenceTerminalValue_of_exact_bounded_path_of_jointSurvival_tendsto_zero`
   from `UniformEquilibrium/Quitting/Paths/JointSurvivalSelection.lean`.
4. Obtain the quantitative target bound from
   `abs_quittingRootSequenceTerminalValue_sub_soloReward_le_tailCharge`, and
   its vanishing from `tendsto_quittingOpponentClockTailCharge_zero`, both in
   `ConditionedDeletedClockTerminalConcentration.lean`.
5. For each `n`, choose a time `select n >= n` where the owner hazard is
   positive. Nonsummability and nonnegativity guarantee such a date. Strict
   monotonicity is unnecessary; `n <= select n` is enough to transport every
   atTop limit.
6. Apply `isUniformEquilibriumPayoff_soloReward_of_deletedQuitLimits` from
   `ConditionedDeletedClockSoloCompletion.lean` to the sampled rows, with:

   ```text
   hazardError n = quittingOpponentClockCharge roots owner (select n)
   targetError n = 2 * quittingRewardBound reward *
     quittingOpponentClockTailCharge roots owner (select n)
   quitError n = 0
   continuation n = value (select n)
   ```

   The `hazardError` identity is definitional. The target bound is Step 4.
   For each outsider, the original forced-Quit bound follows from
   `quittingRootQuitPayoff_le_successor_of_isZeroNash`,
   `quittingRootQuitPayoff_eq_fixedOpponentsQuitValue`, and the Bellman
   identity. Pass `hnormal` after unfolding `IsQuittingNormalPlayer` and
   `quittingSoloSelfPayoff`.

This route reuses the checked hazard-deletion/cap estimate and the exact
fixed-target punishment compiler. No new phase-switch proof and no new
general coupling lemma are required.

An alternative direct route is to construct the cap error from (2.3) and the
TV perturbation theorem, then invoke
`isUniformEquilibriumPayoff_soloReward_of_approximate_caps`. It is longer and
gives the same theorem.

### Proposed two-persistent helper

Add a small wrapper, if no convenient named wrapper already exists:

```text
IsCanonicalExactQuittingNashBellmanSpine.
  exists_uniformEquilibriumPayoff_of_hasTwoPersistent
```

Use `uniformEquilibriumPayoff_or_summableClock_of_exactNashBellmanSpine` and
rule out its summable-clock branch with
`hasTwoPersistentQuittingMarginals_iff_all_opponentClocks`.

### Proposed Fin4 theorem

Add, in a diagnostics adapter importing the generic theorem and
`FullSupportProjectiveQBarResidual.lean`, a theorem such as

```text
all_marginalQuitHazards_summable_of_finFour_of_no_uniformPayoff
```

whose conclusion is

```text
∀ value roots,
  IsCanonicalExactQuittingNashBellmanSpine reward value roots ->
  ∀ who, Summable (quittingMarginalQuitHazard roots who).
```

Obtain the hard residual with
`nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
using `abs_reward_le_quittingRewardBound`. For a nonsummable marginal, split
on whether a second nonsummable marginal exists. Dispatch the two-label case
through the helper and the unique case through the new generic theorem with
`H.all_punishmentNormal who`. Both contradict the assumed absence of every
uniform-equilibrium payoff.

## 9. Recommended final export content

The revised packet should lead with two theorems:

1. **Generic named-payoff theorem.** A normal uniquely persistent owner on a
   bounded exact Nash--Bellman spine makes its singleton reward vector a
   uniform-equilibrium payoff.
2. **Fin4 global corollary.** On the no-uniform branch, every marginal hazard
   on every exact canonical spine is summable.

Then include:

- the exact `c_t` tail estimate (2.3), optionally followed by the sharper
  survival-weighted estimate (2.4);
- the solo cap bound and the citation to
  `isUniformEquilibriumPayoff_soloReward_of_approximate_caps` or the shorter
  `isUniformEquilibriumPayoff_soloReward_of_deletedQuitLimits` handoff;
- the zero-, one-, and two-persistent boundary tests above;
- the exact declaration ledger; and
- the explicit nonclaim that no nonempty-persistence source selector has yet
  been produced.

Do not assign an `L` seal until the new exact-spine wrapper and Fin4 corollary
compile. With the target-consumer citation corrected, the malformed formulas
repaired, and the stronger Fin4 corollary included, I recommend export as a
reviewed ordinary-mathematics result.
