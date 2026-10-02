# Zero-boundary phantom carrier

Author: `CODEX_CEDAR`
Status: `OMEGA SHIFT VALID, BUT ZERO-BOUNDARY PROVENANCE ALONE IS EXHAUSTED; RESET MASS ESCAPES`

Conjecture-closing thesis tested here: work inside the full compact exact Nash--Bellman
predecessor relation, but retain provenance from arbitrarily long finite
chains ending at the literal zero boundary.  The omega carrier of those
chains has an exact shift relation.  Apply the checked opponent-clock
dichotomy to an infinite carrier spine.  Divergence of every deleted-player
opponent clock already gives a uniform-equilibrium payoff.  In the remaining
summable-clock branch, use the zero-boundary approximants to identify the
stored all-Continue phantom annotation with a genuine behavioral punishment
endpoint, or produce a positive punishment-floor-admissible return.  Either
conclusion closes the branch for an arbitrary finite quitting game.

Precise universal obligation tested by this work: prove the following
phantom-realization implication for every finite quitting game.  Let
`x^H_0,...,x^H_H` be arbitrary exact Nash--Bellman chains with
`x^H_H=(0,allContinue)`, let a fixed finite prefix converge as `H -> infinity`,
and suppose one player's opponent clock on the limiting spine is summable
with positive deleted survival.  Then either:

1. some reached tail launches floor-admissible exact blocks of a common
   positive absorption charge back into the same omega carrier; or
2. the limiting annotation in the exceptional coordinate equals a payoff
   delivered by a credible stationary-opponent punishment profile, so the
   phantom can be compiled rather than merely stored.

The quantifiers are over **all** zero-boundary exact predecessor chains, not
one classical-choice orbit, and the conclusion must price every unilateral
behavioral deviation.  A value-only all-Continue self-loop is not sufficient.

Kill criterion: abandon this carrier thesis if one actual finite quitting
game admits a zero-boundary omega spine with a positive-survival summable
opponent clock, a nonrealized nonzero all-Continue limit annotation, bounded
absorption on every floor-admissible return from its omega carrier, and no
credible punishment profile delivering that annotation.  Such an example
would show that zero-boundary provenance does not remove the phantom and
would force either a richer chronological state (deleted-clock/stopping-law
data) or an all-behavior negative-gap construction.

Outcome of the kill check: the compact shift lemma is valid, but even the
one-player positive-solo game realizes the constant all-Continue phantom as
a limit of arbitrarily deep literal-zero chains.  The terminal reset and all
of its refusal credit escape to the last date.  The exact finite accounting
below shows that the lost datum is precisely the already integrated dynamic
debt/stage-gap transport, not a new consequence of omega provenance.

Next concrete question after this exhausted route: test the conjecture-facing
hard-branch assembly in Noether Proposition 43.  In particular, determine
whether the survival-jump lemma can be applied to every row before a selected
crossing and whether the resulting purified prefix satisfies the exact
NearFeasible/clock hypotheses of the checked cyclic-orbit consumer.  A valid
assembly would supply the universal chronological datum that the omega
carrier does not retain.

Everything below is ordinary mathematics unless a named declaration is
explicitly described as proved in Lean.  No Lean file or export is proposed.

## 1. Why the earlier one-active thesis is dead

`periodTwo_residualHardClass` and
`periodTwo_residualHard_fullCore_nonstationary_but_uniform` in
`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean`
place the Solan--Vieille `boundaryReward` in the full-normal standard-Q,
no-homogeneous residual-hard branch.  The ordinary positive exploitability
floor audited in
`feedback/CLAUDE_HILBERT__SINGLETON_LOTTERY_LIMITS__BY_CODEX_CEDAR__ROUND_2.md`
applies to every live calendar having at most one positive prescribed hazard
per date.  Yet `periodTwo_isUniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwo.lean`
gives an exact ordinary equilibrium alternating the two genuinely two-active
roots `{0,2}` and `{1,3}`.

This also fixes a terminology trap in the production circulation interface.
Although a `FaceCirculationCertificate` may have a multi-owner phase mixture,
`exists_multiCirculation_orbit` in
`UniformEquilibrium/Quitting/Circulation/MultiOwnerFaceCirculationOrbit.lean`
uses `balancedWord` and `multiRow`; every micro-row is a `singletonRow`.
`hasQuittingOneActiveSupportRationalDivergentPaths_of_multiCirculation` in
`UniformEquilibrium/Quitting/Circulation/KActiveCompactPath.lean` states the
resulting invariant literally as `K=1`.  Hence that compiler cannot consume
the residual-hard boundary table at arbitrarily small error.

The general checked endpoint remains
`quittingGame_exists_uniformEquilibriumPayoff_of_KActivePaths` in
`UniformEquilibrium/Quitting/Circulation/KActiveCompactPath.lean`.  At
`K=card(I)` its hypothesis is exactly the unrestricted support-rational
divergent-path problem by
`hasQuittingFintypeCardActivePaths_iff_unrestricted`; the support-card label
alone supplies no producer.

## 2. Exact compact relation and the provenance defect

`quittingNashBellmanSerialRelation` in
`UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean` is a
compact serial exact predecessor correspondence: every bounded tail has a
bounded exact one-stage Nash predecessor.  `NashBellmanFactory.lean` anchors
finite predecessor iteration at the literal state

```text
(zero payoff, all-Continue root)
```

and proves `exists_finiteZeroBoundaryExactQuittingNashBellmanChain` for every
cutoff.  In contrast, arbitrary compact infinite-spine selection is vacuous:
`canonicalPhantom_isExactQuittingNashBellmanSpine` in
`NashBellmanClockReduction.lean` keeps the reward bound as a stored
continuation vector forever while everyone continues.

For any supplied bounded exact spine,
`uniformEquilibriumPayoff_or_summableClock_of_exactNashBellmanSpine` in
`NashBellmanClockReduction.lean` gives the exact universal alternative:

- if every player-deleted opponent clock diverges, `value 0` is already a
  uniform-equilibrium payoff;
- otherwise one owner has a summable opponent clock and a positive-survival
  suffix.

Thus selection of an infinite spine is not the hard step.  The hard step is
to retain enough terminal-zero provenance through compactness to rule out or
realize the second branch.

## 3. Punishment-floor comparison

There is a second, independently useful exact relation.  The punishment
floor is predecessor-invariant by
`quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge` in
`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorForward.lean`.
The full reachable charged relation and its canonical budget-to-go potential
are defined in
`PunishmentFloorChargedRelation.lean` and
`PunishmentFloorChargedPotential.lean`.  The checked alternative
`quittingGame_uniformPayoff_or_punishmentFloorReachable_hasFiniteBudget` in
`PunishmentFloorFinitePrefixChargedBridge.lean` says that unbounded exact
floor-prefix charge already yields a uniform payoff; otherwise every
reachable path has finite charge.  A positive exact return is consumed by
`quittingGame_exists_uniformPayoff_of_positive_reachable_return` in the same
file.

Under a terminal exploitability witness, `infiniteOrbit_exists_selfLoop_limit`
in `UniformEquilibrium/Diagnostics/Quitting/Capacity/InfiniteOrbitLimit.lean`
shows that every punishment-floor orbit converges to an exact all-Continue
Nash--Bellman self-loop above both the punishment floor and all solo rewards.
The file explicitly records the missing point: this limit is a Bellman
annotation, not the realized payoff of a strategy profile.

The new route therefore does not seek another self-loop theorem.  It seeks a
realization theorem from **zero-boundary omega provenance** or a positive
return before the phantom limit.

## 4. Ordinary omega-carrier construction to prove

Let `X` be the canonical compact Nash--Bellman box, `R(x,y)` mean that `x`
is an exact predecessor of tail `y`, and let `z=(0,allContinue)`.  For
`H>=0`, define

```text
S_H = {x_0 in X : there are x_0,...,x_H with
                     R(x_t,x_{t+1}) for t<H and x_H=z}.

Omega = intersection_N closure(union_{H>=N} S_H).
```

Every `S_H` is nonempty by serial predecessor existence and `X` is compact,
so `Omega` is nonempty compact.  The first exact shift claim is:

```text
for every x in Omega, there is y in Omega with R(x,y).        (4.1)
```

Indeed choose `H_k -> infinity` and chains with `x^k_0 -> x`.  Compactness
gives a subsequence `x^k_1 -> y`; because `x^k_1 in S_{H_k-1}`, `y in
Omega`; closedness of the edge graph gives `R(x,y)`.  Dependent choice then
selects an infinite exact spine entirely inside `Omega`, to which the checked
clock alternative applies.

This is set-valued and does not privilege the classical predecessor chosen by
`quittingFiniteNashBellmanState`.  It also does not yet imply that the
canonical reward-bound phantom is absent: exclusion requires showing that it
is not approximable by arbitrarily deep chains ending at literal zero.

## 5. Proved and unproved separation

Proved in Lean under the named imports:

- compact serial exact predecessor existence and zero-boundary finite chains;
- the all-behavior opponent-clock alternative for a supplied exact spine;
- punishment-floor invariance, the reachable finite-budget alternative, and
  the positive exact return consumer;
- convergence of bounded-charge punishment-floor orbits to a value-only
  all-Continue exact self-loop.

Proved here as ordinary compactness, pending an independent review:

- the set-valued omega carrier is nonempty and satisfies the forward shift
  property (4.1).

Not proved:

- that the omega carrier lies above the punishment floor;
- that a summable-clock omega spine yields a credible punishment endpoint;
- that a nonrealizable phantom forces a positive exact admissible return;
- the universal finite-quitting uniform-equilibrium conjecture.

## 6. Exact finite refusal-credit identity

The narrow source search found the relevant existing quantities rather than
a new independent carrier invariant.  Fix a finite exact Nash--Bellman chain
of length `H`, a player `i`, and write

```text
v_t       = stored value of i at date t,
c_t       = probability that every opponent of i Continues at date t,
A_t       = current absorbing contribution when i is forced to Continue,
Q_t       = payoff when i is forced to Quit,
C_t       = A_t + c_t v_{t+1},
g_t       = Q_t - C_t,
W_t       = product_{s<t} c_s.
```

Exact policy evaluation and exact root Nash give

```text
v_t = max(Q_t,C_t) = C_t + max(0,g_t).                 (6.1)
```

The first equality is the scalar content of
`quittingPrescribedOneStepResidual_finiteNashBellmanPath_eq_zero_of_edges`
in
`UniformEquilibrium/Quitting/Debt/Dynamic/FiniteDynamicDebtChains.lean`.
The gap `g_t` is exactly `quittingStageGap` from
`UniformEquilibrium/Quitting/Debt/Dynamic/DebtTransportLaw.lean`.
Iterating (6.1) gives the exact ordinary identity

```text
v_0 = sum_{t<H} W_t A_t + W_H v_H
        + sum_{t<H} W_t max(0,g_t).                   (6.2)
```

For the literal zero boundary, `v_H=0`, and the first sum is the actual
finite payoff from forcing `i` to Continue throughout.  It is also
`quittingFirstOpponentRawMean`, by
`quittingFirstOpponentRawMean_eq_sum_continueReward` in
`UniformEquilibrium/Quitting/Debt/Marked/FenceFirstOpponentAdapter.lean`.
Thus the checked inequality
`quittingFirstOpponentRawMean_le_value_of_finiteExactChain` has the sharper
exact explanation

```text
v_0 - Never_i(0,H) = sum_{t<H} W_t max(0,g_t).        (6.3)
```

Complementarity localizes every positive summand.  If the prescribed
Continue probability of `i` is positive, its pure Continue endpoint equals
the mixed root payoff, hence `max(0,g_t)=0`.  Therefore

```text
max(0,g_t)>0  implies  i quits surely at t.           (6.4)
```

This is not a new dynamic-debt theorem.  Substituting (6.3) into the checked
closed transport law
`quittingFiniteDynamicDebt_eq_max_zero_sub_accumulatedStageGaps` in
`DebtTransportLaw.lean` gives, for terminal debt `d_i>=0`,

```text
D_i(0,H) = max(0, W_H d_i - (v_0-Never_i(0,H))).      (6.5)
```

So the zero-boundary chain can pay terminal singleton debt only through
survival-weighted sure-own-Quit refusal credit.  Taking only a fixed-prefix
limit forgets exactly the late credit appearing in (6.3)--(6.5).

## 7. Exact escaping-reset falsifier

Let there be one player and let their singleton quitting reward be `b>0`.
For every `H>=1`, take

```text
v_t=b                 for 0<=t<H,
v_H=0,
root_t=all-Continue   for 0<=t<H-1,
root_{H-1}=sure Quit.
```

At every earlier row the pure Quit and Continue endpoints both equal `b`.
At the last row the endpoints are `Q=b` and `C=0`, so sure Quit is exact
Nash and the Bellman value is `b`.  Hence this is an exact zero-boundary
chain of every length.  Every fixed prefix converges to the constant state
`(b,all-Continue)`, whose opponent clock is identically zero.  The sole
positive refusal credit `b` sits at date `H-1` and escapes every fixed
prefix; (6.2) reads simply `b=0+b`.

This example does not refute the quitting-game conjecture: `b` is itself a
credible solo-quitting endpoint.  It does refute the proposed structural
step that literal-zero provenance excludes a nonzero all-Continue phantom.
More generally, the omega carrier retains neither the position of escaping
sure-Quit resets nor the terminal dynamic debt they discharge.

## 8. Route verdict

The set-valued omega shift (4.1) is valid ordinary compactness, but it adds
no usable chronological datum to the existing exact-debt architecture.
Equations (6.3)--(6.5) identify the missing datum with the same moving
survival-weighted positive stage gaps already tracked by
`FiniteDynamicDebtChains.lean`, `DebtTransportLaw.lean`, and the atom-access
frontier.  Recovering it requires moving-window chronology, not a frozen
omega state.  The carrier thesis is therefore exhausted as an independent
universal producer; it should not be exported or presented as closing the
summable-clock branch.
