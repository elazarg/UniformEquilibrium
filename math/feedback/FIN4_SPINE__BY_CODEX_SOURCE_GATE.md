# Source/API audit of `FIN4_SPINE`

Reviewer: `CODEX_SOURCE_GATE`

Target: [`gpt/FIN4_SPINE.md`](../archive/FIN4_SPINE.md)

## Verdict

The central ordinary-mathematics theorem is **sound**, and its Fin4
specialization really does close the exactly-one-persistent alternative in
[`questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md`](../questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md),
equivalent useful output 4.

There is one mandatory API correction before this should be presented as a
source-exact handoff. The theorem
`quittingStationarilyGeneratedApproximateEquilibria_of_approximate_solo_caps`
does implement the required finite solo-prefix/actual-punishment construction
against arbitrary behavioral deviations, but its conclusion forgets the
prescribed payoff target. Its standard consumer proves existence of *some*
uniform-equilibrium payoff. It does not by itself prove that the particular
vector `r({p})` is the uniform-equilibrium payoff.

The stronger boxed target claim is nevertheless already supported by the
correct checked API:

- `isUniformEquilibriumPayoff_soloReward_of_approximate_caps` in
  `UniformEquilibrium/Quitting/Punishment/ApproximateCompletedCycle.lean`
  has exactly the needed cap and punishment hypotheses and concludes that
  `quittingSoloReward reward p = r({p})` is a uniform-equilibrium payoff; or
- the profiles constructed in the note can be passed directly to
  `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget`
  in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalTargetSemantics.lean`.

Thus this is a citation/handoff mismatch, not a mathematical gap. No hidden
attainment assumption or strategy-class weakening was found.

This review is ordinary mathematics and a declaration audit. It does not
confer Lean status.

## Claim checked

Let `value t` and `roots t` be a uniformly bounded exact Nash--Bellman spine.
Suppose one player `p` has nonsummable marginal Quit hazard and every other
player has summable marginal Quit hazard. If `p` is punishment-normal, then
the singleton reward vector

```text
quittingSoloReward reward p
```

is a uniform-equilibrium payoff. Consequently, in the Fin4 no-uniform-payoff
hard residual, no exact bounded spine has exactly one persistent player.

For a Lean statement, persistence should be expressed with the repository's
actual convention:

```text
¬ Summable (quittingMarginalQuitHazard roots p)
∀ j, j ≠ p → Summable (quittingMarginalQuitHazard roots j)
```

rather than by treating an infinite real series as literally equal to
infinity.

## Exact declaration audit

### 1. Bounded exact Nash--Bellman spine

`IsCanonicalExactQuittingNashBellmanSpine` is defined in
`UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanClockReduction.lean`.
It records exactly:

1. `|value time who| <= quittingRewardBound reward`;
2. the Bellman identity
   `value time = quittingRootSuccessorPayoff reward (value (time+1)) (roots time)`;
3. `IsεQuittingRootNash reward (value (time+1)) 0 (roots time)`.

`exists_bounded_exact_quittingNashBellmanSpine` and its canonical-bound wrapper
`exists_exact_quittingNashBellmanSpine` are in
`UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean`.

The note's generic proof only needs some common bound on `value` and the
terminal table, so it is slightly more general than the canonical structure.
The existing canonical structure is sufficient for the maintained Fin4
question. A Lean theorem intended for arbitrary bounded spines should either
take the bound explicitly or specialize to `IsCanonicalExact...`.

The relevant persistence vocabulary is in
`UniformEquilibrium/Quitting/Paths/PersistentDeletedClockTwoLabel.lean`:

- `quittingMarginalQuitHazard`;
- `HasTwoPersistentQuittingMarginals`;
- `hasTwoPersistentQuittingMarginals_iff_all_suffix_survival_zero`; and
- `HasTwoPersistentQuittingMarginals.survival`.

### 2. Punishment value and normality

The definitions in `UniformEquilibrium/Quitting/Stationary/MinMax.lean` have
the full behavioral quantifiers required by the note:

```text
quittingBestReplyValue reward profile who
  = sup over every BehaviorStrategy replacement of who

quittingPunishmentValue reward who
  = inf over every BehaviorProfile of that full best-reply value.
```

The same file proves:

- `quittingBestReplyValue_stationary`: the best reply against a constant row,
  over all behavioral deviations, equals `quittingStationaryUnilateralCap`;
- `quittingPunishmentValue_eq_stationaryPunishmentValue`: the full behavioral
  min--max equals the infimum of stationary-row caps.

The file explicitly warns that the infimum need not be attained. The note
does not need attainment. For every positive slack,
`exists_stationaryRoot_cap_lt_punishmentValue_add` in
`UniformEquilibrium/Quitting/Paths/SupportWitnessIndividualRational.lean`
selects an actual stationary row with cap strictly below punishment value plus
that slack. Together with `quittingBestReplyValue_stationary`, this supplies
the actual punishment profile used in Step 3.

`IsQuittingNormalPlayer` is defined in
`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean` as

```text
quittingPunishmentValue reward who <= quittingSoloSelfPayoff reward who.
```

For `who = p`, the right side is precisely the `p` coordinate of
`quittingSoloReward reward p = r({p})`. The note's punishment-normality
hypothesis therefore matches the checked definition exactly.

### 3. Solo caps and the stationarily-generated construction

The formula used in equation (20) is checked. For `i != p` and positive owner
hazard,
`quittingStationaryUnilateralCap_solo_other` in
`UniformEquilibrium/Quitting/Boundary/Exceptional/TailFallback.lean` gives

```text
cap_i(solo(p,q)) = max(immediate-Quit value, r_i({p})).
```

`quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix` in
`UniformEquilibrium/Quitting/Stationary/SingletonStationaryRoot.lean`
identifies the immediate-Quit term with the mixture of `r_i({i})` and
`r_i({i,p})` displayed in the note. By
`quittingBestReplyValue_stationary`, this is the cap over arbitrary
time-dependent behavioral stopping, not only stationary or one-stage
deviations.

`quittingStationarilyGeneratedApproximateEquilibria_of_approximate_solo_caps`
in
`UniformEquilibrium/Quitting/Classification/Existence/NoHarmSingletonGenerated.lean`
takes exactly:

- positive owner hazards;
- nonnegative outsider-cap errors tending to zero;
- the full stationary unilateral-cap bound for every outsider; and
- owner punishment-normality.

It produces `QuittingStationarilyGeneratedApproximateEquilibria`. Its proof
uses a long finite solo prefix, an actual near-minmax stationary punishment,
and the full root-sequence deviation inequality. The latter quantifies over
every time-indexed hazard. The equivalence
`isεQuittingRootSequenceNash_iff_isεAsymptoticNash` in
`UniformEquilibrium/Quitting/Paths/SurvivalWindowLanding.lean` identifies this
with arbitrary behavioral replacement in the quitting game.

The conclusion, however, contains no target-payoff field. The checked chain

```text
QuittingStationarilyGeneratedApproximateEquilibria
  -> QuittingApproximateEquilibriumExistence
  -> exists some uniform-equilibrium payoff
```

is implemented by
`quittingApproximateEquilibriumExistence_of_stationarilyGenerated` and
`quittingGame_exists_uniformEquilibriumPayoff_of_approximateEquilibriumExistence`
in
`UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedBranch.lean`.
That chain suffices for the Fin4 contradiction, but not for the stronger
generic assertion that the selected payoff equals `r({p})`.

For the exact target, the direct theorem
`isUniformEquilibriumPayoff_soloReward_of_approximate_caps` in
`UniformEquilibrium/Quitting/Punishment/ApproximateCompletedCycle.lean` has the
same hazard/error/cap/punishment inputs and concludes the desired singleton
vector. Its proof invokes the fixed-target terminal consumer. This is the
narrowest checked endpoint for the note.

### 4. Terminal-to-uniform selection

The target-free equivalence
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` is
in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
It selects some fixed payoff by compactness.

The theorem actually matching equations (26)--(31) is
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget`
in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalTargetSemantics.lean`.
It assumes terminal approximate Nash profiles at every positive error whose
terminal payoffs approach one declared target, and concludes that exact target
is a uniform-equilibrium payoff. The note proves precisely those two fields
for `R = r({p})`.

`StochasticGame.IsεAsymptoticNash`, defined in
`UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Asymptotic.lean`,
quantifies over every `BehaviorStrategy` deviation. There is no bounded-clock,
finite-support, stationary-deviation, or bounded-memory restriction here.

### 5. Fin4 hard residual

`FinFourQuantitativeFullSupportHardResidual` is defined in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.
Its field

```text
all_punishmentNormal : ∀ who, IsQuittingNormalPlayer reward who
```

is exactly what the generic theorem needs.

The checked producer is
`nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff` in
the same file. Given a coordinate reward bound and the absence of every
uniform-equilibrium payoff, it returns a nonempty hard residual. Taking the
canonical `quittingRewardBound reward` supplies its bound hypothesis. After
unfolding `IsQuittingNormalPlayer`, the field gives

```text
quittingPunishmentValue reward p <= reward (quittingSingletonTerminal p) p.
```

There is no change of table and no source-attainment assumption in this
adapter.

## Independent mathematical check

### Singleton-tail convergence

Let `q(t,i)` be the Quit probability in the root at time `t`, let

```text
s_t = sum_{j != p} q(t,j),
a_t = product_{j != p} (1-q(t,j)),
c_t = 1-a_t.
```

Finite union bounds give `0 <= c_t <= s_t`, so outsider summability makes
`sum c_t` finite. Separating the Bellman expectation according to whether an
outsider Quits gives

```text
v_t - R = a_t (1-q(t,p)) (v_(t+1)-R) + e_t,
|e_t|_infinity <= 2 K c_t.
```

The owner product vanishes because its nonnegative hazard series diverges.
Iteration therefore yields

```text
|v_t-R|_infinity <= 2 K * sum_{s>=t} c_s,
```

and hence `v_t -> R`. This part is correct and uses no unproved interchange
of expectation, supremum, or limit.

### Solo reprojection

For an outsider `i`, exact root Nash may be tested only against pure Quit.
After forcing `i` to Quit, replacing all outsiders other than `p` by Continue
changes the terminal payoff only on the event that one of those players
Quits. Its probability is at most `s_t`, and the payoff change is at most
`2 K s_t`. Thus the immediate-Quit value in the solo row satisfies

```text
A_(t,i) <= R_i + |v_t-R|_infinity + 2 K s_t.
```

The checked stationary solo-cap formula then gives the same bound for the
full behavioral cap. The error is nonnegative and tends to zero.

Nonsummability of the owner's nonnegative hazard implies that positive owner
hazards occur arbitrarily late. For the sequence-valued checked solo-cap
theorem, the formalization must explicitly enumerate a strictly increasing
subsequence of such dates; the induced error still tends to zero. An equally
clean alternative is to choose one sufficiently late positive-hazard date for
each requested terminal accuracy and invoke
`exists_isεAsymptoticNash_close_soloReward_of_cap_of_punishmentIR` directly.
The current prose performs the latter selection informally, so there is no
ordinary-mathematics gap, but the subsequence/accuracy choice belongs in the
Lean handoff.

### Punishment seam and fixed target

The note's finite-prefix estimates are correct. Under an outsider deviation,
the finite-prefix profile and the infinite solo profile can differ only if
the owner survives the prefix, whose probability remains `(1-q)^N`
independently of that outsider's deviation. Under an owner deviation, quitting
inside the prefix pays exactly `R_p`, while reaching the actual punishment
tail is bounded by its full behavioral best-reply cap. The prescribed payoff
differs from `R` only on the tail-reach event.

The resulting profiles are terminal approximate Nash against every behavioral
replacement and converge in payoff to the fixed vector `R`. This is exactly
the hypothesis of the checked fixed-target consumer. The note correctly
rejects the shortcut of treating the infinite solo row itself as an exact
global equilibrium when the owner may prefer Never.

## What the result closes

Assume a four-player table has no uniform-equilibrium payoff. The checked
hard-residual producer gives a same-table residual in which every player is
punishment-normal. If any exact bounded spine had exactly one persistent
player `p`, the generic theorem would make `r({p})` a uniform-equilibrium
payoff, contradicting the premise. Therefore every such spine has either zero
or at least two persistent labels.

This is precisely equivalent useful output 4 of
`FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md`: the one-persistent alternative
is incompatible with the Fin4 hard residual. It is stronger than excluding
one selected spine because it excludes every exactly-one-persistent bounded
exact spine on the table.

It does **not** prove equivalent output 1, which also asks to consume the
zero-persistent case, and it does not yet prove the question's main boxed
two-label selector. The remaining producer obligation is exactly the one the
note states: on the no-uniform branch, select an exact source spine with a
nonempty persistent set. The all-Continue zero-persistent phantom remains
live.

If two persistent labels are later supplied on one canonical exact spine,
`HasTwoPersistentQuittingMarginals.survival` gives joint and every
deleted-player survival on every suffix, and
`nonempty_quittingChronologicalDebtShadowingCertificate_of_exactSpine` in
`UniformEquilibrium/Quitting/Debt/Dynamic/NashBellmanChronologicalForcing.lean`
supplies the zero-debt, zero-discrepancy, zero-direct-forcing certificate.
This downstream statement is conditional on the same root sequence and does
not itself produce a nonzero persistent set.

## Mandatory handoff corrections

1. Replace the claim that the stationarily-generated consumer proves the
   exact target `r({p})` with the direct citation
   `isUniformEquilibriumPayoff_soloReward_of_approximate_caps`, or explicitly
   use the approximate-target terminal consumer.
2. In a Lean theorem, express persistence using `Summable`/`¬Summable` and
   record the late positive-hazard subsequence or the equivalent per-accuracy
   selection.
3. Name
   `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
   as the hard-residual producer, and unfold `IsQuittingNormalPlayer` when
   passing its field to the solo-payoff consumer.
4. Keep the scope fence: output 4 is closed; the zero-persistent producer and
   the full two-label selector are not.
5. Before export, repair the malformed displayed-math delimiters and tokens
   such as `===` and `|...|*infty`; this is presentational but currently makes
   several formulas ambiguous.

After corrections 1--4, the declaration map and mathematical scope are
source-exact. The new formal work is the singleton-tail convergence and
solo-cap reprojection (plus routine selection/packaging), not a new punishment
or terminal-to-uniform compiler.
