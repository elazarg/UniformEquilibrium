# Review of `FIN4_MINIMUM_LAW_PURE_NEVER_CONTRACTION`

**Reviewer:** `CODEX_EULER`  
**Verdict:** **PASS**, with one explicit proof-writing handoff and one useful
strengthening.  The result closes the pure-`Never` minimum-law arm and is
Research-formalization worthy.  A narrow export packet is reasonable after a
separate whole-packet gate.

## Claim checked

Let `point = (z, mu)` belong to the joint terminal semantic/law carrier.  Assume
that `z` is a positive global minimizer of total terminal-semantic debt and
that every player is punishment-normal.  If `mu none = 1`, then `z.1 = 0`,
every own-singleton reward is strictly negative, and the literal all-Continue
profile is an exact terminal Nash profile against unrestricted behavioral
deviations.  Hence zero is a uniform-equilibrium payoff.  In the Fin4 hard
residual this is impossible, so every minimum joint law has a positive finite
coalition coordinate.

## Falsification audit

### 1. Joint-law and reward-moment step: PASS

`terminalSemanticLawCarrier_mass_mem_stdSimplex` gives coordinatewise
nonnegativity and total mass one.  With `mu none = 1`, `Fintype.sum_option`
gives

\[
  \sum_S \mu(\operatorname{some} S)=0.
\]

Every summand is nonnegative, so every finite-coordinate mass is zero.  The
orientation of `terminalSemanticLawCarrier_rewardMoment` is exactly

```text
quittingTerminalRewardMoment reward point.2 = point.1.1.
```

Since the `none` reward is zero and all `some S` coefficients vanish, this
does yield `z.1 = 0` coordinatewise.  No realization of `mu` by one behavioral
profile is used.

One proof-writing step should be stated explicitly before applying the
minimum-fiber theorem:

```text
terminalSemanticLawCarrier_fst_mem_carrier point hpoint
```

from
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceRatio.lean`
supplies `z \in quittingTerminalSemanticCarrier reward`.  The hypothesis list
in the note does not separately assume this, but joint-carrier membership
does imply it, so this is not a mathematical gap.

### 2. Strict singleton sign: PASS

The hypotheses of
`minimumTerminalSemantic_strictSingleton_of_punishmentNormal` are exactly:
ordinary carrier membership, global minimality on that carrier, positive total
debt, and

```text
forall who,
  quittingPunishmentValue reward who <=
    reward (quittingSingletonTerminal who) who.
```

Unfolding `IsQuittingNormalPlayer` and `quittingSoloSelfPayoff` converts the
hard residual's `all_punishmentNormal` field to precisely this last premise.
Thus

\[
  r_i(\{i\}) < z^1_i = 0
\]

for every player.  The strict direction in the note is correct.

### 3. All-Continue compiler: PASS, unrestricted scope confirmed

At error zero,
`isεAsymptoticNash_quittingAlwaysContinue_iff reward le_rfl` says exactly
that the literal all-Continue profile is terminal Nash iff all singleton
self-rewards are nonpositive.  Its proof quantifies over every replacement
behavioral strategy, using the complete unilateral-payoff bound; it is not a
stationary or pure-time test.  The strict inequalities above therefore
suffice.

`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` then gives the
uniform-equilibrium payoff equal to the profile's terminal payoff, and
`quittingTerminalPayoff_quittingAlwaysContinue` identifies it with zero.
This contradicts
`FinFourQuantitativeFullSupportHardResidual.witness.not_exists_uniformEquilibriumPayoff`.

### 4. Finite atom corollary: PASS

In the hard residual, `mu none = 1` is excluded.  Simplex nonnegativity gives
`mu none <= 1`, hence `mu none < 1`; normalization then gives

\[
  \sum_S \mu(\operatorname{some}S)=1-\mu(\mathrm{none})>0.
\]

The coalition index is finite, so at least one coordinate is positive.  This
remains a coordinate of a joint carrier law.  The note correctly invokes
`exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` only as a
separate causalization step and does not identify the atom with a prefix root,
Bellman edge, paid row, or reset event.

## Strongest valid statement

The pure-`Never` contraction itself does not use `Fin 4`.  It is valid for any
finite player type (with the usual decidable equality) under the displayed
positive-minimum and all-punishment-normal hypotheses.  Fin4 is used only to
produce those hypotheses from `FinFourQuantitativeFullSupportHardResidual`
and to contradict its witness.  A formalization should therefore separate:

1. a generic theorem excluding `mu none = 1` by constructing the exact
   all-Continue uniform payoff; and
2. a Fin4 hard-residual corollary returning a positive finite law coordinate
   for every minimum joint-law point.

## Novelty and export assessment

A narrow search found the ingredients but not this composition.  The current
`QuittingMinimumLawNeverOrCausalAtomDispatch` only returns
`0 < mu none` in its first arm; it does not exploit punishment normality to
exclude the extreme value `mu none = 1`.  The reviewed theorem therefore
strictly sharpens the maintained Fin4 minimum-law boundary: every minimum
joint law in the hard residual has a finite atom and can enter the checked
causal suffix-atom theorem.

This is a genuine named-arm contraction, not conjecture closure.  It neither
consumes the resulting causal suffix atom nor produces charge, prescribed-
payoff chronology, support descent, or terminal approximation.  Subject to a
separate packet gate and these nonclaims, I recommend a narrow export for
formalization.

## Sources checked

- `terminalSemanticLawCarrier_mass_mem_stdSimplex` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`;
- `terminalSemanticLawCarrier_rewardMoment` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`;
- `terminalSemanticLawCarrier_fst_mem_carrier` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceRatio.lean`;
- `minimumTerminalSemantic_strictSingleton_of_punishmentNormal` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`;
- `IsQuittingNormalPlayer` and `quittingSoloSelfPayoff` in
  `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`;
- `isεAsymptoticNash_quittingAlwaysContinue_iff` and
  `quittingTerminalPayoff_quittingAlwaysContinue` in
  `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/SimpleBranches.lean`;
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
- `FinFourQuantitativeFullSupportHardResidual` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`; and
- `exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`.
