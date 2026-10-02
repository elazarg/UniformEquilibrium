# Independent review: Fin4 minimum-law pure-Never contraction

**Reviewer:** `CODEX_MINER`  
**Verdict:** **PASS mathematically; one mandatory source/proof-writing repair
before packet assembly.**  After that repair I recommend a narrow export for
formalization.  This review was performed independently of the existing Euler
review.

## Claim audited

For a joint terminal-semantic/law carrier point `point=(z,mu)`, assume that
`z` is a positive global minimum of ordinary terminal-semantic total debt and
that every player is punishment-normal.  If `mu none=1`, then `z.1=0`, every
own-singleton reward is strictly negative, and the literal all-Continue
(`all-Never`) profile is exact terminal Nash against every behavioral
unilateral deviation.  Its zero payoff is uniform.  Hence a `Fin 4` hard
residual minimum-law lift cannot have all mass on `none`; every such law has a
positive finite coalition coordinate.

The theorem is correct.  The joint-law argument does not assert attainment of
`mu` by one profile, and the strategic conclusion is proved using a different
literal profile only after the reward signs have been derived.

## 1. Joint carrier projection and simplex boundary

### Ordinary-carrier projection: PASS, but absent from the note's audit

The minimum-fiber singleton theorem requires

```text
z ∈ quittingTerminalSemanticCarrier reward.
```

This follows from joint carrier membership by the checked declaration

```text
terminalSemanticLawCarrier_fst_mem_carrier point hpoint
```

in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceRatio.lean`.
The note's exact assumptions are therefore sufficient, but Section 2.2 and
the declaration audit must cite this projection explicitly.  This is the one
mandatory repair.

### `mu none=1`: PASS

`terminalSemanticLawCarrier_mass_mem_stdSimplex` gives

```text
forall outcome, 0 <= mu outcome,
sum outcome, mu outcome = 1.
```

Using `Fintype.sum_option`, the latter is

\[
  \mu(\mathrm{none})+
  \sum_S\mu(\mathrm{some}\,S)=1.
\]

When `mu none=1`, the finite-coordinate sum is zero.  Every summand is
nonnegative, so each `mu (some S)=0`.  There is no missing possibility from a
zero or singleton player type; the outcome type is finite, and the argument
also works when the finite-coalition subtype is empty.

The exact orientation of
`terminalSemanticLawCarrier_rewardMoment` is

```text
quittingTerminalRewardMoment reward point.2 = point.1.1.
```

`quittingTerminalOutcomeReward reward none=0`, while every finite coefficient
has just vanished.  Thus its left side is the zero payoff vector and `z.1=0`,
as claimed.

## 2. Punishment-normal singleton signs

**PASS.**  The checked theorem
`minimumTerminalSemantic_strictSingleton_of_punishmentNormal` requires:

1. `z` in the ordinary carrier;
2. global total-debt minimality there;
3. positive total debt; and
4. for every player `i`,
   `quittingPunishmentValue reward i <= reward {i} i`.

Items 2--3 are hypotheses and item 1 is supplied by the projection declaration
above.  In `FinFourQuantitativeFullSupportHardResidual`,
`all_punishmentNormal i` has type `IsQuittingNormalPlayer reward i`.
Unfolding that definition and `quittingSoloSelfPayoff` gives exactly item 4 on
the same reward table.  The theorem therefore yields

\[
 r_i(\{i\})<z^1_i=0
\]

for all four players.  No weak/strict sign was reversed.

The pure-Never contraction theorem itself is actually finite-player generic;
`Fin 4` enters only through the current hard-residual adapter.

## 3. Unrestricted all-Never Nash and uniform payoff

**PASS.**  At error zero,

```text
isεAsymptoticNash_quittingAlwaysContinue_iff reward le_rfl
```

identifies exact terminal Nash of `quittingAlwaysContinueProfile reward` with
`reward {i} i <= 0` for every player.  Its proof bounds the payoff from an
arbitrary complete behavioral replacement strategy, including randomized,
history-dependent, delayed, and Never behavior.  The new strict signs are
more than sufficient.

`quittingTerminalPayoff_quittingAlwaysContinue` makes the prescribed payoff
zero, and
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` upgrades the
exact terminal Nash profile to the uniform-payoff contract.  In the hard
residual this contradicts
`residual.witness.not_exists_uniformEquilibriumPayoff`.  There is no
stationary-strategy-class restriction hidden in this step.

## 4. Positive finite atom corollary

**PASS.**  The contradiction excludes `mu none=1`.  Simplex nonnegativity and
normalization imply `mu none<=1`, hence `mu none<1`, and

\[
 \sum_S\mu(\mathrm{some}\,S)=1-\mu(\mathrm{none})>0.
\]

Finiteness gives at least one positive finite coordinate.  This remains a law
coordinate in the joint carrier.  It becomes a literal suffix atom only after
the separate checked causalization theorem
`exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom`; the note
correctly does not identify it with a prefix root, exact Bellman edge, paid
row, or reset.

## 5. Novelty and export recommendation

A narrow search confirms that the checked
`QuittingMinimumLawNeverOrCausalAtomDispatch` only gives

```text
0 < point.2 none OR a causal finite atom.
```

It explicitly calls the first arm genuine because simplex normalization
alone permits pure Never.  The reviewed result uses the additional same-table
punishment-normal minimum-fiber theorem to exclude only the extreme value
`point.2 none=1`; that is enough to force a positive finite coordinate even
when the Never mass remains positive.  This strictly contracts the named
minimum-law boundary in the Fin4 hard residual and supplies the existing
causal finite-atom adapter unconditionally within that branch.

After adding `terminalSemanticLawCarrier_fst_mem_carrier` to Sections 2.1--2.2
and the source audit, I recommend a narrow export packet containing:

1. the generic finite-player pure-Never contraction;
2. the Fin4 hard-residual positive-finite-coordinate corollary;
3. the two independent reviews; and
4. the exact nonclaim that the causal suffix atom is not yet consumed.

The result does not close the conjecture or the causal-atom chronology.  Its
export value is the strict removal of the pure-Never minimum-law arm, not an
asserted charged return.

## Sources checked

- `terminalSemanticLawCarrier_fst_mem_carrier` in
  `TerminalSemanticResetIncidenceRatio.lean`;
- `terminalSemanticLawCarrier_mass_mem_stdSimplex` in
  `TerminalSemanticResetIncidenceCapReturn.lean`;
- `terminalSemanticLawCarrier_rewardMoment` in
  `TerminalSemanticResetIncidenceReturn.lean`;
- `quittingTerminalOutcomeReward` and `quittingTerminalRewardMoment` in
  `Quitting/Root/TerminalSemanticMoment.lean`;
- `minimumTerminalSemantic_strictSingleton_of_punishmentNormal` in
  `TerminalSemanticFinFourMinimumFiberIsolation.lean`;
- `FinFourQuantitativeFullSupportHardResidual` in
  `Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`;
- `IsQuittingNormalPlayer` and `quittingSoloSelfPayoff` in
  `Quitting/Classification/AbnormalPlayers.lean`;
- `quittingAlwaysContinueProfile`,
  `quittingTerminalPayoff_quittingAlwaysContinue`, and
  `isεAsymptoticNash_quittingAlwaysContinue_iff` in
  `ProofView/Concepts/Stochastic/Models/Quitting/SimpleBranches.lean`;
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` in
  `Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`; and
- `QuittingMinimumLawNeverOrCausalAtomDispatch` and
  `exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` in
  `TerminalSemanticLawCarrierCausalization.lean`.

