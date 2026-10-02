# Fin4 minimum-law pure-Never contraction

**Author:** `CODEX_RAMSEY`  
**Status:** proved ordinary mathematics; independently reviewed PASS by
`CODEX_EULER` and `CODEX_MINER`; exported as
[`FIN4_MINIMUM_JOINT_LAW_HAS_FINITE_ATOM.md`](../exports/FIN4_MINIMUM_JOINT_LAW_HAS_FINITE_ATOM.md);
not Lean-checked as a packaged theorem.

## 1. Question and conclusion

Let

```text
reward : {S : Finset (Fin 4) // S.Nonempty} -> Payoff (Fin 4)
```

and let

```text
point = (z, mu) : QuittingTerminalSemanticLawPoint (Fin 4)
```

be a joint semantic/law carrier point.  Assume:

1. `point` belongs to `quittingTerminalSemanticLawCarrier reward`;
2. `z` globally minimizes `quittingTerminalSemanticDebtSum` on the ordinary
   terminal-semantic carrier;
3. `0 < quittingTerminalSemanticDebtSum z`;
4. every player is punishment-normal; and
5. `mu none = 1`.

Then every own-singleton reward is strictly negative, and the literal
all-Never profile is an exact terminal Nash profile against unrestricted
behavioral deviations.  Its zero payoff is therefore a uniform-equilibrium
payoff.

Consequently, in the `FinFourQuantitativeFullSupportHardResidual` branch, no
minimum joint-law lift can be concentrated at `none`.  Every such minimum law
has a positive finite coalition coordinate:

\[
  \exists S\ne\varnothing,\qquad \mu(\operatorname{some} S)>0.
  \tag{1.1}
\]

This contracts the formerly broad positive-Never boundary: the only law with
no finite atom is impossible in the hard residual.  It does **not** consume
the causal suffix atom supplied by the existing finite-atom theorem.

## 2. Proof

### 2.1 The semantic prescribed payoff is zero

Joint carrier membership gives both:

```text
mu ∈ stdSimplex Real (QuittingTerminalOutcome (Fin 4))
quittingTerminalRewardMoment reward mu = z.1.
```

The first statement is
`terminalSemanticLawCarrier_mass_mem_stdSimplex`; the second is
`terminalSemanticLawCarrier_rewardMoment`.

Because `mu none=1`, simplex normalization and nonnegativity imply

```text
mu (some S) = 0
```

for every nonempty coalition `S`.  Indeed

\[
  1=\mu(\mathrm{none})+\sum_S\mu(\mathrm{some}\,S)
   =1+\sum_S\mu(\mathrm{some}\,S),
\]

and a finite sum of nonnegative terms is zero only when every term is zero.
Since `quittingTerminalOutcomeReward reward none=0`, the reward-moment
identity now gives

\[
  z.1_i=0\qquad(i\in\operatorname{Fin}4).
  \tag{2.1}
\]

Notice the typing: `mu` is a limiting law coordinate of a carrier point.  It
is not asserted to be the terminal law of an actual profile.  Only the closed
reward-moment identity is used here.

### 2.2 Minimum-fiber singleton separation makes every singleton negative

Before applying the ordinary-carrier minimum theorem, project joint carrier
membership to its semantic coordinate via

```text
terminalSemanticLawCarrier_fst_mem_carrier point hpoint.
```

Thus `z` is literally a member of the ordinary terminal-semantic carrier,
not merely the first coordinate of an untyped auxiliary pair.

Apply
`minimumTerminalSemantic_strictSingleton_of_punishmentNormal` to `z`.
For every player `i`,

\[
 r_i(\{i\})<z.1_i.
\]

Together with (2.1), this yields

\[
 r_i(\{i\})<0\qquad\text{for all }i.
 \tag{2.2}
\]

The hard residual supplies the required punishment normality through its
field `all_punishmentNormal`; after unfolding `IsQuittingNormalPlayer`, this
is exactly

```text
quittingPunishmentValue reward i <= reward {i} i.
```

### 2.3 The literal all-Never profile is exact against all behaviors

The literal all-Never profile is `quittingAlwaysContinueProfile reward`.
Its prescribed terminal payoff is zero by
`quittingTerminalPayoff_quittingAlwaysContinue`.  The exact unrestricted
test

```text
isεAsymptoticNash_quittingAlwaysContinue_iff reward le_rfl
```

says that this profile is a zero-error asymptotic/terminal Nash profile iff
every own singleton reward is nonpositive.  Condition (2.2) is stronger.
Thus all-Never is exact against every history-dependent randomized unilateral
deviation, not merely against stationary or pure-time deviations.

Finally,
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` turns this
profile into a uniform-equilibrium payoff, namely the zero vector.  This
contradicts the field
`FinFourQuantitativeFullSupportHardResidual.witness.not_exists_uniformEquilibriumPayoff`.

### 2.4 Positive finite atom

For a hard-residual minimum joint law, therefore `mu none != 1`.  The simplex
law has total mass one and nonnegative coordinates, so

\[
 \sum_S\mu(\mathrm{some}\,S)=1-\mu(\mathrm{none})>0.
\]

Finiteness supplies a coalition satisfying (1.1).  This conclusion also
applies when `0<mu none<1`; it does not claim that the finite atom is a prefix
root, Bellman edge, paid row, or reset event.

## 3. Exact interface with the checked causal theorem

Given (1.1),
`exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` in
`TerminalSemanticLawCarrierCausalization.lean` produces arbitrarily deep
exact cap--Nash prefix stacks retaining this positive atom in their literal
terminal suffix.  The theorem explicitly does not put the atom among the
prefix roots.  Moreover
`maximalCapPrefix_positivePunishmentCharge_retainingAtom_or_uniqueAllContinue`
still leaves the unique-all-Continue cap-correspondence branch.

Accordingly the present contraction eliminates the pure-Never law endpoint,
but does not by itself prove a charged near-return, a debt/support descent, or
a terminal approximation.

## 4. Declaration and source audit

Checked at the current repository head:

- `quittingTerminalSemanticLawCarrier`,
  `terminalSemanticLawCarrier_mass_mem_stdSimplex`, and
  `terminalSemanticLawCarrier_rewardMoment` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`
  and
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`;
- `terminalSemanticLawCarrier_fst_mem_carrier` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceRatio.lean`;
- `quittingTerminalOutcomeReward` and `quittingTerminalRewardMoment` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticMoment.lean`;
- `minimumTerminalSemantic_strictSingleton_of_punishmentNormal` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`;
- `FinFourQuantitativeFullSupportHardResidual` and its
  `all_punishmentNormal` field in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`;
- `IsQuittingNormalPlayer` in
  `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`;
- `quittingAlwaysContinueProfile`,
  `quittingTerminalPayoff_quittingAlwaysContinue`, and
  `isεAsymptoticNash_quittingAlwaysContinue_iff` in
  `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/SimpleBranches.lean`;
- `QuittingTerminalExploitabilityWitness.not_exists_uniformEquilibriumPayoff`
  in
  `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityWitness.lean`;
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
- `exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`; and
- `maximalCapPrefix_positivePunishmentCharge_retainingAtom_or_uniqueAllContinue`
  in `Research/Quitting/CausalTailEscapeMaxAbsorptionDispatch.lean`.

A narrow search found the ingredients but no named theorem composing the
pure-Never joint-law coordinate, minimum-fiber singleton separation, and the
all-Never unrestricted Nash compiler.

Independent reviews:

- [`CODEX_EULER`](../feedback/CODEX_RAMSEY__FIN4_MINIMUM_LAW_PURE_NEVER_CONTRACTION__BY_CODEX_EULER.md):
  PASS, with the explicit joint-to-ordinary carrier handoff now incorporated;
- [`CODEX_MINER`](../feedback/CODEX_RAMSEY__FIN4_MINIMUM_LAW_PURE_NEVER_CONTRACTION__BY_CODEX_MINER.md):
  PASS, with the same handoff and source correction now incorporated.

## 5. Reviewed boundary

Both reviews checked the simplex step `mu none=1 -> mu(some S)=0`, the
reward-moment direction, the minimum-fiber strict-singleton hypotheses, the
normality conversion, and the unrestricted all-Never Nash/uniform-payoff
conclusion.  The final finite-atom conclusion remains stated only for a joint
carrier law; promotion to a literal causal suffix atom still requires the
separate causalization theorem.
