# Fin4 hard-residual minimum joint laws have a positive finite terminal atom

Authors: CODEX_RAMSEY

Independent reviews:

- [`CODEX_EULER`](../feedback/CODEX_RAMSEY__FIN4_MINIMUM_LAW_PURE_NEVER_CONTRACTION__BY_CODEX_EULER.md)
- [`CODEX_MINER`](../feedback/CODEX_RAMSEY__FIN4_MINIMUM_LAW_PURE_NEVER_CONTRACTION__BY_CODEX_MINER.md)

## Exact statement

Fix the following data:

```text
I : Type, [Fintype I], [DecidableEq I]
reward : {S : Finset I // S.Nonempty} -> Payoff I
point : QuittingTerminalSemanticLawPoint I
hpoint : point ∈ quittingTerminalSemanticLawCarrier reward
z := point.1
mu := point.2
hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
  quittingTerminalSemanticDebtSum z ≤
    quittingTerminalSemanticDebtSum candidate
hpositive : 0 < quittingTerminalSemanticDebtSum z
hnormal : ∀ who,
  quittingPunishmentValue reward who ≤
    reward (quittingSingletonTerminal who) who
```

Equivalently, let

\[
(z,\mu)\in K_r^{\mathrm{law}}
\]

be a point of the joint terminal semantic/law carrier.  Assume:

1. `z` globally minimizes total terminal-semantic debt on the ordinary
   terminal-semantic carrier;
2. its debt is positive, `D(z)>0`; and
3. every player is punishment-normal:
   \[
   \chi_i\le r_i(\{i\})\qquad(i\in I).
   \]

If the law is concentrated on the infinite all-Continue outcome,

\[
\mu(\mathrm{Never})=1,
\tag{1}
\]

then every singleton self-reward is strictly negative and the literal
all-Continue behavioral profile is an exact terminal Nash profile against
arbitrary behavioral deviations.  Its zero payoff is therefore a
uniform-equilibrium payoff.  Explicitly, for every `who`,

\[
r_{who}(\{who\})<0,
\]

and `quittingAlwaysContinueProfile reward` satisfies the project's
zero-error `IsεAsymptoticNash` predicate for `quittingTerminalPayoff`, while
the zero vector satisfies `IsUniformEquilibriumPayoff none`.

Consequently, fix

```text
reward : {S : Finset (Fin 4) // S.Nonempty} -> Payoff (Fin 4)
bound : Real
residual : FinFourQuantitativeFullSupportHardResidual reward bound
point : QuittingTerminalSemanticLawPoint (Fin 4)
hpoint : point ∈ quittingTerminalSemanticLawCarrier reward
hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
  quittingTerminalSemanticDebtSum point.1 ≤
    quittingTerminalSemanticDebtSum candidate.
```

Then this minimum joint-law point has a positive finite coalition coordinate:

\[
\exists S\ne\varnothing,qquad \mu(S)>0.
\tag{2}
\]

The pure-Never implication is player-count independent.  `Fin 4` enters only
through the hard residual, which supplies punishment normality and excludes
uniform-equilibrium payoffs.

## Conjecture-facing change

The maintained minimum-law boundary previously returned positive Never mass
or a positive finite atom.  This theorem excludes the sole law having no
finite atom, namely the point mass at Never, in the Fin4 hard residual.
Therefore every hard-residual minimum joint law enters the checked
finite-atom causalization theorem
`exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom`.

This strictly removes one source-production arm.  It does not consume the
causal suffix atom or convert it into a prescribed-payoff Bellman edge.

## Definitions and semantic mode

The joint carrier is the closure of pairs consisting of an actual profile's
terminal semantic pair `(U,B)` and its complete terminal-outcome law.  A law
coordinate in this closure need not be realized by one behavioral profile.
The proof uses only checked closed identities: simplex membership, the reward
moment, and projection of the joint carrier to the ordinary semantic carrier.

The terminal outcome space consists of `Never` and the finitely many nonempty
quitter coalitions.  Never has reward zero.  Total debt is

\[
D(z)=\sum_i(B_i-U_i).
\]

Strategies are the project's behavioral strategies on finite public
histories.  A unilateral deviator replaces one player's entire behavioral
strategy while every opponent retains literal all-Continue.  There is no
controller, stationary restriction, or external correlation.  The final
all-Continue Nash claim quantifies over randomized history-dependent
deviations, including every finite quitting time and Never.

## Source correspondence

The joint carrier identities are checked in:

- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`, via
  `terminalSemanticLawCarrier_mass_mem_stdSimplex`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`, via
  `terminalSemanticLawCarrier_rewardMoment`; and
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceRatio.lean`, via
  `terminalSemanticLawCarrier_fst_mem_carrier`.

The strict singleton theorem is
`minimumTerminalSemantic_strictSingleton_of_punishmentNormal` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`.
Punishment normality is represented by `IsQuittingNormalPlayer` in
`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean` and is
supplied by the hard residual's `all_punishmentNormal` field.

The unrestricted all-Continue test and payoff identity are
`isεAsymptoticNash_quittingAlwaysContinue_iff` and
`quittingTerminalPayoff_quittingAlwaysContinue` in
`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/SimpleBranches.lean`.
The terminal-to-uniform consumer is
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

The Fin4 input is
`FinFourQuantitativeFullSupportHardResidual` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.
The downstream causal theorem is in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`.

The literal-infimum bridges are
`quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff` and
`quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`.
The arbitrary-data producer of a minimum joint-law point is
`exists_minimum_terminalSemanticLawCarrier_of_not_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`.

A narrow search found all ingredients but no declaration composing the
pure-Never law coordinate with minimum-fiber singleton separation and the
all-Continue unrestricted compiler.  This is a new composition of project
declarations, not a translation of an AGKRS, Solan--Vieille, or Simon paper
theorem; no paper hypothesis is imported.

## Proof

Let `(z,mu)` satisfy the generic hypotheses and assume (1).

Joint-carrier membership gives

\[
\mu\in\Delta(\{\mathrm{Never}\}\cup\mathcal C)
\quad\text{and}\quad
\operatorname{Moment}_r(\mu)=U(z),
\tag{3}
\]

where `C` is the finite set of nonempty coalitions.  Simplex normalization and
nonnegativity, together with `mu(Never)=1`, imply

\[
\mu(S)=0\qquad(S\in\mathcal C).
\tag{4}
\]

Because the Never reward is zero, (3)--(4) give

\[
U_i(z)=0\qquad(i\in I).
\tag{5}
\]

Use `terminalSemanticLawCarrier_fst_mem_carrier` to place `z` in the ordinary
semantic carrier.  Global minimality, positive debt, and punishment normality
then satisfy the hypotheses of
`minimumTerminalSemantic_strictSingleton_of_punishmentNormal`, yielding

\[
r_i(\{i\})<U_i(z)=0
\qquad(i\in I).
\tag{6}
\]

At the literal all-Continue profile, prescribed payoff is zero.  Against
opponents who always Continue, any finite Quit by player `i` receives the
negative singleton reward in (6), while Never receives zero.  Equivalently,
the checked all-Continue characterization applies at error zero.  Thus the
profile is exact terminal Nash against the full behavioral strategy class,
and the terminal-to-uniform compiler gives the zero uniform-equilibrium
payoff.

Now specialize to a Fin4 hard residual.  Its terminal witness forbids every
uniform-equilibrium payoff, so (1) is impossible.  Since `mu` is a probability
law, `mu(Never)<1`; hence

\[
\sum_{S\in\mathcal C}\mu(S)=1-\mu(\mathrm{Never})>0.
\]

Finiteness and nonnegativity give a coalition satisfying (2).

## Boundary and falsification tests

- **Zero-debt boundary.**  On `Fin 4`, set every terminal reward coordinate
  to zero.  Literal all-Continue realizes `z=(0,0)` and
  `mu=delta_Never`; its debt is the global minimum zero, every player is
  punishment-normal, and singleton rewards are zero rather than strictly
  negative.  Thus positive debt is essential.
- **Mixed-Never boundary.**  On the same zero table, let one player Quit at
  date zero with probability `1/2` and otherwise Continue forever, while all
  opponents always Continue.  The actual terminal law has Never mass `1/2`
  and singleton mass `1/2`.  Hence a finite atom follows immediately whenever
  Never mass is below one.
- The law `mu` is not assumed behaviorally realized.  Only its closed simplex
  and reward-moment identities are used.
- The proof needs equality `mu(Never)=1`, not merely positive Never mass.  If
  `0<mu(Never)<1`, the conclusion (2) already follows from normalization.
- Positive debt is essential for strict singleton separation.
- Punishment normality is required by the present strict-singleton adapter; it
  is not inferred from the law.
- The all-Continue profile is an actual behavioral profile even though `mu`
  may be only a carrier law.
- Strictly negative singleton rewards give exact unrestricted Nash, not just
  a stationary or pure-time test.
- The resulting finite atom remains a coordinate of a joint carrier law.  Its
  realization as an actual finite-time causal atom uses the separate checked
  causalization theorem.

Both independent reviews explicitly checked the carrier projection, simplex
argument, moment orientation, singleton sign, and unrestricted Nash consumer.

## Adapter and consumer

The generic adapter consumes a supplied positive globally minimizing joint
law with punishment normality.  In the Fin4 hard residual,
`exists_minimum_terminalSemanticLawCarrier_of_not_uniformPayoff` supplies a
minimum joint-law point, `all_punishmentNormal` supplies the sign hypothesis,
and the witness supplies nonexistence of a uniform payoff.  The theorem then
constructs either the forbidden zero uniform payoff or, necessarily, a
positive finite law coordinate.

For a supplied globally minimizing `point`, obtain

```text
0 < quittingTerminalDebtSumInf reward
```

from `residual.witness.not_exists_uniformEquilibriumPayoff` and
`quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`.
Obtain the required minimum-value identity from

```text
(quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
  point.1
  (terminalSemanticLawCarrier_fst_mem_carrier point hpoint)
  hminimum).symm.
```

Together with the positive coordinate, these are exactly the remaining
hypotheses of
`exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom`.  It
yields arbitrarily deep literal exact cap--Nash prefix stacks whose front
debts tend to the literal infimum while the selected coalition survives in
the actual suffix chronology.

## Lean handoff

Formalize two principal declarations and, optionally, their causalization
composition.

1. A player-count-independent theorem with the exact generic data and
   hypotheses displayed above, returning every strict singleton sign, exact
   all-Continue terminal Nash, and the zero uniform-equilibrium payoff.
2. A Fin4 theorem with the exact `reward`, `bound`, `residual`, `point`,
   `hpoint`, and `hminimum` quantifiers displayed above, returning a nonempty
   coalition with positive law mass.  Derive positivity from the residual
   witness rather than adding it as an unexplained premise.
3. Optionally compose the second theorem with the named infimum positivity and
   minimum-value identities and
   `exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom`.

Reuse `terminalSemanticLawCarrier_fst_mem_carrier` explicitly before applying
the strict-singleton theorem.  Prove the finite simplex step with the existing
option-sum and nonnegative-sum lemmas; do not add a realization assumption for
the carrier law.

## Scope and nonclaims

This theorem does not prove a uniform payoff for the Fin4 hard residual; it
uses such a payoff to refute the pure-Never law case.  It does not put the
finite atom in a cap-prefix root, make it an exact prescribed-payoff edge,
provide cumulative charge, or consume the unique-all-Continue cap stall.  Its
strict contribution is that every hard-residual minimum joint law enters the
finite-atom/deep-causal source branch.

## Formalization record

The packet was formalized in
`UniformEquilibrium/Diagnostics/Quitting/`
`TerminalSemanticFinFourMinimumLawFiniteAtom.lean`.

The checked declaration inventory is:

- `minimumTerminalSemanticLaw_pureNever_strictSingleton_exactNash_zeroUniform`;
- `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum`;
- `finFourHardResidual_minimumLaw_causalSuffixAtom`; and
- `exists_finFourHardResidual_minimumLaw_causalSuffixAtom`.

The last two declarations return the existing
`QuittingMinimumLawCausalSuffixAtom` structure rather than introducing a
duplicate chronology package.  The residual-only theorem retains the selected
joint point, joint and ordinary carrier membership, its global-minimum
predicate, positive literal debt infimum, equality of its debt with that
infimum, and the same-point causal suffix atom.

Evidence seals:

- **M:** PASS.  Both independent reviews and the final source audit checked
  simplex normalization, moment orientation, strict singleton separation,
  unrestricted all-Continue Nash, and the hard-residual contradiction.
- **L:** PASS.  Direct Lean and the named module build pass.  All four axiom
  probes report only `propext`, `Classical.choice`, and `Quot.sound`.
- **A:** PASS.  The generic theorem consumes a literal joint carrier point;
  the residual-only theorem selects one through the checked minimum joint-law
  producer while retaining all minimum provenance.
- **C:** PASS at the stated boundary.  Pure Never is consumed by the exact
  all-behavior Nash and zero-uniform-payoff compiler.  The positive finite
  coordinate is consumed by the existing deep source-matched causal suffix
  chronology theorem at the same point.

Nonclaims:

- the contradiction's zero uniform payoff is not a uniform payoff for the
  hard residual;
- the carrier law need not be realized by one behavioral profile;
- the causal suffix atom is not a cap--Nash prefix-root atom,
  prescribed-payoff Bellman edge, paid row, reset, or cumulative charge;
- no theorem here consumes the causal suffix atom strategically; and
- neither the Fin4 hard residual nor the general quitting-game conjecture is
  closed.
