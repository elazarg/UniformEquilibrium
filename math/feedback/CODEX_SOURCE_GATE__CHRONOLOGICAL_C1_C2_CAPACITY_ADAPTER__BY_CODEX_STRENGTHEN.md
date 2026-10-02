# Adversarial audit of the normal S.3 delayed-switch compiler

Reviewer: `CODEX_STRENGTHEN`

Claim reviewed: Section 20 of
[`CODEX_SOURCE_GATE__CHRONOLOGICAL_C1_C2_CAPACITY_ADAPTER.md`](../notes/CODEX_SOURCE_GATE__CHRONOLOGICAL_C1_C2_CAPACITY_ADAPTER.md),
especially Theorem 20.1 asserting that playerwise punishment normality plus
`QuittingSequentiallyεPerfectAbsorbingExistence` yields a
uniform-equilibrium payoff.

Verdict: **PASS as ordinary mathematics, subject to the narrow presentation
repairs below.**  I found no counterexample.  The proof does not infer global
Nash optimality from sequential perfection.  It uses sequential perfection
only to bound a finite prefix ledger and to force a uniform opponent-absorption
charge at each bad row; the existing phase-switch consumers then cover every
unrestricted behavioral deviation.  This is a genuinely new direct consumer
of the normal S.3 branch, not a restatement of the existing support-witness
individual-rational package, because normality supplies individual rationality
only after the new finite delayed-switch dichotomy.

## 1. Exact proof audit

Let

\[
 M=\operatorname{quittingRewardBound}(r),\qquad
 B=\max\{1,2M\}.
\]

Then `M >= 0`, `B >= 1`, and choosing `0 < r0 < B` makes
`c=r0/(2B)` satisfy `0<c<1`.  Hence for every `0<theta<1` there is a finite
`L` with `(1-c)^L <= theta`.  After `L` is fixed, S.3 may be invoked at an
arbitrarily small positive `eta`, so all inequalities in (69) can be imposed
simultaneously.  There is no circular parameter choice.

Write

\[
 V_t^i=\operatorname{quittingRootSequenceTerminalValue}(r,x,i,t).
\]

The checked Bellman recursion
`quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector` identifies
`V_t^i` with the mixed successor payoff at row `t`.  Thus the no-profitable-Quit
part of `QuittingPlayerRowεPerfect` has the required orientation:

\[
 Q_t^p\le V_t^p+\eta.
\]

At a bad row, `V_t^p < chi_p-r0`.  Punishment normality
`chi_p <= a_p` and `eta <= r0/2` give

\[
 Q_t^p<a_p-r0/2,
 \qquad |Q_t^p-a_p|>r0/2.
\]

The checked endpoint estimate gives

\[
 |Q_t^p-a_p|
 \le 2M\operatorname{OppAbs}_p(x_t)
 \le B\operatorname{OppAbs}_p(x_t),
\]

so `OppAbs_p(x_t)>c`.  This also covers `M=0`: in that case a bad
row is impossible, and the displayed inequalities derive the contradiction
correctly.  This is the only new local game-theoretic estimate.

S.3 at tolerance `eta` gives support-local error
`alpha=2*eta` by
`supportApproxNash_of_quittingRowεPerfect`.  Complete absorption supplies a
finite first own-survival crossing through
`exists_ownSurvival_crossing_of_completelyAbsorbing`.  At the canonical first
crossing `s`,
`exists_ownSurvival_le_quittingSupportSurvivalSwitchIndex` selects one player
`p` with the own-survival bound, while
`quittingSupportApproxNash_survivalSwitchPackage` supplies the ledger and
regret bounds (and its companion reach lemmas supply the corresponding
joint/deleted bounds):

\[
 \operatorname{OwnSurv}_p(0,s)\le\theta,
 \quad
 \operatorname{Ledger}_i(n)\le \ell+\alpha\ (n\le s),
 \quad
 \operatorname{QuitRegret}_i(t)\le\alpha\ (t<s).
\]

Every later support-local row contributes at most `alpha` to the unweighted
ledger and has Quit regret at most `alpha`.  Consequently every selected
`T<=s+L` satisfies

\[
 \operatorname{Ledger}_i(n)\le\ell+(L+1)\alpha\quad(n\le T),
 \qquad
 \operatorname{QuitRegret}_i(t)\le\alpha\quad(t<T).
\]

If the first good row `T` occurs, then
`chi_p <= V_T^p+r0`.  The checked theorem
`exists_quittingTargetClosedTail_le_of_punishmentValue_le`, invoked with
boundary `V_T^p+r0` and positive slack `zeta`, gives an actual target-closed
tail with marked cap at most `V_T^p+r0+zeta`.  Since `T>=s`, the marked
player's joint reach is at most its own survival through `s`, and every other
player's deleted reach contains that same factor.  Therefore the exact
hypotheses of
`isεAsymptoticNash_quittingPhaseSwitchProfile_marked` hold with

\[
 \begin{aligned}
 \text{ledgerCap}&=\ell+(L+1)\alpha,\\
 \text{quitRegretCap}&=\alpha,\\
 \text{continuationSlack}&=r0+\zeta,\\
 \text{targetJointReach}&=\text{otherReach}=\theta.
 \end{aligned}
\]

Its marked error is

\[
 \ell+(L+2)\alpha+r0+\zeta+2M\theta,
\]

and each unmarked error is at most

\[
 \ell+(L+2)\alpha+7M\theta.
\]

If all `L` inspected rows are bad, each opponent-Continue factor for `p` is
strictly below `1-c`, so

\[
 \operatorname{OppSurv}_p(s,L)\le(1-c)^L\le\theta.
\]

At `T=s+L`, the product split gives
`OppSurv_p(0,T)<=theta`.  For `i != p`, the deleted product for `i` contains
player `p`'s own survival factors, so
`OppSurv_i(0,T)<=OwnSurv_p(0,T)<=OwnSurv_p(0,s)<=theta`.
Thus all deleted survival weights are small.  Choose, for definiteness, the
all-Continue root sequence as the attached actual tail and cap every player's
tail deviation by `M`.  The ordinary checked
`isεAsymptoticNash_quittingPhaseSwitchProfile`, together with
`quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_le_of_plan_ledger_le`,
then gives error at most

\[
 \ell+(L+2)\alpha+7M\theta.
\]

The choices (68)--(69) make both branch errors strictly below the requested
positive epsilon.  Hence every positive epsilon has a terminal epsilon-Nash
profile.  The checked
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
selects one fixed payoff before the uniform-equilibrium accuracy.  No
cross-tolerance ancestry is required.

## 2. Behavioral-deviation and probability audit

The output is a literal behavioral profile: a finite prefix of the selected
S.3 root sequence followed by one actual tail.  Randomization remains the
independent product randomization of the quitting model, and all reach
estimates are finite products on the unique live public history.

The marked and ordinary phase-switch theorems quantify over an arbitrary
behavioral strategy of the deviating player.  Their proofs reduce that
strategy to its complete live-history hazard and use pure-time extremality,
including arbitrarily late stopping and Never.  Accordingly Section 20 does
not silently restrict deviations to stationary, finite-support, bounded-time,
or prescribed-support strategies.

The selected S.3 source may depend on `eta` and hence on the requested
epsilon.  This is harmless: terminal-to-uniform payoff selection takes a
compact cluster of the resulting terminal payoff vectors and returns one
fixed payoff.  It does not require the profiles themselves, their roots, or
their ancestry to be common across accuracies.

## 3. Attempted falsification and sharp boundary

I tested the only possible local failure on a two-player row.  If the selected
player is normal, is bad by more than `r0`, and the opponent absorption is at
most `c`, then the endpoint estimate puts its pure-Quit payoff within
`B*c=r0/2` of its solo payoff, while row perfection and badness put it strictly
more than `r0/2` below that payoff.  These inequalities are inconsistent.
Thus no two-player reward table, and hence no larger finite table, can violate
the bad-row charge while satisfying the stated hypotheses.

The checked `ErrorExponentRefutation` example does not refute Theorem 20.1.
Its sequentially perfect absorbing sequence has a profitable global deviation,
but the affected player is abnormal (`solo=-1`, punishment value `0`).  It
therefore falsifies an unqualified local-to-global inference and pinpoints
where this delayed-switch proof uses normality.  It does **not** prove that
normality is logically necessary for existence of a uniform payoff: that
particular game has a stationary equilibrium.  Section 20 should describe
normality as sharp for the displayed bad-row absorption implication, not as a
necessary condition for the theorem's conclusion in all games.

The weakest clean hypothesis is playerwise normality only for every player who
may be selected by the first-survival crossing.  Global normality is the
natural source-independent formulation and is exactly what
`FinFourQuantitativeFullSupportHardResidual.all_punishmentNormal` supplies.
For one fixed execution it is enough that the selected `p` is normal.

## 4. Mandatory presentation/formalization repairs

No mathematical repair to Theorem 20.1 is required.  Before export or Lean
handoff, make the following points explicit.

1. In (73), the Lean object takes `(start, fuel)`.  Write
   `quittingOpponentSurvivalWeight x p s L`, not an ambiguous
   `OpponentSurvival_p(s,s+L)`, and separately use the product split to reach
   time `T=s+L`.
2. State the Bellman recursion identifying `V_t^p` with the row successor
   payoff before applying the no-profitable-Quit clause.  Without that named
   equality, the orientation is easy to misread.
3. In the all-bad branch, spell out both different reach arguments: the suffix
   bad-row product clears `p`'s deleted survival, whereas `p`'s initial own
   crossing clears every `i != p`.  They are not the same clock.
4. Replace “attach any bounded tail” in the formal handoff by one explicit
   actual tail, for example the all-Continue root sequence, with constant cap
   `M`; or state the universal bounded-tail cap lemma being used.
5. Qualify “normality is essential” as essential to this compiler's local
   charge lemma.  The abnormal regression does not show normality necessary
   for uniform-equilibrium existence.

## 5. Source and novelty comparison

Checked declarations inspected:

- `QuittingSequentiallyεPerfectAbsorbingExistence` and
  `QuittingPlayerRowεPerfect`,
  `UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean`;
- `supportApproxNash_of_quittingRowεPerfect`,
  `UniformEquilibrium/Quitting/Classification/Existence/WellSupportedAbsorbingSequence.lean`;
- `exists_ownSurvival_crossing_of_completelyAbsorbing`,
  `UniformEquilibrium/Quitting/Paths/SupportWitnessAbsorptionBridge.lean`;
- `quittingSupportApproxNash_survivalSwitchPackage`,
  `UniformEquilibrium/Quitting/Paths/SupportWitnessClockCollapse.lean`;
- `quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector`,
  `UniformEquilibrium/Quitting/Paths/SurvivalWindowLanding.lean`;
- `abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass`,
  `UniformEquilibrium/Quitting/Paths/QuitEndpointOpponentBound.lean`;
- `exists_quittingTargetClosedTail_le_of_punishmentValue_le`,
  `UniformEquilibrium/Quitting/Paths/SupportWitnessIndividualRational.lean`;
- `isεAsymptoticNash_quittingPhaseSwitchProfile_marked`,
  `UniformEquilibrium/Quitting/Debt/Marked/PhaseSwitchCap.lean`;
- `isεAsymptoticNash_quittingPhaseSwitchProfile` and the unrestricted
  behavioral cap beneath it,
  `UniformEquilibrium/Quitting/Cycles/PhaseSwitchDeviationCap.lean`;
- `quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_le_of_plan_ledger_le`,
  `UniformEquilibrium/Quitting/Debt/Ledger/TruncationLedgerFold.lean`;
- `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`,
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
- `FinFourQuantitativeFullSupportHardResidual.all_punishmentNormal`,
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`; and
- the exact abnormal regression in
  `UniformEquilibrium/Quitting/Classification/ErrorExponentRefutation.lean`.

The existing `HasQuittingCompletelyAbsorbingSupportWitnessPackage` consumer
assumes individual rationality of the plan continuation at the already chosen
support-survival switch.  Section 20 does not assume that field.  Its new
mathematics is precisely the finite delayed scan proving:

```text
normal selected player
  -> first good continuation boundary within L rows
     or selected player's opponent survival contracts by theta.
```

This discharges the missing individual-rationality field by a new branch
dichotomy and therefore strictly strengthens the existing consumer boundary.
The theorem is suitable for export after an independent second audit required
for its unrestricted-strategy conclusion and after the five presentation
repairs above are incorporated into a self-contained packet.

## 6. Lean handoff refinement

The four-declaration split proposed in Section 20.3 is sound.  The finite
selection lemma should return explicit data rather than a prose disjunction:

```text
exists_normalSupportDelayedSwitch
  -> exists p s T,
       s <= T and T <= s + L
       and ledger/regret bounds through T
       and jointReach(p,T) <= theta
       and
         (punishmentValue p <= V_T p + r0)
         or
         (forall i, opponentSurvival i 0 T <= theta)
```

In the first disjunct it should also return the deleted-reach bound for every
`i != p`.  The all-bad proof needs only finite-product algebra, the endpoint
estimate, and the Bellman recursion.  Keep the terminal consumer separate so
the new combinatorial lemma has no behavioral-strategy or payoff-selection
quantifiers.

## Subsequent disposition

The reviewed presentation repairs were incorporated, and the delayed-switch
compiler is now checked in Lean at commit
`26ecaa9f881562388f2c9861df3c6bf0c51dceb2`; see the
[formalization record](../formalized/NORMAL_S3_DELAYED_SWITCH_UNIFORM_PAYOFF.md).
This review remains historical evidence for the finite selection and strategy-
class audit, but is superseded as an active formalization handoff. The checked
theorem remains conditional on a supplied sequentially perfect or well-
supported completely absorbing source and does not produce S.3.
