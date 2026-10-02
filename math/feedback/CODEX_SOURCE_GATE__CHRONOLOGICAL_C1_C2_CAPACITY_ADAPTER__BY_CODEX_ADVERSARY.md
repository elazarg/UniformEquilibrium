# Second adversarial audit of the normal S.3 delayed-switch compiler

Reviewer: `CODEX_ADVERSARY`

Claim audited: Section 20 of
`notes/CODEX_SOURCE_GATE__CHRONOLOGICAL_C1_C2_CAPACITY_ADAPTER.md`, together
with the first review
`feedback/CODEX_SOURCE_GATE__CHRONOLOGICAL_C1_C2_CAPACITY_ADAPTER__BY_CODEX_STRENGTHEN.md`.
The claimed implication is

\[
  (\forall i,\ \chi_i\le r_i(\{i\}))
  \quad+\quad
  \texttt{QuittingSequentiallyεPerfectAbsorbingExistence}(r)
  \quad\Longrightarrow\quad
  \text{a uniform-equilibrium payoff exists}.
\]

## Verdict

**PASS as ordinary mathematics.** I found no counterexample and independently
recover the displayed constants and all strategy quantifiers. The theorem is
not yet a checked Lean result.

**Export verdict:** the result may pass the mathematical export gate once the
four mandatory packet edits below are incorporated. The present prose should
not be exported literally, chiefly because it calls the target tail stationary
and does not name the checked all-player cap extension needed by the marked
consumer. These are repairable source/presentation gaps, not a failure of the
theorem.

## Independent derivation

Fix a requested terminal error \(\varepsilon>0\), and let
\(M=\texttt{quittingRewardBound}(r)\) and \(B=\max\{1,2M\}\). Choose the
parameters in the order written in Section 20. There is no circularity:
first choose positive \(\theta,r_0,\ell,\zeta\) satisfying (68) and
\(r_0<B\), then \(c=r_0/(2B)\in(0,1)\), then a finite \(L\) with
\((1-c)^L\le\theta\), and only then a positive \(\eta\) satisfying (69).
Put \(\alpha=2\eta\).

For the S.3 sequence \(x\), set

\[
 V_t^i=
 \texttt{quittingRootSequenceTerminalValue}(r,x,i,t).
\]

The checked Bellman identity
`quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector` says that
this is exactly the mixed successor payoff at row \(t\), with boundary vector
given by the actual values at \(t+1\). Thus `QuittingPlayerRowεPerfect` has
the required orientation

\[
 Q_t^p\le V_t^p+\eta.
\]

If \(t\) is bad, \(V_t^p<\chi_p-r_0\). Normality and
\(\eta\le r_0/2\) imply

\[
 Q_t^p<a_p-r_0/2,
 \qquad |Q_t^p-a_p|>r_0/2.
\]

The checked endpoint bound then gives

\[
 r_0/2
 < |Q_t^p-a_p|
 \le 2M\operatorname{OppAbs}_p(x_t)
 \le B\operatorname{OppAbs}_p(x_t),
\]

so \(\operatorname{OppAbs}_p(x_t)>c\). This also handles \(M=0\): in that
case the inequalities show that a bad row is impossible. No positivity of a
reward coordinate is being assumed.

S.3 gives support-local error \(\alpha\) by
`supportApproxNash_of_quittingRowεPerfect`. Complete absorption and
`exists_ownSurvival_crossing_of_completelyAbsorbing` give a genuine finite
crossing. At the canonical first switch \(s\),
`quittingSupportApproxNash_survivalSwitchPackage`, using
\(\alpha\le\ell\theta\), gives the ledger bound through \(s\), the Quit
regret bound before \(s\), and a marked player \(p\) whose own survival
bounds both joint survival and every other player's deleted survival.

For later rows, the support-local estimate
`quittingLedgerStageAdvantage_le_delta_mul_ownQuitProbability`, the fact that
a Quit probability is at most one, and `quittingLedger_succ` add at most
\(\alpha\) per stage. Therefore for every selected
\(s\le T\le s+L\),

\[
 \operatorname{Ledger}_i(n)\le\ell+(L+1)\alpha\quad(n\le T),
 \qquad
 \operatorname{QuitRegret}_i(t)\le\alpha\quad(t<T).
\]

There is no off-by-one error here. `quittingPhaseSwitchRoots` uses the plan
exactly at rows \(t<T\) and restarts the tail at row \(T\). Hence the good
boundary is precisely \(V_T^p\), while in the all-bad branch the inspected
rows \(s,\ldots,s+L-1\) are exactly the additional plan rows before the
switch \(T=s+L\).

### Good branch

At a good \(T\), \(\chi_p\le V_T^p+r_0\). Applying
`exists_quittingTargetClosedTail_le_of_punishmentValue_le` with boundary
\(V_T^p+r_0\) and slack \(\zeta\) returns a target-closed tail \(y\) with

\[
  \operatorname{Val}_p(y,0)\le V_T^p+r_0+\zeta.
\]

It is important that this is not, in general, a stationary tail: its
opponents are stationary, while the target uses an actual cap-attaining
time-dependent response. The checked
`exists_quittingPhaseSwitchPunishCap_of_targetClosedTail` extends target
closedness to a cap function \(C\) satisfying

\[
 C_p=\operatorname{Val}_p(y,0),\qquad C_i\le M,
\]

and caps every hazard deviation of every player against the same tail. This
is the missing all-player hypothesis of
`isεAsymptoticNash_quittingPhaseSwitchProfile_marked`.

Monotonicity from the initial crossing to \(T\) gives joint reach at most
\(\theta\) for \(p\), and deleted reach at most \(\theta\) for every
\(i\ne p\). The marked error is

\[
 \ell+(L+2)\alpha+r_0+\zeta+2M\theta,
\]

while an unmarked player pays at most

\[
 \ell+(L+2)\alpha+5M\theta
   +\theta(\max\{C_i,0\}+M)
 \le \ell+(L+2)\alpha+7M\theta.
\]

These are exactly the two quantities in (76).

### All-bad branch

For each of the \(L\) rows,
`quittingRootOpponentContinueMass_eq_one_sub_absorptionMass` gives the
opponent-Continue factor for \(p\) strictly below \(1-c\). Thus

\[
 \texttt{quittingOpponentSurvivalWeight}(x,p,s,L)
 \le (1-c)^L\le\theta.
\]

The exact product split `quittingOpponentSurvivalWeight_add`, followed by the
prefix bound by one, gives the time-zero deleted-survival bound for \(p\) at
\(T=s+L\). For \(i\ne p\), the deleted product for \(i\) contains all of
\(p\)'s own Continue factors, so the initial own-survival crossing of \(p\)
gives the bound by \(\theta\). These are two different clocks, as the first
review correctly stresses.

Take, explicitly, the all-Continue root sequence as the tail. Every player's
arbitrary hazard deviation against it has terminal value at most \(M\), so
one may take the constant punishment cap \(M\) and punishment error zero.
`quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_le_of_plan_ledger_le`
first gives plan error

\[
 \ell+(L+2)\alpha+5M\theta,
\]

and the ordinary `isεAsymptoticNash_quittingPhaseSwitchProfile` adds at most
\(2M\theta\). The total is (75).

Finally, \((L+2)\alpha=(2L+4)\eta<\varepsilon/2\), while (68) controls the
remaining terms. Both branches therefore give a terminal
\(\varepsilon\)-Nash profile.

## Quantifier and adversarial-strategy audit

The two phase-switch consumers quantify over an arbitrary
`BehaviorStrategy who`. Their checked reduction uses the deviator's hazard
on the unique live all-Continue history. It therefore includes stationary
and nonstationary deviations, arbitrary stopping times along the live path,
arbitrarily late Quit, and Never. No bounded-controller or finite-support
restriction is introduced.

The S.3 sequence, its switch, marked player, and tail may all depend on
\(\varepsilon\). This does not make the payoff depend on the later requested
uniform accuracy. The checked
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
chooses terminal profiles at a null sequence of errors, extracts a convergent
subsequence of their payoff vectors in the finite reward cube, and returns
one fixed `IsUniformEquilibriumPayoff none payoff`.

I tested the two fragile boundary cases separately:

- with one player, opponent absorption is zero, so badness contradicts
  normality and row perfection; the proof necessarily enters the good branch;
- with \(M=0\), the same contradiction rules out bad rows before any division
  by \(M\); using \(B=1\) keeps all parameter definitions valid.

The abnormal exact-row-perfect regression in `ErrorExponentRefutation.lean`
does not refute the theorem because its deviating player violates
\(\chi_i\le a_i\). It shows only that normality is needed for this local
absorption-charge argument, not that normality is necessary for uniform
equilibrium existence in every quitting game.

## Mandatory packet edits

1. Replace “actual stationary target-closed tail” by “target-closed tail with
   stationary opponents and a cap-attaining target response.”
2. Invoke and source
   `exists_quittingPhaseSwitchPunishCap_of_targetClosedTail`. Target
   closedness alone supplies only the marked cap, whereas the marked consumer
   requires one same-tail cap for every player.
3. In the all-bad branch, replace “attach any bounded tail” by an explicit
   tail (the all-Continue sequence is enough), state the constant cap \(M\),
   and name the truncated-plan ledger cap theorem producing the \(5M\theta\)
   term.
4. In the exported proof, use the exact `(start,fuel)` survival notation and
   the product split, state the Bellman equality before the row-perfect
   inequality, and qualify “normality is essential” as essential to the
   displayed charge/compiler.

## Strengthening that survives the audit

Global normality is stronger than the finite decoder itself needs. For a
particular S.3 witness and threshold, it is enough that the player selected at
the first global own-survival crossing is normal. The source-independent
theorem correctly assumes all players normal because that selected player is
not known in advance. Equivalently, the theorem may start from
`QuittingWellSupportedAbsorbingSequenceExistence`, since the checked adapter
between that interface and S.3 only changes the local tolerance.

## Checked declarations inspected

- `QuittingSequentiallyεPerfectAbsorbingExistence` and
  `QuittingPlayerRowεPerfect`,
  `UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean`;
- `supportApproxNash_of_quittingRowεPerfect`,
  `UniformEquilibrium/Quitting/Classification/Existence/WellSupportedAbsorbingSequence.lean`;
- `quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector`,
  `UniformEquilibrium/Quitting/Paths/SurvivalWindowLanding.lean`;
- `abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass`,
  `UniformEquilibrium/Quitting/Paths/QuitEndpointOpponentBound.lean`;
- `exists_ownSurvival_crossing_of_completelyAbsorbing`,
  `UniformEquilibrium/Quitting/Paths/SupportWitnessAbsorptionBridge.lean`;
- `quittingSupportApproxNash_survivalSwitchPackage`,
  `UniformEquilibrium/Quitting/Paths/SupportWitnessClockCollapse.lean`;
- `exists_quittingTargetClosedTail_le_of_punishmentValue_le`,
  `UniformEquilibrium/Quitting/Paths/SupportWitnessIndividualRational.lean`;
- `exists_quittingPhaseSwitchPunishCap_of_targetClosedTail`,
  `UniformEquilibrium/Quitting/Paths/SupportWitnessReduction.lean`;
- `quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_le_of_plan_ledger_le`,
  `UniformEquilibrium/Quitting/Debt/Ledger/TruncationLedgerFold.lean`;
- `isεAsymptoticNash_quittingPhaseSwitchProfile_marked`,
  `UniformEquilibrium/Quitting/Debt/Marked/PhaseSwitchCap.lean`;
- `isεAsymptoticNash_quittingPhaseSwitchProfile`,
  `UniformEquilibrium/Quitting/Cycles/PhaseSwitchDeviationCap.lean`;
- `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`,
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
- `IsQuittingNormalPlayer`,
  `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`.

## Subsequent disposition

The reviewed presentation repairs were incorporated, and the delayed-switch
compiler is now checked in Lean at commit
`26ecaa9f881562388f2c9861df3c6bf0c51dceb2`; see the
[formalization record](../formalized/NORMAL_S3_DELAYED_SWITCH_UNIFORM_PAYOFF.md).
This review remains historical evidence for the constants and unrestricted-
deviation audit, but is superseded as an active formalization handoff. The
checked theorem is still conditional on a supplied sequentially perfect or
well-supported completely absorbing source and does not produce S.3.
