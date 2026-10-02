# Review of `FINITE_NEAR_SURE_ROOT_ACTUAL_CAP_HANDOFF`

Reviewer: `CODEX_NEGATIVE_CERTIFICATE`

Reviewed file:
[`notes/CODEX_HAHN__FINITE_NEAR_SURE_ROOT_ACTUAL_CAP_HANDOFF.md`](../notes/CODEX_HAHN__FINITE_NEAR_SURE_ROOT_ACTUAL_CAP_HANDOFF.md)

Reviewed SHA-256:
`3e09677e8a801e3f9ee4ded2913c40b0d0cb6aa9a6493e07ca71e353e4d25c8e`

## Verdict

**PASS as exact ordinary mathematics, with the Lean-handoff and hypothesis
qualifications below.** I found no counterexample to the finite cap update,
the killed owner debt, the distinct terminal-gap debtor, the actual-reach
bounds, or the floor split. The note does not overclaim renewal, a return, or
a uniform equilibrium.

The main positive point is source ancestry: every object through the paid row
is constructed at the literal finite child

\[
 \chi_n=(q_n::\tau_n)[k\leftarrow\beta_{n,k}],
\]

not at the compact stationary limit. Stationarity is used only to prove that
the old tail cap in \(\beta_{n,k}\) is attained by Quit0 or Never.

## Reconstruction of the finite cap edge

Alternative B.2 of the reviewed survivor theorem supplies a complete
cap-attaining response \(\beta_{n,k}\) at \(\rho_n=q_n::\tau_n\). It forces
Continue at the new root and uses the attained stationary tail response after
opponent joint Continue. Thus it is an actual behavioral strategy on the
literal profile, not merely a root endpoint.

Replacing player \(k\)'s own strategy changes none of the opponents on which
its unrestricted best-response cap depends. Hence

\[
 B_k(\chi_n)=B_k(\rho_n),\qquad
 U_k(\chi_n)=B_k(\rho_n),
\]

and therefore

\[
 d_k(\chi_n)=0,
 \qquad
 U_k(\chi_n)-U_k(\rho_n)=d_k(\rho_n)\ge D_*/2.
\]

This is also the content of the checked general reset mechanism around
`quittingTerminalSemanticDebt_update_eq_zero_of_payoff_eq_bestReply` and
`QuittingExactPureTimeCapStep.target_reset` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinitePureTimeResetArrival.lean`.
No stationarity of \(\rho_n\) or \(\chi_n\) enters this calculation.

Apply the terminal exploitability witness at \(\chi_n\). Choose one returned
observer \(j_n\) and its behavioral deviation of gain at least \(\Gamma\).
Then \(d_{j_n}(\chi_n)\ge\Gamma\), while the displayed equality above gives
\(d_k(\chi_n)=0\); hence \(j_n\ne k\). This establishes the claimed label
change without a limit argument.

## Paid rows and the exact constants

For this fixed \(j_n\), the expectation/support-pair proof used by
`HasTerminalExploitabilityGap.exists_supported_pureTimePayoff_sub_at` selects
source and receiving pure-time atoms retaining the full gap. Applying
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` gives a paid
row of gain \(\Gamma\) for the same observer at the exact child.

There is one narrow formal packaging qualification. The currently named
theorem `HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at`
existentially chooses its observer; it cannot literally be invoked after
fixing an independently named \(j_n\) while retaining definitional equality
of those labels. The ordinary proof is sound by fixing the witness first and
repeating the checked expectation argument. A Lean wrapper should return the
behavioral witness, the two supported atoms, and the row simultaneously. This
is a packaging seam, not a mathematical gap.

The stronger reach statement needs no cap attainment for \(j_n\). Apply
`positiveDebt_exists_actualReach_paidRow_withSupport` from
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualReachPaidFirstDisagreement.lean`
with \(\Delta=\Gamma\). Its output is a (possibly different) row for the same
\(j_n\), of gain \(\Gamma/4\), satisfying exactly

\[
 \Gamma\le 4M\,\operatorname{OwnSurvival},\qquad
 \Gamma\le 8M\,\operatorname{OpponentLiveMass},
\]

and its source witness is in the prescribed stopping-law support. The
orientation and constants in (6) are correct. The two rows need not be
identified, and the note does not require that identification.

## Approximate singleton-base calculation

Let \(\alpha_n=1-q_{n,k}\), and couple \(q_n\) to the profile in which \(k\)
Quits surely. With probability \(1-\alpha_n\), the endpoint differences for
every free player agree. On the remaining event, each endpoint difference is
in \([-2M,2M]\), so their difference has absolute value at most \(4M\).
This proves (1). Multiplying the two endpoint-Nash inequalities by the
unchanged own-action weights gives (2), including the pure boundary cases.
Every compact limit is consequently in the exact persistent-base Nash set.

The asserted positive owner-floor excess on that exact set is indeed supplied
uniformly for the prescribed owner by
`QuittingTerminalExploitabilityWitness.exists_prescribedOwner_stationaryHandoff`
in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PrescribedOwnerStationaryHandoff.lean`.
Continuity transfers half of that fixed positive bound to \(z_n\) eventually.
As the note stresses, this approximate entrance is not needed for the actual
finite-source cap edge.

## Exact floor and orbit consequence

The checked inequality `quittingPunishmentValue_le` applies to every actual
opponent profile. Since \(U_k(\chi_n)=B_k(\chi_n)\), it gives

\[
 \operatorname{Pun}_k\le U_k(\chi_n).
\]

Thus failure of the all-player floor necessarily displays an underfloor
player \(i_n\ne k\). No stationary or sure-Quit floor-repair theorem applies
to that player from these data alone.

In the all-player floor arm there is a more precise already checked generic
entry than the note needs. The child, either positive paid row, and its floor
inequalities form a `QuittingPaidRowFloorSafeSource`. The theorem
`QuittingPaidRowFloorSafeSource.exists_markedExactOrbit_alternative_of_witness`
in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidRowExactPortAlternative.lean`
returns a literal marked exact-prefix orbit beginning at \(\chi_n\). Under
the same no-uniform witness, its uniform-payoff arm is impossible, so the
remaining output includes a summable all-Continue semantic port and positive
limiting reach of the unchanged paid suffix. In particular root absorption
tends to zero.

Moreover, the original terminal-gap deviation at \(\chi_n\) may copy the
prescribed observer action through the first \(H\) exact roots and then act in
the unchanged suffix. Its gain is the original gain multiplied by the joint
suffix reach. For each fixed \(n\), this eventually gives a delayed profitable
fork of size at least \(\ell_n\Gamma/2\), where \(\ell_n>0\) is the orbit's
reach limit. There is no uniform lower bound on \(\ell_n\) as \(n\) varies.

The note's weaker claim that fixed positive absorption/charge recurrence is
unavailable is valid from the summable-absorption arm. At Lean handoff it
should be phrased through the generic marked-orbit/summable-port theorem just
cited, rather than through the singleton-handoff-specific declaration
`not_repairedExactOrbit_chargedPayoffRecurrence`.

## Hypotheses that must remain explicit

The displayed `Question` paragraph does not itself bind every hypothesis used
later. A formal or export statement must explicitly carry:

- the terminal exploitability witness and its gap \(\Gamma>0\);
- provenance from alternative B.2, or equivalently the literal attained cap
  response with the Continue-then-stationary-tail form;
- stationarity of each \(\tau_n\), used only for that attainment;
- the eventual owner-debt floor \(D_*/2>0\); and
- for the floor-safe orbit conclusion only, no uniform-equilibrium payoff (or
  the terminal witness which supplies the corresponding alternative).

These hypotheses are present in the note's stated provenance and subsequent
text, so this is a statement-hygiene qualification rather than a failed
implication.

## Falsification attempts and nonclaims

I tested the following possible regressions.

1. A nonstationary tail can have a nonattained cap. This does not refute the
   theorem because the cap response is retained from the stationary tail in
   alternative B.2; it does show why that provenance cannot be dropped.
2. Replacing only the date-zero action by Continue need not attain the cap.
   The theorem correctly replaces the entire behavioral strategy, including
   the conditional tail response.
3. Killing \(k\)'s debt can activate another player. The terminal witness
   forces exactly this possibility, and the theorem records a distinct
   \(j_n\) rather than claiming renewal of the unique-owner chamber.
4. The underfloor player need not be sure and \(\chi_n\) need not be
   stationary. Hence no pair-base floor repair follows. The note makes no such
   claim.
5. The marked exact orbit need not return semantically to \(\chi_n\), retain
   the cap pin, or regenerate a tropical minimum source. Positive suffix reach
   preserves a delayed deviation, not a Nash--Bellman return. The note's final
   scope is correct.

Accordingly the finite-source bypass is valid and materially removes the
compact stationary source-entry seam, but it ends at the already identified
paid-port/floor waist.

## Delta review of strengthened finite-source statement

Rechecked exact SHA-256
`5a53237e7a7ea7e1cb5ef93e64ca0663303bbb242da7f240d11e712cd603f7fb`.

**PASS.** The input boundary now explicitly binds the terminal witness,
alternative-B provenance, stationary actual tails, the finite attained
Continue-then-Quit0-or-Never response, and the eventual owner-debt floor.
This exactly resolves the statement-hygiene qualification above; it does not
broaden the class in which cap attainment is asserted.

The strengthened floor-safe conclusion is also correct. From the literal
paid child and its row one assembles
`QuittingPaidRowFloorSafeSource`; the generic
`QuittingPaidRowMarkedExactOrbit.nonempty_of_floorSafe` begins at that exact
child. The arbitrary-orbit results in
`UniformEquilibrium/Diagnostics/Quitting/Capacity/InfiniteOrbitConsequences.lean`
give summability, hence convergence to zero, of the selected roots'
absorption masses under the terminal witness. The marked-orbit theorem in
`PaidRowExactPortAlternative.lean` gives positive limiting reach of the
unchanged paid suffix. Copying the original observer's prescribed action
through the finite prefixes and then using its old suffix deviation multiplies
the old gain by that reach. The note correctly makes this lower bound
orbit-dependent and does not claim a uniform lower bound over \(n\), a
charged return, or renewal.

The original observer-packaging Lean qualification remains: a formal wrapper
should retain the behavioral witness and its supported pure-time pair for one
common label. That does not affect this exact ordinary-mathematics PASS.
