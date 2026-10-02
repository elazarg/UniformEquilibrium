# Review of finite near-sure actual cap handoff

Reviewer: `CODEX_SPINOZA`

Reviewed file:
`notes/CODEX_HAHN__FINITE_NEAR_SURE_ROOT_ACTUAL_CAP_HANDOFF.md`

Reviewed SHA-256:
`3e09677e8a801e3f9ee4ded2913c40b0d0cb6aa9a6493e07ca71e353e4d25c8e`

## Verdict

**REVISE (one hypothesis-boundary repair; the intended Alternative-B
application and its central finite-child calculation pass).**

The actual finite handoff in Section 2 is correct when the input is the full
Alternative B of
`FIRST_EXACT_ROOT_SURVIVAL_AND_UNIQUE_SURE_RESET`.  The displayed question,
however, lists only actual profiles, exact roots, a unique-sure root limit,
and the lower bound on the prefixed owner debt.  Those displayed hypotheses
alone do not supply a cap-attaining response in the tail.  Section 2 then
uses the additional, essential fact that each \(\tau_n\) is one of the
stationary structured sources and that its owner cap is attained by the
literal Quit0-or-Never endpoint retained by Alternative B.

The repair is to state the theorem explicitly under the full Alternative-B
packet, or add as a hypothesis a tail response \(\theta_{n,k}\) attaining
\(B_{n,k}\), with the survivor theorem's stationarity/Quit0-or-Never field as
the intended adapter.  It is not safe to call the presently displayed data
“exactly” Alternative B: for an arbitrary nonstationary quitting profile a
complete cap is a supremum over pure times and need not be attained.

No change to the conclusion or constants is needed after that repair.

## Reconstruction of the central claim

Write \(Y_n=\operatorname{Sem}(q_n::\tau_n)\), and let
\(\beta_{n,k}\) force Continue at the new root and use the attained cap
response in the literal tail on opponent Continue.  The exact root and
positive prefixed debt force the Continue-with-old-cap endpoint to be the
strict complete-cap branch.  Hence \(\beta_{n,k}\) attains the complete
behavioral cap at \(\rho_n=q_n::\tau_n\).

For
\[
 \chi_n=\rho_n[k\leftarrow\beta_{n,k}],
\]
the opponents are unchanged, so player \(k\)'s complete cap is unchanged.
The updated payoff equals that cap.  Therefore the two exact identities are
\[
 U_k(\chi_n)-U_k(\rho_n)=d_k(Y_n),\qquad d_k(\chi_n)=0.
\]
Thus the claimed gain \(D_*/2\), the debt kill, and the literal finite
ancestry all pass.  No limiting/stationary profile is substituted at this
step.

Applying the terminal exploitability gap at the actual profile \(\chi_n\)
gives a debtor \(j_n\) with debt at least \(\Gamma\).  Since the killed
coordinate has debt zero, \(j_n\ne k\); finite-label extraction legitimately
fixes \(j\) on a subsequence.  The declarations
`HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at` and
`positiveDebt_exists_actualReach_paidRow_withSupport` then give respectively
the full-gap paid row and the supported row of gain \(\Gamma/4\), with the
exact bounds
\[
 \Gamma\le4M\,\operatorname{OwnSurvival},\qquad
 \Gamma\le8M\,\operatorname{OpponentLiveMass}.
\]
These are unrestricted behavioral-cap statements at the same literal child.

## Approximate singleton-base calculation

The coupling in Section 1 is sound.  The endpoint difference is unchanged on
the event that the nearly sure owner quits.  Its complement has probability
\(\alpha_n=1-q_{n,k}\), and two endpoint differences in
\([-2M,2M]\) differ by at most \(4M\).  This proves (1).  Combining it with
the two exact complementarity inequalities gives (2), so the free marginals
are \(4M\alpha_n\)-Nash for the persistent singleton-base game.  This is only
approximate at finite \(n\), as the note correctly emphasizes.

## Floor/orbit branch

The floor split is exact because the repaired owner is at its cap and hence
above punishment.  In the all-floor arm, the generic marked exact-orbit
construction can indeed be applied directly to \(\chi_n\): its payoff is in
the canonical box, the literal paid row is retained in the suffix, and the
punishment-floor hypothesis is exactly the missing orbit premise.  The
terminal witness then gives summable root absorption and hence absorption
tending to zero.  This is not recurrence or a consumer, and the note's
nonclaims correctly stop at the paid-port/vanishing-absorption waist.

For provenance, the already named generic route is
`QuittingPaidRowMarkedExactOrbit.nonempty_of_floorSafe` in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidRowExactPortAlternative.lean`,
together with the arbitrary-orbit results in
`UniformEquilibrium/Diagnostics/Quitting/Capacity/InfiniteOrbitConsequences.lean`.
Naming those declarations would make Section 3 sharper, but this is not a
second mathematical objection.

## Scope after repair

The result is a genuine finite-source adapter: it removes the need to enter
the compact limiting singleton source merely to obtain a debt-killing owner
update and a distinct full-gap paid row.  It does not make \(\chi_n\)
stationary, preserve the tropical cap pin for the new debtor, produce an
exact Nash--Bellman return, or supply a renewable orbit.  The note states
those limits accurately.

## Corrected-hash delta review

Corrected SHA-256:
`5a53237e7a7ea7e1cb5ef93e64ca0663303bbb242da7f240d11e712cd603f7fb`

**PASS.**  The Question now explicitly takes the full vanishing-survival
Alternative B, including stationary structured tails and the literal
Quit0-or-Never cap-attaining response at each finite source.  It also states
that this field is a hypothesis and need not exist for an arbitrary
nonstationary tail.  This exactly resolves the sole objection above.

The generic floor-safe continuation is now tied directly to
`QuittingPaidRowMarkedExactOrbit.nonempty_of_floorSafe`.  Under the terminal
witness, the arbitrary-orbit summability theorem supplies summable
absorption; the checked strict-survival theorem in
`PaidRowExactPortAlternative.lean` then gives a positive limiting reach of
the unchanged paid suffix along each selected orbit.  The note correctly
does not claim a lower bound uniform in \(n\), charged recurrence, or
renewal.  This is faithful to the named checked interface.  No mathematical
objection remains at this hash.
