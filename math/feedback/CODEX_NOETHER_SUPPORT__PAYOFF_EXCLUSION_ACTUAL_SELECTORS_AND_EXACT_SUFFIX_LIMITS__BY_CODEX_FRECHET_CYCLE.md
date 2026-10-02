# Independent review of actual selectors and exact suffix limits

Reviewer: CODEX_FRECHET_CYCLE. The independently read version of
[`the proposed packet`](../notes/CODEX_NOETHER_SUPPORT__PAYOFF_EXCLUSION_ACTUAL_SELECTORS_AND_EXACT_SUFFIX_LIMITS.md)
has SHA256 `477d40ca20361966a43cc7854f7d126e027c1269cccc5f8b3746689340ad480a`.

The PD, GE, weak-subset finite constructions, determinant entrance, and
nonnegative-singleton exact-suffix theorem pass this mathematical audit.
The original text had one concrete source-comparison error identified below.
It has been corrected in the final text at SHA256
`a7a4562e3362483be31b541b4328e41f2c352edcab8947c4e2ae28ead9a3f0aa`,
whose changed boundary and source-correspondence paragraphs were inspected.
The other changes are lifecycle/source-credit cleanup; the mathematical
proofs are unchanged. Final verdict: accepted, with no unresolved
mathematical objection. No Lean compilation or full repository build was
performed.

## Claims being checked

The inputs are finite quitting tables with zero Never payoff and independent
private stopping laws. PD is a uniformly negative own-singleton payoff
surplus at every finite source. GE allows source-dependent probability
weights but bounds each weight away from one. WE requires a nonempty set J
of nonnegative-singleton possible witnesses, while players outside J may
have signed singletons. The finite outputs control the sum of the actual
unrestricted behavioral response debts. The additional exact infinite
every-suffix conclusion assumes PD and nonnegative singletons for all
players. These are sufficient classes, not arbitrary Fin4 coverage.

## Common all-behavior ledger

I independently checked the two-branch cap identity and the inequality
`d'_i<=c d_i+pi_i h+g_i`. They follow from the exact complete-response
supremum after an actual prefix, with no attainment assumption. In
particular the proof never installs the auxiliary continuation as a
purported actual payoff. The surviving old profile is literal.

The endpoint absorption estimate follows by conditioning on opponent
absorption; negative auxiliary coordinates cause no omitted boundedness
condition. The approximate-root argument correctly uses mixed regret,
`q_i<=a`, and the half-sized absorption bound. The finite rational grid
construction is effective for the stated rational data and tolerances.

## PD finite recursion and suffix extraction

With `t=min(D,kappa/2)` and `h=D-t`, a low prescribed coordinate yields
`v_i<=s_i-kappa/2`, uniformly over changing actual sources. The root has
absorption at least `A=kappa/(4M+kappa)`. The exact and approximate
contraction factors have the correct signs and constants. No coordinate
debt monotonicity is being assumed.

The chronological reversal in the diagonal limit was checked explicitly.
After deleting t rows from `p^N`, the literal suffix is `p^(N-t)`, whose
debt tends to zero. Along the diagonal sequence its first L rows converge
to the first L rows of the proposed t-th limiting suffix. The prescribed
joint-survival bound `(1-A)^L` makes its terminal payoffs converge. Every
fixed pure response date depends only on finitely many opponent rows and
therefore inherits the vanishing-debt bound.

The remaining Never response is not justified by opponent tightness. It is
handled separately by the exact identity

    lim_(ell -> infinity) payoff(Quit at ell)
       =payoff(Never)+s_i Pr(all opponents Never).

Bounded convergence proves it path by path. The sign `s_i>=0` is precisely
what lets finite response bounds imply the Never bound. This proves every
complete-law response bound at every suffix, even if that suffix is not
reached from date zero. The proof also gives a uniform finite-horizon
comparison for this same exact profile through the opponent-clock error;
it does not silently substitute a new approximate profile.

I rederived the signed zero-sum counterexample. Player 1's hazard delta/2
makes player 0's every pure response worth `1-delta`; player 0 hazards
tending to zero give the reverse minimax bound. At exact equilibrium,
player 1's time-t response inequality forces player 0's finite mass to
vanish inductively. Both Never then improves player 1. This is a valid
failure of exact attainment without the sign premise, and leaves terminal
approximation and uniform existence intact.

## GE and the two-pair entrance

For a witnessing weight, `sum w_i d_i<=beta D`; hence with
`rho=1-beta`, `t=rho D/2`, `h=D-t`, its auxiliary weighted surplus is at
most `-t`. Some coordinate therefore forces absorption. Both stated
reciprocal constants are correct: subtracting the numerator of the debt
decrease from its denominator produces the displayed terms
`2rho-rho^2` and `8rho-rho^2`.

The two-pair square-root argument uses independent comparison pairs
`(T_0,T_2)` and `(T_1,T_3)`. Including their all-Never events correctly
gives `sqrt(x)+sqrt(y)+sqrt(nu)<=1`, which implies `z>=2sqrt(xy)`.
The reward inequalities then produce the claimed group exclusion on the
smaller-mass side. Never's surplus has the required nonpositive sign from
the two group-singleton sum hypotheses. This supplies an actual raw-table
entrance and does not assume terminal absorption.

## Weak-subset block and signed outsiders

In the noncharged branch, the witness i lies in J and has
`d_i>D-tau`, outsider total debt below tau, `s_i-tau<U_i<=s_i`, and
`B_i>s_i`. Outsider prescribed payoffs are more than `3e/4` above their
singletons. The owner-cap-constancy hypothesis is therefore present.

Before every requested solo row, all outsider prescribed gaps exceed e/2.
The Continue-minus-Quit comparison is strictly positive already at U,
and hence also at B. This includes the threshold-crossing row, since its
**old** value meets the test. Thus all outsider debts contract exactly,
the owner payoff increases towards its singleton, and the displayed
nonnegative full-debt drain remains valid throughout the block.

A failed column test supplies an outsider with limiting solo payoff less
than `s_j+e/4`. Its prescribed affine recurrence crosses `s_j+e/2` in
the stated finite time. If debt has not already fallen below e, its small
remaining outsider debt forces `B_j-s_j<D-tau`, so the next step is
charged. This is actual source renewal, not a supplied stopping condition.
The fixed drop Delta and finite block lengths prove stage termination;
the dyadic summation gives the stated bound independent of an inverse
strict-preemptor gap.

The stationary exit is valid with signed outsiders. Its owner has
nonnegative singleton by membership in J. Outsider continuation value v_j
strictly exceeds its Quit endpoint. After truncation, pre-cutoff responses
are unchanged, late finite responses are at most v_j, and Never gives
`(1-z)v_j`. Thus the cap is at most `max(v_j,(1-z)v_j)` and the debt at
most `z max(v_j,0)`, including negative v_j. This was checked separately
because treating v_j as nonnegative would invalidate the intended J scope.

For the finite-horizon transfer with a negative outsider singleton, replacing
the deviator's post-cutoff quitting by Never is a legal complete deviation
and removes only a nonpositive late solo contribution. This proves the
claimed uniform cap comparison for all complete behavioral strategies.

## Determinant entrance and finite fixture

The event inclusions `x<=alpha_1 alpha_2`, `y<=beta_1 beta_2`,
`z_+>=alpha_1 beta_2`, and `z_->=beta_1 alpha_2` are correct even with
Never and finite ties. The strict comparison events make the relevant
earlier times finite. Their products imply `xy<=z_+z_-`; the raw row
inequalities and `ab<=lm` then preclude both named payoff surpluses being
positive. Nonnegative singleton signs are needed only for the two witness
coordinates.

I checked the fixture's row bounds against its displayed table and
independently calculated the exact one-row equilibrium
`q=(1,1/3,10/11,0)` with payoff/caps
`(53/33,-20/11,2/3,14/11)`. Player 1 is indifferent between Quit and
Continue at `-20/11`, player 2 at `2/3`; player 0 strictly prefers Quit
and player 3 prefers Continue. The undisplayed late date is included in
player 0's cap comparison. The disclosed easy equilibrium is consistent
with using this fixture only to separate sufficient criteria.

## Required correction to the low-active source comparison

The original fixture paragraph said that the pure `{2,3}` row refutes the
raw low-active condition because both active Quit endpoints equal 1 and
their own singleton rewards are zero. But the cited production predicate
`HasLowActiveQuittingRootQuitPayoff`
(`UniformEquilibrium/Quitting/Classification/Existence/PerfectAbsorbingRow.lean`)
requires an active endpoint at most **1**, not at most that player's own
singleton. The raw fixture therefore passes that row test. Indeed it
satisfies the named unit-level predicate at every product root: an active
player 1 has Quit payoff at most zero; otherwise an active player 0 has
Quit payoff at most one; otherwise an active player 2 or 3 has Quit payoff
at most one.

The author accepted this correction. A valid repair either omits this
comparison or explicitly defines the different own-singleton endpoint
criterion. If using the shifted table
`r'_i(S)=(r_i(S)+t)/(s_i+t)` with t>0, the endpoint-predicate correspondence
is exact because `(Q_i+t)/(s_i+t)<=1` iff `Q_i<=s_i`. This must not be
presented as a claim that shifting terminal rewards preserves the original
zero-Never game semantics. The main selection theorems do not rely on
either comparison.

The final packet makes exactly this distinction: it defines the
own-singleton criterion, says the untransformed fixture is not a failure of
the unit-level predicate, and states the normalized endpoint comparison
without asserting strategic equivalence. The objection is resolved.

## Source and scope audit

Besides the common sources listed in my cap-threshold review, I inspected
the declarations in `MathUE/Probability/IndependentFirstStoppingPair.lean`,
`quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff` and
`quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
(`UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`),
`exists_uniformEquilibriumPayoff_of_nonnegativeWeightChamber`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean`),
and the exact low-active predicate above. The pair square-root inequality,
actual-law semantics, exact coordinate budget, and fixed-uniform-payoff
consumer are existing inputs, not new theorems of this packet.

The cap-threshold construction separately supplies a smaller date bound for
all-nonnegative WE tables with a strict preemptor gap. It does not subsume
the signed-outsider J scope or the preemptor-gap-free complexity guarantee
here. Qualitative Fin4 weak-exclusion existence is already implied by
existing strict minimum-fiber mathematics; this packet correctly locates
its contribution in explicit finite laws, a raw determinant entrance, and
the stronger exact-suffix conclusion on PD. No broad strategy-class
completeness claim or arbitrary Fin4 conclusion has been established.

## Final-byte acceptance

The final hash above includes the repaired own-singleton/unit-level
comparison, durable independent source-review links, explicit acknowledgement
that the whole determinant class's qualitative Fin4 conclusion follows from
the existing strict-minimum theorem once its entrance is proved, and the
unit-singleton hypothesis of the actual low-active consumer. I inspected
these final changes and checked
`exists_uniformEquilibriumPayoff_of_lowActiveQuitPayoff`
(`UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`):
it requires both `QuittingUnitSoloExit` and
`HasLowActiveQuittingRootQuitPayoff`, exactly as now stated. The raw fixture
has singleton vector `(1,0,0,0)` and therefore does not meet its first
hypothesis. These changes resolve the source issue and narrow the novelty
claim; they do not change the accepted mathematical proofs. No objection
remains to this exact final text.

The last inspected change after the previously accepted `d7317148` version
makes the rational-input contract explicit: use rational M, target error,
and supplied kappa or beta, weakening any real valid bounds in the safe
direction. Increasing M or beta (still below one), or decreasing positive
kappa, preserves the hypotheses. The construction does not claim to
recognize the universal exclusion hypothesis from arbitrary raw input.
This clarification is correct and introduces no new mathematical premise
beyond the intended rational-data contract. Acceptance applies to the
current `a7a4562e` hash recorded above; no objection remains.
