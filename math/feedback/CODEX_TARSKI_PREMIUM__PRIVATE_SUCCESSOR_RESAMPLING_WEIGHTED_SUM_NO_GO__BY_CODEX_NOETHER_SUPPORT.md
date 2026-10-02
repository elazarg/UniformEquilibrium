# Preliminary independent assessment of the successor-resampling certificate

Reviewer: CODEX_NOETHER_SUPPORT.

Verdict: the stated fixed-weight expected-sum obstruction is correct. It
is useful internal evidence for stopping that particular certificate test,
but I do not recommend spending an export gate or formalization effort on
it as new conjecture-facing progress. This is a preliminary mathematical
and value assessment, not export authorization.

## Independent proof and exact manuscript

Before reading the author, I independently constructed the law by the
same finite-CDF recursion in
[the blind record](../notes/CODEX_NOETHER_SUPPORT__FOUR_RESPONSE_MENU_BLIND_CHECK.md),
SHA256 `e899b652cce331f06c5cdb024f36d0e35e6ad057de8934d6c213ac6979884c36`.
That record is preserved unchanged. I then read the full 253-line
[author note](../notes/CODEX_TARSKI_PREMIUM__PRIVATE_SUCCESSOR_RESAMPLING_WEIGHTED_SUM_NO_GO.md),
SHA256 `23c771462c52fd43ca552e431cbd0a618495359c4692f59eeb12b45b11a639f9`.

The independent derivation and Section 2 agree exactly. The strict delay
makes the finite CDF at date n depend only on opponent CDFs at n−1.
The polynomial map is coordinatewise monotone, starts at the Quit-now
weights, and stays in the unit cube. Its increments and residual limit
mass define a genuine probability law on finite dates plus Never.
Matching all finite CDFs then matches the Never atom too. Players with
zero total raw weight may be assigned Never without dividing by zero;
their weighted payoff equality is vacuous.

Each player's prescribed law equals its normalized weighted mixture of
the four response laws. The privately sampled opponents are independent
copies, not the actual opponents' future clocks. Affinity of expected
payoff in one complete replacement law therefore proves the weighted
gain equality before any reward table is selected. No continuity of
terminal payoffs, proper-clock assumption, common randomization, or
equilibrium interpretation is required.

## Added examples and finite witness

The equal-weight polynomial, its factorization, the first two CDF values
1/4 and 51/128, and the limiting CDF 1/2 are correct. Its Never mass is
exactly 1/2, not escaped or unrealized mass. The participant-reward-one
example correctly has a Quit-now gain at least 1/2 there. Thus positive
individual gains can coexist with zero weighted sum; the claim does not
control the maximum or positive parts of gains.

The sixteen diagonal two-copy configurations also give the stated exact
pointwise obstruction. At each such configuration the delayed min/max
responses have the same payoff as Never. Independent binary mixing with
the aggregate Quit/Never coefficient ratios cancels the expected diagonal
expression, so a strictly positive bound on every diagonal type is
impossible. For equal weights, the coefficients 3^(4−|S|) and their sum
256 are correct. This witness is used only for pointwise inequalities;
the manuscript does not falsely treat its diagonal mixture as the law of
two independent nondegenerate profile copies. Section 2 separately supplies
the actual-law obstruction to the expected certificate.

## Narrow source comparison and research value

I inspected
`exists_quittingBehaviorProfile_forall_mem_finiteMenu_payoff_le` in
`UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdog.lean`,
and the nearby finite-menu discussion in
`notes/CODEX_SPINOZA__FINITE_TESTER_SEPARATION_AND_TWO_ESCAPE_BOUNDARY.md`.
The source theorem supplies a profile with nonpositive gain for EVERY
member of each fixed finite menu of complete strategies. It does not
directly apply to these profile-dependent delayed-law maps, whose ranges
need not lie in one finite menu. That distinction in the author note is
genuine and correct.

The new statement is nevertheless not a strict domination of that theorem:
it handles different, profile-dependent test families but gives only a
fixed weighted-average cancellation, not simultaneous safety against all
individual tests. In particular it does not rule out a positive lower bound
on the maximum of the four profile-dependent test gains.

The law-level argument is an elementary fixed-point corollary. On the
one-point compactification N∪{∞}, successor with ∞ fixed, min, and max
are continuous. Their independent-product pushforwards and fixed mixtures
give a continuous self-map of the compact convex product of probability-law
spaces. The usual compact-convex fixed-point principle supplies a fixed
point; the author's triangular monotone recursion is a more explicit direct
proof for these particular rules. This observation concerns continuity of
the law transformation, NOT joint payoff continuity or best-response
continuity. I am not claiming an already checked project declaration of
the complete resampling statement.

The relevant existing law and payoff interfaces inspected were
`compactStoppingLawEquivPMF` and `compactStoppingLawBarycenter` in
`MathUE/ProbabilityMassFunction/CompactStoppingLaw.lean`,
`quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
`UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`, and
`quittingBehaviorStoppingLaw_finiteStoppingLawMixture` and
`quittingTerminalPayoff_update_finiteStoppingLawMixture_eq_expect` in
`UniformEquilibrium/Quitting/Paths/FiniteStoppingLawMixture.lean`.
No source edit or Lean build was performed.

My assessment is therefore: retain the exact note as a short stopped-template
record. It does reject the expected fixed-weight delayed-response certificate,
which the finite-watchdog theorem alone does not literally reject. But no
named conjecture-complete or purportedly exhaustive certificate obligation
has been closed, and the proof is available directly from law-mixture
fixed-point structure, independent of rewards. It does not warrant a new
research packet, hierarchy, broader survey, or an inference about positive
or negative quitting tables. The bounded preliminary assessment is complete.
