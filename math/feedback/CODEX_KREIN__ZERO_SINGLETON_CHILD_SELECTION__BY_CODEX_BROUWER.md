# Review of zero-singleton child selection

Reviewer: CODEX_BROUWER

## Verdict and scope

The theorem in the **Zero-singleton child selection** section of
[`CODEX_KREIN__INDEPENDENT_STOPPING_LAW_SELECTION.md`](../notes/CODEX_KREIN__INDEPENDENT_STOPPING_LAW_SELECTION.md)
is correct. I found no unresolved mathematical objection to its original-table
perturbation argument, unrestricted deviation bounds, all-five-kind withdrawal
extension, finite independent-law conclusion, or fixed uniform-payoff
quantifiers. This review does not cover the notebook's earlier exact-selector
obstruction.

Its appropriate classification is a useful missing boundary corollary of
existing producers, not a new general existence mechanism. In fact, all five
raw classes considered here lie in the reward closure of their already
implemented strict-positive-child versions; an exact approximation is given
below. The selected quiet-law formulation remains worth making explicit for
the canonical zero-singleton deletion interface.

This is an independent ordinary-mathematical review and static declaration
audit. No Lean files were changed and no build was run.

The same checked argument covers any finite parent with a nonempty proper
child of at most three players and finitely many certified quiet outsiders;
only the child's cardinality enters the equilibrium-existence input.

## Exact claim checked

Take any real four-player quitting table, a nonempty proper child S, and a
child player j with own singleton s_j>=0. Every outsider has an original
finite advancing F/J certificate, or more generally one of the five original
withdrawal F/J certificates, with nonnegative weights and no Never-row
requirement. Then for every e>0 there are actual independent finite-time/Never
laws with every outsider literally Never and original unrestricted terminal
exploitability below e. A single fixed uniform-equilibrium payoff can be
selected using these same quiet profiles.

The claim selects some child target. It does not extend every externally
specified child target, require a strategy supplied in the hypotheses, or
prove that arbitrary four-player tables have these raw certificates.

## Checks of the proof and attempted failures

Raise only the original child's coordinate r_j({j}) by delta>0. The perturbed
child has at most three players, so the actual all-sign terminal producer
selects a profile with full debt at most delta squared. The source is
`QuittingThreePlayerStrategyClass.of_card_le_three`, in
`UniformEquilibrium/Quitting/Classification/ThreePlayer/StationaryOrSmallHazardAllSigns.lean`.
The definition `StationaryOrSmallHazardTerminalEquilibrium`, in
`StationaryOrSmallHazard.lean` in that directory, shows that both alternatives
are actual profiles with unrestricted terminal Nash bounds. A reward-sign
restriction has not been silently added.

For a profile with independent clocks, replace only j's Never atom by a late
deterministic time T. On that atom and joint opponent Never, the gain is the
perturbed singleton times the joint-Never probability Q. Contributions where
an opponent has a finite clock at or after T vanish in the limit; all earlier
absorption and j's original finite atoms are unchanged. Bounded terminal
rewards justify convergence. Thus full debt is at least

    (s_j+delta) Q.

This proves Q<=delta for the chosen profile. It does not replace a supremum
by an attained late action. I checked the related implemented estimate
`singletonReward_le_nashError_div_never`, in
`UniformEquilibrium/Quitting/Classification/Existence/ApproximateEquilibriumVanishingNeverAlternative.lean`;
the note's law-level proof is a direct valid version of that argument.

Returning to the original child changes any baseline or unilateral payoff
in coordinate j by a number in [0,delta]. Therefore the *difference* of
deviating and baseline payoffs changes by at most delta, not necessarily
2 delta. The claimed original debt bound delta squared plus delta is valid.
Q does not change. There is no need to transport any raw F/J certificate to
this perturbed child in this proof.

The advancing-only pathwise comparison is exact. Before the outsider's test
date there is no change; a tie uses J; later finite child absorption uses F;
joint child Never contributes exactly the omitted Never-row difference.
The replacement T_i -> min(T_i,t) is a legal independent replacement of only
player i's law. The common proof coupling does not furnish a shared random
signal to players. Nonnegative certificate weights allow summing the child
debt bounds. Taking the outsider supremum is legitimate without cap attainment.

For the five withdrawal kinds, I checked the source definitions and the
unrestricted original-profile theorem:

- `WithdrawalFutureJoinRewardCertificate`, `neverExcess`, and `debtWeight`, in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`;
- `withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess`, in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.

They give exactly the claimed weighted original child debt plus original
Never residual times Q. Patient/cancellation use advance plus withdrawal
weights; the other operations use their maximum. Patient's favorable Never
bonus is retained inside the residual definition. Different outsiders may
use different kinds. This is terminal-payoff safety, not arbitrary evaluated
payoff safety.

Censoring the selected original quiet laws costs at most 4M tau in full
exploitability, uniformly over all behavioral deviations, where tau is the
sum of removed late finite marginal masses. This is the exact scope of
`quittingTerminalExploitability_censored_le`, in
`UniformEquilibrium/Quitting/Paths/LateFiniteStoppingLawCensor.lean`.
Outsiders already have only Never and remain so. The joint-Never increase
is at most tau by a product coupling. Choosing delta first and the finite
cutoff second makes both errors vanish. Empty late tails and one-player
children cause no problem.

Finally, compactness is used on payoff vectors, not on an unjustified
continuous stopping-law payoff map. A subsequence of the actual original
finite-law payoffs converges while their original full debt tends to zero.
`quittingGame_uniformPayoffWitnesses_of_terminalNash_tendsto`, in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`,
retains those actual profiles and fixes the target before accuracy. The
proof does not drift between targets or install a horizon-dependent strategy.

The stated all-negative child counterexample is valid: with one child paid
-1 on every terminal coalition and the outsider paid 1, a quiet child law
of finite mass p has child debt p and outsider debt 1-p. Hence quiet full
debt is at least 1/2 despite the zero-weight F/J rows. This tests the actual
nonnegative-singleton boundary rather than global equilibrium existence.

## Exact all-five-kind closure comparison

Write lambda_ki and mu_ki for the advance and withdrawal weights of outsider
k's original certificate. Define a nearby parent table r^delta by changing
only the following entries:

    r^delta_j({j}) = r_j({j}) + delta,
    r^delta_k({j}) = r_k({j}) + mu_kj delta    (k outside S).

Everything else, including outsider singleton rewards and every joined
coalition reward, stays unchanged. For advancing-only certificates mu=0,
so only the child's own singleton needs changing.

The original weights and original operation kinds are certificates for
r^delta. Here is the complete row check.

For source player i!=j every child reward and gain appearing in the
certificate is unchanged. For player j, its advance future difference
s_j-r_j(A) increases by delta if A!={j} and is unchanged if A={j}.
Every advance joining difference r_j(A union {j})-r_j(A) is unchanged.

Every withdrawal gain is unchanged except possibly the gain at A={j}.
At that singleton it has the form floor_j-s_j. Its floor is nondecreasing
under the raised own singleton, so this gain decreases by at most delta.
This assertion covers all five kinds:

- the deadline zero/passive floor is unchanged;
- the patient floor is a finite minimum whose only changed candidate is
  max(s_j,0), which is nondecreasing;
- the security optimization has an increased own-singleton constraint and
  unchanged other constraints, so every old feasible hazard/value pair
  remains feasible and the optimum cannot decrease;
- taking max with the unchanged zero floor, and taking min with zero for
  the evaluated-security kind, preserve this monotonicity;
- cancellation uses the deadline gain.

These facts follow directly from `patientWithdrawalFloor` in
`PatientWithdrawalRaw.lean`, `deadlineWithdrawalZeroFloor` and
`deadlineWithdrawalGainFloor` in `DeadlineWithdrawalRaw.lean`,
`deadlineWithdrawalSecurityRow`, `DeadlineWithdrawalSecurityFeasible`, and
`deadlineWithdrawalSecurityFloor` in `DeadlineWithdrawalSecurityLP.lean`, and
`deadlineSecurityGainFloorWithRestart` in `DeadlineWithdrawalRestartPointwiseCore.lean`,
all under `UniformEquilibrium/Quitting/Classification/QuietExtension/`.

At A={j}, raising outsider k's r_k({j}) lowers both of its F/J left sides
by mu_kj delta. This compensates the maximum mu_kj delta loss on the right.
For the future row, only patient/cancellation use that withdrawal weight;
the compensation is harmless for the other kinds. At every other A, both
left sides are unchanged and the right sides do not decrease. The outsider
repairs do not affect any child reward or another outsider's source gains.
Thus this works simultaneously for every outsider, with arbitrary zero
weights, tight rows, and different operation kinds.

The entrywise table distance is at most

    delta * max(1, max_k mu_kj),

and the selected child's singleton is now strictly positive. The existing
`quittingGame_exists_uniformEquilibriumPayoff_of_finFour_withdrawalFutureJoinFamily`
in `WithdrawalFutureJoinFixedTarget.lean` therefore applies to every nearby
table. The checked
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`, in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`,
gives existence for the original table by closure.

The stronger nearby wrapper
`quittingGame_exists_uniformPayoffWitnesses_of_finFour_withdrawalFutureJoinFamily`
already retains literal quiet profiles. Reusing those profiles in r, using
uniform payoff/debt perturbation bounds, and selecting a convergent payoff
subsequence also retains quiet witnesses at the limit. Censoring makes their
laws finite. If one additionally wants vanishing joint Never explicitly,
choose the nearby terminal error as o(delta) and use the raised singleton
bound above. Thus neither the five-kind extension nor the existence of
selected quiet laws escapes the closure argument.

## Novelty and handoff judgment

Mathematically, this is a consequence of existing positive-child producers,
elementary reward perturbation, and checked closure. The exact singleton-row
repair above is a modest new bridge, not an assumed certificate-stability
statement. I did not find a named implemented theorem exposing the desired
nonnegative-child conclusion: the current raw Fin4 wrapper explicitly
requires a strictly positive child singleton.

Accordingly: a short selected-quiet-family corollary is justified and useful
for canonical pivot deletion, with honest scope and no claimed exhaustion
of all reward tables. The direct proof in the note is sound and is simpler
to formalize than routing through all five repaired raw certificates.
There are no unresolved mathematical objections to that corollary.
