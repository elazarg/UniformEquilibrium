# Literal appended-menu separation for exact auxiliary Nash sources

Author: CODEX_NOETHER_SUPPORT.

Status: elementary same-source admissibility check, not a new selection
no-go or an export. It explains why the enlarged-calendar all-law minimax
argument cannot be applied unchanged to the exact auxiliary-Nash family.
Joint law reselection and order-changing retiming remain entirely allowed.

Fix a canonical Fin4 table with |r_i(S)|≤M, zero Never, independent clocks,
and full behavioral exploitability E. Let p be ANY exact auxiliary Nash
source on F_N={0,...,N−1,Never}, using private planned-Never bonuses in
[0,δ]^4. Suppose E(p)>δ. Then the pivot's first omitted date N attains
its full original gain E(p), since every original menu gain is at most δ
and no nonpivot has a larger full cap than its menu cap.

Embed p on a larger literal calendar F_L, L≥N+1, without changing dates
or masses. For EVERY permitted bonus vector ζ∈[0,δ]^4, its auxiliary gain
from finite date N is

    V_(0,N)(p_-0)−U_0(p)−ζ_0 p_0(Never)
      =E(p)−ζ_0 p_0(Never)≥E(p)−δ>0.                 (1)

Thus p does not even belong to the enlarged exact auxiliary-Nash set.
Unlike the all-law domain, adjoining the old complete cap response does
not preserve source feasibility. No normalization of bonuses is needed
for this observation.

There is a horizon-independent distance version. Use total variation
TV(μ,ν)=sup_A|μ(A)−ν(A)|. If q is ANY exact auxiliary Nash law on F_L
with some permitted ζ, then

    Σ_i TV(p_i,q_i)≥(E(p)−δ)/(4M+δ).                 (2)

To prove it, hold q's bonus ζ fixed and use its finite date-N auxiliary
gain as a function of the profile. Bounded independent-product coupling
gives a change at most 2MΣ_(j≠0)TV(p_j,q_j) in its deviation payoff, at
most 2MΣ_jTV(p_j,q_j) in its prescribed payoff, and at most δTV(p_0,q_0)
in its bonus credit. Therefore this gain changes by at most
(4M+δ)Σ_jTV(p_j,q_j). At p it is at least E(p)−δ by (1); at q it is
nonpositive by exact auxiliary Nash. This proves (2). The same reasoning
with an auxiliary ε-Nash output gives numerator E(p)−δ−ε when positive.

In particular, if b_δ=inf_N A(N,δ)>δ, every actual finite A minimizer is
separated from every enlarged-calendar auxiliary Nash law by the uniform
floor (b_δ−δ)/(4M+δ), under this literal-date embedding. This assertion
does use the genuine global objective, unlike a chosen bad-branch test.
It does NOT exclude a globally better equilibrium outside the neighborhood.
It also does not imply a gap in payoff or semantic-pair distance: merely
shifting every finite date can have large total variation without changing
terminal payoffs or full caps. The exact prefix constructions use such a
different embedding and do not contradict (2).

## Source comparison and remaining work

The enlarged all-law argument reviewed in
[FRECHET's note](CODEX_FRECHET_CYCLE__ENLARGED_CALENDAR_NEAR_OPTIMALITY_AND_CROSS_AMPLIFICATION.md)
uses actual independent chords through a source feasible in X_(K+1).
It never claimed those chords preserve auxiliary Nash. Inequality (1) is
the exact extra feasibility obstruction in the bonus-family comparison.

The bounded prior lookup included RENY's
[positive-bonus exactification calculation](CODEX_RENY__POSITIVE_BONUS_APPROXIMATE_COMPLETENESS_TEST.md),
the finite-error/menu-enlargement passages of
[approximate finite timing Nash and reach](CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH.md),
and the stated source and local separation proof in
[the minimum-cap forced-pair tube](SERIAL_ENDPOINT_AUDITOR__MINIMUM_CAP_TUBE_FORCED_PAIR_BARRIER.md).
They already warn that exact support is not recovered from small regret,
that a smaller-menu Nash law is not automatically Nash on its final menu,
and that certain fixed-cap roots cannot be locally exactified. The present
statement is the direct quantitative specialization to the newly internal
pivot date, not a new generic tube theorem. It uses the complete cap split
in `singlePivot_pivot_fullCap_eq_max_menu_never_add_deletedNever`
(`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`).

Next investigation: use global comparison between DIFFERENT auxiliary
equilibria or continuation branches. No further local-chord obstruction
is needed; (1) already stops the direct transfer.
