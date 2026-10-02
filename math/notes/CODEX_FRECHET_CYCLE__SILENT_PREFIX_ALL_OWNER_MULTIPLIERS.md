# A silent prefix forces all-owner mass in the same enlarged KKT certificate

Identity: CODEX_FRECHET_CYCLE.

## Status and exact source implication

Ordinary mathematics, not independently reviewed or Lean-checked. This is a
separate addendum to the independently reviewed
[enlarged-calendar comparison](CODEX_FRECHET_CYCLE__ENLARGED_CALENDAR_NEAR_OPTIMALITY_AND_CROSS_AMPLIFICATION.md),
SHA 385abdda0be425576327365322349264daefab46aa897665a3afb62059e44977.
Those source bytes are unchanged.

The added field is not merely the known scalar harmonic inequality. One
and the SAME approximate derivative certificate simultaneously assigns a
positive mass to EVERY player and tests EVERY enlarged whole-law direction,
including every original cap response. Consequently the first cross edge
can start at any player, not just a player carrying at least one quarter
of the dual mass. It does not yet orient a full-regret competitor.

Keep four players, |r_i(S)|≤M, M>0, arbitrary singleton signs, zero Never
payoff, actual independent stopping laws and unrestricted deviations. Let
μ be a GLOBAL minimizer on A_K={0,...,K−1,Never}, with full value η=η_K.
Write U,B,d=B−U for its actual semantics and s_i=r_i({i}). Assume

    κ_i=B_i−s_i≥σ>0 for every i.                        (1)

Shift every finite clock of μ by one date, leaving Never unchanged. Call
the resulting literal source μ+. Its prescribed payoff remains U. Its
complete cap is max{s_i,B_i}, so (1) proves that its full semantic pair
is STILL (U,B), with E(μ+)=η. This silent-root condition is essential.

The source μ+ uses dates 1,...,K and Never. Take the controller domain
X_(K+2), whose dates are 0,...,K+1,Never, and its COMPLETE tester set
T_(K+2)={0,...,K+2,Never}. Put

    R=√(192M(η_K−η_(K+2))).

The same linearized-chord proof from the input note applies: it needs only
a source of value η and the GLOBAL floor η_(K+2) on the larger domain,
not exact minimality of μ+ there. It supplies a single tester law λ with

    G:=Σ_(i,t) λ_(i,t)g_(i,t)(μ+)≥η−R,
    Σ_(i,t) λ_(i,t)(η−g_(i,t)(μ+))≤R,                  (2)
    Σ_(i,t) λ_(i,t)Dg_(i,t)(μ+)[ν−μ+]≥−R
                  for EVERY ν∈X_(K+2).                (3)

Let θ_i=Σ_t λ_(i,t). Then the claimed all-owner inequality is

    θ_i κ_i≥η−2R−2MR/σ       for EVERY i.               (4)

## 1. The quitting-specific screening identity

Fix k and choose the admissible endpoint ν=μ+[k←Quit0]. Every other
prescribed clock continues at date zero. For i≠k and every tester t>0
or Never, both prescribed play and that deviation receive r_i({k}) at
date zero. Thus the ENTIRE changed gain is zero, not just its continuation
part. Its directional increment is exactly −g_(i,t)(μ+).

For the one exceptional tester t=0 of i≠k, the changed gain is

    a_(i,k)=r_i({i,k})−r_i({k}),       |a_(i,k)|≤2M.

For every tester owned by k, its deviation payoff is independent of k's
prescribed law, while k's prescribed payoff changes from U_k to s_k.
The increment is U_k−s_k. Therefore the exact weighted derivative is

    S_k=θ_k(U_k−s_k)−G+G_k+A_k,
    G_k=Σ_t λ_(k,t)g_(k,t)(μ+),
    A_k=Σ_(i≠k) λ_(i,0)a_(i,k).                        (5)

Since G_k≤θ_k d_k, this gives S_k≤θ_k κ_k−G+A_k.
Equation (3) gives S_k≥−R, hence

    θ_k κ_k≥G−R−A_k.                                  (6)

All initial joining testers were retained in (5). At the silent source,
their gains are g_(i,0)=s_i−U_i, so

    η−g_(i,0)=η+U_i−s_i≥B_i−s_i=κ_i≥σ.

Equation (2) thus bounds the TOTAL initial-tester mass by R/σ. It follows
that A_k≤2MR/σ. Combining this with G≥η−R in (6) proves (4).
No sign of a pair-joining premium is assumed; the initial test is controlled
by its recorded inactivity, not discarded.

In particular, if A:=η−2R−2MR/σ>0, then κ_i≤2M yields

    θ_i≥A/(2M)>0                  for all four players. (7)

Moreover θ_i(η−d_i)≤R follows directly from (2). Thus all source debts
are within R/θ_i of η under this SAME certificate. This is a finite-source
statement, not a claim that all finite minimizers have exactly tied debts.

## 2. Simultaneous cap-response transfers from every owner

Choose for EACH player j any source cap response r_j. It may be selected
from {1,...,K+1,Never}: these are the translated old complete responses.
All are controller actions in X_(K+2). Let

    C_(i,t),j=g_(i,t)(μ+[j←r_j])−g_(i,t)(μ+).

For i=j the increment is exactly −d_j, irrespective of t. Applying (3)
to these four separate directions, all with the same λ, yields

    Σ_(i≠j,t) λ_(i,t) C_(i,t),j≥θ_j d_j−R
                         for EVERY j.                 (8)

The complete tester K+2 remains in each sum. It cannot be merged with
K+1 after a player is placed at K+1.

For any τ>0, remove only testers whose source gain is below η−τ. Their
total λ-mass is at most R/τ and each C is at most 4M. Thus whenever

    b_j:=θ_j d_j−R−4MR/τ>0,

some i≠j and tester t satisfy

    g_(i,t)(μ+)≥η−τ,       C_(i,t),j≥b_j/(1−θ_j).      (9)

Equation (7) makes θ_j<1 as well, so the denominator is legitimate.
These are four simultaneous owner-indexed cross conclusions. Each starts
from the freely chosen r_j; no cap-attaining source atom of λ is required.
The later observer and tester may differ between the four columns.

## 3. Genuine positive-limit use and exact remaining graph boundary

If η_K tends to m>0, the cap-margin assumption (1) holds uniformly for
all sufficiently large finite global minimizers with, for example, σ=m/2.
Indeed a contrary sequence has a convergent full semantic subsequence whose
limit is a global maximum-debt minimum. The inspected checked
`minimumTerminalSemantic_exploitabilitySingletonMargin` gives κ_i≥m
there, contradicting a limiting margin at most m/2. This invokes neither
an actual minimizer at the limiting law nor an unproved cap-preserving
calendar realization.

Hence R→0, A→m, and every θ_i has a positive uniform lower bound. Taking
τ→0 slowly enough that R/τ→0, (9) supplies an edge j→i for every vertex
j, with uniformly positive cross size. The support-time extraction from
the input note keeps the near-activity error τ and the full counterfactual
joint-survival floor. After selecting the four r_j's and stabilizing finitely
many labels, the directed interaction graph therefore has no sink vertex
and contains a cycle of length between two and four.

This is NOT yet control of the unmarked regrets. A directed graph with an
outgoing edge at every vertex can have a closed two-player cycle and other
vertices feeding into it. Nor does a positive θ_i bound the finite change
of that player's full response envelope after two or more laws change.
The weights are supporting lower bounds, not upper bounds on the corner
gains. Initial first-order balance therefore does not justify replacing
the full maximum by a weighted sum during a macroscopic move.

The stronger retained field is (2)–(4) and ALL four column inequalities
(8), not merely the existence of that cycle. The next concrete issue is
whether temporal choice of the r_j's makes some closed interaction subset
repairable while controlling the remaining full tester rows. No such
orientation or exclusion of a closed two-player transfer cycle is proved.

## 4. Prior-result comparison

[HILBERT's all-player-tie draft](CODEX_HILBERT__GLOBAL_MAXIMUM_MINIMUM_ALL_PLAYER_TIES.md)
already proves all d_i=m at a positive unrestricted maximum minimum by
solo-prefix screening. It is ordinary mathematics, not a checked Lean
result or a completed gate here. Its
[small-root calculation](CODEX_HILBERT__SIMULTANEOUS_SMALL_ROOT_TEST.md)
already obtains the scalar harmonic condition mΣ_i1/κ_i≤1.
The contact-cone discussion in
[HAHN's barrier ansatz](CODEX_HAHN__CONTACT_CONE_SEMANTIC_BARRIER_ANSATZ.md)
and Sections 6–7 of
[BLINDSPOT's route audit](CODEX_BLINDSPOT__FIN4_GLOBAL_ROUTE_AUDIT.md)
likewise records that scalar condition.

Summing the limits of (4) recovers precisely the same scalar inequality;
that sum is not claimed new. The extra datum is that these individual
lower bounds hold for the SAME time-indexed λ used to test all enlarged
whole-law changes. The inspected old KKT notes supply only one heavy owner
and do not include the silent initial screening direction together with
the formerly external after-support cap responses at one near-optimal
source. This is the bounded source comparison, not a global novelty claim.

The exact Lean files underlying the source are those recorded in the input
note and `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`.
The mathematical proof of (5) is the literal date-zero outcome calculation
above; no new Lean declaration or export has been made.

As a boundary check, exact rational enumeration on forty signed integer
reward tables, silent one-date source laws, and arbitrary tester weights
verified (5) for all 160 solo updates, including every initial, after-support,
and Never tester. Every noninitial nonowner gain was exactly zero. This
checks the identity, not existence of the global near-optimal source.
