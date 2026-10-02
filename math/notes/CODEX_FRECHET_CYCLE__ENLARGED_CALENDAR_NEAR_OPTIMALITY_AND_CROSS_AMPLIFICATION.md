# Enlarged-calendar near-optimality gives a boundary-free approximate cross source

Identity: CODEX_FRECHET_CYCLE.

## Status and exact question

Ordinary mathematics, not independently reviewed or Lean-checked. This
source-level calculation uses genuine GLOBAL near-optimality on one larger
calendar. It gives an approximate simultaneous derivative certificate on
the enlarged domain and, under a hypothetical positive limiting value, a
near-active cross-amplification square at EVERY sufficiently large finite
global minimizer. The selected first response may be the formerly external
date K; the genuinely new tester K+1 is retained. No profitable full-objective
competitor or chronological Nash--Bellman chain is concluded.

The question is whether the after-menu-only exception in the old finite KKT
dichotomy survives when η_K−η_(K+1) tends to zero. It does not survive as a
separate source alternative: the comparison below yields a cross square
also in that case. Exact activity is weakened to vanishing inactivity, and
the source is not called an exact minimizer of the enlarged domain.

## 1. Finite data and the two different domains

There are four players, arbitrary signed terminal rewards with |r_i(S)|≤M,
M>0, zero reward at Never, and independent stopping laws. Every complete
behavioral replacement is allowed. Put

    A_K={0,...,K−1,Never},          X_K=∏_i Δ(A_K),
    T_K={0,...,K,Never},
    g_(i,t)(p)=V_(i,t)(p_-i)−U_i(p),
    E(p)=max_(i,t∈T_K) g_(i,t)(p),  η_K=min_(p∈X_K) E(p).

Fix K≥1 and ANY global minimizer μ∈X_K. Write

    η=η_K,       Δ=η_K−η_(K+1)≥0,       R=√(192MΔ).

Embed μ, with the same dates and masses, in X_(K+1). On this larger domain
the COMPLETE testers are T_(K+1)={0,...,K+1,Never}. All gains below use
this larger tester set. At the source, dates K and K+1 have identical
payoffs: all opponents stop before K or choose Never. Hence E(μ)=η also
when evaluated on T_(K+1). They need not coincide at any changed profile.

For each tester a=(i,t) let Dg_a(μ)[ν−μ] be its ordinary multilinear
directional derivative in the four marginal probability vectors. Every
ν∈X_(K+1) is a possible simultaneous whole-law endpoint.

## 2. The enlarged linearized minimax value

Define the finite convex optimization value

    L=min_(ν∈X_(K+1)) max_a {g_a(μ)+Dg_a(μ)[ν−μ]}.

Then

    η−R≤L≤η.                                           (1)

The upper bound uses ν=μ. For the lower bound choose a minimizer ν and
write γ=η−L≥0. Consider the ACTUAL independent profile

    p_i(α)=(1−α)μ_i+αν_i,        0≤α≤1.

Each complete gain is multiaffine in these four whole laws. A mixed second
derivative in two distinct coordinates is an alternating sum of four
corner gains. Since every corner gain lies in [−2M,2M], its absolute value
is at most 8M. There are twelve ordered distinct-coordinate pairs, so the
second derivative along this joint chord has absolute value at most 96M.
Taylor's formula therefore gives, uniformly in every complete tester,

    g_a(p(α))≤g_a(μ)+αDg_a(μ)[ν−μ]+48Mα².

The maximum of the affine first-order part is at most
(1−α)η+αL. Thus

    E(p(α))≤η−αγ+48Mα².                                (2)

Every derivative endpoint increment in a single coordinate has absolute
value at most 4M, so L≥−18M and γ≤20M. Consequently α=γ/(96M) lies in
[0,1]. Substitution into (2) gives η−γ²/(192M). Since p(α) belongs to
X_(K+1), GLOBAL optimality there gives

    η−Δ=η_(K+1)≤E(p(α))≤η−γ²/(192M).

This proves (1). The old KKT stationarity on X_K alone does not prove this
inequality for endpoints using the new date K.

## 3. One simultaneous near-active dual law

Finite affine minimax duality applied to L supplies a probability law λ
on ALL testers a∈I×T_(K+1) such that, for every ν∈X_(K+1),

    Σ_a λ_a {g_a(μ)+Dg_a(μ)[ν−μ]}≥L≥η−R.

Taking ν=μ and using g_a(μ)≤η gives the two simultaneous conclusions

    Σ_a λ_a(η−g_a(μ))≤R,                               (3)
    Σ_a λ_a Dg_a(μ)[ν−μ]≥−R    for EVERY ν∈X_(K+1).   (4)

No tester is assumed exactly active. The average inactivity in (3), not
an unspecified near-active set, is the retained error account. Both (3)
and (4) use the SAME λ. The second statement includes all four marginal
directions at once and all whole-law endpoints using date K.

## 4. Cross amplification, including a formerly external first response

Let θ_j=Σ_t λ_(j,t), and select j with θ_j≥1/4. Write d_j=B_j(μ)−U_j(μ).
Since every gain owned by j is at most d_j, (3) implies

    d_j≥η−R/θ_j≥η−4R.                                 (5)

Choose ANY complete cap-attaining pure response r of j at μ. It can always
be chosen in T_K, including K or Never. Therefore μ'=μ[j←δ_r] belongs to
X_(K+1), and U_j(μ')−U_j(μ)=d_j. For every tester owned by j, irrespective
of activity, its derivative in this coordinate is exactly −d_j.

For a tester a owned by another player put C_a=g_a(μ')−g_a(μ). Single-law
affinity identifies this with its derivative. Equation (4) therefore gives

    Σ_(a not owned by j) λ_a C_a≥θ_j d_j−R.            (6)

Fix τ>0 and suppose

    η>8R+16MR/τ.                                      (7)

By (3), the total λ-mass of testers with g_a(μ)<η−τ is at most R/τ.
Every C_a is at most 4M, so deleting those testers removes at most 4MR/τ
from the right-directed sum in (6). In particular some remaining tester
(i,t), i≠j, exists. Its cross increment is at least

    [θ_j d_j−R−4MR/τ]/(1−θ_j).

Here θ_j<1, since otherwise (4) and (5) would give d_j≤R and η≤5R,
contrary to (7). The function (θd−b)/(1−θ) is increasing in θ whenever
d>b. With b=R+4MR/τ, condition (7) gives d_j>b. Using θ_j≥1/4 and (5)
therefore yields the precise source package

    g_(i,t)(μ)≥η−τ,
    g_(i,t)(μ')−g_(i,t)(μ)≥β,
    β=η/3−8R/3−16MR/(3τ)>0.                            (8)

The first response r is a genuine cap response, paid d_j≥η−4R. The
second response t is near-active and may be K+1. In particular it cannot
be replaced by K after j is moved to r=K. Equation (8) holds for EVERY
choice of r in j's old complete cap set, with the later i,t allowed to
depend on that choice. This quantifier permits subsequent temporal choice
of the first response; it does not prescribe a favorable second response.

If Δ=0, then R=0, (3) supports λ on exactly active tests and (8) gives
β=η/3. If η_K tends to m>0, choose τ_K=√(MR_K) whenever R_K>0; for R_K=0
use any positive τ_K tending to zero. Then (7) holds eventually,
τ_K→0, β_K→m/3, and every source admits (8). There is no separate
after-menu-only alternative at these sufficiently large sources.

## 5. What the existing chronological extraction now receives

Keep (8), and assume β>τ. For player i write V_a and V'_a for response
payoffs before and after j's change. Whole-law affinity gives

    g_(i,t)(μ')−g_(i,t)(μ)
      =Σ_(s∈A_K) μ_i(s)[(V'_t−V'_s)−(V_t−V_s)].

Select s in the LITERAL support of μ_i with its bracket at least β.
Near-activity gives V_t−V_s≥−τ, since B_i−V_t≤τ. Hence

    (V'_t−V'_s)−(V_t−V_s)≥β,
    V'_t−V'_s≥β−τ=:G>0.                               (9)

Let ell be the finite first-disagreement date of s,t. The two responses
coincide whenever an opponent stopped strictly before ell, and payoffs
differ by at most 2M. Thus

    Pr_(μ'_-i)(all opponent clocks≥ell)≥G/(2M).         (10)

Because j is deterministic at r, this implies r≥ell, with Never treated
as larger than every finite date. Also s,t≥ell. Therefore the actual
corners μ[j←r,i←s] and μ[j←r,i←t] each have full four-player survival
to ell equal to the same pair-deleted source survival, at least G/(2M).

The elementary extraction in HAHN's pure-time row and full timing-bubble
notes thus applies with the explicit inactivity subtraction τ. It retains
the full fixed-face/remote-tail/escaping-first-disagreement alternatives.
In the escaping case only the COUNTERFACTUAL corners acquire a positive
all-Never cylinder in their weak clock limit. No such minimum provenance
or terminal-law convergence is transferred from μ to those corners.

What is stronger than merely a paid row is (3)–(4) on the full enlarged
domain, together with the universal first-cap-response choice in (8).
Previously the old-domain KKT certificate did not constrain r=K; its
deadline arm supplied a paid edge but not this linked two-player square.
All these enlarged constraints remain at the same genuinely minimizing μ.

This does NOT fix the chronological consumer. The first change is still
a horizontal best-response replacement and the second is a counterfactual
paid row. Neither is a prescribed Nash--Bellman edge. Making both selected
laws pure may raise some other complete regret; the full mixed-law square
still needs every unmarked tester controlled. Approximate dual balance
alone does not provide that upper bound. No adjacent-horizon exact-Nash
source, cap-preserving source replacement, or renewed low-regret selector
has been constructed.

## Sources and exact boundary of the claim

The following notes were read completely for this bounded comparison:

- [HAHN's simultaneous finite KKT dichotomy](CODEX_HAHN__FINITE_CLOCK_EXPLOITABILITY_KKT_BOUNDARY_OR_CROSS_AMPLIFICATION.md).
- [HAHN's pure-time extraction](CODEX_HAHN__KKT_CROSS_AMPLIFICATION_TO_PURE_TIME_PAID_ROW.md).
- [HAHN's fixed-face/full-timing compactification](CODEX_HAHN__FINITE_CLOCK_KKT_FIXED_FACE_OR_FULL_TIMING_BUBBLE.md).
- [RENY's simultaneous active-response recombination boundary](CODEX_RENY__SIMULTANEOUS_ACTIVE_RESPONSE_RECOMBINATION_BOUNDARY.md).
- [NOETHER's actual two-law full-cap comparison](CODEX_NOETHER_SUPPORT__GLOBAL_KKT_TWO_LAW_COMPETITOR_CHECKPOINT.md).

The first already has simultaneous exact KKT on X_K; merely restating that
would add nothing. RENY explicitly isolates that its inequality gives no
control in an external direction using K and keeps the new K+1 tester.
The added argument here is (1), from global near-optimality on X_(K+1),
with an explicit same-source inactivity account. No matching enlarged-
domain near-optimality estimate was found in those concrete sources.

The named Lean interfaces inspected for this lane are
`exists_minimum_quittingControllerFiniteWordLoss`,
`antitone_quittingControllerFiniteWordValue`, and
`tendsto_quittingControllerFiniteWordValue` in
`UniformEquilibrium/Quitting/ControllerTester/FiniteWordValue.lean`, and
`quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul` in
`UniformEquilibrium/Quitting/Paths/SurvivalWeightedSuffixRegret.lean`.
Their use does not make (1)–(10) Lean-checked.

Boundary checks: if an opponent j is Never at the source, responses K and
K+1 both earn the deviator's singleton on that event. Set that singleton
to zero, r_i({j})=1, and r_i({i,j})=−1. After j is moved to K, the same
two responses earn −1 and 1. Thus their equality at μ cannot be used to
merge their gradients or their child caps. This is a branch test, not a
global-minimum counterexample. Separately, 1,000 exact rational choices of
the sixteen corner gains in [−2,2] and rational chord parameters verified
the uniform 48α² Taylor remainder used in (2), with M=1. The derivative
bound above, not this finite experiment, proves the general inequality.

Next question: can the universal enlarged-domain balance (4), with the
first response r chosen for temporal advantage, orient a noninfinitesimal
whole-law competitor while bounding every unmarked tester? Discarding (4)
and retaining only (9) would simply rejoin the existing paid-row boundary.
