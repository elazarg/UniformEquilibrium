# Worst reward tables: one coupled reward and enlarged-calendar certificate

Author: CODEX_NOETHER_SUPPORT.

Status: complete ordinary-mathematics source calculation, not independently
reviewed or Lean-checked. The construction couples an outer reward normal
with the SAME near-active response weights that control actual enlarged
calendar directions. It also extracts one retained source with a signed
own-singleton account. No improving profile, positive-gap table, uniform
equilibrium theorem, or impossibility of a positive certificate is proved.

## 1. Exact question and probability model

There are four players I={0,1,2,3}, fifteen nonempty coalitions C, and Never.
The reward table ranges over the fixed cube R=[−1,1]^(I×C); Never pays zero.
Every prescribed profile consists of independent private stopping laws on
the nonnegative integers together with Never. A unilateral deviation
replaces one complete law. No correlated choice among profiles is allowed.

For an actual profile p let μ_p be its terminal outcome law. If player i
uses pure time t, let ν_(p,i,t) be the resulting outcome law. Its reward row
v_(p,i,t) has only player i's coordinates nonzero, where it equals
ν_(p,i,t)(S)−μ_p(S). Its gain is g_(i,t)(r,p)=v_(p,i,t)·r.
Include a labelled zero row a=0, with v_0=g_0=0. Write

    E_r(p)=sup_(i,t) g_(i,t)(r,p),
    η(r)=inf_(all independent actual p) E_r(p),
    Ω=max_(r∈R) η(r).

The cap is unrestricted: mixed stopping laws average pure-time payoffs.
Thus the displayed supremum includes every behavioral deviation. The zero
row does not change E. Since every reward row has ℓ¹ norm at most two,
E and η are 2-Lipschitz in r. Consequently the maximum defining Ω exists.
No attainment of the unrestricted profile infimum is assumed.

The question is conditional on Ω>0: does global reward maximization force
one certificate retaining both genuine near-minimizing source provenance
and simultaneous profile-direction constraints, rather than two unrelated
dual averages? The theorem below answers this source question positively.
It does not determine whether Ω is zero.

## 2. Common smoothing on a window of calendars

Fix m≥1 and τ>0. Put L=2m+1 and

    A_N={0,...,N−1,Never},       X_N=∏_i Δ(A_N),
    T_L={0,...,L,Never},         J={0}∪(I×T_L),
    q=|J|=4(L+2)+1,             ε=τ log q.

All X_N, N≤L, are embedded by their literal dates in X_L. On X_L define

    F(r,p)=τ log Σ_(a∈J) exp(g_a(r,p)/τ),
    λ_a(r,p)=exp(g_a(r,p)/τ) / Σ_b exp(g_b(r,p)/τ).

The same function F and same labelled tester list J are used for EVERY
calendar in this construction. In particular, the number or multiplicity
of late rows is not changed between two adjacent minimizations. For p∈X_N,
all finite tests t≥N are equal in value, but remain labelled in J.

Every test beyond L has the value of test L on X_L. Therefore throughout
X_L the maximum over J is the actual full E, and

    E_r(p) ≤ F(r,p) ≤ E_r(p)+ε.                         (1)

Let f_N(r)=min_(p∈X_N) F(r,p), and select a table r_m maximizing

    Φ(r)=(1/(m+1)) Σ_(N=m,...,2m) f_N(r)                (2)

over R. These minima and the outer maximum are attained by continuity and
compactness. The order is MAX over the table of an AVERAGE of separate
MINIMA over independent laws. It is not a max over tables and profiles
jointly, and the average in (2) is not a game strategy.

The checked quantile-clock approximation, specialized to the reward cube,
implies a bound ρ_m→0, uniform in r and N≥m, such that

    η(r) ≤ min_(p∈X_N) E_r(p) ≤ η(r)+ρ_m.               (3)

One explicit choice for m≥9 is k_m=floor((m−1)/8) and ρ_m=24/k_m.
The support bound 8k_m+1≤m makes the profile from that theorem a literal
member of X_m. Set ρ_m=2 for m<9. Only convergence of ρ_m is used below.

Equations (1)–(3) give, with h=Φ(r_m),

    Ω ≤ h ≤ Ω+ρ_m+ε,
    η(r_m) ≥ Ω−ρ_m−ε,                                  (4)
    0 ≤ E_(r_m)(p)−η(r_m) ≤ ρ_m+ε                      (5)

for EVERY minimizer p of EVERY f_N(r_m), m≤N≤2m.
Indeed f_N lies between η and η+ρ_m+ε, so the same holds for Φ;
at a minimizer E≤F=f_N. No source is chosen merely because it has a small
finite-menu Nash error.

## 3. The coupled finite certificate

Set

    H=96+256/τ,
    Δ_N=f_N(r_m)−f_(N+1)(r_m)≥0,
    R_N=sqrt(2HΔ_N),
    Rbar=sqrt(2H(2+ε)/(m+1)).                           (6)

There are finitely many weights θ_b≥0, Σ_b θ_b=1, and, for every b and
N=m,...,2m, an actual source p_(b,N) minimizing f_N(r_m). At each source
use EXACTLY its softmax weights λ^(b,N)=λ(r_m,p_(b,N)). They satisfy:

1. For every simultaneous independent-law endpoint ν∈X_(N+1),

       Σ_a λ_a^(b,N) D_p g_a(r_m,p_(b,N))[ν−p_(b,N)]
          ≥ −R_N.                                      (7)

   For ν∈X_N, the same quantity is nonnegative exactly.

2. The weighted inactivity, including every labelled complete tester, obeys

       Σ_a λ_a^(b,N)[E_(r_m)(p_(b,N))−g_a(r_m,p_(b,N))]
          ≤ ε.                                         (8)

3. The reward-gradient average

       G=Σ_b θ_b (1/(m+1)) Σ_N Σ_a λ_a^(b,N) v_(p_(b,N),a)

   belongs to the outward normal cone N_R(r_m). In coordinates, G_k=0 at
   interior reward coordinates, G_k≥0 on the +1 face, and G_k≤0 on the −1
   face. Moreover

       h−ε ≤ r_m·G=||G||₁ ≤ h.                         (9)

4. The SAME source mixture has a vanishing-capable enlarged-direction
   error account:

       Σ_b θ_b (1/(m+1)) Σ_N R_N ≤ Rbar.              (10)

At most 61 indices b suffice; no sparsity optimization is intended. A b is
a tuple of actual sources, one on each calendar. None of the tuples, the
weights θ, or the average laws is asserted to be executable as one profile.

### Proof of the source and entropy claims

The gain polynomials are multiaffine in the four complete marginal laws.
Differentiating F gives

    D_p F=Σ_a λ_a D_p g_a,        ∇_r F=Σ_a λ_a v_a.     (11)

At any global minimizer on X_N, differentiation along the feasible segment
to ν∈X_N proves the exact nonnegative part of (7). This holds for ALL
coordinates together, not four independently chosen multiplier laws.

With entropy Hent(λ)=−Σ_a λ_a log λ_a, direct substitution gives

    Σ_a λ_a g_a=F−τ Hent(λ),      0≤Hent(λ)≤log q.

Since E≤F and every g_a≤E, this proves (8). It also proves (9) after the
outer normal statement, because the sources' F values average to h.

### Proof of enlarged-calendar control with the same weights

Fix one source p∈X_N and any ν∈X_(N+1), and let
p_i(α)=(1−α)p_i+αν_i for 0≤α≤1. These are actual independent laws on
X_(N+1)⊆X_L. Each gain is bounded by two in absolute value. Its derivative
along the chord is bounded by 16: each of the four one-coordinate endpoint
differences is at most four. Its second derivative is bounded in absolute
value by 96: there are twelve ordered distinct-coordinate pairs, each an
alternating sum of four gains bounded in absolute value by eight.

Consequently, at every point of the chord,

    (d²/dα²) F(r_m,p(α))
       = Σ_a λ_a g_a'' + Var_λ(g_a')/τ
       ≤ 96+256/τ = H.                                (12)

Let the derivative at zero be −c<0. The derivative bound gives c≤16,
and H≥96, so α=c/H lies in [0,1]. Taylor's upper bound gives

    F(r_m,p(c/H)) ≤ f_N(r_m)−c²/(2H).

The left side is at least f_(N+1)(r_m). Thus c≤sqrt(2HΔ_N), proving (7)
for the ORIGINAL softmax weights from (11). No new minimax multiplier is
selected for this enlargement.

The complete tests at the changed profile include N+1. Its row must not be
identified with N. Tests t≥N+1 ARE identical, with identical derivatives,
on X_(N+1). Thus one may aggregate their λ masses into the single label
N+1 AFTER (7), obtaining precisely the complete tester set T_(N+1).
This does not drop that new tester, or identify opponent survival with joint
survival. Never retains its separate row.

Finally the Δ_N telescope at the SAME selected reward table:

    Σ_(N=m,...,2m) Δ_N=f_m(r_m)−f_(2m+1)(r_m)≤2+ε.

The last inequality uses 0≤F≤2+ε. Cauchy–Schwarz yields (10). Maximizing
each f_N at a different reward table would not justify this calculation.

### Proof of the outer normal with the same source tuples

For completeness, the required elementary envelope fact is as follows.
If f(r)=min_(p∈X) F(r,p), with X compact and F continuously differentiable,
then for every fixed direction d,

    f'_+(r;d)=min_(p∈argmin F(r,·)) ∇_r F(r,p)·d.      (13)

The upper bound follows by holding any old minimizer fixed. For the lower
bound choose minimizers p_t at r+td, extract a convergent subsequence, and
use uniform differentiability in r. Its limit minimizes at r, while
F(r,p_t)−f(r)≥0. This proves the lower bound for every subsequential lower
limit, and hence (13). No differentiability of the minimizing-law selector
or generic game regularity is assumed.

Apply (13) separately to the finitely many terms in (2). The derivative of
Φ equals the minimum over tuples (p_N)_N of their average reward-gradient
dot d. Those tuples form a compact set. If the convex hull of their average
gradients missed N_R(r_m), finite-dimensional strict separation from that
closed convex cone would give a feasible cube direction d with every such
dot product strictly positive. Equation (13) would make Φ increase, contrary
to maximality. Therefore their convex hull meets N_R(r_m), giving G.
In dimension sixty, affine-dependence elimination leaves at most 61 tuples.
The normal signs imply r_m·G=||G||₁; the entropy identity proves (9).

This smooth envelope step would NOT be justified by directly replacing F
with the nonsmooth maximum E and freezing old active tester sets. Moving
independent laws can change the active set on the reward perturbation's
scale. Smoothing is used before the two optimizing quantifiers.

## 4. Limiting worst-table provenance and one retained-source condition

Take τ=m^(−1/2). Then ε→0, ρ_m→0, and Rbar→0. Compactness extracts
r_m→r*, and (4) plus reward Lipschitz continuity gives η(r*)=Ω. Every
source in the certificate, reused literally at r*, is uniformly
near-minimizing for its FULL regret. No convergence of its stopping laws
to an actual minimizer is claimed. Since ||G||₁≤2, take a further subsequence
on which G converges. The inequalities G·(r−r_m)≤0 for every fixed r∈R
pass to the limit. Equation (9) therefore gives a limiting reward normal
of norm Ω, nonzero if Ω>0.

There is a concrete consequence at ONE retained actual source, not merely
an averaged law. Assume Ω>0. The existing MAX-minimum singleton-margin
theorem, together with caps bounded above by one, gives

    r*_i({i})≤1−Ω for all i.                            (14)

Therefore for large m every own-singleton reward coordinate of r_m is
strictly below +1. For each source define its weighted singleton pressure

    S_(b,N)=Σ_(i,t) λ_(i,t)^(b,N)
                    [ν_(p_(b,N),i,t)({i})−μ_(p_(b,N))({i})].

Always |S_(b,N)|≤1. The normal signs at these four reward coordinates give

    Σ_b θ_b (1/(m+1)) Σ_N S_(b,N)
        =Σ_i G(i,{i})≤0.                               (15)

Let a=sqrt(Rbar)<1. By (10), the mixture mass on calendars with R_N>a is
at most a. Removing those entries changes the upper bound in (15) by at
most a. Hence SOME retained source p=p_(b,N), with its SAME λ, satisfies

    R_N≤a,       S_(b,N)≤a/(1−a).                      (16)

Indeed the surviving mass is at least 1−a, so one surviving value is no
larger than its normalized average. Combining (5), (7), (8), and (16)
produces ONE actual sequence with full regret tending to Ω, vanishing
near-activity error, vanishing simultaneous enlarged-direction error, and
nonpositive limiting weighted singleton pressure. In literal clock terms,

    ν_(p,i,t)({i})=Pr_p(T_j>t for every j≠i) for finite t,
    ν_(p,i,Never)({i})=0.

Thus the new signed condition is about actual singleton probabilities on
one source and its weighted complete responses, not about a fictitious
public mixture. The selection may depend on this chosen reward direction;
it does not make all four singleton coordinates individually nonpositive
at one source.

## 5. Tests, source comparison, and the remaining mathematical question

The proof retains several possible failure modes explicitly.

- Separate global table maximizers at each N do not telescope; (2) uses
  one common table and a calendar average.
- Changing the softmax tester list between adjacent N changes λ at the
  source. The common pool J prevents that substitution.
- Outer normalization alone does not make any individual source gradient
  a cube normal. Extraction (16) gives only its displayed scalar sign.
- Projecting G onto one player, as in the earlier 15-vector result, can
  destroy the simultaneous profile-gradient inequalities at its sources.
  That projection is not performed here.
- The error in (7) is for X_(N+1), with complete testers T_(N+1) after the
  justified aggregation. No unbounded new-date direction, silent-prefix
  all-owner multiplier bound, or chronological return is asserted.

An exact elementary check is the one-player specialization with singleton
reward one and Never zero. For a common pool of finite tests 0,...,L plus
Never and the zero row, X_0 contains only Never, with

    f_0=τ log((L+1)exp(1/τ)+2).

On X_1 the sure date-zero law minimizes F, giving

    f_1=τ log(L+2+exp(−1/τ)).

At the X_0 source the direction toward that sure law has derivative
−((L+1)exp(1/τ)+1)/((L+1)exp(1/τ)+2)<0. Thus old-domain stationarity
alone cannot constrain the external direction. Its strictly positive
adjacent minimum gap is exactly the error source used in (12). Omitting
the after-support test at X_0 would incorrectly report zero full regret.
This check does not claim a positive unrestricted minimum; the sure law
is exact Nash. No numerical grid or new search was run.

The bounded source audit read the complete HILBERT
[extremal-table note](CODEX_HILBERT__EXTREMAL_REWARD_TABLE_VARIATIONAL_TEST.md),
SKEPTIC's [global portfolio dual](CODEX_SKEPTIC__GLOBAL_PORTFOLIO_DUAL_AND_SINGLETON_RAY.md),
[operation audit](CODEX_SKEPTIC__GLOBAL_PORTFOLIO_REFINEMENT_AUDIT.md), and
[explicit approximation rate](CODEX_SKEPTIC__EXPLICIT_FINITE_PORTFOLIO_RATE.md).
HILBERT already gives approximation-safe reward normals from true
near-minimizers. SKEPTIC already gives the global finite-portfolio LP dual
and a complete-grid singleton-ray balance. Neither identifies its reward
weights with simultaneous marginal-law optimality weights; the grid sources
in the singleton-ray result need not approach the true minimum.

HAHN's [finite KKT note](CODEX_HAHN__FINITE_CLOCK_EXPLOITABILITY_KKT_BOUNDARY_OR_CROSS_AMPLIFICATION.md)
and RENY's [simultaneous-response audit](CODEX_RENY__SIMULTANEOUS_ACTIVE_RESPONSE_RECOMBINATION_BOUNDARY.md)
already retain simultaneous old-domain multipliers. FRECHET's
[enlarged-calendar note](CODEX_FRECHET_CYCLE__ENLARGED_CALENDAR_NEAR_OPTIMALITY_AND_CROSS_AMPLIFICATION.md)
already supplies enlarged-domain approximate multipliers from adjacent
minimum gaps. The new contribution here is THEIR COUPLING to the outer
reward-normal account through one common smooth objective and same-table
calendar telescoping, plus the single-source extraction (16). No independent
newness of ordinary KKT, entropy calculus, or convex separation is claimed.

Exact declarations inspected, without a Lean build:

- `abs_quittingTerminalExploitabilityInf_sub_le_of_reward_close` and
  `quittingTerminalExploitabilityInf_scaleQuittingReward` in
  `Research/Quitting/TerminalExploitabilityRewardRobustness.lean`;
- `exists_finiteClockSemanticPair_exploitability_eq_upper`,
  `escapeAwareQuantileClockUpper_sub_exploitabilityInf`,
  `quantileClockSupport_fin4`, and
  `escapeAwareQuantileClock_fin4_normalized_quantitative_bracket` in
  `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`;
- `minimumTerminalSemantic_exploitabilitySingletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`.

No literature-derived theorem is used. Narrow searches in these source
neighborhoods and the cited notebooks found no common smoothed-calendar
reward/profile certificate; this is not an exhaustive priority claim.

Concrete next question: can the SAME near-active enlarged-direction weights
in (16), under true positive-minimum source constraints, force strictly
positive weighted singleton pressure? That would contradict this source.
No such sign has been proved. In particular, a two-player mixed replacement
coefficient Σ_a λ_a Δ_jΔ_k g_a is a different reward-linear functional
from Σ_a λ_a v_a at the original source. Its sign does not follow from
reward normality without an additional exact identity or feasible-direction
argument. There is an exact obstruction to identifying the entire mixed
tester family with one same-source reward perturbation d. For every i,

    Σ_(t∈A_N) p_i(t) g_(i,t)(d,p)=0.

But, when i is one of the two changed owners, Δ_iΔ_j g_(i,t) is the
constant −Δ_iΔ_j U_i across ALL t. Its p_i-average is nonzero whenever
that mixed prescribed-payoff coefficient is nonzero. Thus the testerwise
identification is impossible in that case. This does not rule out a weaker
aggregate identity or a separately justified counterfactual-source argument.

Nor does (7) control every full-response inequality after a finite move.
The result supplies coupled variational data, not an equilibrium producer
or a conjecture-closing descent.
