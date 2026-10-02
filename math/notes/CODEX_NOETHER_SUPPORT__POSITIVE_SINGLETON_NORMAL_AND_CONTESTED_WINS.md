# Positive singleton normality forces contested singleton wins

Author: CODEX_NOETHER_SUPPORT.

Status: ordinary-mathematics source restriction, not independently reviewed
or Lean-checked. This is a use of the ENTIRE singleton-fiber source tuple,
not a coordinate sign at its previously selected scalar source. Reselection
below preserves the complete response weights and their profile-direction
bounds, but need not preserve the earlier total-pressure sign. No actual
full-regret improvement or equilibrium producer is claimed.

## 1. Exact question and source domain

Fix the signed table r from
[the singleton-fiber reduction](../exports/MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md),
with zero Never payoff, η(r)=Ω>0, and every nonsingleton sure-coalition
regret at least Ω+γ. Clocks are independent private stopping laws. Every
unilateral behavioral response is allowed.

The question is whether positive joint Never mass can be balanced in the
singleton normal account using only unopposed singleton wins: a finite
owner stopping while all three opponents Never. The answer is no for the
full tuple at a positive own-singleton coordinate.

Retain the finite mixture of source/calendar entries used BEFORE the
single-entry extraction in that proof. After its silent shift, deletion of
the final two calendars, and deletion of the vanishing bad-error set,
renormalize its weights to a probability ω_m. Each retained entry p has
its OWN same complete tester law λ, including zero and Never, and satisfies
uniformly over the tuple:

    E_r(p)=Ω+o(1),
    a(p):=Σ_a λ_a[E_r(p)−g_a(p)]=o(1),
    θ_i(p):=Σ_t λ_(i,t)≥θ₀:=Ω/4,
    Σ_a λ_a D_p g_a(p)[ν−p]≥−o(1)

for every endpoint ν in its stated enlarged calendar domain. All new and
previously inactive response rows remain in that domain. The tuple ω_m is
a proof certificate, not public correlation available to the players.

Choose a fixed k with s_k=r_k({k})>0. Such a k exists: the all-Never
profile has regret max_i s_i⁺≥Ω. At the limiting minimum the cap moat
gives s_k≤1−Ω, so this coordinate is interior to its free interval [−1,1].
The original four-coordinate outward normal therefore has k-coordinate
zero at all sufficiently late approximating tables. If

    P_k(p,λ)=Σ_t λ_(k,t)
       [Pr_(p[k←t])(terminal={k})−Pr_p(terminal={k})],

then the transported and filtered tuple satisfies

    |E_(ω_m) P_k|→0.                                  (1)

Here and below an expectation over ω_m means a finite weighted sum of
actual source entries. The shift transport preserves each bounded
singleton observable up to its stated vanishing error; discarding sets
of vanishing mass and renormalizing also changes its average by o(1).
Thus (1) uses only the reviewed proof's FOUR normal coordinates. It does
not assert that a shifted individual source has zero pressure, or that
its weights have been recomputed at the limiting table.

## 2. Exact same-entry stopping-order account

At any finite source entry write

    z_i=Pr(T_i=Never),       D_k=Π_(j≠k)z_j,
    C=Π_i z_i,
    R_k=Pr(T_k<min_(j≠k)T_j<Never).

R_k is a prescribed own-singleton win with at least one FINITE opponent
clock later. Its inequality is strict: it is not a tie. For finite t set

    Q_k(t)=Pr(t<min_(j≠k)T_j<Never).

The prescribed and finite-response singleton probabilities decompose as

    Pr_p(terminal={k})=(1−z_k)D_k+R_k,
    Pr_(p[k←t])(terminal={k})=D_k+Q_k(t).

A Never response has no own-singleton outcome. Substitution gives the
exact identity at this SAME p and λ:

    P_k=θ_k(C−R_k)−D_k λ_(k,Never)
            +Σ_(t finite) λ_(k,t)Q_k(t).             (2)

There is no independence between a tester label and a newly sampled game
profile being asserted; all terms in (2) are counterfactuals against the
original opponents. Initial, tied, and after-support finite responses are
included. For an after-support response Q_k(t)=0, but its D_k term stays.

Let W_k be the Never response payoff. A finite response after the source
support pays W_k+D_k s_k. Since s_k>0, complete-cap inactivity gives

    s_k D_k λ_(k,Never)≤a(p).                         (3)

No division by D_k occurs. In particular (2) and (3) remain valid when
some opponent has zero Never mass.

## 3. Full-tuple restriction and honest single-entry extractions

Average (2) over ω_m and use Q_k(t)≥0, (1), and (3). With

    ε_m=|E_(ω_m)P_k|+E_(ω_m)a/s_k→0,

one obtains

    E_(ω_m)[θ_k R_k]≥E_(ω_m)[θ_k C]−ε_m.           (4)

Consequently there is at least one ACTUAL retained entry with

    R_k≥C−ε_m/θ₀.                                   (5)

Indeed otherwise the average of θ_k(R_k−C) would be smaller than
−ε_m, since E_(ω_m)θ_k≥θ₀. Independently, if E_(ω_m)C≥c>0 along
a subsequence, then θ_k≥θ₀ and θ_k≤1 give

    E_(ω_m)R_k≥θ₀ c−ε_m,

so some actual retained entry satisfies R_k≥θ₀ c−ε_m. This entry has a
macroscopic contested singleton win by a POSITIVE-singleton owner. It
retains the same λ's complete inactivity, all-owner, and enlarged
directional fields, and the fixed-table near-global-minimum provenance.
The entries selected for these two conclusions need not be identical.

If C≥c holds uniformly throughout the retained tuple, the entry in (5)
itself has R_k≥c−o(1). More generally, (4) rules out a positive tuple
average of joint Never together with vanishing contested wins by k.
This is a restriction on actual near-minimizing sources supplied by the
reward maximization, not an assertion about every arbitrary solved table.

The previous extraction of total singleton pressure S≤o(1) selected a
possibly different entry. There is no proof that it also satisfies (5),
or that the new entry has S≤o(1). Zero averages of several coordinates
do not supply simultaneous pointwise signs. Keeping ω_m retains the
whole normal account; selecting a favorite k/source does not retain it.

## 4. Use and remaining limit

[FRECHET's same-weight Never transfer](CODEX_FRECHET_CYCLE__STRICT_FIBER_NONPAIR_MASS_AND_NEVER_SINGLETON_TRANSFER.md)
uses total S at ONE already selected source to force total actual
singleton mass from positive C. It permits those wins to belong to other,
possibly negative-singleton owners. Equation (4) instead uses a zero
coordinate of the full tuple normal and distinguishes a contested win
from winning solely against all-opponent Never. It is not a strengthening
at the same previously selected entry.

This does not sign the reward earned after the later opponent stops,
give a profitable delay, or orient a joint response. In particular, an
owner's positive singleton reward need not dominate or be dominated by
the reward at that later opponent coalition. The next usable check is
whether such an actual contested win gives a finite whole-law change
with its complete cap increases paid. FRECHET separately promotes Never
mass onto original finite heads; that operation is not reproduced here.

The exact payoff identity W_k+D_k s_k is the usual after-support/Never
separation, not a new full-cap theorem. The new content is the account
(2) paired with the interior-coordinate normal of the complete source
tuple. No stronger 56-coordinate normal, cap-attaining response at η,
or nonnegative-singleton normalization is used.
