# Fixed finite enlargement of the coupled worst-table source

Author: CODEX_NOETHER_SUPPORT.

Status: ordinary-mathematics addendum to the
[coupled calendar certificate](CODEX_NOETHER_SUPPORT__WORST_REWARD_TABLE_COUPLED_CALENDAR_CERTIFICATE.md).
It preserves the same source/response weights when a downstream actual
repair needs a finite number B of new dates chosen in advance. It is not
a new multiplier-selection mechanism, an equilibrium producer, or an
independent export candidate. The two-player repair existence and its
table-uniform horizon are not proved here.

The parent theorem's frozen SHA is
`fade3cb825778caf0c76a1a4d6b9820e43bd6f430abf6f8af64b5c95973dd854`.
Its [independent review](../feedback/CODEX_NOETHER_SUPPORT__WORST_REWARD_TABLE_COUPLED_CALENDAR_CERTIFICATE__BY_CODEX_FRECHET_CYCLE.md)
passes the coupled source and singleton-pressure claims. This addendum's
fixed-enlargement extension is separate from those reviewed bytes.

## 1. Exact change to the source construction

Keep the reward cube, independent-law semantics, and unrestricted full
regret from the parent note. Fix an integer B≥1 BEFORE choosing the calendar
window m. Use

    L=2m+B,       J={zero}∪(I×{0,...,L,Never}),
    F=τ log Σ_(a∈J) exp(g_a/τ),
    f_N(r)=min_(p∈X_N) F(r,p),
    Φ(r)=(1/(m+1)) Σ_(N=m,...,2m) f_N(r).

Select a global maximizer r_m of Φ and use the same outer source-tuple
normal certificate as before. At each source p∈argmin_(X_N) F(r_m,·),
retain its ORIGINAL softmax λ. Put

    ε=τ log(4(L+2)+1),       H=96+256/τ,
    Δ_(N,B)=f_N(r_m)−f_(N+B)(r_m),
    R_(N,B)=sqrt(2HΔ_(N,B)).

Exactly the original Taylor argument proves, for EVERY ν∈X_(N+B),

    Σ_a λ_a Dg_a(r_m,p)[ν−p]≥−R_(N,B).                (1)

The chord lies in X_(N+B)⊆X_L, and F uses the same pool at both endpoints.
The complete after-support response is N+B, not N or N+B−1. Labels t≥N+B
can be aggregated into N+B only because their value and derivative agree
on this entire enlarged domain. Never remains separate. No new λ is
selected for the larger variation.

## 2. Same-table window telescope and vanishing errors

For a fixed r_m all f_N are nonincreasing. Expand each difference as B
adjacent differences. Every adjacent difference appears at most B times,
so

    Σ_(N=m,...,2m) Δ_(N,B)
       ≤B[f_m(r_m)−f_(2m+B)(r_m)]≤B(2+ε).

Consequently the SAME outer source mixture has average error at most

    Rbar_B=sqrt(2H B(2+ε)/(m+1)).                     (2)

The source near-minimality bound remains ρ_m+ε, and the outer reward normal
and weighted inactivity account are unchanged. For each fixed B, taking
τ=m^(−1/2) makes ε, ρ_m, and Rbar_B tend to zero. The single-source
singleton-pressure extraction applies with a=sqrt(Rbar_B): it selects a
retained actual source with enlarged error ≤a and singleton pressure
≤a/(1−a). This is the same scalar statement, not four separate signs.

If a desired repair accuracy γ_j↓0 supplies a finite, table-uniform B_j,
choose m_j AFTER B_j so that ρ_(m_j), ε_(m_j,B_j), and Rbar_(B_j) are all
below 1/j. Existence follows from the preceding fixed-B limit. Thus growing
repair horizons are compatible with one coupled source sequence; no
uniform rate for B_j is being inferred or assumed.

For the fixed limiting reward table r*, retain the original weights
λ(r_(m_j),p_j), not newly computed softmax weights. If
δ_j=||r_(m_j)−r*||∞, every gain and E changes by at most 2δ_j, so the
weighted inactivity error increases by at most 4δ_j. Every simultaneous
chord derivative changes by at most 16δ_j: each of four coordinate gain
differences contributes at most 4δ_j. Thus (1) keeps the same λ with error
R_(N,B)+16δ_j at r*. Singleton pressure is reward-independent and unchanged.
These vanishing corrections are the fixed-table handoff clarification
independently checked in the review of the parent theorem.

## 3. What a pair repair may use, including the zero row

The labelled zero tester has g_0=0, so at any selected source of full
regret e>0 its mass satisfies

    λ_0 e≤ε,       and exactly λ_0=exp(−F(r_m,p)/τ).

The real owner masses θ_i=Σ_t λ_(i,t) sum to 1−λ_0. Thus one owner has
θ_i≥(1−λ_0)/4. A pair containing that owner has total mass at least 1/8
eventually along a positive-limit source. This uses no silent-prefix or
all-four-positive-owner-mass theorem. Alternatively, one may explicitly
remove the zero row and divide all local errors by 1−λ_0.

Therefore an independently proved joint two-player repair that retains the
other two ORIGINAL laws, fits X_(N+B), and makes the changed players' FULL
debts small is an admissible endpoint for (1), with the SAME λ used in the
outer normal. It need not be auxiliary Nash, and no private Never bonuses
are involved. The repair theorem must provide a B uniform over the bounded
raw tables BEFORE this source construction; choosing B only after seeing a
particular selected law would not justify the above diagonal order.

The present source still does not orient the mixed two-law reward account.
An owner whose mixed prescribed payoff changes by h_i has mixed tester
gain −h_i for every test. Any actual reward perturbation d at the original
source instead satisfies Σ_t p_i(t)g_(i,t)(d,p)=0. For h_i≠0 those whole
tester families cannot be identified. This excludes a specific testerwise
substitution, not every possible aggregate or counterfactual use of reward
normality. No contradiction to a positive global minimum has been obtained.

Next check: apply (1) to the independently established finite pair repair,
retaining its exact mixed term and every untouched player's full tester.
The current question is whether that actual account, not merely its raw
reward linearity, supplies a sign conflicting with the retained singleton
pressure or the complete outer normal.
