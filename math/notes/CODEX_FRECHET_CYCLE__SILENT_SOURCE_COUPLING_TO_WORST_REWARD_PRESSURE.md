# One silent worst-table source with common all-owner weights and singleton pressure

Identity: CODEX_FRECHET_CYCLE.

## Status and exact added field

Ordinary mathematical proof, not independently reviewed or Lean-checked.
This is a separate addendum to CODEX_NOETHER_SUPPORT's
[coupled worst-table certificate](CODEX_NOETHER_SUPPORT__WORST_REWARD_TABLE_COUPLED_CALENDAR_CERTIFICATE.md),
reviewed independently at SHA
`fade3cb825778caf0c76a1a4d6b9820e43bd6f430abf6f8af64b5c95973dd854` in
[this review](../feedback/CODEX_NOETHER_SUPPORT__WORST_REWARD_TABLE_COUPLED_CALENDAR_CERTIFICATE__BY_CODEX_FRECHET_CYCLE.md).
That source is not modified here. The solo-screening calculation is credited
to the separate
[all-owner addendum](CODEX_FRECHET_CYCLE__SILENT_PREFIX_ALL_OWNER_MULTIPLIERS.md).

Conditional on a positive worst unrestricted regret Ω, the result produces
ONE sequence of actual silent finite-calendar profiles and ONE tester law
at each source which simultaneously has:

- full regret tending to Ω at a fixed worst table;
- vanishing inactivity and simultaneous enlarged-calendar directional error;
- a uniform positive weight for every owner; and
- nonpositive limiting TOTAL weighted own-singleton pressure.

The new weights are recomputed softmax weights at the shifted source. They
are not identified with NOETHER's old weights. The proof transports the
actual reward-row coefficients with a vanishing error using the duplicated
late tester labels. No improving profile, individually normal retained source,
four separate singleton-pressure signs, or equilibrium producer is claimed.

## 1. Retained input and uniform silent margin

Use the input theorem's notation: four players, signed rewards in [−1,1]^60,
zero Never payoff, independent private complete stopping laws, and unrestricted
unilateral deviations. At m let τ=m^(−1/2), L=2m+1,
J={0}∪(I×{0,...,L,Never}), ε=τ log|J|, and H=96+256/τ.
The single selected table r_m maximizes the average of f_N over m≤N≤2m,
where f_N is the minimum of the SAME smooth F on X_N.

The input supplies tuple weights θ_b and literal sources p_(b,N) attaining
f_N(r_m), with old softmax λ^(b,N). Set w_(b,N)=θ_b/(m+1). Their total
weight is one. At the SAME table,

    Δ_N=f_N(r_m)−f_(N+1)(r_m)≥0,
    Σ_(N=m,...,2m) Δ_N≤2+ε.                            (1)

The old weighted reward gradient G_m is an outward cube normal. When Ω>0,
pass to the input's subsequence r_m→r*, with η(r*)=Ω and a limiting normal
of norm Ω. For all sufficiently large m, the old weighted singleton pressure
has mean at most zero. All old sources, uniformly over b and N, have full
regret tending to Ω, also when reused literally at r*.

There is a UNIFORM σ>0 such that, for every sufficiently large m and EVERY
smooth minimizer at every calendar in the window,

    κ_i:=B_i(r_m,p)−r_(m,i)({i})≥σ       for every i.   (2)

For example σ=Ω/2 works eventually. If not, choose violating minimizers and
an owner along a subsequence. Reuse those exact laws at r*. Reward Lipschitz
continuity makes their complete semantic pairs near-minimizing at r*. By
compactness a further subsequence tends to a carrier minimum with maximum
debt Ω. Its singleton cap margin is at least Ω by the checked
`minimumTerminalSemantic_exploitabilitySingletonMargin`. Cap and singleton
values change by at most the uniform reward distance when laws are reused.
The limiting violating margin would be at most Ω/2, a contradiction.
This argument covers ALL smooth minimizers, not only the later selected tuple.
It realizes no limiting carrier point by a behavioral profile.

Shift every finite clock of p forward by one, leaving Never unchanged; call
this actual profile p̂. The terminal outcome law and prescribed payoff U are
unchanged. Its full cap is max{s_i,B_i}=B_i by (2), so E(p̂)=E(p) exactly.
The original source uses 0,...,N−1 and Never; p̂ uses 1,...,N and Never.

## 2. Exact partition and reward-row transport

Keep the SAME common pool J. Let Z and Ẑ be its unnormalized softmax
partition sums at p and p̂, both at r_m. For each player,

    g_(i,t+1)(r_m,p̂)=g_(i,t)(r_m,p)     (0≤t<L),
    g_(i,Never)(r_m,p̂)=g_(i,Never)(r_m,p),
    g_(i,0)(r_m,p̂)=s_i−U_i.                            (3)

The corresponding COMPLETE terminal outcome laws, and therefore the whole
sixty-coordinate reward rows v, obey these same shifted identities. They
are not merely equal numerical gains at one table. The zero row stays zero.

For p∈X_N, all finite labels N,...,L have the same row and value. There
are d_N=L−N+1 such labels per owner. Define

    ℓ_N=Σ_i exp(g_(i,L)(r_m,p)/τ)/Z,
    a_N=Σ_i exp((s_i−U_i)/τ)/Z,
    a_m=4 exp(−σ/τ).

Then the exact identity and uniform bounds are

    Ẑ/Z=1−ℓ_N+a_N,
    ℓ_N≤1/d_N,       0≤a_N≤a_m.                        (4)

Indeed d_N ℓ_N is the old total mass of the repeated late labels and is at
most one. Also s_i−U_i=d_i−κ_i≤E(p)−σ and Z≥exp(E(p)/τ), proving the
initial-label bound. Therefore

    F(r_m,p̂)≤f_N(r_m)+τ a_m.                           (5)

This is exponentially small compared with τ. A generic O(ε) smoothing loss
here would NOT suffice after multiplication by the Hessian bound H≈1/τ.

Let λ̂=λ(r_m,p̂), genuinely recomputed. For any bounded scalar observable
z_a∈[−1,1] of a reward row which is transported by (3), the old and new
expectations differ by at most

    4(1/d_N+a_m),                                      (6)

provided d_N≥2. To see this, the new expectation is
(old expectation − lost numerator + added numerator)/(1−ℓ_N+a_N).
The two removed/added numerators have absolute values at most ℓ_N,a_N.
Subtracting the old expectation gives a bound
2(ℓ_N+a_N)/(1−ℓ_N)≤4(ℓ_N+a_N). The argument also follows by comparing
the old shifted label measure, including the removed label L+1, with the new
measure on their union. It does not claim the two softmax laws are equal.

In particular (6) applies to ACTUAL singleton pressure:

    S(p,λ)=Σ_(i,t) λ_(i,t)
                  [ν_(p,i,t)({i})−μ_p({i})].             (7)

The prescribed law μ_p is shift invariant; every retained response law shifts
literally. The new date-zero response has its actual singleton law because
all other players Continue at date zero. Thus (6) controls Ŝ−S, not just
a surrogate gain function. For vector reward rows of ℓ¹ norm at most two,
the corresponding ℓ¹ expectation bound is 8(1/d_N+a_m).

## 3. The NEW same weights control head changes and all owners

Use only N=m,...,2m−2, dropping the final TWO calendars. Then N+3≤L.
This keeps an actual reserved date for joint head changes as well as every
complete after-menu response. Compare the source p̂∈X_(N+1) with ALL
simultaneous independent-law endpoints ν∈X_(N+3). The common pool still
contains every complete tester of the enlarged domain.

The input's Hessian bound H is valid on every such chord. Equations (1), (5)
and global minimality of f_(N+3) give, with

    R̂_N=√(2H(Δ_N+Δ_(N+1)+Δ_(N+2)+τ a_m)),

the SAME new-weight inequalities

    Σ_a λ̂_a D_p g_a(r_m,p̂)[ν−p̂]≥−R̂_N
                      for EVERY ν∈X_(N+3),              (8)
    Σ_a λ̂_a(E(p̂)−g_a(r_m,p̂))≤ε.                      (9)

The proof of (8) uses derivative magnitude at most sixteen and the actual
chord step c/H, exactly as in the input theorem. It does not need p̂ to
minimize F on its new calendar. It needs (5) and the global f_(N+3) floor.
Tester N+3 remains distinct from N+2 on X_(N+3); later common-pool labels
may be aggregated only because they coincide on this entire domain.

Put θ̂_i=Σ_t λ̂_(i,t). The total NEW initial tester mass is at most
a_N/(1−ℓ_N+a_N)≤2a_m. Fix k and use the admissible endpoint that makes
k Quit at date zero. Every other prescribed clock continues there. For each
nonowner, every noninitial tester's changed gain is zero. The initial joining
tester's changed gain is r_i({i,k})−r_i({k}), of absolute value at most two.
Owner k's gain increment is U_k−s_k for every tester.

Writing Ĝ=Σλ̂g and Ĝ_k=Σ_tλ̂_(k,t)g_(k,t), the exact weighted derivative
is θ̂_k(U_k−s_k)−Ĝ+Ĝ_k plus the initial joining terms. Since Ĝ_k≤θ̂_k d_k,
(8)–(9) and the initial mass bound yield

    θ̂_k κ_k≥E(p̂)−ε−R̂_N−4a_m       for EVERY k.        (10)

This is the SAME λ̂ as in (7)–(9), not a separate all-owner witness. Since
κ_k≤2, any selected sequence with R̂_N→0 eventually has, for example,
θ̂_k≥Ω/4>0 for all four owners. Also (9) implies
θ̂_k(E(p̂)−d_k)≤ε. Initial, joining, Never and every full after-menu row are
retained throughout this calculation.

## 4. One source retains all fields simultaneously

The dropped old tuple mass is q_m=2/(m+1). On the remaining entries put

    T_m=4/(m+1) Σ_(N=m,...,2m−2)(1/d_N+a_m),
    B_m=√(2H(3(2+ε)/(m+1)+τ a_m)).

Here T_m→0, since the reciprocal sum is at most a harmonic sum, and B_m→0,
since H=O(√m), ε→0 and a_m decays exponentially in √m.

Removing the final two calendars from the old pressure average loses at most
q_m in its upper bound because |S|≤1. Applying (6) to each retained entry
therefore proves

    Σ_remaining w_(b,N) Ŝ_(b,N)≤q_m+T_m.              (11)

Each Δ appears at most three times in the remaining three-step gaps.
Cauchy–Schwarz with the original tuple weights gives

    Σ_remaining w_(b,N) R̂_N≤B_m.                      (12)

Set γ_m=√B_m. The mass of entries with R̂_N>γ_m is at most γ_m. For large
m, the good entries have total mass at least 1−q_m−γ_m>0. Discarding the
bad entries from (11) increases its upper bound by at most γ_m. Consequently
ONE retained pair (b,N), chosen with its actual p̂ and its actual λ̂, satisfies

    R̂_N≤γ_m,
    Ŝ_(b,N)≤(q_m+T_m+γ_m)/(1−q_m−γ_m).                (13)

Equations (8)–(10) and (13) prove the advertised simultaneous source fields.
This selection preserves one scalar singleton account; it does not make the
four pressure coordinates individually nonpositive.

The outer normal ancestry is retained as well, if required. The unnormalized
average of the NEW reward gradients over the remaining shifted sources differs
from the old normal G_m in ℓ¹ norm by at most 2q_m+2T_m. The missing mass
costs at most 2q_m and the vector form of (6) costs at most 2T_m. Thus this
average has the same limiting normal of norm Ω. Neither it nor the old tuple
mixture is an executable correlated law, and no individual source gradient
is claimed normal.

Finally reuse the selected silent laws at the FIXED table r*. Retain their
weights λ̂(r_m,p̂_m). If δ_m=||r_m−r*||∞, full regret changes by at most
2δ_m, inactivity by at most 4δ_m, and simultaneous chord derivatives by
at most 16δ_m. Singleton pressure is reward-independent. Thus all errors
in (8)–(13) still vanish. The same-source all-owner weights and scalar sign
are now co-realized at one fixed worst table, without a new softmax selection.

## 5. Boundary checks and next sign question

The common-pool endpoint count is essential: two calendars were removed so
that N+3≤L, not inferred from equality of source cap values. Both the lost
late label and the added initial row occur in (4). The singleton-pressure
argument uses their actual law coefficients, not a payoff-only comparison.
The cap margin is uniform over ALL smooth minimizers by Section 1; it is
not postulated for a conveniently chosen source. All singletons may be signed.

On twelve signed rational tables, exact enumeration verified prescribed-law
and shifted response-row identities, including singleton coefficients and
Never. Seventy-digit arithmetic checked the partition identity, lost-mass
bound and pressure transport formula. These are algebra checks on arbitrary
sources, not numerical evidence that Ω>0 or that a sampled source minimizes F.

This proof uses the same exact quantile, reward-Lipschitz and MAX-minimum
singleton-margin declarations listed and checked in the input's independent
review. The all-owner screening is proved explicitly above. No additional
literature theorem, Lean implementation, or export is invoked.

The remaining question is now genuinely SAME-source: do these common
all-owner, enlarged-direction and singleton-pressure fields force a strict
positive pressure or orient the full joint-head gains in Section 7 of the
[clamp calculation](CODEX_FRECHET_CYCLE__CLAMP_CROSS_AMPLIFICATION_AND_SOURCE_INTERVAL_REACH.md)?
The bridge removes the unrelated-multiplier obstruction. It does not supply
the missing raw reward sign, or permit a weighted scalar to replace the full
response maximum.
