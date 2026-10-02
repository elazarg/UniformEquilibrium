# Membership stretching and a singleton-only worst-table source

Author: CODEX_NOETHER_SUPPORT.

Status: complete ordinary-mathematics candidate, not independently reviewed
or Lean-checked. It removes equality with a nonsingleton sure-coalition
regret from the worst-table singleton-pressure program. It does not remove
the remaining positive-gap source or prove uniform equilibrium. The source
has a four-coordinate normal, not the original sixty-coordinate cube
normal. No export has been made.

FRECHET's pure-pair equality calculation motivated the test. ROOT suggested
freezing the other reward coordinates instead of retaining a small box.
The simultaneous eleven-coalition stretching calculation below needs no
all-player-ties theorem.

## 1. Exact counterexample reduction

There are four players I={0,1,2,3}. A table r gives each player a reward
in [−1,1] at each of the fifteen nonempty quitting coalitions. Never pays
zero. Each profile is a product of private complete stopping laws on
the nonnegative integers and Never. Every unilateral behavioral deviation
is admitted. Let

    E_r(p)=max_i(sup_(all complete deviations of i) U_i(deviation,p_−i)
                 −U_i(p)),
    η(r)=inf_(all actual independent p) E_r(p),
    Ω=max_(r∈[−1,1]^60) η(r).

For S⊆I with |S|≥2, let p^S prescribe Quit0 to every member of S and Never
to every outsider. Write

    e_S(r)=E_r(p^S),       Γ(r)=min_(S:|S|≥2) e_S(r).       (1)

There are eleven coalitions in (1), including the grand coalition.

**Reduction.** If Ω>0, there exist fixed values b for the 56 coordinates
other than the four own singletons, and a number γ>0, with the following
properties. Let r(s) have those fixed coordinates b and own-singleton
vector s∈[−1,1]^4. Then

    Ω_b:=max_(s∈[−1,1]^4) η(r(s)) > 0,
    Γ(r(s)) = Γ_b ≥ Ω_b+γ       for EVERY s∈[−1,1]^4.       (2)

Thus existence of a positive-gap table is equivalent to existence of a
family of the form (2) with positive Ω_b. The reverse implication is
immediate. The forward implication is an existence reduction, not an
algorithm for evaluating Ω or selecting low-regret strategies.

## 2. Complete pure-profile caps and common stretching

At p^S, at least two players quit surely at date zero. If i∈S, quitting
at zero yields r_i(S); any continuation at zero yields r_i(S\{i}), since
another member still quits surely. If i∉S, quitting at zero yields
r_i(S∪{i}); any continuation yields r_i(S). There is no earlier date.
All later finite dates and Never have exactly that continuation outcome.
Arbitrary random or behavioral responses average these two payoffs. Hence

    e_S(r)=max_i [r_i(S△{i})−r_i(S)]_+.                    (3)

Every coalition in (3) is nonempty. None of the reward coordinates in (3)
is an OWN singleton: if deletion leaves {j}, then j≠i. Consequently Γ
is independent of all four own-singleton coordinates. The formula retains
the full response supremum; it is not a one-stage-only regret substitute.

For every owner i, pair its fourteen remaining coordinates as

    (B, B∪{i}),       ∅≠B⊆I\{i}.

For a pair with values a<b, move a toward −1 and b toward +1. For a>b,
move a toward +1 and b toward −1. Leave equal pairs fixed. Leave each own
singleton fixed. More precisely, let P(r) be this endpoint table, and put

    r_α=(1−α)r+αP(r),       0≤α≤1.                       (4)

All entries stay in [−1,1], and ||r_α−r||_∞≤2α. This is ONE common
reward perturbation for all coalitions, not an owner- or source-selected
change of table. It need not be a physical transformation of game outcomes.

A directed membership difference c becomes

    (1−α)c+2α       if c>0;
    (1−α)c−2α       if c<0;
    0              if c=0.                              (5)

It follows from (3), with no assumption about which owner is maximal, that

    e_S(r)>0 ⇒ e_S(r_α)=(1−α)e_S(r)+2α.                  (6)

In particular Γ(r)>0 implies

    Γ(r_α)=(1−α)Γ(r)+2α.                                (7)

The identical stretch handles all eleven nonsingleton coalitions. No
membership edge is assigned conflicting targets: its two orientations
are precisely the positive and negative cases in (5).

## 3. Proof of the reduction

For any fixed profile and any unilateral response, uniform reward distance
δ changes its payoff by at most δ. It therefore changes a gain by at most
2δ, and changes E and η by at most 2δ. Thus η is continuous on the compact
reward cube and Ω is attained. Also 0≤Ω≤1: at all Never the full regret
is max(0,max_i s_i)≤1.

Choose r* with η(r*)=Ω>0. Every p^S is an actual profile, so Γ(r*)≥Ω.
Choose any 0<α<Ω/8. Equations (4), (7) give

    η(r*_α) ≥ Ω−4α > Ω/2,
    Γ(r*_α) ≥ (1−α)Ω+2α = Ω+γ,
    γ:=α(2−Ω)>0.                                        (8)

Freeze the 56 non-own-singleton coordinates at their values in r*_α and
allow all four own singletons to vary freely. This family contains r*_α
and lies inside the original reward cube. Therefore compactness and (8)
give

    Ω/2 < Ω_b ≤ Ω.

Equation (3) shows Γ is the same number Γ_b throughout this entire family.
Equation (8) now gives Γ_b≥Ω+γ≥Ω_b+γ, proving (2).

No neighborhood in the 56 fixed coordinates is needed. If a later use
requires one, a sufficiently small product neighborhood, intersected with
the original cube, preserves a strict version of (2), by the same
2-Lipschitz bound for Γ. Such an enlargement is not used here.

## 4. The actual source retained after singleton-only maximization

The following source fields survive. Their construction is given below
to specify exactly how the restricted parameter family enters.

There is a fixed table r_∞=r(s_∞) in the family with η(r_∞)=Ω_b>0.
There are finite, actual independent profiles p_m, silent at date zero,
integers N_m→∞, and probability weights λ_m on labelled pure responses
and a zero tester, such that:

1. E_(r_∞)(p_m)→Ω_b, while EVERY e_S(r_∞), |S|≥2, is at least
   Ω_b+γ. The same strict pure-profile bound holds at every approximating
   table, not merely at the limit.
2. p_m uses dates 1,...,N_m and Never. On the ENTIRE competitor domain
   X_(N_m+3), retain every complete finite response through N_m+3 and
   the distinct Never response. For every simultaneous independent-law
   endpoint ν in that domain,

       Σ_a λ_(m,a) D_p g_a(r_∞,p_m)[ν−p_m] ≥ −o(1).       (9)

   The error is uniform over ν. Later duplicate response labels may be
   aggregated only when they coincide on this entire enlarged domain.
3. The SAME weights satisfy

       Σ_a λ_(m,a)[E_(r_∞)(p_m)−g_a(r_∞,p_m)]→0.         (10)

4. With θ_(m,i)=Σ_t λ_(m,i,t), eventually θ_(m,i)≥Ω_b/4
   for every owner i.
5. The SAME source and weights have

       limsup_m Σ_(i,t) λ_(m,i,t)
           [Pr_(p_m[i←t])(terminal={i})−Pr_(p_m)(terminal={i})]
          ≤0.                                            (11)

The weights at the fixed table are transported weights computed at nearby
tables. They are not asserted to be freshly recomputed softmax weights
at r_∞. A tuple mixture used in their construction is not a game strategy.
No individual retained source has a reward normal, and (11) is one TOTAL
scalar sign, not four separate signs.

## 5. Restricted outer optimization and unchanged common-calendar estimates

Write A_N={0,...,N−1,Never} and X_N=∏_i Δ(A_N). For a large integer m
put τ=m^(−1/2), L=2m+1, and use the SAME labelled pool

    J={0}∪(I×{0,...,L,Never}),
    F(r,p)=τ log Σ_(a∈J) exp(g_a(r,p)/τ),
    λ_a(r,p)=exp(g_a/τ)/Σ_b exp(g_b/τ),
    ε=τ log|J|,        H=96+256/τ.

The zero row has gain and reward vector zero. On X_L the pool is complete:
every finite response beyond L has the value of L; Never is separate.
Thus E≤F≤E+ε everywhere on X_L. Let f_N(r)=min_(p∈X_N)F(r,p).
Choose s_m maximizing the average of f_N(r(s)) over m≤N≤2m.
Only s, not the 56 fixed coordinates, is optimized.

The reward-uniform complete quantile approximation gives ρ_m→0 with

    η(r)≤min_(p∈X_N)E_r(p)≤η(r)+ρ_m       for every N≥m.

For example the previously checked Fin4 bound is ρ_m=24/k when
k=floor((m−1)/8)≥1; only convergence is needed. Consequently the selected
tables r_m=r(s_m) satisfy η(r_m)→Ω_b. EVERY minimizer of EVERY f_N in
the window is uniformly near η(r_m) in full regret. Passing to a
subsequence gives r_m→r_∞ and η(r_∞)=Ω_b. These statements concern actual
source laws, not only a prescribed-payoff image or a finite-menu Nash set.

Compact minimization and the smooth envelope formula provide finitely many
tuples (p_(b,N))_N of actual inner minimizers and weights ω_b≥0, Σω_b=1,
such that the OWN-SINGLETON BLOCK of

    G_m=Σ_b ω_b (1/(m+1)) Σ_N Σ_a λ_a(r_m,p_(b,N))v_(p_(b,N),a)

belongs to the outward normal cone of [−1,1]^4 at s_m. To see the exact
parameter change, the one-sided derivative of min_p F(r(s),p) in direction
d∈ℝ^4 is the minimum, over its old minimizers, of the own-singleton
gradient dotted with d. This follows from uniform differentiability and
compactness. Averaging gives the minimum over tuples. If the convex hull
of these four-coordinate gradients missed the normal cone, finite
separation would give a feasible d for which every tuple derivative is
positive, contradicting the selected outer maximum. No normality of the
other 56 coordinates follows. The entropy identity still gives

    h_m−ε ≤ r_m·G_m ≤ h_m,

where h_m is the selected average of f_N. The identity r_m·G_m=||G_m||₁
from the full-cube construction is NOT asserted or used.

Put Δ_N=f_N(r_m)−f_(N+1)(r_m). The SAME table and SAME common pool yield
Δ_N≥0 and Σ_(N=m)^(2m) Δ_N≤2+ε. Along an actual simultaneous law chord,
|g'_a|≤16 and |g''_a|≤96; differentiation of log-sum-exp therefore gives
F''≤H. At an inner minimizer, a derivative −c<0 toward X_(N+1), followed
for step c/H, would lower F by at least c²/(2H). Its new value is at
least f_(N+1). Hence the ORIGINAL λ at EVERY inner minimizer satisfies

    Σλ D_pg_a[ν−p]≥−√(2HΔ_N)       for all ν∈X_(N+1).

Its inactivity is at most ε by the entropy identity. The averaged error
is at most √(2H(2+ε)/(m+1))→0. These estimates and their quantifiers are
unchanged by restricting the reward parameters.

## 6. Singleton sign, silence, and all-owner transfer

The positive MAX-minimum singleton-cap margin states that every complete
semantic minimum (U,B) at r_∞ satisfies B_i−s_(∞,i)≥Ω_b. This is the
checked `minimumTerminalSemantic_exploitabilitySingletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`.
Since B_i≤1, it implies s_(∞,i)≤1−Ω_b. Eventually all four s_(m,i)<1.
The four-coordinate normal from Section 5 therefore has every own-singleton
component nonpositive. Its total is precisely the weighted mean of the
actual scalar in (11), so that mean is at most zero.

Uniformly over ALL inner minimizers in the window, eventually
B_i(r_m,p)−s_(m,i)≥σ:=Ω_b/2. Otherwise reuse violating actual laws at
r_∞; reward continuity and compactness of the closed semantic carrier
give a global minimum violating the displayed singleton-cap margin.
This argument does not realize a limiting semantic pair as one profile.

Shift every finite clock of every tuple source by one, leaving Never fixed.
Prescribed outcomes and payoffs are unchanged; its full cap becomes
max(s_i,B_i)=B_i. Thus full E is unchanged. Call the shifted source p̂.
Keep the old common pool J and recompute λ̂ at (r_m,p̂).

For old labels t<L, the whole response reward row at t becomes the row
at t+1; the Never and zero rows are unchanged. The new date-zero gain is
s_i−U_i. Put d_N=L−N+1, and let Z,Ẑ be the two softmax partition sums.
The exact relation is

    Ẑ/Z=1−ℓ_N+a_N,
    ℓ_N≤1/d_N,      a_N≤a_m:=4exp(−σ/τ),
    F(r_m,p̂)≤f_N(r_m)+τa_m.                              (12)

Here ℓ_N is the mass of the removed last finite label, summed over owners;
the d_N old late labels per owner were identical. The added initial terms
are exponentially small because s_i−U_i≤E−σ. For any transported scalar
row observable of absolute value at most one, the old and new averages
differ by at most 4(1/d_N+a_m), for d_N≥2. This follows by subtracting
the two numerators and dividing by 1−ℓ_N+a_N. It applies to the actual
singleton indicator differences, not only numerical gains.

Omit the final two calendars, so N≤2m−2 and N+3≤L. The preceding Hessian
argument and (12) give for the SAME λ̂, uniformly on X_(N+3), the
directional error

    R̂_N=√(2H[Δ_N+Δ_(N+1)+Δ_(N+2)+τa_m]),               (13)

and inactivity at most ε. The total new initial tester mass is at most
2a_m. Use the legal direction making owner k Quit0, with every other
prescribed clock still silent. At that endpoint all nonowner noninitial
gains are zero; initial joining gains have absolute value at most two.
Every owner-k gain increments by U_k−s_k. Combining the directional
inequality and near-activity therefore yields

    θ̂_k(B_k−s_k) ≥ E−ε−R̂_N−4a_m       for EVERY k.       (14)

For clarity this is the direct same-weight solo-screening calculation,
not an imported multiplier. If W=Σλ̂g and W_k=Σ_tλ̂_kt g_kt, its exact
derivative is θ̂_k(U_k−s_k)−W+W_k plus the initial joining terms; use
W≥E−ε and W_k≤θ̂_k(B_k−U_k) to obtain (14).

The removed calendar mass is q_m=2/(m+1). The remaining pressure average
is at most q_m+T_m, where

    T_m=4/(m+1) Σ_(N=m)^(2m−2)(1/d_N+a_m)→0.

The remaining average of R̂_N is at most

    B_m=√(2H[3(2+ε)/(m+1)+τa_m])→0.

This uses the same-table telescope, in which each Δ occurs at most three
times, followed by Cauchy–Schwarz. Discard entries with R̂_N>√B_m; their
mass is at most √B_m. Since absolute singleton pressure is at most one,
one remaining actual pair (p̂,λ̂) has R̂_N≤√B_m and pressure at most

    (q_m+T_m+√B_m)/(1−q_m−√B_m)→0.                       (15)

Equation (14), B_k−s_k≤2, and E→Ω_b give θ̂_k≥Ω_b/4 eventually.
Finally reuse these selected laws at the FIXED r_∞, retaining the weights
λ̂(r_m,p̂). If δ_m=||r_m−r_∞||_∞, full regret changes by at most 2δ_m,
inactivity by at most 4δ_m, and the weighted simultaneous derivative by
at most 16δ_m. Singleton pressure and owner weights are unchanged. This
proves all fields in Section 4. All sources remain in the fixed family,
so Γ_b≥Ω_b+γ is unaffected by selection, shifting, or taking the limit.

## 7. Audit boundary and the exact consumed arm

The source construction uses the same complete quantile approximation,
reward continuity, and MAX singleton-margin sources checked in
[the original coupled certificate](CODEX_NOETHER_SUPPORT__WORST_REWARD_TABLE_COUPLED_CALENDAR_CERTIFICATE.md)
and its
[independent audit](../feedback/CODEX_NOETHER_SUPPORT__WORST_REWARD_TABLE_COUPLED_CALENDAR_CERTIFICATE__BY_CODEX_FRECHET_CYCLE.md).
The silent row transport is reproduced from
[FRECHET's source bridge](CODEX_FRECHET_CYCLE__SILENT_SOURCE_COUPLING_TO_WORST_REWARD_PRESSURE.md),
independently checked in
[TARSKI's review](../feedback/CODEX_FRECHET_CYCLE__SILENT_SOURCE_COUPLING_TO_WORST_REWARD_PRESSURE__BY_CODEX_TARSKI_PREMIUM.md).
Only its own-singleton mean sign, not the old full-normal norm identity,
is used in (12)–(15).

The bounded novelty search compared HILBERT's extremal-table variation
note, the global portfolio audits, the collision-subsidy test, and the
previous owner-edge averaging failure. The new step is (6)–(8), followed
by freezing all reward coordinates except those needed for the scalar
pressure. The stretch need not increase η; continuity only preserves its
positivity, and re-maximization in the restricted family supplies the
correct actual source afterwards. It is not a positive directional
derivative claim about η at the original worst table.

The pure-pair equality arm Γ=Ω no longer has to be analyzed by this
singleton-pressure program: if any counterexample exists, the program can
start with the stronger source (2), (9)–(11), with a strict gap for ALL
eleven nonsingleton sure coalitions. This does not say an original pure
global minimizer was assigned positive tuple weight or was itself normal.

Remaining open: consume the strict-gap source by an actual full-regret
improvement or a contradiction. The result supplies no upper cap-leakage
bound, no sign for an arbitrary mixed two-law reward account, no individual
normal source, and no normality in the 56 frozen reward directions. A use
requiring the original sixty-coordinate cube normal is outside this
reduction. The immediate requested check is independent falsification of
the full-cap formula (3), simultaneous stretch (6), and preservation of
the SAME-source fields under the four-coordinate outer optimization.
