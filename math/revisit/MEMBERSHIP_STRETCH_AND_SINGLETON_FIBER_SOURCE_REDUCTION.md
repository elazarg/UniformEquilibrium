# Membership stretching and a singleton-fiber source reduction

This reduction removes equality with a nonsingleton sure-coalition regret
from the worst-table singleton-pressure problem.
It does not prove uniform equilibrium. The selected source has a
four-coordinate reward normal, not a sixty-coordinate cube normal.

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

### Semantic meaning and normalization

For this finite quitting model, η(r)>0 is equivalent to nonexistence of a
uniform-equilibrium payoff. Indeed η>0 implies that, for every actual
profile, some actual unilateral response gains more than η/2: the supremum
exceeds η/2, whether or not it is attained. Thus there is a fixed positive
all-behavior gap. Conversely a fixed positive behavioral gap is a lower
bound for E at every profile and hence for η. The existing semantic
equivalence between such a gap and nonexistence of a uniform-equilibrium
payoff is cited in Section 9. No cap-attaining deviation at gain η is
claimed.

An arbitrary real four-player reward table is finite and bounded. Scaling
ALL its rewards by one positive common constant normalizes it into
[−1,1]^60 and scales E and η by that constant; Never remains zero.
Therefore the reduction concerns existence of a four-player counterexample,
not only a previously normalized input. There is no terminal affine shift
or normalization to nonnegative own singletons.

The construction is existential and may change the counterexample TABLE:
it first chooses a worst table in the full normalized cube, stretches that
table, then maximizes over its own-singleton fiber. It does not preserve
the incoming table or regenerate a supplied profile at that table.

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

For an actual profile p, write μ_p for its terminal outcome law, including
Never. For a pure response label a=(i,t), with t finite or Never, let
ν_(p,i,t) be the outcome law after replacing only player i's clock by t.
The signed reward-coefficient vector v_(p,a) has zero coordinates for
every owner other than i, and

    v_(p,(i,t))(i,S)=ν_(p,i,t)(S)−μ_p(S),
    g_(i,t)(r,p)=v_(p,(i,t))·r
                =U_i(p[i←t])−U_i(p).

Never contributes no reward coordinate because its payoff is zero. The
additional zero tester is a separate label with v_(p,0)=0 and g_0=0.
For a competitor profile ν, the notation D_p g_a(r,p)[ν−p] means the
derivative at β=0 along the simultaneous marginal chord

    p_j(β)=(1−β)p_j+βν_j       for EVERY player j.

These marginals are sampled independently; this is not a public mixture
between two joint profiles. The finite-player gain along the chord is a
polynomial, so the derivative is unambiguous.

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

The quantifier order is important. The fixed data b, γ, Ω_b and r_∞ are
chosen BEFORE the accuracy or calendar-depth request. Equivalently, for
every ε>0 and every requested depth d, one can choose N≥d and one actual
silent finite profile p with its own weights such that |E(p)−Ω_b|≤ε,
the errors in (9) and (10) are at most ε, the scalar in (11) is at most ε,
and every owner has weight at least Ω_b/4. Later duplicate labels may be
aggregated into N+3, yielding the complete finite tester pool through
N+3, Never, and zero. The same fixed b, γ and r_∞ work for all requests.
Neither the tuple mixture nor a limiting clock law is played as a profile.

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

For example the Fin4 approximation bound is ρ_m=24/k when
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
semantic minimum (U,B) at r_∞ satisfies B_i−s_(∞,i)≥Ω_b. This is
`minimumTerminalSemantic_exploitabilitySingletonMargin` in
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

## 7. Source comparison and conjecture-facing tradeoff

The proof uses complete quantile approximation, reward continuity, and the
MAX singleton margin through the tracked declarations in Section 9.
Sections 5–6 prove the common-calendar coupling, projected normal sign,
silent row transport, and same-weight selection.

The stretch need not increase η; continuity preserves its positivity,
and re-maximization in the restricted family supplies the actual source.
Only the own-singleton block of the averaged gradient is normal to its
four-dimensional cube. No full reward-gradient norm identity is needed
in (12)–(15), and no positive directional derivative of η at the initial
worst table is asserted.

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
reduction. The surviving task is a contradiction or actual full-regret
improvement from the strict-gap source; that task is not supplied as a
conclusion.

## 8. Exact boundary tests

These are tests of the formulas, not examples of the unknown premise Ω>0.

1. For an owner edge with values a=−1/2, b=1/2 and α=1/4, the new
   values are −5/8, 5/8. The positive gap changes from 1 to 5/4,
   exactly (1−α)·1+2α. The reverse directed gap remains negative.
2. Equal edge values remain equal. In particular the zero reward table
   has Γ=0 before and after stretching. Formula (7) requires Γ>0;
   stretching does not manufacture a positive counterexample from zero
   regret or remove a zero-regret nonsingleton profile p^S.
3. The saturated pair (−1,1) is unchanged. Its gap is 2, which agrees
   with (6). No direction outside the reward cube is needed.
4. All six pairs, four triples, and the grand coalition satisfy (3).
   A singleton is deliberately excluded. If only player i quits at zero,
   with all others Never, its own debt is max(s_i,0)−s_i; this depends on
   its own-singleton coordinate. Deleting its only quitter also exposes
   any declared continuation. The fixed-coordinate argument cannot
   silently include that case.
5. The full-regret formula does not drop Never: for |S|≥2, Never and
   every post-zero response have the same already-absorbed endpoint.
   In the finite-source transfer they remain separate from a finite
   response when joint Never is possible.
6. Signed own singleton parameters remain free in [−1,1]. Their upper
   faces are excluded at the positive maximizing limit by B_i≤1 and
   B_i−s_i≥Ω_b, not by assuming they are nonnegative. Freezing these
   four coordinates instead of the other 56 would lose this normal
   sign argument.

The proof handles arbitrary real entries, ties, and cube-boundary values.
It never assumes that the endpoint-stretch map is continuous across
tables with a tied edge: the base table is fixed before its segment (4)
is traversed.

## 9. Exact source correspondence

The following tracked declarations supply the semantic and approximation
dependencies. The reduction and common-calendar construction are proved
in Sections 2–6.

- `quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card`
  in `UniformEquilibrium/Quitting/Paths/SureExitSet.lean` supplies the
  existing full payoff/cap formula underlying (3), independent of the
  declared counterfactual tail.
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`
  identifies the unrestricted behavioral cap with pure finite dates and
  Never. All actual response comparisons in this packet use that scope.
- `abs_quittingTerminalExploitabilityInf_sub_le_of_reward_close` and
  `quittingTerminalExploitabilityInf_scaleQuittingReward` in
  `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean` give the
  2-Lipschitz bound and exact common scaling of the true all-profile
  infimum, without requiring a cap-attaining deviation.
- `escapeAwareQuantileClock_fin4_normalized_quantitative_bracket`,
  `quantileClockSupport_fin4`, and
  `exists_finiteClockSemanticPair_exploitability_eq_upper` in
  `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean` give the
  reward-uniform 24/k objective approximation on literal finite clocks
  with support calendar 8k+1. The normalized bracket instantiates
  compression through `hasEscapeAwareQuantileClockCompression_of_normalized`
  in `Research/Quitting/EscapeAwareQuantileClockTransport.lean`;
  no unproduced compression hypothesis is assumed. Their explicit error
  controls complete caps, not merely prescribed payoffs.
- `minimumTerminalSemantic_exploitabilitySingletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`
  gives the cap-minus-singleton margin at a positive global minimum of
  MAXIMUM debt. The statement is not replaced by a total-debt theorem.
- `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean` and
  `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  identify the all-behavior semantic endpoint used in Section 1.
  The positive-gap claim uses any smaller fixed gain, not attainment of
  the response supremum at η.

The common-calendar coupling and silent same-weight selection are proved
in Sections 5–6. The strict sure-coalition floor is a normalization of a
hypothetical counterexample, not a class of games with an equilibrium.

## 10. Lean handoff

A direct implementation can separate the following mathematical outputs.

1. Reuse the existing pure-set semantic-pair theorem to express the
   original full regret by (3), and prove independence from the four own
   singletons for every |S|≥2.
2. Define the owner-edge endpoint table by the three sign cases. Prove
   its reward bound, own-singleton invariance, and the exact positive-gap
   identity (6). Do not add a false continuity hypothesis at equal
   endpoints.
3. Combine reward Lipschitz continuity, compact worst-table attainment,
   and four-coordinate maximization to construct b, γ and Ω_b satisfying
   (2). Keep the original full-cube maximum Ω distinct from Ω_b.
4. Formalize or reuse the compact smooth-envelope/separation argument
   for the FOUR parameter coordinates. Couple its source tuples to the
   same full tester softmax gradients and common-calendar telescope.
   A structure field asserting the desired scalar sign would not prove
   this step.
5. Implement the actual silent shift, partition-sum transport and
   discarded-calendar selection of Section 6. Preserve the new tester
   N+3 on all X_(N+3) competitors, the separate Never row, and the same
   λ in every output. Reuse actual laws at the fixed limiting table
   with the stated reward-error bounds.
6. State the final existential source reduction with b, γ and r_∞
   outside all accuracy/depth quantifiers. The normal is projected to
   own-singleton coordinates; no sixty-coordinate norm identity or
   normality in the frozen reward directions belongs in its conclusion.

The handoff supplies no admissible chronological return, debt-regeneration
mechanism, upper cap-leakage estimate, or low-regret strategy producer.
Any such consumer must be proved separately from the retained strict-gap
source. No counterexample to uniform equilibrium is constructed.
