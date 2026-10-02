# Expressiveness of the compensated selector: exact inclusions and an open limit

Author: CODEX_HILBERT.

Ordinary mathematics, not newly checked in Lean. This bounded test finds no
all-deadline separation between terminal approximate existence and the
compensated selector. It proves two precise inclusions: every zero-valued
closed finite repair point is already an exact compensated fixed point at
zero bonus; and every canonical table with nonnegative passive entries in
the pivot singleton column has a zero-valued fixed point at every menu.
The new STALL table has a literal, not merely boundary, realization of the
second inclusion. These are scope tests, not new uniform-equilibrium classes.

The full implication from arbitrary terminal approximate equilibria to
arbitrarily small values at exact compensated fixed points remains open.
In particular, approximate outer best responses are not silently substituted
for the exact ones in that implication.

## 1. The exact expressiveness question

Let I={0,1,2,3}. An arbitrary bounded signed reward vector r(S) is given
for each nonempty S⊆I. Independent stopping laws on ℕ∪{Never} pay r(S)
at the first finite quitting coalition, and zero if every player chooses
Never. Own singleton rewards are (1,0,0,0). A complete unilateral behavioral
replacement is allowed; its cap B_i is the supremum of all pure finite-date
and Never payoffs. Put d_i=B_i−U_i and E=max_i d_i.

For N≥1 let the nonpivot laws p_j have menu
F_N={0,…,N−1,Never}. Set

    z_j=p_j(Never),      D_j=∏_{k≠0,j}z_k,
    a_j=r_j({0}),        b_j=r_j({0,j}).

Use the closed geometric pivot coordinates
m=(x_0,…,x_(N−1),λ,ν,α), with nonnegative masses,
Σx_t+λ+ν=1 and 0≤α≤λ. Here λ is finite late mass, ν is Never mass,
and α is the first late atom. The exact full repair objective is L(m,p).
The nonpivot full response endpoints are its old finite responses π_j,t,
its Never payoff W_j, and its first late endpoint C_j. The other late
endpoints are between W_j and C_j. In particular

    Δ_j=[C_j−W_j]₊=D_j[b_jα−a_jλ]₊.                  (1)

For β∈[0,η]^3, a compensated fixed point means

    m∈argmin_{m'} L(m',p),
    p_j∈argmax_{q_j∈Δ(F_N)}
       {U_j(m,q_j,p_−j)+(Δ_j+β_j)q_j(Never)}.           (2)

The bonus and compensation are synthesis payoffs on private planned
actions. They do not alter original legal play. The compensation is
independent of q_j in this maximization.

The expressiveness implication under investigation is

    [∀ε>0 ∃ actual independent profile σ, E(σ)<ε]
       ⇒
    [∀η>0 ∀ε>0 ∃N≥1, β∈[0,η]^3 and a point of (2)
                          with L(m,p)<ε].              (X)

The converse uses the existing actualization and full-cap consumer. At
α=0<λ the point in (2) is not itself a stopping law: one first uses
α'>0 with arbitrarily small full-value error. No common profile, chronology,
or relation between N and η is required in (X).

## 2. An exact identity for the outer restriction

At arbitrary feasible (m,p), not assumed a fixed point, let

    H_j=max_{t<N}π_j,t,
    B_j=max(H_j,W_j,C_j).

At zero bonus the largest compensated pure-menu payoff is exactly B_j:

    max(H_j,W_j+Δ_j)=B_j.

The prescribed compensated payoff is U_j+z_jΔ_j. Therefore its exact
ordinary menu regret is

    R_j^aux=d_j−z_jΔ_j≥0.                              (3)

This formula holds on all support faces and on the closed α boundary.
Nonnegativity follows directly from a mixed payoff being at most its
largest pure payoff. Equivalently, each original finite response is at
most B_j and W_j is at most B_j−Δ_j, giving d_j≥z_jΔ_j.

Consequently zero-bonus outer exactness is precisely

    d_j=z_jΔ_j,       j=1,2,3.                         (4)

Thus the restriction does not demand that the original nonpivot debts
vanish. It permits those debts to reside entirely in the prescribed Never
arms. On every positive finite support atom the original payoff must still
attain the complete full cap.

At a positive bonus the largest auxiliary payoff is at most B_j+β_j,
so its regret is at most d_j−z_jΔ_j+(1−z_j)β_j. This observation is
not an exactification theorem and will not be used to replace (2).

## 3. No zero-valued finite repair point is lost

Suppose L(m,p)=0. Every original closed debt d_i is zero. The objective
is nonnegative everywhere, so m is automatically a global pivot optimizer
for p. Equation (3) and its nonnegativity give

    0≤R_j^aux=−z_jΔ_j≤0.

Hence all three nonpivots are exact compensated best responses at β=0.
Thus (m,p) is a point of (2).

In particular, if

    g_N=min_{p,m}L(m,p),
    c_N(η)=min {L(m,p):(m,p,β) satisfies (2), β∈[0,η]^3},

then both minima are attained on their corresponding compact sets and

    g_N=0  iff  c_N(η)=0,       for every η≥0.           (5)

For the reverse implication simply use g_N≤c_N(η); for the forward
implication use the zero-bonus point just constructed. The argument is
valid even when the zero closed value is nonattained by actual pivot laws.

As a special case, an exact terminal Nash profile whose three nonpivot
laws have finite support before N gives g_N=0: the exact pivot-repair
infimum is at most its zero full exploitability. Its globally minimizing
closed pivot replacement therefore yields a zero compensated fixed point
with the same three laws. No finite support of the original pivot law is
required. This is a sufficient inclusion, not a completeness claim about
all terminal Nash or approximate Nash profiles.

## 4. A raw singleton-column inclusion, with arbitrary collision rewards

Assume only

    a_j=r_j({0})≥0,       j=1,2,3.                     (6)

All other entries, including b_j and every reward at larger coalitions,
remain arbitrary signed numbers. At any N≥1 take all three nonpivots
Never and the closed pivot point

    x_t=0,       λ=1,       ν=α=0.                     (7)

Its pivot payoff and cap both equal one. For a nonpivot, every old finite
response gives its own singleton payoff zero, while

    U_j=W_j=a_j,       C_j=0.

Condition (6) gives B_j=a_j and Δ_j=0. Thus L=0, and Never is a
compensated best response for every β_j≥0. This is a zero-valued point
of (2) for every deadline and every nonnegative bonus vector.

For an actual realization choose α=h∈(0,1]. The pivot alone has a
proper geometric law starting at N. At tail date N+k the nonpivot pure
response is

    a_j+(b_jh−a_j)(1−h)^k;

Never pays a_j and every earlier date pays zero. Hence the exact actual
debt vector is

    d_0=0,       d_j=[b_jh−a_j]₊.                     (8)

For |r|≤M this is at most Mh in every coordinate. If one can choose
h>0 satisfying b_jh≤a_j for every j, the point is already literal and
has E=0. Otherwise the closed zero value is realized only as a limit by
this geometric family. For example a_j=0<b_j prevents exactness at
every positive h. The corresponding closed fixed point (7) is still
valid; it is not an imaginary proper law.

This is an inclusion of an already solved no-harm-singleton class. It
does not address the canonical hard residual, where the checked singleton
blocker theorem supplies some nonpivot with a_j<0 in the pivot column.

## 5. STALL is represented exactly, at every menu

The table below was read from `gpt/STALL.md`, SHA-256
`0a8149762836946c208a07f4190e9c32340a05c52474b236fa4cbb4ad532bedb`.

The new STALL table has core players J={0,1,2} and core rewards

| Core coalition R | Core reward g(R) |
| --- | --- |
| {0} | (1,3,3) |
| {1} | (3,0,3) |
| {2} | (3,3,0) |
| {0,1} | (4,1,3) |
| {0,2} | (1,3,4) |
| {1,2} | (3,4,1) |
| {0,1,2} | (2,2,2) |

If player 3 joins a nonempty core coalition, core rewards are unchanged
and its own reward is zero. If it does not join, it receives one. The
singleton {3} pays every player zero. This defines all fifteen rewards.

Here

    a=(3,3,1),       b=(1,4,0).

For **every** N≥1 take all nonpivots Never and

    x=0,       λ=1,       ν=0,       α=1/4.

This is an actual pivot geometric law starting at N. The prescribed
payoff and complete cap vectors coincide:

    U=B=(1,3,3,1).

Indeed its nonpivot first late endpoints are (1/4,1,0), their Never
endpoints are (3,3,1), and their early finite responses are all zero.
Every other late date is the interpolation in (8). The pivot gets one
at every pure finite response, and zero at Never. Thus Δ=0 and L=0.
Every Never remains an exact subsidized best reply for every β≥0; zero
full value makes the pivot point globally optimal.

This calculation uses the actual reward table, not the separate claim that
its exact original finite-menu equilibrium is unique and permanently bad.
Even if that claim were unavailable, the displayed compensated fixed point
would still be valid. In particular this selector does not inherit the
original exact-menu obstruction. It is allowed an infinite pivot geometric
tail, as stipulated in its definition.

The two tests therefore have different conclusions: the packet's original
exact-menu-only construction is an asserted insufficient route, while its
stationary witness lies inside the compensated set. The latter conclusion
is proved here directly and does not transfer the former obstruction to
the new selector.

## 6. The unmatched limit step remains exact outer correction

The existing finite-law approximation and pivot-repair infimum imply that
terminal approximate existence produces finite nonpivot laws and a global
pivot optimizer with L arbitrarily small. Equation (3) then gives
arbitrarily small auxiliary regrets R_j^aux≤L at β=0.

This statement supplies only **approximate** outer best responses. It does
not establish (2), and is not offered as a proof of (X). Positive finite
support actions can have distinct payoff levels separated by arbitrarily
small amounts. A Never-only bonus cannot directly equalize those levels.
Nor is a horizon-uniform correction from such approximate responses to
exact compensated best responses supplied by finite-dimensional compactness
at each fixed N. Changing the pivot can also change those payoff levels.

The exact equality of zeros in (5) consequently does not imply

    inf_N g_N=0  ⇒  inf_N c_N(η)=0.

No claim is made that the latter implication is false. The STALL test and
the singleton-column calculation give positive coverage evidence only.
The previously classified VANISH one-menu floor is likewise not an
all-deadline counterexample: that table has good large-menu compensated
branches already proved elsewhere.

One surviving question is whether the original full-response structure
can yield an exact outer correction with small L while allowing the
deadline to change. Allowing arbitrary action-dependent subsidies would
be a different selector; no such enlargement is used in these conclusions.

## 7. Narrow source comparison

The source definition is
[RENY's compensated correspondence](CODEX_RENY__LATE_CAP_COMPENSATED_NEVER_SELECTOR.md),
SHA-256 `22a63c4acbe3b67f20bc2c70f675bded8b9a8bfb211e4cc74fb94904cabdeea0`.
Its existing upper bound and fixed-point existence are not reproved here.
The independent one-menu regression is
[the exact matching obstruction](CODEX_HILBERT__COMPENSATED_FIXED_POINT_TAIL_MATCHING_OBSTRUCTION.md).

Named production sources inspected for the present claims were:

- `exists_objective_minimizer_eq_behavioral_infimum` and
  `isGLB_pivotLaw_exploitability_of_objective_minimizer` in
  `UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralInfimum.lean`;
- `zeroBoundaryMass_is_zero_minimizer`, `objective_massAt`, and
  `geometric_exploitability_massAt` in
  `UniformEquilibrium/Diagnostics/Quitting/PivotRepairNonattainedZeroLP.lean`,
  which already contain a concrete a_j=0<b_j boundary instance;
- `quittingStationarilyGeneratedApproximateEquilibria_of_normal_noHarmSingleton`
  in `Quitting/Classification/Existence/NoHarmSingletonGenerated.lean`,
  the existing no-harm singleton producer;
- `exists_singletonColumnBlockerCertificate_of_fourPlayer_noUniform`
  in `Quitting/Classification/LCP/FourPlayerSingletonColumnBlockers.lean`,
  which excludes condition (6) on a canonical positive-gap counterexample.

The expressiveness inclusions above add correspondence information about
the new exact outer rule, not a new proof of the already solved table
classes. No all-game transfer or all-deadline separating table has been
proved in this bounded test.
