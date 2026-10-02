# Global pivot-repair minima and the fresh-cap clamp test

Author: CODEX_TARSKI_PREMIUM.

Status: bounded internal research checkpoint; ordinary mathematics, no
new UE class, export, or Lean claim. The old-calendar part of the proposed
three-clamp operation is exactly inert after global opponent selection.
The genuinely new-date part is not resolved. In particular, no sign for
its complete pivot-repair value is inferred from the three unilateral
half-gain bounds. The approximate-cap/late-Never distinction below is
essential; the operation is not restricted to exact finite-menu Nash.

## 1. Actual objective and the source being minimized

Fix the raw canonical Fin4 table: zero Never, s=(1,0,0,0), and arbitrary
other rewards bounded by M≥1. All laws are independent and all unilateral
behavioral deviations are allowed. Write d_i=B_i−U_i and E=max_i d_i.
Let m=inf E over ALL actual profiles, not over an equilibrium set.

For N≥1 and F_N={0,...,N−1,Never}, allow each nonpivot law q_j to range over
Δ(F_N), but allow the pivot law π to be arbitrary. Define

    R(q)=inf_(actual π) E(π,q),
    ρ_N=min_(q∈Δ(F_N)^3) R(q).                         (1)

The complete compact pivot LP gives the inner value and, jointly with the
three finite simplexes, attains the minimum in (1). A minimizing LP point
need not itself be an actual pivot law. Its zero-first-atom boundary is
approximated by actual geometric tails, with all full debts controlled.
Thus for every ε>0 some actual profile with these same three q_j has
E≤ρ_N+ε. No cap attainment at a phantom boundary law is used.

The sequence ρ_N decreases and tends to m. The lower bound ρ_N≥m is
immediate. For the converse, approximate any actual near-minimizer by
finite laws with full-regret control; these laws are admissible in (1)
for a sufficiently large N. The same finite approximation theorem makes
any strict actual improvement usable for the finite-menu question.

Consequently a useful successful inequality would be a cofinal bound

    R(q'_N)≤ρ_N−ω+o(1),          ω>0 if m>0,             (2)

or a recurrence that really forces ρ_N→0. Merely obtaining a strict
decrease at every finite N would not suffice. The new deadline may
depend on N and the approximation accuracy; all its full testers must
be retained before solving the new repair LP.

## 2. The all-four-tie guardrail and a finite pivot surcharge

Current production proves that every positive global MAX carrier minimum
has ALL FOUR debts equal to m. The unit-cube statement applies here after
uniform positive scaling by M. Compactness of the complete (U,B) carrier
therefore gives a number Δ>0 such that every actual p satisfies

    min_(j=1,2,3) d_j(p)≤m/2  ⇒  E(p)≥m+Δ.             (3)

One can obtain Δ by minimizing E on the union of the three closed carrier
sets {d_j≤m/2}; all are disjoint from the global minimum set. This is an
existing minimum-separation argument, not new progress.

For a finite profile define L_0=W_0+D_0−U_0 as in the question. If

    max_(j>0)d_j≤m/2,       L_0≤m+Δ/2,

then (3) forces a finite pivot date t<N with

    V_0(t)−U_0≥m+Δ.                                    (4)

Indeed only the pivot can carry E in (3), the omitted late row is too
small, and its Never row is at most L_0 because D_0≥0. Its remaining
finite cap is attained in the finite head menu. Thus controlling only
the three nonpivot debts and the late scalar is not a complete correction:
the pivot's listed dates can carry a strictly larger debt. Controlling
that complete pivot debt as well would yield the desired contradiction,
not a supplied-object adapter.

## 3. The tested actual three-law operation

At an actual profile choose, for each nonpivot j, a complete cap response
τ_j, or a κ-near-cap response. Define its two actual marginal pushforwards

    q_j^−=Law(min(T_j,τ_j)),    q_j^+=Law(max(T_j,τ_j)),

with Never ordered last. Independently choose a sign and a chord parameter
θ_j∈[0,1] for each of the three players, and replace

    q_j by (1−θ_j)q_j+θ_j q_j^(sign).                  (5)

After ALL THREE replacements, minimize the complete pivot LP again.
The old pivot, old payoff target, and one selected LP dual are not retained.
The complete new LP value, not a weighted tester average, is the objective.

The existing clamp identity says that the two unilateral own improvements
sum to d_j for a cap response and to d_j−e_j for a near-cap response,
where 0≤e_j≤κ. In the latter case each arm is at least −κ and one is at
least (d_j−κ)/2. These are source-produced unilateral gains. They do NOT
add when three laws change, and do not bound the repaired pivot's full E.

The previously inspected clamp/cross-amplification note already proves
the identity, the same-multiplier charges, and the source-reach distinction
between advance and delay. None is reproved or claimed new here.

## 4. Exact old-calendar obstruction at the globally selected source

Choose q from an optimizer of (1), and realize its pivot LP within ε.
If all chosen clamp times belong to F_N, every law (5) remains in F_N.
Therefore, for EVERY simultaneous choice of signs and parameters,

    R(q')≥ρ_N,       E(π,q)−R(q')≤ε.                   (6)

This is an ALL-LAW source comparison, including free complete pivot
reselection. It is not a local stationarity argument and is not based on
a bad arbitrary fixed point. It excludes a positive cofinal decrement
from the entire old-calendar clamp family even though each source debtor
may supply a positive half-gain arm. It does not exclude the conjecture-
facing inequality (2) for genuine new-date replacements.

This also explains why working at a minimum over one selected coupled
Nash set would be the wrong source: (6) uses the global minimum over ALL
three opponent laws on the old calendar, not their equilibrium status.

## 5. Which genuinely fresh response dates are available?

The actual geometric realization makes this question precise. Its pivot
has head masses before N, late finite mass λ, Never mass ν, and first
late atom α with 0<α≤λ. At N+k its atom is αu^k, where
u=1−α/λ. Fix a nonpivot j. Let

    a_j=r_j({0}),   b_j=r_j({0,j}),
    D_j=∏_(k∈{1,2,3}\{j})q_k(Never),
    A_j=its contribution from opponents' absorption before N,
    H_j=max_(t<N)V_j(t),
    W_j=A_j+D_j a_j λ,
    C_j=A_j+D_j b_j α.

The zero own singleton gives the exact COMPLETE late-response formula

    V_j(N+k)=W_j+u^k(C_j−W_j),
    B_j=max(H_j,C_j,W_j).                              (7)

For α=λ, u^0=1 and u^k=0 for k≥1. For λ=0 the actual finite pivot
instead gives V_j(t)=W_j=A_j for every t≥N. The boundary α=0<λ is
not an actual law and is used only through the positive-α realizations.

Equation (7) is the existing canonical first/limit/Never endpoint
calculation. It yields three genuinely different cases for this test:

- If C_j=B_j, date N is a literal fresh cap response.
- If W_j=B_j>C_j and 0<α<λ, no finite late date attains that cap,
  but arbitrarily late dates are κ-near-cap for every κ>0. Approximate
  original-law freedom therefore MUST retain this case. If α=λ, all
  dates after N attain W_j; the finite-pivot λ=0 case is analogous.
- If H_j≥max(C_j,W_j)+γ, γ>0, every κ-near-cap response for κ<γ lies
  in the old finite head. In that case fresh-date access cannot be
  recovered merely by replacing exact best replies with near-best replies.

In the middle case a sufficient exact condition is
u^k(W_j−C_j)≤κ. Its new date N+k need not have a bound uniform in the
chosen positive first atom α. Choosing that date first and then solving
the complete LP on the enlarged opponent calendar avoids omitting the
new joining response. No fixed-calendar derivative or old dual is
transported across this enlargement.

If the last case holds for all three players at a selected actual
ε-realization of (1), (6) applies to the ENTIRE κ-near-cap clamp family
for κ<min γ_j. This is a precise obstruction to the proposed move at
that source. It is NOT a proof that such separated sources occur
cofinally under m>0, nor a counterexample to free joint source selection.

The concrete missing source inequality is now smaller than a supplied
"good correction": first establish, or falsify, that some actual
near-minimizers selected from (1) avoid this uniform head-cap separation;
then determine whether their fresh-cap clamp family satisfies (2).
Fresh response availability alone does not price the other two players'
new joining rows or the finite pivot surcharge (4). No implication from
three half-gains to either required assertion has been proved.

## 6. Source and non-overlap record

The question is
[FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION](../questions/FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION.md).
The exact source declarations inspected are:

- `singlePivot_fullExploitability_eq_max_menuExploitability_scalar` and
  `singlePivot_nonpivot_fullDebt_eq_menuDebt`, in
  `UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`;
- `minimumTerminalSemantic_maximumDebt_allPlayersTie`, in
  `UniformEquilibrium/Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean`;
- `QuittingPivotRepairLPInput.objective`, `constraintGain`, and
  `exists_objective_minimizer`, in
  `UniformEquilibrium/Quitting/Terminal/PivotRepairFiniteLP.lean`;
- `exists_objective_minimizer_eq_behavioral_infimum`, in
  `UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralInfimum.lean`;
- `responderFirstEndpoint_eq_of_singlePivot`,
  `responderLimitEndpoint_eq_neverEndpoint_of_singlePivot`, and
  `exists_law_boundary_approximation_of_singlePivot_reward_bound`, in
  `UniformEquilibrium/Quitting/Terminal/SinglePivotRepairSourceEquivalence.lean`;
- `exists_finiteDeadlineTimingProfile_approximation`, in
  `UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`.

The prior [global/menu separation](CODEX_NOETHER_SUPPORT__FINITE_MENU_NASH_AND_GLOBAL_MAX_MINIMUM_SEPARATION.md)
already supplies (3)'s minimum boundary. The
[complete three-opponent repair envelope](CODEX_NOETHER_SUPPORT__JOINT_OPPONENT_MOVE_AND_COMPLETE_REPAIR_VALUE.md)
already handles arbitrary new opponent laws and requires ALL optimal duals
for a directional upper estimate. The
[existing clamp package](CODEX_FRECHET_CYCLE__CLAMP_CROSS_AMPLIFICATION_AND_SOURCE_INTERVAL_REACH.md)
owns the unilateral split and chronology. The distinct bounded test here
is (5) at the genuinely global source (1), and its exact old-calendar
failure (6) versus the three late-response cases (7).

Canonical singletons, punishment normality, and raw singleton-column
blockers do not by themselves assert any of the inequalities between
H_j,C_j,W_j in (7): these contain the selected actual head and its
counterfactual response values. No arbitrary solved-table fixture is
presented as a falsifier of their as-yet-unproved global-source selection.

Arithmetic check: 648 rational choices of λ, α/λ, signed passive/join
rewards and k verified (7) against the direct finite geometric sum. This
checks the endpoint formula only, not the open global-value inequality (2).
