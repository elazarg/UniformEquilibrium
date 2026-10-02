# Degree-one germs: arbitrary local scheduling still requires a macroscopic exit

Author: CODEX_FRECHET_CYCLE.

Status: completed bounded ordinary-mathematical consumption test, not
independently reviewed or Lean-checked. It stops a specified operation:
concatenate arbitrarily chosen sufficiently small points of the actual
discounted equilibrium germ. This includes nonstationary calendars and
positive Never mass. It is not a new equilibrium class, a counterexample,
or a claim that the complete germ cannot inform a different construction.
The global discounted-component question remains open.

## 1. Exact source and attempted operation

There are four players with independent private behavioral choices at the
single live state, zero live/Never reward, and arbitrary finite signed
rewards r_i(S) at nonempty first-quitting coalitions. Deviations may replace
the whole behavioral strategy. Put s_i=r_i({i}) and

    Γ_ij=r_i({j})−s_i.

The benchmark is

    Γ=[0 3 −1 −1; 3 0 −1 −1; −1 −1 0 3; −1 −1 3 0].

Its inverse B is strictly positive: diagonal 2/15, paired entries 7/15,
and cross-pair entries 1/5. Its determinant is 45 and integer LCP degree
is +1. No degree contradiction is attempted.

Keep the ACTUAL punishment anchor

    c_i=min(0,P_i),       a_i=s_i−c_i,

where P_i is the infimum over independent opponent plans of the supremum
over all terminal behavioral replies. Under no original uniform payoff,
the checked same-table normality source gives P_i≤s_i, hence a≥0.
Some s_i>0: otherwise all Never is an exact equilibrium at every horizon.
In particular a≠0 and h=Ba>0 coordinatewise.

The auxiliary reward is r'_i(S)=r_i(S)−c_i, with live/Never still zero.
Let λ be the discount complement and q(λ) an actual discounted Bellman
equilibrium approaching all Continue. The complete-root localization in
the earlier index proof, not a supplied annotation, gives

    q_i(λ)=λh_i+O(λ²),                 h=Ba>0.             (1)

Here and below constants depend on this one fixed reward table and its
actual anchor. Under no UE, (1) holds uniformly for EVERY equilibrium at
sufficiently small λ. Briefly, the exact polynomial displacement is
D(λ,q)=λa−Γq+O((|λ|+Σ|q_i|)²). The all-root source excludes nonzero
limits and R0 excludes unbounded q/λ. Strict inverse positivity forces
every scaled limit to h=Ba>0; after dividing by λ the derivative in
q/λ is −Γ, so the ordinary implicit-function theorem gives the unique
local analytic branch and (1). This local fact is credited, not proposed
as new progress here.

Attempted operation: choose ANY deterministic sequence λ_n∈[0,δ],
with no monotonicity, periodicity or lower bound, and at date n let the
players use the actual row q(λ_n). Define q(0)=0 to allow silent rows
and an all-Never tail after a finite calendar. On the surviving history,
fresh player randomizations are independent. The resulting profile is
actual. Neither the auxiliary values nor the discounted Bellman equation
is declared to be its terminal continuation value.

Question: can a choice of these parameters, retaining all collision
coefficients of the actual germ, make full terminal regret tend to zero
as δ→0?

## 2. Exact stopping theorem

No. For the fixed source above there are δ₀>0 and g>0 such that EVERY
such profile with δ≤δ₀ has full terminal exploitability at least g.
The same result holds for any fixed source satisfying (1), h>0,
Γh=a, c≤0 and some s_i>0; the paired matrix is the intended actual
degree-one application, not an extra proof hypothesis hidden in the
estimates.

The proof retains the full independent law, including simultaneous
coalitions, the grand coalition and Never. One legal family of late
finite responses supplies the positive lower bound; a smaller response
menu is never substituted for the true cap.

Write

    H=Σ_j h_j,     ρ_i=h_i/H∈(0,1),
    J_n=∏_j(1−q_j(λ_n)),
    O_(i,n)=∏_(j≠i)(1−q_j(λ_n)),
    C=∏_(n≥0)J_n,                 D_i=∏_(n≥0)O_(i,n).

C and D_i are the actual joint and deleted-player Never probabilities.
No assumption says either is zero.

### 2.1 Uniform first-outcome account

At row n, (1) implies

    1−J_n=Hλ_n+O(λ_n²),
    Pr(the row Quit set is {j})=h_jλ_n+O(λ_n²),
    Pr(at least two players Quit)=O(λ_n²).              (2)

For sufficiently small δ, 1−J_n≥Hλ_n/2. If L_n=∏_(m<n)J_m,
telescoping gives

    Σ_n L_n λ_n≤2/H,
    Σ_n L_n λ_n²≤(2/H)δ.

Consequently the total probability of nonsingleton first outcomes is
O(δ), including every triple and the grand coalition. Comparing the
first two lines of (2) and summing with L_n gives, uniformly over the
ENTIRE chosen sequence,

    Pr(first coalition={j})=(h_j/H)(1−C)+O(δ).

The identical argument after deleting player i uses the three fixed
opponents and the positive sum H−h_i. Thus for j≠i their first-singleton
mass is h_j(1−D_i)/(H−h_i)+O(δ). These are original source-clock laws,
not a correlated lottery or a conditional playable block.

Let U_i be the prescribed original terminal payoff and W_i the original
payoff from the complete Never response of i. Since all reward entries
are bounded for this fixed table,

    U_i=(s_i+a_i/H)(1−C)+O(δ),
    W_i=(s_i+a_i/(H−h_i))(1−D_i)+O(δ).                 (3)

For the first equality use Γh=a. For the second, Γ_ii=0 means
deleting h_i leaves Σ_(j≠i)Γ_ij h_j=a_i unchanged. Signed rewards
are retained in the error bound; no reward translation at Never is used.

### 2.2 The SAME clocks link joint and deleted survival

Uniformly in the sequence,

    D_i=C^(1−ρ_i)+O(δ).                                 (4)

To verify this without assuming finite total hazard, put
A=Σ_n −log J_n and B_i=Σ_n −log O_(i,n). For small rows,

    −log J_n=Hλ_n+O(λ_n²),
    −log O_(i,n)=(H−h_i)λ_n+O(λ_n²).

If A is infinite then B_i is infinite and both sides of (4), without
the error, are zero. If A is finite, the same estimates give
|B_i−(1−ρ_i)A|≤KδA. Choose δ small enough that B_i≥(1−ρ_i)A/2.
The mean-value theorem then bounds the difference of their exponentials
by Kδ A exp(−(1−ρ_i)A/2), which is O(δ) uniformly over A≥0.
Thus (4) does not lose control on very long calendars or at positive
Never mass.

### 2.3 A literal complete response and the positive floor

Let B_i^full be i's unrestricted terminal response cap. The pure strategy
Quit at date N has payoff tending, as N→∞, to

    W_i+s_i D_i.

Indeed the earlier opponent absorption contribution tends to W_i.
If D_i=0 the remaining survival contribution vanishes. If D_i>0,
the opponents' cumulative hazards are finite, their row hazards tend to
zero, and conditional Quit-at-N reward tends to the own singleton s_i.
Thus no final-date collision or noncontracting Never branch is omitted.
Since each N is a legal response,

    B_i^full−U_i≥W_i+s_iD_i−U_i.                       (5)

Choose an owner i with s_i>0. Set t_i=a_i/H>0 and ρ=ρ_i. Equations
(3)–(5) yield the uniform lower bound

    B_i^full−U_i ≥ G_i(C)−O(δ),

    G_i(C)= t_i/(1−ρ) · [ρ+(1−ρ)C−C^(1−ρ)] + s_i C.   (6)

Weighted arithmetic–geometric mean gives
C^(1−ρ)≤ρ+(1−ρ)C, strictly when 0≤C<1. Therefore G_i(C)>0
on [0,1): its first term is positive. At C=1 its second term is s_i>0.
Continuity on the compact interval gives min G_i>0. Finally choose δ₀
so the uniform O(δ) error is less than half that minimum. This proves
the stated floor without optimizing any constant.

The result does not require finite total hazard, absorption almost surely,
an attained best response, or a stationary deviation. It survives every
choice of the sequence λ_n, so optimizing or reordering the local germ's
parameters does not remove it.

## 3. Exact calibration and overlap

For s=(1,1,1,1) and actual c=0, one has a=h=(1,1,1,1), H=4.
Equation (6) is

    G(C)=1/12+(5/4)C−(1/3)C^(3/4)>0,       0≤C≤1.

At C=0 it recovers the stationary refusal limit 1/12 already computed
by CODEX_CEDAR. At C=1 it gives the immediate/late singleton gain 1.
The positivity proof is the same AM–GM inequality, not a numeric scan.
The condition c=0 is stated explicitly; nonpositive c need not vanish
for an arbitrary signed completion. Formula (6), not this calibration,
is the actual-anchor theorem.

Prior work read before this test:

- [NOETHER's paired diagnostic](CODEX_NOETHER_SUPPORT__PAIRED_SINGLETON_CYLINDER_AND_GLOBAL_TWO_PHASE_TEST.md),
  Sections 6–9, frozen SHA256
  18ba47962f9e0476014fa86909308425bc243f2aa0361d72af0e58536ed2f0eb:
  pure-exit-free completion, complete-cap stationary repair, and the
  existing boundary table excluding a stationary-only cylinder argument.
- [CEDAR's radial-debiasing account](CODEX_CEDAR__DISCOUNTED_RADIAL_DEBIASING.md),
  Sections 3–5: the exact stationary refusal price and all-germ leading
  packet of the boundary table. No new stationary calculation is claimed.
- [Summable-seam semantic rigidity](../formalized/CHRONOLOGICAL_SHADOWING_SEAM_REDUCTION.md):
  actual bounded chronological Bellman accounts require their seam and
  deleted-survival budgets; root-Nash at an auxiliary value alone does
  not supply them.
- The original strict-index packet and
  [integer-degree packet](INTEGER_LCP_DEGREE_CRITERION_FOR_FOUR_PLAYER_QUITTING_GAMES.md):
  all-root localization is an actual no-UE consequence, not a freely
  selected germ. Neither existing packet supplies a positive mechanism
  when the total degree is +1.

The checked theorem
`no_nearAllContinue_terminalApproximateEquilibrium` in
`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryNonstationarity.lean`
already rules out uniformly small-root approximation for its specific
boundary reward table, even without the fixed-ray condition (1).
The present bounded test is not claimed as new boundary-table coverage.
Its scope is the arbitrary fixed collision completion with the ACTUAL
positive-inverse normalized source and an arbitrarily scheduled local
germ, including signed singleton levels and Never.

## 4. Named source correspondence and stopping point

Declarations and definitions inspected under their imports:

- `boundaryReward`, `soloReward_eval`,
  `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`:
  the exact solved benchmark, not an invented no-UE example.
- `no_nearAllContinue_terminalApproximateEquilibrium`, in the neighboring
  `SolanVieilleBoundaryNonstationarity.lean`: its precise all-row smallness
  and full terminal-Nash quantifiers.
- `quittingAuxiliaryGermValue_nonneg_of_punishment_nonpos`,
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/AuxiliaryShift.lean`:
  its punishment-sign hypothesis is explicit. No global positive-value
  assertion for every finite discount was imported into this proof.
- `quittingContinuationBestResponseValue_stationary_eq_max_quitNow_never`,
  `UniformEquilibrium/Quitting/Stationary/CompleteBehavioralCap.lean`:
  the existing stationary cap comparison. The new schedule is not passed
  to that stationary-only declaration.
- `QuittingChronologicalDebtData.prescribedDefect`, `directDebtDefect`,
  `semanticPair_eq_prefix`, and
  `exists_quittingTerminalSemanticPrefix_secant`,
  `UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean`:
  actual chronology retains every max-affine cap branch. This note does
  not assert its all-errors certificate is produced.

Stopped implication: the actual analytic germ, its positive anchor,
all higher collision coefficients, and arbitrary parameter scheduling
do NOT by themselves give a low-regret chronology consisting only of
vanishing points on that germ. The same complete laws that realize those
rows impose (3)–(6). The higher-order collision terms cannot accumulate
to order one along this operation, because the reached total in (2)
is O(δ), including after deleting any owner.

This neither proves that the original game lacks UE nor that the
collision information in the full analytic germ is useless. A new
operation must leave this local-ray regime. The distinct next question
is global and presently unproved: can the supplied table's discounted
equilibrium component select a macroscopic collision row AND an actual
continuation architecture that absorbs the artificial discount value,
or an already-covered endpoint exit? Continuing the germ to a finite
discount does not itself supply that continuation. No positive theorem
or new raw-table class is asserted here, and no further local coefficient
or scheduling optimization is proposed.
