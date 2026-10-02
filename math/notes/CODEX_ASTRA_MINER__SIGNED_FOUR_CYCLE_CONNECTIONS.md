# Signed four-cycle consequences and implementation opportunities

Author: `CODEX_ASTRA_MINER`.

Status: bounded source audit and ordinary mathematical corollaries, not checked
in Lean here. No production edits, Lean builds, exports, or literature priority
claims. The existing production coverage is recorded separately in
[SIGNED_FOUR_CYCLE_LEAN_COVERAGE.md](../formalized/SIGNED_FOUR_CYCLE_LEAN_COVERAGE.md).
The arguments below are candidates for independent review and implementation;
their absence as named declarations was checked only in the relevant signed
cycle, balanced certificate, singleton arc, and censoring sources.

## Question and semantic scope

Fix four players and an actual real reward vector r(S) for every nonempty
quitting coalition. At every live date players independently choose Continue or
Quit; all histories are observed. Infinite all-Continue pays zero. A deviation
may replace one player's entire behavioral strategy. Assume the actual
singleton comparison matrix satisfies the signed four-cycle strict tests.

Write sᵢ = rᵢ({i}), qᵢ for the constructed hazards, cᵢ = 1 − qᵢ,
and vᵏ for the four constructed coarse values, with indices modulo four.
The inspected construction gives 0 < qᵢ < 1 and

    vᵏ = qₖ r({k}) + cₖ vᵏ⁺¹,
    vⁱᵢ = vⁱ⁺¹ᵢ = sᵢ,
    vⁱ⁺²ᵢ > sᵢ,       vⁱ⁺³ᵢ > sᵢ.

Every equilibrium claim below keeps its selected target fixed before the
accuracy. The implementing profile and common threshold for all sufficiently
long finite horizons may depend on the accuracy. Own singleton values and all
nonsingleton rewards remain arbitrary signed reals unless explicitly restricted.

The concrete question is what stronger useful conclusions already follow from
this construction and its generic consumer, without another game-theoretic
existence argument.

## Ranked implementation opportunities

| Rank | Deliverable | Mathematical work remaining |
| --- | --- | --- |
| 1 | All four coarse values are UE payoffs; exact floor equalities; pairwise incomparability | Certificate initial-phase update and finite algebra |
| 2 | Every point on each consecutive coarse-value segment is a UE payoff | One reusable hazard-splitting certificate construction |
| 3 | Finite menus retain the specified target as well as full cap and early absorption | Expose the payoff estimate already available in the censoring proof |
| 4 | A continuous selected UE payoff on an open set of actual reward tables | Finite-dimensional continuity of explicit formulas |
| 5 | Singleton-only dependence and positive affine row transport of the selected values | Algebraic congruence lemmas; no general payoff-set transport |
| 6 | Exact coarse terminal Nash under a pair-collision upper bound | Instantiate the existing bounded compiler with collision cap zero |

Ranks 1, 3, and 6 are particularly small formalization tasks. Rank 2 produces
a stronger payoff-set conclusion using elementary certificate algebra. Rank 4
improves the meaning of the open class from existence to a continuous explicit
selection. None decides an additional arbitrary-game branch.

## 1. Exact floors and four incomparable equilibrium targets

The missing public equalities from formula (11) are

    vⁱ⁺²ᵢ − sᵢ = qᵢ₊₁ bᵢ / (1 − qᵢ₊₁),
    vⁱ⁺³ᵢ − sᵢ = qᵢ₊₃ hᵢ.

For the first, evaluate Bellman at phase i+1 in coordinate i and substitute
vⁱ⁺¹ᵢ = sᵢ and rᵢ({i+1}) = sᵢ − bᵢ. Rearrangement gives
cᵢ₊₁(vⁱ⁺²ᵢ − sᵢ) = qᵢ₊₁bᵢ. Divide by cᵢ₊₁ > 0.
For the second, evaluate Bellman at phase i+3, substitute
vⁱᵢ = sᵢ and rᵢ({i+3}) = sᵢ + hᵢ, and expand.

The existing signed certificate fixes `initial := 0`, but none of its fields
depends on that choice. For every k, update its initial field to k and apply
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`).
This proves, in ordinary mathematics, that all four vᵏ are UE payoffs.

The exact coordinate equality pattern is

    {i : vᵏᵢ = sᵢ} = {k, k−1}.

For distinct k and l these are different two-element sets. Choose an index in
each set difference. At the first index vᵏ is strictly below vˡ; at the second
it is strictly above. Thus the four targets are pairwise distinct and pairwise
Pareto incomparable. They are not being claimed Pareto optimal among all UE
payoffs or all feasible payoffs.

The rational heterogeneous fixture provides a concrete regression:

    v⁰ = (1,4,2,1),       v¹ = (1,1,4,2),
    v² = (2,1,1,4),       v³ = (39/10,2,1,1).

These exact values are already stated by `dagger_coarse_values`
(`UniformEquilibrium/Diagnostics/Quitting/SignedFourCycleValueFixtures.lean`).
The new inference is their simultaneous equilibrium interpretation and
coordinate comparison, not the calculation of those values.

## 2. The four segments are equilibrium payoffs

This is an ordinary proof using the existing certificate consumer. It does
not assume convexity of the entire equilibrium-payoff set or a public lottery.

Fix k and 0 ≤ t ≤ 1. Put

    x = (1−t)vᵏ + t vᵏ⁺¹,
    β = (1−t)qₖ,
    α = (qₖ−β)/(1−β).

Then 0 ≤ α,β < 1, and

    x = β r({k}) + (1−β)vᵏ⁺¹,
    (1−α)(1−β) = 1−qₖ,
    vᵏ = α r({k}) + (1−α)x.

Replace phase k in the four-phase certificate by two consecutive phases, both
owned by k, with hazards α and β. Assign their coarse values vᵏ and x. Leave
the other phases unchanged. This is an explicit five-phase certificate:

- The displayed identities prove the two new Bellman equations.
- Both endpoints have owner coordinate sₖ, so xₖ = sₖ.
- Every coordinate of x is above its singleton floor by convexity of scalar
  inequalities.
- Opponent divergence is preserved. For a deviator equal to k, the other three
  phases still have positive hazards. For another deviator, at least one of α
  and β is positive because their combined hazard is qₖ > 0.

Start this certificate at x and use the balanced certificate consumer. This
proves every point on [vᵏ,vᵏ⁺¹] is a fixed UE target, with the usual unrestricted
behavioral and uniform-horizon semantics. At t=0 or t=1 one inserted hazard is
zero, which the generic certificate permits.

An implementation should preferably expose generic certificate phase splitting
and arbitrary initial-phase choice, then specialize to the signed construction.
Existing `quittingMeshPayoffInterpolant_at_length_eq_next` and
`le_quittingMeshPayoffInterpolant_of_arcEndpoints`
(`UniformEquilibrium/Quitting/Circulation/SingletonFlowMesh.lean`) handle equal
mesh subdivisions. They are useful neighboring results, but the two arbitrary
hazards above are a separate small operation.

For an interior point of the kth segment, exactly coordinate k is at its
singleton floor. The two endpoints have the equality sets described in
Section 1. Consequently distinct open edges do not meet; an edge meets a
vertex only at its designated endpoints. Each edge is nondegenerate. Their
union is a simple closed polygon, hence contains infinitely many UE payoffs.

In fact this polygon is a Pareto antichain. Interior points on different edges
have different unique floor coordinates, giving two strict comparisons in
opposite directions. On one edge, all differences are nonzero multiples of
the incomparable endpoint difference. For a vertex and a nonincident edge,
use their different floor coordinates; for an incident edge, use the same-edge
argument. This is a statement about the constructed polygon only.

Do not infer that the filled convex hull is a UE-payoff set. The phase-splitting
proof establishes the four boundary segments and has no such consumer for
arbitrary interior convex combinations.

## 3. Finite-menu target delivery can be retained

The existing `hasTerminalProfiles_liveMassZero`
(`UniformEquilibrium/Quitting/Cycles/SignedFourCycleFiniteEarlyAbsorption.lean`)
forgets a useful part of the theorem it calls: the meshed profile has terminal
payoff exactly v⁰, at every mesh size. That equality is present in
`BalancedSingletonCycleCertificate.isTerminalNash_and_hasValue`
(`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`).

A useful strengthened ordinary conclusion is: for every e>0, η>0, H≥1,
ρ>0, and lower deadline N₀, there exist N≥max(H,N₀) and one actual finite
product timing law p satisfying simultaneously

    Eᵣ(p) < e,       maxᵢ |Uᵢ(p)−v⁰ᵢ| < η,
    Rₚ(N−H) < ρ.

Proof: choose the exact-target meshed profile with exploitability below e/2.
Let M≥0 bound all absolute rewards, and censor its marginal late-finite tails
with total tail mass T smaller than

    min(e/(8(M+1)), η/(2(M+1)), ρ/4).

The current proof gives exploitability increase at most 4MT, and joint Never
mass after censoring at most T because the original joint Never mass is zero.
The additional payoff estimate is at most 2MT in each coordinate. It is already
`abs_expectedPayoff_censorLateFiniteStoppingLaws_sub_le`
(`UniformEquilibrium/Quitting/Paths/LateFiniteStoppingLawCensor.lean`).
The same deadline padding and exact finite-law realization in
`finiteMenuFullEarlyAbsorption_of_terminalProfiles_liveMassZero`
(`UniformEquilibrium/Quitting/Terminal/TerminalProfileFiniteEarlyAbsorption.lean`)
finish the argument. No second independently selected approximation is needed.

This is a generic improvement for an exact-target, zero-live-mass source. The
same statement then applies to all the targets of Sections 1 and 2, once their
certificate profiles retain the same zero-live-mass argument. Finite censoring
generally loses exact target equality, so the finite-output assertion is
approximation, not exact delivery.

## 4. Continuous explicit selection on actual reward space

Let O be the set of all actual reward tables whose comparison matrix satisfies
`Math.HasSignedFourCycleStrictTests`. The map r ↦ Γ(r) is linear in the finitely
many singleton entries. Thus O is open by
`Math.isOpen_hasSignedFourCycleStrictTests`
(`MathUE/SignedFourCycleStrictOpenness.lean`). The zero diagonal of Γ introduces
no restriction on openness in the domain of actual reward tables: this is a
continuous preimage of an open matrix set.

There is a continuous explicit selection F:O→ℝ⁴ of UE payoffs. Define

    F(r) = Σⱼ [Wⱼ(Γ(r))/ΣₗWₗ(Γ(r))] r({j}).

Cancellation of 1−A in the current target formula proves F(r)=v⁰(r). Successor
denominators are nonzero throughout O; square root is continuous; λ>1; every
raw weight and their sum are positive. Hence the coefficients, eigenvalue,
raw weights, normalized weights, hazards, and all four coarse values are
continuous on O. This is elementary finite-dimensional continuity. Some needed
continuity facts currently exist only as private lemmas in the openness module.

All barycentric coefficients are strictly positive and sum to one, so F(r)
is a convex combination of the four singleton vectors. Singleton coordinates
which are not constant across the four singleton vectors have F strictly
between their minimum and maximum. In this signed class every player's
singleton row is nonconstant because its successor comparison is negative
and its predecessor comparison is positive.

Restricting O to the comparison neighborhood in
`exists_relative_open_uniformPayoff_neighborhood`
(`UniformEquilibrium/Diagnostics/Quitting/SignedFourCycleNeighborhood.lean`)
retains the stated noncyclicity and matrix classifications. The result adds a
continuous selected target to that theorem's existence conclusion.

This does not imply continuous equilibrium-strategy selection, a common mesh
over the unbounded class, continuity of the entire UE-payoff correspondence,
or continuation through the boundary λ=1 or vanishing raw weights.

## 5. Singleton-only dependence and row transport

If two reward tables agree on every singleton vector, the raw coefficients,
strict tests, hazards, and all four values agree. The existing producer then
makes each selected value a UE payoff for both tables, regardless of their
nonsingleton completions. This merits a named congruence/transport result.
It does not assert that one common accuracy-dependent mesh works for all
unbounded nonsingleton completions.

More generally, take positive dᵢ and arbitrary real aᵢ. Suppose the new singleton
vectors satisfy r'ᵢ({j})=dᵢrᵢ({j})+aᵢ; again choose all new nonsingleton entries
arbitrarily. Then Γ'ᵢⱼ=dᵢΓᵢⱼ. Both coefficient ratios in each row are unchanged,
so the same strict tests and hazards apply, and

    v'ᵏᵢ = dᵢvᵏᵢ+aᵢ.

The new producer independently establishes each transported target as a UE
payoff. The same holds for the polygon, by linearity of the segment formula.
The proof is exact ratio cancellation and a barycentric sum of one.

This argument deliberately uses the actual producer. Infinite all-Continue
still pays zero in the new game; arbitrary affine shifts therefore do not
justify generic affine payoff transport for every profile or the entire
equilibrium-payoff set. In particular no conclusion is being borrowed from
the separate single-pivot normalization machinery.

## 6. Exact coarse terminal Nash under collision control

Assume additionally rᵢ({i,j})≤sᵢ for every pair of distinct players i,j.
The bounded balanced certificate can then use collisionBound=0, because every
positive part of the pair collision excess is zero. Keep the same intensity
bound, hazards, values, and divergence. Instantiate
`BalancedSingletonCycleCertificateWithBounds.isTerminalNash_and_hasValue`
(`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`) with
mesh size one. Its error is zero and its terminal value is the selected vᵏ.

Thus the coarse profile is exact terminal Nash under this additional pair
condition. Triple and four-player coalition rewards may remain arbitrary:
with one prescribed owner at a time and one deviator, at most two players can
quit at the first absorbing date. This condition is sufficient, not claimed
necessary. Exact terminal Nash is not exact finite-horizon Nash.

The counterexample `coarse_profile_not_exactNash`
(`UniformEquilibrium/Diagnostics/Quitting/SignedFourCycleCoarseNonNash.lean`)
has s₀=1 and r₀({0,1})=3, so it violates precisely this extra sufficient
collision upper bound and does not contradict the corollary.

## Source audit and next task

Navigation began at the signed-cycle and finite-menu entries in
`docs/TOOLKIT.md`. Besides the exact declarations cited above, the inspected
dependencies were:

- `SignedFourCycleSingletonData`, `StrictTests`, and
  `weighted_singleton_comparison_balances`
  (`UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`).
- `targetValue`, `coarseValue`, `phaseHazard`, and `coarse_bellman`
  (`UniformEquilibrium/Quitting/Cycles/SignedFourCycleValues.lean`).
- `next_coarse_owner_eq`, `coarse_active`, `phaseHazard_pos_and_lt_one`,
  `coarse_two_after_owner_gt`, `coarse_three_after_owner_gt`, `coarse_soloFloor`,
  `certificate`, and `targetValue_isUniformEquilibriumPayoff`
  (`UniformEquilibrium/Quitting/Cycles/SignedFourCycleCertificate.lean`).
- `rawWeightSum_pos`, `sum_normalizedWeight`, `tails_pos`, and
  `survival_product_eq_periodSurvival` (`MathUE/SignedFourCycleWeights.lean`),
  with their raw definitions in `MathUE/SignedFourCycleAlgebra.lean`.
- `coefficientsOfSingletonMatrix_eq`, `hasStrictTests_singletonMatrix`,
  `ofSingletonMatrixStrictTests`, and `ofSingletonMatrixStrictTests_strictTests`
  (`UniformEquilibrium/Quitting/Cycles/SignedFourCycleStrictSourceBridge.lean`).
- `singletonArcCycle_isUniformEquilibriumPayoff` and
  `quittingSingletonArcCycle_phase_certificate`
  (`UniformEquilibrium/Quitting/Cycles/SingletonArcCycle.lean`).
- `openRegime_classification` and `exists_common_open_matrix_regime_neighborhood`
  (`UniformEquilibrium/Diagnostics/Quitting/SignedFourCycleMatrixRegimeOpenness.lean`).

No shared Lake build was run. This note records source inspection and explicit
ordinary proofs; it adds no Lean seal to the proposed corollaries.

Concrete next task: formalize Section 1 as a small signed-cycle extension,
then independently review and implement the generic phase-splitting operation
of Section 2. The finite-menu target retention in Section 3 is independent and
can proceed without any phase-splitting implementation.
