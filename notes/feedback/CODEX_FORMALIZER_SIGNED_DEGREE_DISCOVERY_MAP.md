# Signed degree: bounded discovery map before implementation

Status: static source audit, not a build or a new proof. No topology foundation
has been started. This map addresses the next dependency of
`math/exports/INTEGER_LCP_DEGREE_CRITERION_FOR_FOUR_PLAYER_QUITTING_GAMES.md`.
It supplements the earlier formalizer integer-degree audit; the endpoint and
localization layers described there as pending have since been implemented.
Exact current declarations, not the older audit's historical task list, govern
reuse.

## Outcome

No integer-valued topological degree, signed local fixed-point index, or proved
degree package with homotopy/excision/affine-normalization laws was found in
the selected pinned Mathlib topology, analysis, and algebraic-topology trees,
the fixed-point dependency, MathUE, or the relevant Research topology files.
This is a bounded negative search, not a statement about external projects.

There is substantial reusable geometry. In particular the concrete Research
Kuhn-prism construction must not be rebuilt merely because its current
conclusion is modulo two. Its incidence and endpoint bijections are actual
theorems. What is absent is a compatible oriented integer count, its signed
cancellation laws, and a bridge making that count independent of admissible
approximation/subdivision.

A separate, smaller source obligation precedes the degree comparison: the
actual discounted displacement must have its linear expansion on a signed
ambient neighborhood, not only on probabilistic hazards.

## 1. Already available: do not re-prove

### Actual game source and localization

- `quittingDiscountedClippedMap_eq_self_iff`
  (`UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean`)
  preserves all lower/interior/upper face signs of the supplied cube fixed
  point. It does not impose strict complementarity.
- `quittingDiscountedBellmanAssignment_of_hazard_fixedPoint`
  (`UniformEquilibrium/Quitting/Bellman/Discounted/FixedPointLift.lean`)
  preserves the supplied discount, hazard and actual quotient value in the
  complete polynomial Bellman assignment.
- `exists_analyticBellmanGerm_at_discountedFixedPoint_hazardCluster`
  (`UniformEquilibrium/Quitting/Bellman/Discounted/ClusterCompletion.lean`)
  supplies bounded value completion while retaining the specified hazard
  cluster. The specified-endpoint curve-selection library is not missing.
- `auxiliaryDiscounted_fixedPoint_sum_lt_of_no_uniformEquilibriumPayoff`
  (`UniformEquilibrium/Quitting/Classification/AuxiliaryDiscountedLocalization.lean`)
  gives a threshold before all actual auxiliary fixed points under original
  noUE; it is not merely convergence of a selected family.
- `sum_le_of_isStandardLCPSolution`
  (`MathUE/LinearProgramming/R0Margin.lean`) bounds every exact standard-LCP
  solution for bounded right-hand sides, using the positive full-matrix R₀
  margin. No approximate-LCP library is needed for this use.
- `isR0Matrix_quittingSingletonMatrix_of_normal_of_no_uniformPayoff`
  (`UniformEquilibrium/Quitting/Classification/LCP/PunishmentNormalR0.lean`)
  is the generic original-game homogeneous-witness contradiction.
- `quittingSingletonMatrix_sub_payoff`
  (`UniformEquilibrium/Quitting/Classification/LCP/QuittingRewardAdapter.lean`)
  proves raw terminal-shift cancellation without analytic dependencies or a
  strategic-equivalence claim.

### Finite geometry, stronger than its parity-only corollaries

In `Research/Topology/BoxComplementaritySpernerLocalCount.lean`:

- `boxComplementarityLocalCompleteSimplices_eq_of_difference_subset_cleared`
  proves literal equality of finite simplex sets at one resolution when the
  regions' symmetric difference is cleared. Reuse this set equality before
  applying any proposed integer weight; do not re-prove it as signed excision.
- `boxComplementarityLocalCompleteSimplices_union` and
  `boxComplementarityLocalCompleteSimplices_disjoint` supply literal finite
  union/disjointness, not just equality after reduction modulo two.
- `BoxComplementarityProblem.exists_isolatingFrontierCollar_eventually_cleared`
  produces a collar with no fine-grid complete-simplex vertex from isolation.
  It does not assert resolution-independent signed degree.

In `Research/Topology/BoxComplementaritySpernerSubdivisionPrism.lean`:

- `completeSimplexEquivKuhnEndpointLabeledSimplex` connects the two existing
  finite simplex representations.
- `KuhnPrismCell.completeDeletionEquivIncidentFace` and
  `KuhnPrismFace.incidentCellEquivParent` expose actual incidence bijections.
- `boxComplementarityDiscretePrismLeftEndEquiv` and
  `boxComplementarityDiscretePrismRightEndEquiv` identify the actual endpoint
  faces with endpoint simplices. Their orientation behavior is not yet proved.
- `boxComplementarityDiscretePrism_endpointParity_eq` equates endpoint counts
  on ONE common grid, in `ZMod 2`. It is not signed homotopy invariance.
- `kuhnStarSubdivision_completeFacetParity_eq` proves one stellar move's
  mod-two count identity. Its statement explicitly does not connect arbitrary
  coarse and fine Kuhn triangulations by those moves.
- `productRefinement_unitJump_not_unit_of_one_lt` records why multiplying
  vertex coordinates alone does not yield the required simplex refinement.

`BoxComplementarityProblem.eventually_localCompleteSimplexParity_eq_one`
(`Research/Topology/BoxComplementaritySpernerEventualLocalParity.lean`) applies
when one open region contains the full solution set. It gives eventual
mod-two equality on each sufficiently fine resolution, not an integer index.
Research declarations are not imported by production; reuse would require
root-owned coherent promotion, not a production import of Research.

### Linear orientation and block determinants

- `Module.Basis.orientation_comp_linearEquiv_eq_iff_det_pos` and
  `Module.Basis.orientation_comp_linearEquiv_eq_neg_iff_det_neg`
  (pinned `Mathlib/LinearAlgebra/Orientation.lean`) identify linear orientation
  with determinant sign. They do not identify nonlinear local degree.
- `Matrix.twoBlockTriangular_det`
  (pinned `Mathlib/LinearAlgebra/Matrix/Block.lean`) already gives the block
  determinant factorization after the inactive-to-active block is zero.
- `Matrix.det_reindex_self` and `Matrix.det_fromBlocks_zero₂₁`
  (pinned `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`) provide the
  simultaneous coordinate reorder and active-block determinant calculation.

Consequently, the regular LCP sample does not need a new block determinant
proof or general differentiable local-degree theorem. Strict active/slack
inequalities make its min-map locally affine; after an actual affine-degree
theorem exists, these existing determinant identities suffice.

### Topology that does not yet produce an integer

- `ContinuousMap.Homotopy.affine`
  (pinned `Mathlib/Topology/Homotopy/Affine.lean`) constructs the actual
  straight-line homotopy of continuous maps. Boundary avoidance and equality
  of an integer degree remain separate obligations.
- `AlgebraicTopology.singularHomologyFunctor`
  (pinned `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`) exists.
- `TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor`
  (pinned neighboring `HomotopyInvariance.lean`) equates induced homology
  morphisms for homotopic maps. It is not yet a computation in a canonically
  oriented copy of the integers. No punctured-space/sphere generator,
  relative excision and determinant-normalization package was found here.
- `brouwer_fixed_point`
  (`.lake/packages/fixed-point-theorems/FixedPointTheorems/brouwer.lean`)
  proves existence for continuous self-maps of nonempty compact convex
  finite-dimensional sets. Existence is not a proof that the signed sum of
  their local indices is one.

`ModTwoBoxComplementarityParitySpec`
(`Research/Topology/ModTwoBoxComplementarityParity.lean`) still takes its
invariance laws as fields. It is not a reusable constructed invariant.
Likewise `IsStandardQOnPocketCirculants`
(`MathUE/LinearProgramming/CirculantPocketR0.lean`) is explicitly an unproved
proposition, not a hidden LCP-degree theorem.

## 2. Actual missing primitives, in dependency order

1. **Signed finite count and orientation compatibility.** Choose a concrete
   existing triangulation representation, attach actual integer local signs,
   and prove interior-face cancellation plus endpoint orientation. The existing
   even-incidence statements cannot distinguish equal from opposite signs.
2. **Subdivision/approximation independence.** Prove signed invariance under
   the actual refinements used, then that sufficiently close admissible
   approximations give the same integer. Generic fields asserting invariance
   are not an implementation. Existing collar/mesh geometry should be reused.
3. **Actual continuous degree on bounded open boxes.** Construct an integer
   for continuous maps avoiding zero on the frontier. Prove normalization,
   zero-free degree zero, finite additivity and excision preserving ALL zeros.
   Do not restrict the packet's actual roots to regular, isolated, interior,
   or fixed-support roots.
4. **Boundary-avoiding homotopy and positive rescaling.** Prove equality under
   joint continuous homotopies on the closed box and under positive domain and
   output dilation. Boundary perturbation stability then follows by the
   existing straight-line homotopy construction.
5. **LCP degree and the actual-source comparison.** The existing R₀ bound
   supplies one box for all roots while the RHS ranges along a compact
   segment. Homotopy gives RHS-independent total degree. Local-affine
   determinant signs evaluate the explicit regular sample only. The actual
   discounted branch comparison must retain the entire zero set.

The signed PL route above is a dependency proposal, not an implemented or
fully costed construction. The singular-homology alternative would instead
need the absent oriented relative/sphere computation and excision bridge.
This audit does not justify starting both routes or rebuilding generic
homotopy/linear algebra already available.

## 3. Smaller source obligation before the comparison

`abs_quittingDiscountedSingletonRemainder_le`
(`UniformEquilibrium/Quitting/Stationary/DiscountedQuadraticRemainder.lean`)
bounds the actual remainder by `4M (discount + totalHazard)^2` for nonnegative
discount and cube hazards. This is enough for localization of actual roots.
It does NOT prove uniform convergence on a degree domain containing negative
hazard coordinates.

For any fixed bounded ambient box in the scaled variable `h`, the packet needs
the SAME actual polynomial displacement to satisfy

```text
−D(discount, discount · h) / discount → Γ h − a
```

uniformly over that box as positive discount tends to zero. A sufficient
ordinary source adapter identifies the Fréchet derivative of actual D at
the ambient origin with `(discount, q) ↦ discount · a − Γ q`.

Do not implement Taylor theory for this. The exact reusable pieces include
`contDiff_eval_mvPolynomial` and `fderiv_eval_mvPolynomial_apply_single`
(`MathUE/Polynomial/MvPolynomialFDeriv.lean`),
`eval_mvPolynomialAffineSubstitution` and
`fderiv_mvPolynomialAffineSubstitution`
(`MathUE/Polynomial/PolynomialDerivativeApproximation.lean`), and the pinned
`HasFDerivAt.isLittleO` theorem. First inspect whether the actual polynomial
already has a coordinate representation or use existing finite sum/product
derivative rules directly; do not create a new polynomial merely to rename D.
The derivative identity and the compact scaled-box adapter remain to be
proved. No such proof was begun in this discovery pass.

## 4. Bounded fable lookup and nonclaims

The relevant symbol search in `math/fable/lean` covered degree, homotopy,
excision, determinant, LCP, singleton-matrix and fixed-point terminology.
The only orientation hits concern postmark strategic orientation or prose
about a payoff seam, not oriented simplex or integer-degree statements.
No fable proof relevant to this signed-degree obligation was found; unrelated
fable constructions were not re-audited or copied.

No source, cache, umbrella or math-owned note was edited. No Lean build was
run for this map. The map does not claim the degree packet complete, infer
integer signs from parity, or reopen new quitting-game mathematics.
