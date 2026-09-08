# Signed local degree: remaining source contracts

## Scope of the checked finite construction

`sum_parameterFaceWeight_left_eq_right`
(`MathUE/Topology/KuhnSignedParameterEnd.lean`) compares sums over the entire
parameter ends of one finite cube. The literal discrete-family adapter is
`boxComplementarityDiscretePrism_endpointSignedWeight_eq`
(`Research/Topology/BoxComplementaritySpernerSubdivisionPrism.lean`). It uses
the existing actual boundary classification and endpoint equivalences. These
are fixed-resolution, full-box integer identities. They do not establish a
local index, local homotopy invariance, or independence of resolution.

The domain factor is the signed lattice determinant, not Euclidean volume.
At a unit Kuhn cell it is a unit integer. Label orientation is the determinant
of its ordered label-incidence matrix. An arbitrary subdivision cell need
not have unit determinant, so its geometric orientation must use the sign
of that determinant, not its unnormalized volume as a counting multiplicity.

## Exact existing local source to retain

`boxComplementarityLocalCompleteSimplices`
(`Research/Topology/BoxComplementaritySpernerLocalCount.lean`) already selects
the literal finite set of complete simplices whose label-dimension anchor
belongs to a displayed region. Reuse this set and this anchor; do not replace
them with an independently defined collection of cells.

The following declarations in the same file are stronger than parity-only
results and directly support arbitrary signed sums over the existing set:

- `boxComplementarityLocalCompleteSimplices_union`;
- `boxComplementarityLocalCompleteSimplices_disjoint`;
- `boxComplementarityLocalCompleteSimplices_eq_of_anchor_mem_iff`;
- `boxComplementarityLocalCompleteSimplices_eq_of_difference_subset_cleared`;
- `boxComplementarityLocalCompleteSimplices_eq_empty_of_no_vertex`;
- `BoxComplementarityProblem.exists_isolatingFrontierCollar_eventually_cleared`.

`boxComplementarityLocalSignedCount`
(`Research/Topology/BoxComplementaritySignedLocalCount.lean`) sums the existing
endpoint signed weight over that set. Its union, excision, and cleared-collar
theorems use these exact equalities and ordinary finite-sum theorems. The
companion imports the prism owner without introducing a cycle through its
local-count dependency. These results do not stabilize the signed count in
the mesh parameter.

## Required local restricted-prism source

Let a family of box-complementarity problems have a jointly continuous gain
function of parameter and spatial point. Let the same relatively open region
be isolating for every parameter in the closed unit interval.

The next source theorem must produce a positive spatial collar radius and a
mesh threshold such that every sufficiently fine actual parameter-spatial
prism has no externally complete face meeting that collar. A face can carry
labels evaluated at several adjacent parameter levels. Consequently, the
existing single-problem eventual-clearing theorem does not by itself supply
this mixed-parameter assertion, even if invoked separately at every time.

The standard proof obligations are:

1. Compactness of parameter times the region frontier and absence of family
   solutions there give one uniform solution-free collar. Preserve the same
   family and region; do not assume a supplied unrelated clearance oracle.
2. Generalize the existing complete-simplex cluster argument to actual prism
   faces: adjacent vertex parameters and spatial positions converge to one
   pair, and joint continuity transfers all retained label inequalities to a
   complementarity solution at that pair. This rules out complete faces in
   the collar uniformly at fine meshes.
3. Select a literal finite family of prism cells from the region. Prove that
   a complete face with one selected and one unselected parent lies in the
   collar. The geometric step uses the mesh bound and an actual path or
   segment crossing the relative frontier. Merely restricting the existing
   full-box sum does not discharge this new boundary obligation.
4. Use the checked integer row and interior-column cancellation on those
   actual selected cells. Identify the selected parameter-end faces with
   the existing anchor-selected simplex sets, using cleared-collar set
   equality to reconcile the selection convention with the existing anchor.

The resulting local, same-resolution theorem should have the order:

> For every jointly continuous family and one region isolating for all its
> parameters, there exists a threshold such that at every positive mesh
> resolution above it, the two endpoint local signed sums are equal.

This is a known-mathematics formalization obligation, not a new quitting-game
proposition. It is stronger in locality than the checked full-box theorem,
but it still does not compare different resolutions.

## Separate cross-resolution and approximation independence

For one fixed problem and isolating region, the required eventual mesh
independence has two independent mesh quantifiers:

> There exists a threshold such that for every pair of positive resolutions
> above it, the existing anchor-selected signed sums at those resolutions
> are equal.

For approximation independence, retain a uniform frontier nonvanishing
margin and the actual approximating maps or label-producing fields. One
must prove the induced admissible approximations are connected on a common
finite refinement without a complete artificial-boundary face. An interface
assuming equality of the desired signed counts is not a construction.

`productRefinementVertex` and
`boxComplementarityGridPoint_productRefinementVertex`
(`Research/Topology/BoxComplementaritySpernerSubdivisionPrism.lean`) preserve
the represented coarse grid points in a product resolution. They do not
send coarse unit Kuhn simplices to target unit Kuhn simplices:
`productRefinement_unitJump_not_unit_of_one_lt` records that obstruction.
The missing construction is a compatible geometric triangulation or
subdivision-chain comparison, including its restriction to the local region
and its cleared collar. No such producer was found in the bounded search.

## Subdivision library discovery and reuse boundary

`kuhnStarSubdivision_completeFacetParity_eq`
(`Research/Topology/BoxComplementaritySpernerSubdivisionPrism.lean`) is a
local label-deletion parity identity. It constructs neither geometric
stellar cells nor a sequence connecting the two grid triangulations.
Its integer label analogue follows routinely from
`SignedSimplexLabel.sum_deletionWeight_eq_zero`
(`MathUE/Topology/SignedSimplexLabelBoundary.lean`), but should not be added
without a consumer that also supplies the missing geometric source.

The pinned Mathlib `AlgebraicTopology/SimplicialSet/Subdivision.lean` defines
`SSet.sd`, `SSet.ex`, `SSet.sdExAdjunction`, and `SSet.stdSimplex.sdIso`.
These are subdivision functor/adjunction constructions, not a geometric
Kuhn common-refinement, mesh-control, or realization-homeomorphism theorem.

`CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy` and
`CategoryTheory.SimplicialObject.Homotopy.map_homology_eq`
(`Mathlib/AlgebraicTopology/SimplicialObject/ChainHomotopy.lean`) already
provide genuine signed chain-homotopy algebra. Reuse them if an actual
simplicial-map/homotopy representation is selected; they do not supply that
representation for the grid source.

The geometric `SimplicialComplex.convexHull_inter_convexHull`
(`Mathlib/Analysis/Convex/SimplicialComplex/Basic.lean`) and
`Affine.Simplex.affineIndependent_points_update_centroid`
(`Mathlib/LinearAlgebra/AffineSpace/Simplex/Centroid.lean`) provide useful
face/interior-point foundations, but no complete geometric stellar or common
subdivision constructor was found. No replacement generic chain or finite
double-counting library is warranted.

## Nonclaims

All remaining interfaces above concern standard finite-dimensional topology
and combinatorics. They introduce no new uniform-equilibrium argument.
Neither local integer degree nor its homotopy, approximation-independence,
cross-resolution, or regular-Jacobian comparison theorem is supplied by the
current full-box count. Signed integer information must not be replaced by
parity in the integer-LCP degree criterion.
