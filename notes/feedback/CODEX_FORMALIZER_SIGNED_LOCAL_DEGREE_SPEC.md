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

## Constructed same-mesh local comparison

Let a family of box-complementarity problems have a jointly continuous gain
function of parameter and spatial point. Let the same relatively open region
be isolating for every parameter in the closed unit interval.

`IsContinuousBoxComplementarityFamily.exists_isolatingFrontierCollar_eventually_prismCleared`
(`Research/Topology/BoxComplementarityPrismCluster.lean`) produces a positive
spatial collar radius and one mesh threshold: every sufficiently fine actual
parameter-spatial prism has no complete face with a spatial vertex in that
collar. Each label is evaluated at its own vertex's parameter; joint continuity
passes all label inequalities to the same space-time limit. The uniform
solution-free collar is constructed in
`Research/Topology/BoxComplementarityFamilyCollar.lean`.

This is vertex clearance, not a statement that the geometric realization of
every face avoids the collar. The selected-cell boundary argument below
uses an actual shared face vertex in the cleared collar.

The proof dependencies are:

1. Compactness of parameter times the region frontier and absence of family
   solutions there give one uniform solution-free collar. This is proved by
   `IsContinuousBoxComplementarityFamily.exists_uniform_isolatingFrontierCollar`
   (`Research/Topology/BoxComplementarityFamilyCollar.lean`).
2. Generalize the existing complete-simplex cluster argument to actual prism
   faces: adjacent vertex parameters and spatial positions converge to one
   pair, and joint continuity transfers all retained label inequalities to a
   complementarity solution at that pair. This is proved by
   `IsContinuousBoxComplementarityFamily.isSolution_of_prismFace_vertex_tendsto`
   (`Research/Topology/BoxComplementarityPrismCluster.lean`); compactness then
   gives the uniform vertex-clearance theorem above.
3. Select a literal finite family of prism cells by base-point membership in
   the region. `prismFace_vertex_mem_frontierCollar_of_parent_membership`
   (`Research/Topology/KuhnPrismBoundaryCollar.lean`) puts every shared face
   vertex within one mesh width of the frontier when parent selections differ.
   It reuses a connected coordinate rectangle. The same file's
   `IsContinuousBoxComplementarityFamily.eventually_prismFace_parent_base_mem_iff`
   combines this bound with actual uniform clearance to prove parent-selection
   agreement at all sufficiently fine resolutions.
4. Weighted integer row and interior-column cancellation transports the
   selected endpoint sums. The endpoint-base representation in
   `Research/Topology/BoxComplementaritySignedLocalCount.lean` retains the
   existing label-dimension anchor; cleared-face membership coherence
   identifies it with the base-point selection.

`sum_weighted_parameterFaceWeight_left_eq_right`
(`MathUE/Topology/KuhnSignedParameterEnd.lean`) supplies the weighted finite
algebra for step 4. Its integer multipliers must agree on actual incidences.
`IsContinuousBoxComplementarityFamily.eventually_localSignedCount_endpoints_eq`
(`Research/Topology/BoxComplementarityLocalSignedHomotopy.lean`) supplies those
multipliers from the original family and region and proves equality of the
existing local counts at the actual parameter endpoints.

The proved local, same-resolution theorem has the quantifier order:

> For every jointly continuous family and one region isolating for all its
> parameters, there exists a threshold such that at every positive mesh
> resolution above it, the two endpoint local signed sums are equal.

This proves local homotopy invariance at every sufficiently fine common
resolution. It does not compare different resolutions or construct an
integer degree independent of the mesh.

## Cross-resolution stabilization and remaining approximation independence

For one fixed problem and isolating region,
`BoxComplementarityProblem.eventually_localSignedCount_eq`
(`Research/Topology/BoxComplementarityFloorRefinementSignedTransport.lean`)
proves eventual mesh independence with two independent mesh quantifiers:

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
The coordinate-floor construction below supplies the needed comparison,
including the local region and its cleared collar. It does not use the
point-preserving product embedding as a simplex map.

### Coordinate-floor comparison specification

The coordinate-floor maps and injective-image simplex theorem are proved in
`MathUE/Topology/KuhnFloorRefinement.lean`. The unique noncollapsed lift and
coordinate-raising agreement are proved in
`MathUE/Topology/KuhnFloorSimplexLift.lean`. Complete-simplex equivalence and
integer determinant preservation are proved in
`MathUE/Topology/KuhnFloorCompleteSimplex.lean`. The mixed-label prism,
sample-point clearance, and local signed-count transport below are proved
in Research.
For positive resolutions `p` and factors `k`, round a fine-grid coordinate
`v` to `v / k` using natural-number division. This preserves the zero and
top faces and moves its represented point by at most `1 / p`, independently
of `k`.

The required combinatorial producer has three parts:

1. An injectively rounded fine Kuhn simplex is a coarse Kuhn simplex.
   This is `simplex_kuhnFloorVertex_of_injective`
   (`MathUE/Topology/KuhnFloorRefinement.lean`), for arbitrary compatible
   labelled cubes and arbitrary simplex dimension. It reuses the existing
   simplex constructor, monotonicity, and endpoint coordinate bounds.
2. Each coarse top simplex with base `b` has exactly one noncollapsed fine
   preimage, with coordinate bases `k * (b + 1) - 1` and the same chronological
   coordinate permutation. The explicit `kuhnFloorSimplexLift`,
   `simplex_kuhnFloorSimplexLift`, `kuhnFloorVertex_kuhnFloorSimplexLift`, and
   `eq_kuhnFloorSimplexLift_of_floor_eq`
   (`MathUE/Topology/KuhnFloorSimplexLift.lean`) prove construction, simplex
   validity, literal tuple recovery, and uniqueness. Dimension zero is
   included. `kuhnFloorVertex_spernerChainStep_eq` in the same file supplies
   the coordinate-raising agreement needed for signed weights.
3. `floorPullbackSpernerCube` pulls the coarse labels back by rounding.
   Complete pulled-label simplices cannot collapse: `floorCompleteSimplex`
   derives injectivity from completeness. `completeSimplexFloorEquiv` gives
   the resulting bijection, and `kuhnFloorSimplexLift_determinant_eq` proves
   equality of the integer geometric determinants. These declarations are
   in `MathUE/Topology/KuhnFloorCompleteSimplex.lean` and reuse the existing
   coordinate-permutation sign theorem. There is no Euclidean volume factor.

This compares coarse labels with pulled labels, not with the actual fine
labels. `externalCubeLabelPrism`
(`Research/Topology/KuhnExternalCubePrism.lean`) constructs a discrete switch
between two proper labelings on one grid.
`externalPrismParameterEndEquiv` and
`KuhnPrismSpatialBoundaryLabeling.externalEndpointWeightedSum_eq`
(`Research/Topology/BoxComplementaritySpernerSubdivisionPrism.lean`) supply
the shared endpoint equivalence and weighted transport for arbitrary proper
prism labels with specified endpoint labels. Ordered vertices and signed
weights are preserved. The box-family and discrete-switch theorems both
specialize this construction under an incident-compatible integer selection.
The finite cancellation needs spatial boundary rules, not continuity of
the switch.

`boxComplementarityFloorRefinementPrism`
(`Research/Topology/BoxComplementarityFloorRefinementPrism.lean`) constructs
that switch for the actual problem: its left endpoint uses floor-pulled
coarse labels and its right endpoint uses actual fine labels.
`dist_boxComplementarityGridPoint_kuhnFloor_le_one_div` in the same file
proves that every fine-grid point and its rounded coarse point are at most
one coarse mesh width apart, uniformly over positive refinement factors.
The sample-point collar is proved below. The signed-transport module uses it
to supply incident-compatible local selection; the prism construction alone
does not equate counts.

`BoxComplementarityProblem.exists_isolatingFrontierCollar_eventually_floorRefinementCleared`
(`Research/Topology/BoxComplementarityFloorRefinementPrismCluster.lean`)
establishes one collar radius and one coarse threshold working for every
positive refinement factor. Each label is sampled either at the actual fine
point or at its rounded coarse point, within one coarse mesh width.
`dist_floorRefinementPrismFace_labelSamplePoints_le_three_div` in that file
bounds the distance between any two samples on a complete face by three
coarse mesh widths. Thus they share a limit as the coarse resolution tends
to infinity even when the refinement factor varies.
`BoxComplementarityProblem.isSolution_of_floorRefinementPrismFace_sample_tendsto`
in the same file identifies that limit as an actual solution from the sampled
label inequalities. Compactness then gives clearance, not a clearance premise.
These are Research declarations.

Local anchor membership also needs this collar. The coarse label-dimension
anchor and its fine lift can be different points: in dimension one an
anchor at zero can lift to `(k - 1) / (p * k)`. Equality for arbitrary
regions without clearance is not part of the specification.

`boxComplementarityLocalSignedCount_floorRefinement_eq_of_cleared`
(`Research/Topology/BoxComplementarityFloorRefinementSignedTransport.lean`)
proves transport under the actual sample-clearance condition. It identifies
the left samples with coarse endpoint points and the right samples with
fine endpoint points, transports signed weights, and uses the collar to
compare anchor membership without asserting equality of the anchor points.
`BoxComplementarityProblem.eventually_localSignedCount_floorRefinement_eq`
in that file supplies one threshold such that for every coarse resolution
above it and every positive factor, the existing local count at `p` equals
the count at `p * k`. Comparing `p` and `q` through `p * q` proves the
independent-resolution theorem above.

`BoxComplementarityProblem.localDegree`
(`Research/Topology/BoxComplementarityStabilizedLocalDegree.lean`) is the
resulting integer value. Its
`BoxComplementarityProblem.eventually_localSignedCount_eq_localDegree`
identifies it with every sufficiently fine positive grid count.
`IsContinuousBoxComplementarityFamily.localDegree_endpoints_eq` in the same
file proves homotopy invariance on a common isolating region by comparing
both stabilized values on one sufficiently fine common mesh. Affine
normalization and approximation independence remain further obligations.

`BoxComplementarityProblem.localDegree_union_of_disjoint`
(`Research/Topology/BoxComplementarityLocalDegreeConsequences.lean`)
proves additivity on disjoint isolating regions. Isolation of the union is
derived from that of its two components.
`BoxComplementarityProblem.exists_isolatingFrontierCollar_localDegree_coherent`
in the same file gives one actual collar permitting all region changes
whose symmetric difference lies inside it. Its more general excision
theorem accepts eventual finite-grid vertex clearance.
`BoxComplementarityProblem.exists_solution_mem_of_localDegree_ne_zero`
proves existence of an actual solution in any isolating region with nonzero
degree. It does not require the open region itself to be compact: compactness
of its closure and absence of frontier solutions suffice.

## Normalization and ambient comparison: implementation specification

The next finite calculation is the actual resolution-one count.
`boxComplementarityLocalSignedCount_univ_eq_resolution_one`
(`Research/Topology/BoxComplementarityFloorRefinementSignedTransport.lean`)
identifies every positive-mesh whole-cube count with the mesh-one count.
`BoxComplementarityProblem.localDegree_univ_eq_resolution_one`
(`Research/Topology/BoxComplementarityStabilizedLocalDegree.lean`) identifies
the stabilized value with that finite count, without an isolation premise.
Both specialize the actual floor comparison to the empty frontier collar.
At mesh one, the label rule depends only on the corner: its label is the
first coordinate equal to one, or the dimension if there is none. The
candidate unique complete ordered simplex raises coordinates in reverse
order. Its vertex at position `j` has coordinate `i` equal to one exactly
when `n - 1 - i < j`. The required producer must prove completeness and
uniqueness for the existing simplex type, then evaluate its actual weight.
A displayed corner or determinant alone is not that enumeration theorem.

The chronological coordinate permutation and the label permutation have
different sizes, `n` and `n + 1`. Their sign product is expected to give
`(-1)^n` under the current raw orientation. A kernel-checked one-dimensional
determinant calculation confirms the negative edge weight, but the general
whole-cube normalization is not yet proved. Do not identify the raw degree
with the conventional degree of `x - T(x)` without proving its sign
conversion. Even dimension four can conceal the distinction; quotient
dimensions need not be even.

The remaining geometric adapters are separate from that finite calculation:

1. Pull an ambient map through a positive rectangular chart and use its
   negative as the complementarity gain. The existing `rectangularPoint`
   (`MathUE/Topology/RectangularPoincareMiranda.lean`) supplies the coordinate
   map. Local zero regions must lie inside the chart. Chart independence,
   positive-dilation invariance, and the orientation conversion still need
   proofs against the constructed count.
2. Compute the local degree of an invertible affine root as the sign of its
   determinant under the conventional orientation. Existing prism
   cancellation does not supply that affine comparison.
3. At a strictly complementary LCP root, the minimum map is locally affine:
   active rows select slack and inactive rows select coordinates. This
   application needs affine comparison and a block-determinant calculation,
   not a general differentiability theorem.
4. General regular-Jacobian comparison can then use the derivative's small
   remainder and the inverse linear map's lower bound to construct a
   boundary-free straight homotopy. It is not a premise to put into the
   degree definition.

These are known finite-dimensional constructions still to implement, not
new strategic hypotheses or a new mathematical conjecture.

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
Local homotopy invariance of the mesh-dependent count is proved above.
The local integer degree and its homotopy invariance are proved above.
Approximation independence and regular-Jacobian comparison remain to be
constructed. Signed
integer information must not be replaced by parity in the integer-LCP criterion.
