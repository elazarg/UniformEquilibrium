# Sorin planar nullhomotopy dependencies

## Mathematical target and scope

For a nonempty path-connected subset S of the complex plane, suppose that for
every base point b in S, every continuous based loop γ in S, and every z outside
S, there is a continuous L on [0,1] satisfying exp(L(t)) = γ(t) − z and
L(0) = L(1). The target is a based nullhomotopy of every loop inside S.
Compactness of S may be retained in an initial interface, but local connectivity
of S must not be silently added.

The quantifier over **all loops** is essential. The assertion that one loop
with zero winding about every outside point must itself be nullhomotopic is
not the proposed lemma. Hole detection can produce a different loop.

Sorin's Proposition 11 applies to compact continuous mixed games, including
discounted repeated games, not only finite-dimensional strategy simplices.
The source is the supplied article, printed pages 148 and 155. The checked
covering construction does not lift arbitrary payoff loops to strategy loops.

## Primary proof route

Fischer and Zastrow, *The fundamental groups of subsets of closed surfaces
inject into their first shape groups*, Algebraic & Geometric Topology 5
(2005), 1655–1676:
[primary article](https://msp.org/agt/2005/5-4/agt-v5-n4-p18-s.pdf).
The proof of Theorem 2, Lemma 12, and Theorem 15 supply the route.

Given a loop α in S, let Y be its image together with precisely those
complementary components of its image that are contained in S. Then Y is a
Peano continuum and Y is contained in S. Theorem 15 supplies a pointed
perforated-disk model; its proof actually constructs a deformation retraction
fixing Y pointwise. One omitted point is selected in each remaining hole.
If there are no holes, the model is a disk. Otherwise, transport a disk-boundary
loop into Y using the retraction, adding a stem and its reverse so that the
base point stays in Y. The resulting loop detects an omitted point.

This is a known-mathematics formalization dependency, not an assertion that
Sorin's result is mathematically open. The composed detection criterion has
not been formalized here. Its disk-boundary obstruction remains a separate
library obligation.

## Precise interfaces to preserve

1. **Path image.** A continuous image of [0,1] in a Hausdorff space is compact;
   its range is path connected and locally path connected. The latter uses
   the canonical compact-to-Hausdorff quotient map, not a continuous selector.
2. **Selected filling (Lemma 12).** For Peano continua A contained in B and
   an arbitrary selected family of components of B minus A, adjoining those
   components to A again gives a Peano continuum. Apply the paper's planar
   specialization to the loop image. Retain the canonical inclusion in S.
3. **Perforated disk (Theorem 15).** For a planar Peano continuum Y and base
   point in Y, select an omitted point in every bounded complementary
   component. Construct a closed disk with disjoint disk interiors removed,
   containing Y, and a deformation retraction onto Y fixing Y pointwise.
   The holes can be infinite: continuity of the glued retraction uses the
   null-sequence estimate of Lemma 16, not merely finite pasting.
4. **Based hole transport.** Join the fixed base point to a disk boundary in
   the perforated model. Concatenate the stem, boundary loop, and reversed
   stem. Apply the retraction homotopy, which fixes that base point and avoids
   the selected omitted point. The raw boundary base point need not be fixed.
5. **Exponential obstruction.** A disk boundary around an interior point has
   no closed continuous logarithm after translation. The standard round-circle
   calculation is a bounded first unit; it is not the general Jordan-boundary
   theorem. Based conjugation and endpoint-fixed homotopy transport the
   obstruction without an assumed integer-valued index.
6. **Consumer.** Universal closed logarithmic lifts rule out the detected
   hole; the pointed disk model then contracts the original loop in Y and S.
   Finally convert interval-square homotopies to the paper's real-parameter
   `NullHomotopicIn` convention by clamping both coordinates to [0,1].

## Existing Lean reuse and missing owners

- `exists_closed_logarithmic_lift`
  (`MathUE/Topology/SeparatelyAffineComplexLoopLift.lean`) supplies the actual
  logarithmic lifts for compact separately-affine images.
- `liftPath_imageLoop_apply_one`
  (`MathUE/Topology/SeparatelyAffineCoveringEndpoint.lean`) is the more general
  actual covering-endpoint result.
- `Topology.IsQuotientMap.of_surjective_continuous`
  (`Mathlib/Topology/Separation/Hausdorff.lean`) and
  `Topology.IsQuotientMap.locallyPathConnectedSpace`
  (`Mathlib/Topology/Connected/LocallyPathConnected.lean`) supply path-image
  local path connectivity. No new generic quotient wrapper is necessary.
- `Complex.isCoveringMap_exp` (`Mathlib/Analysis/Complex/CoveringMap.lean`),
  `IsCoveringMap.eq_of_comp_eq` (`Mathlib/Topology/Covering/Basic.lean`), and
  `IsCoveringMap.monodromy_trans_apply` plus
  `IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`
  (`Mathlib/Topology/Homotopy/Lifting.lean`) supply covering uniqueness and
  transport. `Complex.exp_two_pi_mul_I`
  (`Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean`) normalizes
  the standard circle.
- `simply_connected_iff_loops_nullhomotopic`
  (`Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean`)
  packages the eventual conclusion; it does not prove the planar criterion.
- No matching selected planar filling, perforated-disk retraction, or general
  Jordan-boundary exponential obstruction was available at the initial scoped
  library audit. The generic selected-filling development now lives in
  `MathUE/Topology/SelectedComponentFill.lean` and its local-path-connectivity
  companion; consult their checked declarations for current scope. The
  perforated-disk and Jordan-boundary tasks remain separate.

## Exact remaining disk-model dependencies

Fischer–Zastrow's proof of Theorem 15 uses the following known results, not a
supplied disk-model callback:

- The Riemann mapping theorem for the relevant complementary domains.
  The pinned `Mathlib/Analysis/Complex/RiemannMapping.lean` explicitly contains
  only partial results toward that theorem. Its filename does not establish
  availability of the final conformal equivalence.
- Continuous extension of the conformal map to the closed disk when the
  relevant boundary is locally connected. The paper cites Theorem 2.1 of
  C. Pommerenke, *Boundary Behaviour of Conformal Maps*, Springer (1992),
  its reference [17]. The exact book theorem must be inspected before
  selecting a formal telescope; the citation in Fischer–Zastrow is not a
  checked Lean boundary-extension API.
- Descent of annular deformation retractions through that boundary quotient,
  preserving the boundary pointwise. The resulting disk model need not consist
  of round Euclidean holes.
- Lemma 16's null-sequence property for bounded complementary components of
  a planar Peano continuum. Its proof uses planar separation of polygonal
  arcs and disks, followed by a contradiction to local path connectivity.
- Infinite gluing of the componentwise retractions, controlled by the
  null-sequence bound, as in Theorem 15's continuity proof.
- A nonclosed exponential lift for a topological disk boundary about an
  interior point, and based transport through the resulting retraction.
  The explicit round-circle calculation does not supply a Jordan/Schoenflies
  theorem or this general disk-boundary step.

No matching Jordan/Schoenflies, conformal boundary-extension, or complete
perforated-disk owner was found in the scoped pinned libraries. The actual
canonical compact-carrier loop fill and Sorin payoff-image adapter construct
the relevant compact Peano set in the planar specialization. They do not
discharge these planar dependencies or restrict the original proposition to
semialgebraic images. The supplied analytic factorization, circle multiplicity
and Hurwitz/injective-limit prerequisites live in
`MathUE/Analysis/AnalyticCompactZeroFactorization.lean`,
`MathUE/Complex/CircleArgumentPrinciple.lean` and
`MathUE/Complex/HurwitzLimit.lean`. They derive their finite-zero data rather
than assuming a census. Normal-family compactness and an actual maximizing
embedding are now supplied by the checked project chain through
`Math.ComplexAnalysis.exists_bijOn_unitBall_map_eq_zero`
(`MathUE/Complex/NormalizedDiskBijection.lean`). This gives the actual
holomorphic disk bijection, not the general non-injective boundary extension.

An accessible source for that remaining step is Milnor's *Dynamics in One
Complex Variable*, Sections 15–16, Theorem 16.6 and its proof, together with
Appendix A.3 ([author's notes](https://legacy-www.math.harvard.edu/archive/118r_spring_05/docs/milnor.pdf)).
It supplies continuous extension onto the closure under the local-connectivity
conditions, without boundary injectivity. Its formalization still needs the
spherical length/area, crosscut and Jordan separation ingredients.
`Math.ComplexAnalysis.eqOn_zero_of_bounded_radial_sequence_zero`
(`MathUE/Complex/RadialSequenceUniqueness.lean`) supplies the Appendix A.3
radial uniqueness step, with a computed Jensen lower bound, actual Fatou
argument and almost-everywhere removal of circle zeros. It allows any radii
sequence in a positive terminal annulus; convergence to the outer radius is
unnecessary. Pommerenke's cited book proof remains inaccessible; this is an
alternative known-proof source, not a checked boundary-extension theorem.
`Math.ComplexAnalysis.exists_normalized_disk_homeomorphism`
(`MathUE/Complex/NormalizedDiskHomeomorphism.lean`) supplies the actual subtype
homeomorphism. `Math.ComplexAnalysis.exists_normalized_disk_holomorphic_inverse`
(`MathUE/Complex/NormalizedDiskHolomorphicInverse.lean`) supplies both
holomorphic bijections, inverse identities, normalizations and nonzero
derivatives. Its generic inverse theorem works on arbitrary open domains,
without a connectedness or nonvanishing-derivative input. These are interior
domain results, not closed-disk boundary extension.

`Math.RectangleLengthArea.measure_two_sqrt_energy_le_quarter`
(`MathUE/Analysis/RectangleLengthArea.lean`) supplies the generic measurable
slice estimate with its literal square-root threshold; zero-energy and
almost-everywhere finite-slice cases are separate declarations.
`Math.ComplexAnalysis.spherical_energy_lt_top`
(`MathUE/Complex/HolomorphicSphericalEnergy.lean`) derives the real determinant
from the actual complex derivative and uses weighted change of variables to
bound energy by the integrable spherical density in a complex-valued chart.
`Math.ComplexAnalysis.exists_chart_short_slice`
(`MathUE/Complex/HolomorphicRectangleLengthArea.lean`) composes these results
for an actual open square in the holomorphic injective domain, with no global
measurability assumption on the arbitrary outside values. This does not supply
a chart containing infinity, spherical curve length, or a crosscut.
Nested short crosscuts with distinct landing endpoints and
Jordan separation remain separate known-proof library obligations. No scoped
Jordan/Schoenflies or crosscut producer has been found. Section 16.6 requires
continuous extension onto the boundary, not boundary injectivity, and the
whole feasible carrier is not silently assumed locally connected.

Fischer–Zastrow's Peano convention permits a singleton. Their Theorem 2
application excludes constant loops via its non-null hypothesis, but an
all-loop consumer must explicitly dispatch constant loops and singleton fills
before invoking the disk-domain parametrization in Theorem 15. These guards
must not be silently replaced with a stronger nondegeneracy assumption.

## Finite-simplex alternative is narrower

`MathUE.IsSemialgebraic.image_polynomialMap`
(`MathUE/Semialgebraic/PolynomialMap.lean`) can establish semialgebraicity of
a literal finite-simplex bilinear payoff image after its coordinate adapter.
Coste's *Real Algebraic Sets*, Theorem 1.10, supplies compact semialgebraic
triangulation; Theorem 1.19 supplies local conic structure:
[author's lecture notes](https://indico.ictp.it/event/a02455/session/9/contribution/6/material/0/0.pdf).
Those notes explicitly distinguish triangulating an image from triangulating
an arbitrary vector-valued map. This alternative does not cover the original
general compact-strategy proposition or its discounted specialization.

## Implementation boundary

The actual standard-circle nonclosed-logarithm calculation, compact-carrier
path-image filling and accumulating null-family continuity are supplied by
their project owners. No full planar nullhomotopy, Jordan theorem, general-game
Proposition 11 closure, or supplied index oracle is claimed by these units.
The analytic prerequisites likewise do not supply the remaining planar disk
model. Larger topology owners require separate plan review.
