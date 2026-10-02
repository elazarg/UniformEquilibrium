Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Canonical Hessian and minimizing-vertex joins 51–52

Frozen drafts, unapplied and uncompiled here. Shared checkout read-only;
only apply_patch wrote this fresh /tmp unit. No Lean/Lake/Git/private caches,
worktrees or children. Units44–50 and all earlier frozen bytes unchanged.

Dependencies and root check order:

1. Existing checked CoordinateResetFTC and CoordinateHessianExtrema (27,34,
   their canonical Hessian/calculus closure, including root compiler repairs).
2. 51_CANONICAL_COORDINATE_HESSIAN_ENTRIES.patch, new generic module
   MathUE.Analysis.CoordinateHessianEntries. It needs neither game imports
   nor future fixture/polynomial modules.
3. Original07 CoordinateAffineBoxMinimum and12 RationalPolynomialRegularity.
4. Original45 RationalPolynomialCoordinateDerivatives and46 PairedFacePotential.
5. 52_PAIRED_CANONICAL_SPECTRUM_AND_MINIMIZING_VERTEX.patch, new consumer
   MathUE.Analysis.Examples.PairedFacePotentialCanonicalJoins.
6. AXIOM_HARNESS.lean; root owns inventory/audit promotion.

Source: REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS.md boundary test5.
Same actual translatedExpression/translatedPotential from46 throughout.

51 is standard operator glue, not another Hessian/spectral proof. Actual
coordinateMixedPartial is identified with actual second Fréchet derivative.
Canonical Euclidean single-coordinate Hessian entries are then identified
with those mixed partials; conjugation by EuclideanSpace.equiv gives literal
operator equality with Matrix.toLin' of the actual mixed-partial matrix.
HasEigenvalue transports by the same equivalence using actual eigenvectors.
The reusable glue explicitly assumes globally C2 potential; the actual
fixture supplies it from12, not as a new game/shape input. It makes no claim
about C2 functions only on a box beyond this stated helper scope.

52 supplies actual global C2 regularity via canonical12 for the same rational
expression; its canonical Hessian is conjugate to46's actual matrix, exact
HasEigenvalue iff96/32/-64 follows by reuse of46's reviewed matrix spectrum.
The literal coordinateLeastHessianEigenvalue at every point is -64, via
existing attained-eigenvalue and eigenvalue-comparison owners, and the
literal full-box coordinateMinimumHessianEigenvalue is -64 as well. No
recreated Rayleigh bound/spectral attainment/eigenbasis proof occurs.

Coordinate affinity is a finite expansion of the printed expression, not
a weakened coordinate-degree assertion. Compactness produces a minimum
internally; canonical07 then produces a minimizing vertex. Reviewed46's
top-not-minimum proof forces this vertex to be non-top, hence an actual
-3 coordinate, strictly below its singleton1/4. This is the internally
produced violation of source(M), not a supplied favorable minimum witness.

Nonclaims: still no actual quitting counterexample game or standard-Q
realization is asserted. The shape fixture's face-drift facts remain weaker
than the full-root requirement. Actual game exclusions belong to reviewed
09/actual full-root minimum owners; these joins do not recreate them.

Verification: static source/API inspection and100-column payload checks only.
Compiler uncertainty remains ordinary Euclidean-equivalence/CLM application
coercion simplification, differentiation of constant-coordinate evaluations,
matrix basis-vector evaluation, and finite update-expression normalization.
There are no new trust assumptions, supplied eigenvalues/minima or weakened
spectral conclusions. Root should inspect exact proof functions before repairs.
