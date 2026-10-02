Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Shape packet: final retirement checklist

Source read in full: math/exports/QUITTING_POTENTIAL_SHAPE_EXCLUSIONS.md.
SHA256: 6c2eda2191454a85a3fc892265561d241ffed84cc50a68643330e902b1e45e7f.

## Result and evidence boundary

The exact next source/fixture group closes every remaining printed useful claim
against the current checked core. No new mathematical obligation was found.
This is a static correspondence and preparation record, not a retirement seal.
The eight new modules and their proof/name overlays remain unapplied/uncompiled
at this inspection. Root's shared full build1205 is still pending here.

Root reports silent named checks for the minimum/quasiconvex, face-only Q,
robust face/mixed/Hessian, simplex representation and same-expression
characterization closures. The quantitative characterization56A passed68297.
Robust charge58 passed90508, including generic57; its manual applied harness
passed14947 with only propext, Quot.sound and Classical.choice. Current57/58
hashes match those reports:
57 db6f0ab7f79a8b1ea103b4d9b00975ac16b7d7542a0f0a3913810f976aa92d57;
58 c67b9cef34d39f011a229d39e971d68c9891e3f2d46838683154bd189dbc0ebf.
Those named/manual PASS results are not an overall full-build PASS.

## Complete claim correspondence

Paths below are production paths; short file labels mean the corresponding
MathUE/Analysis or UniformEquilibrium/Quitting/Projective module unless stated.

| Printed claim | Exact declaration and owner | Remaining dependency |
| --- | --- | --- |
| Thm1: matrix-free not quasiconvex; internally positive exact and robust rejecting edge | GameTheory.IsQuittingFullExactRootPotential.not_quasiconvex; exists_positive_exactRoot_potential_violation_of_quasiconvex; not_quasiconvex_of_quittingRobustPotential_add_two; exists_positive_quittingRobustEdge_potential_violation_of_quasiconvex (FullExactRootPotentialQuasiconvexExclusion.lean) | Current checked core |
| Thm1 proof/minimum claim: every full-box minimum strictly above own singletons; both attained minima, same minimum on C and K0, strict boundary gap | GameTheory.IsQuittingFullExactRootPotential.minimum_above_singleton_of_differentiable; minimum_lt_lowerBoxBoundary; exists_minima_strict_gap (FullExactRootPotentialMinimum.lean) | Current checked core; simultaneous IsMinOn at the same point already expresses equality of the two attained values |
| Thm2: genuine face-only zero-diagonal textbook-Q obstruction | Math.LinearProgramming.not_quasiconvexOn_of_standardQ_positive_face_drift (MathUE/Analysis/StandardQFaceQuasiconvexExclusion.lean); GameTheory.not_quasiconvex_singletonBox_of_standardQ_positive_face_drift (SingletonBoxStandardQFaceExclusion.lean) | Current checked core, not the stronger matrix-free full-root theorem |
| Thm3(1): 1+τ L1 lower-face drift, L1≥1/(W−τ), c=W/(W−τ) | GameTheory.quittingRobustPotential_singletonFace_fderiv_bounds (RobustPotentialSingletonFaceDrift.lean) | Current checked core; all lower faces, including upper-face intersections |
| Thm3(2): closed-box additive and nonmonotone scalar-composition exclusion from ONLY supplied nonnegative simplex image | GameTheory.not_singletonBox_additive_of_simplex_positive_face_drift; not_singletonBox_scalarComposition_of_simplex_positive_face_drift; quittingRobustPotential_not_singletonBox_representations_of_simplex (SingletonBoxRepresentationExclusions.lean) | Current checked19/20/24+75; explicit component and outer regularity, EqOn only the closed box, no added Q/normality/noUE/monotonicity |
| Thm3(3): exact coordinate-reset FTC; signed account≥c+λᵀRz≥c at EVERY actual minimum | Math.coordinatePartial_reset_eq_sub_integral; Math.signedMixedCurvatureAccount_at_every_box_minimum (CoordinateResetFTC.lean; SignedMixedCurvatureAccount.lean); GameTheory.quittingSingletonBox_coordinatePartial_reset_eq_sub_integral (RobustPotentialMixedCurvature.lean); quittingRobustPotentialWithCharge_mixedCurvature at coefficient1 (RobustPotentialChargeScale.lean) | Current checked core plus checked58; λ is the partial only on lower-binding coordinates, genuine upper minima allowed |
| Thm3(4): attained actual off-diagonal max and bound c/((n−1)W²) | Math.exists_box_mixed_curvature_max_ge_of_face_drift (MixedCurvatureSupBound.lean); GameTheory.quittingRobustPotentialWithCharge_mixedCurvature at coefficient1 (RobustPotentialChargeScale.lean) | Current checked core/58; internally selected point and distinct indices, arbitrary finite n≥2, no standard-Q premise here |
| Thm3(5): actual attained least-Hessian minimum≤−c/A, internal A>0 and M>0 simplification | GameTheory.quittingPositiveFaceCurvatureBudget_pos_of_standardQ; quittingPositiveFaceCurvatureBudget_le; quittingRobustPotential_negativeHessianEigenvalue_of_standardQ (RobustPotentialNegativeHessian.lean) | Current checked core; actual canonical Euclidean coordinateHessian, A=one-quarter max positive column squares; C² only on an open neighborhood of C, convexification uses face-only Thm2 |
| Thm4: ONE rational exact source-Nash solo rejection, actual successor, positive absorption=h, drop<3h/4 | GameTheory.exists_rational_exact_solo_rejection_of_standardQ_quasiconvex (RationalExactSoloRejection.lean) | 36→38→canonical Bernoulli overlay→42; same rational polynomial, rational table/bound, exact owner face retained, source/successor in K; no supplied face/rate/minimum |
| Eq6: SAME selected rational expression/tolerance additionally not quasiconvex | GameTheory.quittingGame_noUniformPayoff_iff_noSureRoot_and_nonquasiconvex_rationalPotential (NonquasiconvexPolynomialForwardCharacterization.lean) | Current checked13; exact original normality, positive-singleton and reward-bound hypotheses; reverse forgets extra conjunct |
| Paragraph after Eq6: SAME expression/tolerance additionally nonseparable and quantitative signed/mixed/least-Hessian bounds | GameTheory.quittingGame_noUniformPayoff_iff_noSureRoot_and_nonseparable_rationalPotential (NonseparablePolynomialForwardCharacterization.lean); quittingGame_noUniformPayoff_iff_noSureRoot_and_quantitative_rationalPotential (QuantitativePolynomialForwardCharacterization.lean) | Current checked26/56A; actual Fin4 Q/simplex produced from noUE, no second candidate selection; every minimum retained |
| Eq7 and boundary5: printed coupled cubic, quasiconvex/nonconvex/nonadditive, actual derivatives and rational syntax | Math.CoupledCubicShape.potential_eq_printed; coordinatePartial_eq; coordinateMixedPartial_eq; quasiconvexOn; not_convexOn; not_exists_additive_eqOn; rationalExpression_eval (MathUE/Analysis/Examples/CoupledCubicShape.lean) | 48; arbitrary finite n≥2 and widths≥1, closed-box additive impossibility requires NO regularity of hypothetical components |
| Boundary1: corrected collision source(0,2/3), successor(0,1/4), exact endpoint indifference/Nash/absorption1/4; uncorrected point not Nash | GameTheory.CollisionAdjustedProbeBoundary.corrected_source; corrected_successor; corrected_endpoint_indifference; corrected_exact_nash; quarter_absorption; uncorrected_endpoints; uncorrected_not_nash (UniformEquilibrium/Quitting/Examples/CollisionAdjustedProbeBoundary.lean) | Renamed49; canonical actual collision probe reused, no one-stage⇒behavioral-equilibrium claim |
| Boundary2: EVERY0<h<1/2 cap2 frozen source, actual difference2−4h and successor2−3h boxed; unfrozen lift leaves box | GameTheory.CollisionAdjustedProbeBoundary.upper_two_fixture; frozen_source; unfrozen_upper_sources (UniformEquilibrium/Quitting/Examples/CollisionAdjustedProbeBoundary.lean) | Same renamed49; not merely its additional cap3 fixture |
| Boundary3: convex linear positive face drift but R not textbook Q | Math.NonQLinearFace.convexOn; face_drift_ge_one; negative_residual; not_standardQ (MathUE/Analysis/Examples/NonQLinearFace.lean) | 50; literal RHS−1 residual for EVERY nonnegative vector |
| Boundary4/6: ALL-root constants accepted with zero charge; positive exact charge P/κ delegation | GameTheory.constant_isQuittingFullExactRootPotentialWithCharge_zero; isQuittingFullExactRootPotentialWithCharge_iff_div (FullExactRootPotentialChargeScale.lean) | 54→Fréchet-domain API repair; same box/table/potential normalization, no affine reward transport |
| Boundary4: zero-table SOLO sure-quitter self-loop rejects EVERY potential | GameTheory.exists_zeroReward_solo_exact_charged_selfLoop; not_isQuittingFullExactRootPotential_zeroReward (UniformEquilibrium/Quitting/Examples/ExactRootPotentialPlayerCountBoundary.lean) | Renamed59→retargeted59A→retargeted public-solo-identity overlay; exact root identity explicitly retained |
| Boundary6: κ>0 robust c=κW/(W−τ), original P's signed/sup/spectral bounds, κ=0 constants | GameTheory.isQuittingRobustPotentialWithCharge_iff_div; quittingRobustPotentialWithCharge_singletonFace_fderiv_bounds; quittingRobustPotentialWithCharge_mixedCurvature; quittingRobustPotentialWithCharge_negativeHessianEigenvalue; constant_isQuittingRobustPotentialWithCharge_zero (RobustPotentialChargeScale.lean) | Current checked57/58; optional60 not needed |
| Boundary6: M=0 excludes textbook Q; no zero denominator in simplification | GameTheory.quittingPositiveFaceCurvatureBudget_pos_of_standardQ plus quittingPositiveFaceCurvatureBudget_le at bound0 (RobustPotentialNegativeHessian.lean) | Current canonical consequence A>0 and A≤0; no duplicate source-specific proof needed |
| Boundary7: ONE player rejects ALL functions at boxed actual singleton; EMPTY players every root has charge0 and constants satisfy exact/robust tests | GameTheory.exists_singlePlayer_singleton_exact_charged_selfLoop; not_isQuittingFullExactRootPotential_of_singlePlayer; quittingRootAbsorptionMass_eq_zero_of_isEmpty; constant_isQuittingFullExactRootPotential_of_isEmpty; constant_isQuittingRobustPotential_of_isEmpty (UniformEquilibrium/Quitting/Examples/ExactRootPotentialPlayerCountBoundary.lean) | Same renamed59 stack; no regularity/sign/shape premise and no supplied favorable root |
| Source all-Continue/zero-Never semantics and reverse consumer | GameTheory.quittingRootSuccessorPayoff_allContinueRoot_eq (UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanClockReduction.lean); quittingStationaryContinueMass_allContinueRoot (UniformEquilibrium/Quitting/Stationary/LiveMass.lean); isQuittingFullExactRootPotential_of_robustPotential (ExactRootPotentialRestriction.lean); quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential (PolynomialForwardCertificateCharacterization.lean) | Current owners reused, not copied; reverse characterization still has fixed payoff target before accuracy and all sufficiently long horizons/unrestricted behavioral deviations |

Theorem/proof sublemmas are covered by their owning checked declarations:
compact boundary minima, full sign classification, connected lower-boundary
image and internally derived one-sign outer derivative, exact reset integral,
positive-row/Q simplex production, canonical Hessian attainment and box-only
convexification. No favorable certificates have been appended to source inputs.
Representation regularity remains explicit; composite C¹ does not imply it.

## Exact next application order

Use ORDERED_APPLICATION_MANIFEST.json for immutable paths and SHA256 records.

1. Original36; original38; canonical Bernoulli38 overlay; original42.
   Then SOURCE_GROUP_IMPORTS.patch.
2. Original48; renamed49 ADD; original50; original54; its Fréchet-domain repair;
   renamed59 ADD; retargeted59A; retargeted59B public-solo identity.
   Then FIXTURE_GROUP_IMPORTS.patch.

The fixtures are independent against current checked owners, except the two
linear overlay stacks54→repair and59→59A→59B. Neither54 nor59 depends on the
other. The two umbrella patches are intentionally source-first then fixtures;
their exact base/result hashes are in the manifest. Root must check current
base hashes before application. If unrelated root imports advance, use the
recorded unique contexts and record the actual resulting hash rather than
pretending that the precomputed complete-file hash is unchanged.

DO NOT apply old49/59 in addition to renamed ADD payloads, nor the old-path59A/
public-solo overlays. All originals remain immutable.49 was changed ONLY by
literal replacement PotentialPacketCollisionBoundary→CollisionAdjustedProbeBoundary,
including module path and namespace.59's body is byte-identical: only its ADD
path changed. Retargeted overlays change ONLY that target path. Final59 body
therefore has the same reviewed final hash as the old-path reconstruction.
No theorem statements/proofs were changed by the renaming payloads.

## Root-owned retirement gates

Before applying the group, root's current shared-wave full gate must terminate.
Then check the exact42 target and the five fixture targets serially, inspect the
final source-scope harness, and run FINAL_GROUP_AXIOM_HARNESS.lean. That narrow
harness imports only the six consumers covering this group and audits every new
public fixture theorem and rational-interface/producer declaration. The old
immutable source-scope harness remains valid because42 was not renamed:
 /tmp/ue-rational-exact-rejection-stage-z6wdoL/SOURCE_SCOPE_HARNESS.lean.
Its hash is 7c49c0559edb41776f410aff0ae734b884e6b5bcae20e9a67f8c7aaada33e872.

Root owns umbrella application, exhaustive AxiomAudit regeneration, lexical
trust/import/duplicate/telescope/docs checks and the final shared full gate.
Retire the packet only after those actual checks PASS and source-current
declarations match this complete map; static review alone is not that seal.

No optional43/60, reflection-only approximate-search or paired fixture chain,
screened-root chain, or calendar library is a prerequisite for SHAPE retirement.
No denominator/runtime bound, complete decision algorithm, all-polynomial
exclusion, behavioral realization of continuation annotations, favorable
counterexample strategy, UE construction, return regeneration or calendar
completion is claimed. Those are not missing printed conclusions of this packet.

No shared writes, compiler/Lean/Lake, Git, caches, worktrees, children, warning
suppression, new mathematics or project-note edits were performed.
