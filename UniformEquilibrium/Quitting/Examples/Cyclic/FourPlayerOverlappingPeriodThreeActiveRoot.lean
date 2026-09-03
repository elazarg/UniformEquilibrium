import UniformEquilibrium.Quitting.Examples.Cyclic.FourPlayerOverlappingPeriodThreeMeanValueBound
import MathUE.Topology.RectangularPoincareMiranda
import UniformEquilibrium.Quitting.Examples.Cyclic.FourPlayerOverlappingPeriodThreePreconditioner

/-!
# Active-gap root for the overlapping-support period-three system

The supplied exact neighborhood bounds give strict cube-face signs for the
preconditioned field.  Poincare--Miranda supplies an interior root, and exact
nonsingularity of the preconditioner recovers all eight original gap zeroes.
-/

noncomputable section

namespace GameTheory.FourPlayerOverlappingPeriodThree

open Function Metric Set
open Math.Interval Math.Interval.RationalPolynomial

/-- Symmetric normalized cube for the eight active hazards. -/
def normalizedHazardCube : Set (HazardCoordinate → ℝ) :=
  Icc (fun _ => (-1 : ℝ)) (fun _ => 1)

/-- Symmetric normalized cube for the sixty independent reward coordinates. -/
def normalizedRewardParameterCube : Set (Fin 60 → ℝ) :=
  Icc (fun _ => (-1 : ℝ)) (fun _ => 1)

theorem leadingCoordinatePoint_mem_fullNormalizedCoordinateBox
    (point : HazardCoordinate → ℝ) (parameter : Fin 60 → ℝ)
    (hpoint : point ∈ normalizedHazardCube)
    (hparameter : parameter ∈ normalizedRewardParameterCube) :
    leadingCoordinatePoint point parameter ∈
      dyadicBoxSet fullNormalizedCoordinateBox := by
  change ∀ coordinate : Fin (8 + 60),
    (fullNormalizedCoordinateBox coordinate).Contains
      (leadingCoordinatePoint point parameter coordinate)
  intro coordinate
  rw [DyadicInterval.Contains, RationalInterval.Contains]
  norm_num [fullNormalizedCoordinateBox,
    DyadicInterval.toRationalInterval, DyadicInterval.scale,
    neighborhoodPrecision]
  refine Fin.addCases ?_ ?_ coordinate
  · intro input
    simpa [leadingCoordinatePoint] using
      And.intro (hpoint.1 input) (hpoint.2 input)
  · intro input
    simpa [leadingCoordinatePoint] using
      And.intro (hparameter.1 input) (hparameter.2 input)

theorem leadingCoordinatePoint_zero_mem_rewardParameterCenterBox
    (parameter : Fin 60 → ℝ)
    (hparameter : parameter ∈ normalizedRewardParameterCube) :
    leadingCoordinatePoint (0 : HazardCoordinate → ℝ) parameter ∈
      dyadicBoxSet rewardParameterCenterBox := by
  change ∀ coordinate : Fin (8 + 60),
    (rewardParameterCenterBox coordinate).Contains
      (leadingCoordinatePoint (0 : HazardCoordinate → ℝ)
        parameter coordinate)
  intro coordinate
  refine Fin.addCases ?_ ?_ coordinate
  · intro input
    rw [DyadicInterval.Contains, RationalInterval.Contains]
    norm_num [rewardParameterCenterBox, leadingCoordinatePoint,
      fullNormalizedCoordinateBox, DyadicInterval.toRationalInterval,
      DyadicInterval.ofInt, DyadicInterval.scale,
      neighborhoodPrecision]
  · intro input
    rw [DyadicInterval.Contains, RationalInterval.Contains]
    norm_num [rewardParameterCenterBox, leadingCoordinatePoint,
      fullNormalizedCoordinateBox, DyadicInterval.toRationalInterval,
      DyadicInterval.ofInt, DyadicInterval.scale,
      neighborhoodPrecision]
    exact And.intro (hparameter.1 input) (hparameter.2 input)

theorem dist_zero_le_one_of_mem_normalizedHazardCube
    (point : HazardCoordinate → ℝ)
    (hpoint : point ∈ normalizedHazardCube) :
    dist point (0 : HazardCoordinate → ℝ) ≤ 1 := by
  rw [dist_pi_le_iff zero_le_one]
  intro coordinate
  rw [Real.dist_eq]
  simpa using (abs_le.mpr
    (And.intro (hpoint.1 coordinate) (hpoint.2 coordinate)))

/-- The real preconditioned active-gap field at fixed reward parameters,
scaled by the inverse hazard radius. -/
def scaledPreconditionedActiveGapField
    (parameter : Fin 60 → ℝ)
    (point : HazardCoordinate → ℝ) (output : HazardCoordinate) : ℝ :=
  ((1 / hazardRadius : ℚ) : ℝ) *
    evalReal (leadingCoordinatePoint point parameter)
      (faceFieldExpression output)

theorem continuous_scaledPreconditionedActiveGapField
    (parameter : Fin 60 → ℝ) :
    Continuous (scaledPreconditionedActiveGapField parameter) := by
  apply continuous_pi
  intro output
  apply continuous_const.mul
  rw [continuous_iff_continuousAt]
  intro point
  exact (hasFDerivAt_evalReal_leadingCoordinatePoint
    (faceFieldExpression output) point parameter).continuousAt

theorem normalizedHazardDisplacement_evalReal_eq
    (parameter : Fin 60 → ℝ) (point : HazardCoordinate → ℝ)
    (output : HazardCoordinate) :
    evalReal (leadingCoordinatePoint point parameter)
        (normalizedHazardDisplacementExpression output) =
      point output - scaledPreconditionedActiveGapField parameter point output := by
  rw [evalReal_normalizedHazardDisplacementExpression]
  rw [show hazardVariableIndex output = Fin.castAdd 60 output by
    apply Fin.ext
    rfl]
  simp [leadingCoordinatePoint, scaledPreconditionedActiveGapField,
    evalReal_faceFieldExpression]

/-- Every choice of sixty normalized reward parameters in the cube admits an
interior normalized hazard point at which all eight active cleared gaps
vanish exactly. -/
theorem exists_interior_activeResidual_zero
    (parameter : Fin 60 → ℝ)
    (hparameter : parameter ∈ normalizedRewardParameterCube) :
    ∃ point ∈ normalizedHazardCube,
      (∀ coordinate, -1 < point coordinate ∧ point coordinate < 1) ∧
      ∀ coordinate,
        evalReal (leadingCoordinatePoint point parameter)
          (activeResidualExpression coordinate) = 0 := by
  have hfullCenter := leadingCoordinatePoint_mem_fullNormalizedCoordinateBox
    (0 : HazardCoordinate → ℝ) parameter
    (by exact ⟨fun _ => by norm_num, fun _ => by norm_num⟩) hparameter
  have hcenterParameter :=
    leadingCoordinatePoint_zero_mem_rewardParameterCenterBox
      parameter hparameter
  obtain ⟨point, hpoint, hinterior, hfieldZero⟩ :=
    Math.Topology.exists_symmetric_unit_cube_zero_of_displacement_bound
      (scaledPreconditionedActiveGapField parameter) ((5 : ℝ) / 6)
      (continuous_scaledPreconditionedActiveGapField parameter)
      (by norm_num) (by
        intro varying hvarying output
        rw [← normalizedHazardDisplacement_evalReal_eq]
        exact normalizedHazardDisplacement_abs_le_five_sixths
          output (0 : HazardCoordinate → ℝ) varying parameter
          hfullCenter
          (leadingCoordinatePoint_mem_fullNormalizedCoordinateBox
            varying parameter hvarying hparameter)
          hcenterParameter
          (dist_zero_le_one_of_mem_normalizedHazardCube varying hvarying))
  have hfaceZero : ∀ output,
      evalReal (leadingCoordinatePoint point parameter)
        (faceFieldExpression output) = 0 := by
    intro output
    have hscaled := hfieldZero output
    change ((1 / hazardRadius : ℚ) : ℝ) *
      evalReal (leadingCoordinatePoint point parameter)
        (faceFieldExpression output) = 0 at hscaled
    exact (mul_eq_zero.mp hscaled).resolve_left (by
      norm_num [hazardRadius])
  let residual : HazardCoordinate → ℝ := fun coordinate =>
    evalReal (leadingCoordinatePoint point parameter)
      (activeResidualExpression coordinate)
  have hpreconditioned :
      Matrix.mulVec
          (fun row column => (preconditioner row column : ℝ)) residual = 0 := by
    funext output
    have hzero := hfaceZero output
    rw [evalReal_faceFieldExpression] at hzero
    fin_cases output <;>
      simpa [Matrix.mulVec, dotProduct, residual,
        linearCombinationValue, hazardCoordinates, preconditioner,
        Fin.sum_univ_succ] using hzero
  have hresidual : residual = 0 := by
    apply realPreconditioner_mulVec_injective
    simpa using hpreconditioned
  refine ⟨point, hpoint, hinterior, ?_⟩
  intro coordinate
  exact congrFun hresidual coordinate

end GameTheory.FourPlayerOverlappingPeriodThree

end
