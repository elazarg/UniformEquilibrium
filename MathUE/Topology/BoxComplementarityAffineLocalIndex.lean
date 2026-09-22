import MathUE.Topology.BoxComplementarityCenteredMatrixLocalIndex
import MathUE.Topology.BoxComplementarityPositiveRescalingDegree

/-!
# Affine local index in a displayed root-centered chart

The ambient affine field `point ↦ matrix * (point - root)` is pulled back
through the literal box with endpoints `root - radius` and `root + radius`.
The actual inner ambient box has half that radius. Its pullback is exactly
the central counting region, and the pulled-back gain is a positive scalar
multiple of the centered matrix model. Thus its normalized integer degree
is the sign of the determinant, including dimension zero.

This affine calculation uses the existing counted centered model and
positive gain rescaling. It does not assert independence of arbitrary
ambient charts.
-/

noncomputable section

namespace Math

open Set Math.Topology

variable {n : ℕ}

/-- The literal affine field with its displayed root. -/
def affineRootField (matrix : Matrix (Fin n) (Fin n) ℝ) (root : Fin n → ℝ)
    (point : Fin n → ℝ) : Fin n → ℝ :=
  matrix.mulVec (point - root)

theorem continuous_affineRootField
    (matrix : Matrix (Fin n) (Fin n) ℝ) (root : Fin n → ℝ) :
    Continuous (affineRootField matrix root) :=
  continuous_const.matrix_mulVec (continuous_id.sub continuous_const)

/-- Positive radius supplies the actual chart's coordinate widths. -/
theorem affineRootBox_width (root : Fin n → ℝ) {radius : ℝ} (hradius : 0 < radius) :
    ∀ who, root who - radius < root who + radius := by
  intro who
  linarith

/-- The actual ambient affine problem in the displayed root-centered chart. -/
def affineRootProblem (matrix : Matrix (Fin n) (Fin n) ℝ) (root : Fin n → ℝ)
    (radius : ℝ) (hradius : 0 < radius) : BoxComplementarityProblem (Fin n) :=
  BoxComplementarityProblem.ofAmbientMap
    (fun who => root who - radius) (fun who => root who + radius)
    (affineRootBox_width root hradius) (affineRootField matrix root)
    (continuous_affineRootField matrix root).continuousOn

/-- The literal ambient counting box, strictly inside the source chart. -/
def affineRootRegion (root : Fin n → ℝ) (radius : ℝ) : Set (Fin n → ℝ) :=
  {point | ∀ who, root who - radius / 2 < point who ∧
    point who < root who + radius / 2}

/-- The centered chart has the displayed displacement from its root. -/
theorem rectangularCubePoint_affineRoot_sub (root : Fin n → ℝ) (radius : ℝ)
    (point : UnitCube (Fin n)) :
    rectangularCubePoint (fun who => root who - radius)
        (fun who => root who + radius) point - root =
      (2 * radius) • (fun who => (point who : ℝ) - 1 / 2) := by
  funext who
  dsimp [rectangularCubePoint, rectangularPoint]
  ring

/-- The actual affine pullback is a positive gain scaling of the counted model. -/
theorem affineRootProblem_eq_scaleGain
    (matrix : Matrix (Fin n) (Fin n) ℝ) (root : Fin n → ℝ)
    (radius : ℝ) (hradius : 0 < radius) :
    affineRootProblem matrix root radius hradius =
      (centeredMatrixProblem matrix).scaleGain (2 * radius) := by
  apply BoxComplementarityProblem.ext
  funext point who
  change -(matrix.mulVec
      (rectangularCubePoint (fun coordinate => root coordinate - radius)
        (fun coordinate => root coordinate + radius) point - root)) who =
    (2 * radius) * -(matrix.mulVec (fun coordinate => (point coordinate : ℝ) - 1 / 2)) who
  rw [rectangularCubePoint_affineRoot_sub, Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_neg]

/-- The inner ambient box pulls back to the actual central counting region. -/
theorem preimage_affineRootRegion (root : Fin n → ℝ)
    {radius : ℝ} (hradius : 0 < radius) :
    rectangularCubePoint (fun who => root who - radius)
        (fun who => root who + radius) ⁻¹' affineRootRegion root radius =
      diagonalCentralRegion n := by
  ext point
  change (∀ who, _ ∧ _) ↔ ∀ who, _ ∧ _
  constructor <;> intro hpoint who
  · have h := hpoint who
    dsimp [rectangularCubePoint, rectangularPoint] at h
    constructor <;> nlinarith
  · have h := hpoint who
    dsimp [rectangularCubePoint, rectangularPoint]
    constructor <;> nlinarith

/-- Nonsingularity derives isolation on the actual inner ambient box. -/
theorem isIsolating_affineRootProblem
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hnonsingular : matrix.det ≠ 0)
    (root : Fin n → ℝ) (radius : ℝ) (hradius : 0 < radius) :
    (affineRootProblem matrix root radius hradius).IsIsolating
      (rectangularCubePoint (fun who => root who - radius)
        (fun who => root who + radius) ⁻¹' affineRootRegion root radius) := by
  rw [affineRootProblem_eq_scaleGain, preimage_affineRootRegion root hradius]
  exact ((centeredMatrixProblem matrix).isIsolating_scaleGain_iff
    (mul_pos (by norm_num) hradius) _).mpr
      (isIsolating_centeredMatrix_centralRegion matrix hnonsingular)

/-- The affine local degree in this literal chart and isolating region is the
integer determinant sign. Both source and output scalar factors are positive. -/
theorem localDegree_affineRootProblem_eq_sign_det
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hnonsingular : matrix.det ≠ 0)
    (root : Fin n → ℝ) (radius : ℝ) (hradius : 0 < radius) :
    (affineRootProblem matrix root radius hradius).localDegree
      (rectangularCubePoint (fun who => root who - radius)
        (fun who => root who + radius) ⁻¹' affineRootRegion root radius)
      (isIsolating_affineRootProblem matrix hnonsingular root radius hradius) =
        (SignType.sign matrix.det : ℤ) := by
  have hdegree := (centeredMatrixProblem matrix).localDegree_scaleGain
    (mul_pos (by norm_num : (0 : ℝ) < 2) hradius)
    (diagonalCentralRegion n) (isIsolating_centeredMatrix_centralRegion matrix hnonsingular)
  rw [localDegree_centeredMatrix_eq_sign_det matrix hnonsingular] at hdegree
  simpa only [affineRootProblem_eq_scaleGain, preimage_affineRootRegion root hradius]
    using hdegree

end Math
