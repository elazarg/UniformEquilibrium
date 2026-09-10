import Research.Topology.BoxComplementarityDiagonalLocalIndex
import MathUE.LinearAlgebra.MatrixDiagonalDeterminantPath
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Local index of the centered nonsingular matrix model

The actual determinant-preserving path to a diagonal matrix gives a common
isolating homotopy on the fixed central region. Isolation uses only pointwise
injectivity, not a supplied solution identity or uniform inverse estimate.
This is not an arbitrary affine-chart or ambient Brouwer comparison.
-/

noncomputable section

namespace Math

open Classical Set

variable {n : ℕ}

/-- The literal negative centered matrix field on the reference cube. -/
def centeredMatrixProblem (matrix : Matrix (Fin n) (Fin n) ℝ) :
    BoxComplementarityProblem (Fin n) where
  gain point who := -(matrix.mulVec (fun coordinate => (point coordinate : ℝ) - 1 / 2)) who
  continuous_gain who := by
    have hcentered : Continuous (fun point : UnitCube (Fin n) =>
        fun coordinate => (point coordinate : ℝ) - 1 / 2) :=
      continuous_pi fun coordinate =>
        ((continuous_apply coordinate).subtype_val).sub continuous_const
    exact ((continuous_apply who).comp (continuous_const.matrix_mulVec hcentered)).neg

/-- For a nonsingular matrix, vanishing gain is exactly the displayed central point. -/
theorem centeredMatrixProblem_gain_eq_zero_iff
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hnonsingular : matrix.det ≠ 0)
    (point : UnitCube (Fin n)) :
    (centeredMatrixProblem matrix).gain point = 0 ↔ ∀ who, (point who : ℝ) = 1 / 2 := by
  have hinjective : Function.Injective matrix.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det matrix).mpr (isUnit_iff_ne_zero.mpr hnonsingular))
  constructor
  · intro hzero
    have hmul : matrix.mulVec (fun who => (point who : ℝ) - 1 / 2) = 0 := by
      funext who
      have hcoord := congrFun hzero who
      exact neg_eq_zero.mp hcoord
    have hvector := hinjective (hmul.trans (Matrix.mulVec_zero matrix).symm)
    intro who
    exact sub_eq_zero.mp (congrFun hvector who)
  · intro hcenter
    funext who
    simp only [centeredMatrixProblem, hcenter, sub_self]
    exact neg_eq_zero.mpr (congrFun (Matrix.mulVec_zero matrix) who)

/-- The diagonal matrix constructor gives exactly the previously counted diagonal problem. -/
theorem centeredMatrixProblem_diagonal (entries : Fin n → ℝ) :
    centeredMatrixProblem (Matrix.diagonal entries) = centeredDiagonalProblem entries := by
  apply BoxComplementarityProblem.ext
  funext point who
  simp only [centeredMatrixProblem, centeredDiagonalProblem, Matrix.mulVec_diagonal, neg_mul]

/-- Every nonsingular centered model has the same actual central isolating region. -/
theorem isIsolating_centeredMatrix_centralRegion
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hnonsingular : matrix.det ≠ 0) :
    (centeredMatrixProblem matrix).IsIsolating (diagonalCentralRegion n) := by
  refine ⟨isOpen_diagonalCentralRegion, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  rintro point ⟨hsolution, hfrontier⟩
  have hbounds := coordinate_bounds_of_mem_closure_diagonalCentralRegion
    (frontier_subset_closure hfrontier)
  have hinterior (who : Fin n) : 0 < (point who : ℝ) ∧ (point who : ℝ) < 1 := by
    have h := hbounds who
    constructor <;> linarith
  have hzero := (BoxComplementarityProblem.isSolution_iff_gain_eq_zero_of_coordinateInterior
    (centeredMatrixProblem matrix) point hinterior).mp hsolution
  have hcenter := (centeredMatrixProblem_gain_eq_zero_iff matrix hnonsingular point).mp hzero
  have hmem : point ∈ diagonalCentralRegion n := by
    intro who
    rw [hcenter who]
    norm_num
  have hnot : point ∉ interior (diagonalCentralRegion n) := hfrontier.2
  rw [isOpen_diagonalCentralRegion.interior_eq] at hnot
  exact hnot hmem

/-- A continuous matrix family gives an actual jointly continuous complementarity family. -/
theorem isContinuous_centeredMatrixFamily
    (family : Icc (0 : ℝ) 1 → Matrix (Fin n) (Fin n) ℝ) (hfamily : Continuous family) :
    IsContinuousBoxComplementarityFamily (Fin n) (fun parameter =>
      centeredMatrixProblem (family parameter)) := by
  intro who
  have hcentered : Continuous (fun data : Icc (0 : ℝ) 1 × UnitCube (Fin n) =>
      fun coordinate => (data.2 coordinate : ℝ) - 1 / 2) :=
    continuous_pi fun coordinate =>
      (((continuous_apply coordinate).comp continuous_snd).subtype_val).sub continuous_const
  exact ((continuous_apply who).comp
    ((hfamily.comp continuous_fst).matrix_mulVec hcentered)).neg

/-- The actual centered nonsingular matrix model has normalized local degree equal
to the integer sign of its determinant. -/
theorem localDegree_centeredMatrix_eq_sign_det
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hnonsingular : matrix.det ≠ 0) :
    (centeredMatrixProblem matrix).localDegree (diagonalCentralRegion n)
      (isIsolating_centeredMatrix_centralRegion matrix hnonsingular) =
        (SignType.sign matrix.det : ℤ) := by
  obtain ⟨entries, path, hdet, hnonzero⟩ :=
    LinearAlgebra.exists_path_diagonal_det_ne_zero matrix hnonsingular
  have hdiagonalDet : (Matrix.diagonal entries).det = matrix.det := by
    simpa only [Path.target] using hdet 1
  have hentries : ∀ who, entries who ≠ 0 := by
    have hproduct : (∏ who, entries who) ≠ 0 := by
      rw [← Matrix.det_diagonal]
      exact hdiagonalDet.trans_ne hnonsingular
    exact fun who => (Finset.prod_ne_zero_iff.mp hproduct) who (Finset.mem_univ who)
  have hcontinuous := isContinuous_centeredMatrixFamily path path.continuous
  have hisolating := fun parameter =>
    isIsolating_centeredMatrix_centralRegion (path parameter) (hnonzero parameter)
  have hdegree := hcontinuous.localDegree_endpoints_eq (diagonalCentralRegion n) hisolating
  have hequal :
      (centeredMatrixProblem matrix).localDegree (diagonalCentralRegion n)
        (isIsolating_centeredMatrix_centralRegion matrix hnonsingular) =
      (centeredDiagonalProblem entries).localDegree (diagonalCentralRegion n)
        (isIsolating_centeredDiagonal_centralRegion entries hentries) := by
    simpa only [Path.source, Path.target, centeredMatrixProblem_diagonal] using hdegree
  rw [hequal, localDegree_centeredDiagonal_eq_sign_det entries hentries, hdiagonalDet]

end Math
