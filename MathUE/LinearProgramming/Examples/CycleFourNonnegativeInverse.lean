import MathUE.LinearProgramming.NonnegativeInverseDegree
import MathUE.LinearProgramming.NonnegativeInverseApproximation

/-!
# A unique regular test root without R0

The positive four-cycle permutation matrix has determinant minus one and a
nonnegative inverse. Its LCP at minus one has exactly the all-ones root.
Nevertheless the first coordinate vector is a nonzero homogeneous root.
Thus uniqueness at the regular test offset does not supply R0.

The literal perturbation by one twentieth of the off-diagonal-ones matrix
has a strictly positive inverse. Four entries remain zero through the first
inverse correction, and the second-order cumulative correction is positive.
-/

noncomputable section

namespace Math.LinearProgramming.CycleFourNonnegativeInverse

open Set Math.Topology Math.LinearAlgebra

def matrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0]

theorem diagonal_zero (who : Fin 4) : matrix who who = 0 := by
  fin_cases who <;> rfl

theorem det_eq : matrix.det = -1 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [matrix, Matrix.det_fin_three, Fin.sum_univ_succ, Fin.succAbove,
    Matrix.submatrix]

theorem inverse_eq : matrix⁻¹ = matrix.transpose := by
  apply Matrix.inv_eq_left_inv
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [matrix, Matrix.transpose_apply, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.one_apply]

theorem inverse_nonnegative (row column : Fin 4) : 0 ≤ matrix⁻¹ row column := by
  rw [inverse_eq]
  fin_cases row <;> fin_cases column <;> norm_num [matrix, Matrix.transpose_apply]

/-- The entire actual root set at minus one is a singleton. -/
theorem isStandardLCPSolution_neg_one_iff (root : Fin 4 → ℝ) :
    IsStandardLCPSolution matrix (-1) root ↔ root = 1 := by
  rw [isStandardLCPSolution_neg_one_iff_of_nonnegative_inverse matrix
    (by rw [det_eq]; norm_num) inverse_nonnegative]
  have hroot : matrix⁻¹.mulVec (1 : Fin 4 → ℝ) = 1 := by
    rw [inverse_eq]
    funext who
    fin_cases who <;>
      norm_num [matrix, Matrix.transpose_apply, Matrix.mulVec, Fin.sum_univ_succ,
        Matrix.vecHead, Matrix.vecTail, dotProduct, Pi.one_apply]
  rw [hroot]

/-- The actual all-ones root at minus one has a local isolating box of degree minus one. -/
theorem exists_box_localDegree_at_allOnes_eq_neg_one :
    ∃ (radius : ℝ) (hradius : 0 < radius),
      ∃ hisolating :
        (lcpMinBoxProblem matrix (-1) (1 : Fin 4 → ℝ) radius hradius).IsIsolating
          (rectangularCubePoint
            (fun who => (1 : Fin 4 → ℝ) who - radius)
            (fun who => (1 : Fin 4 → ℝ) who + radius) ⁻¹'
              affineRootRegion (1 : Fin 4 → ℝ) radius),
        (lcpMinBoxProblem matrix (-1) (1 : Fin 4 → ℝ) radius hradius).localDegree
          (rectangularCubePoint
            (fun who => (1 : Fin 4 → ℝ) who - radius)
            (fun who => (1 : Fin 4 → ℝ) who + radius) ⁻¹'
              affineRootRegion (1 : Fin 4 → ℝ) radius) hisolating = -1 := by
  have hroot : IsStandardLCPSolution matrix (-1) (1 : Fin 4 → ℝ) :=
    (isStandardLCPSolution_neg_one_iff 1).2 rfl
  have hstrict : ∀ who, (1 : Fin 4 → ℝ) who = 0 →
      0 < lcpResidual matrix (-1) (1 : Fin 4 → ℝ) who := by
    intro who hzero
    norm_num at hzero
  have hselected : lcpSelectedMatrix matrix (1 : Fin 4 → ℝ) = matrix := by
    ext who coordinate
    simp [lcpSelectedMatrix]
  have hactiveDet :
      (matrix.toSquareBlockProp (fun who => 0 < (1 : Fin 4 → ℝ) who)).det = -1 := by
    calc
      _ = (lcpSelectedMatrix matrix (1 : Fin 4 → ℝ)).det :=
        (det_lcpSelectedMatrix matrix 1).symm
      _ = matrix.det := congrArg Matrix.det hselected
      _ = -1 := det_eq
  obtain ⟨radius, hradius, hisolating, hdegree⟩ :=
    hroot.exists_box_localDegree_eq_sign_det hstrict (by rw [hactiveDet]; norm_num)
  refine ⟨radius, hradius, hisolating, ?_⟩
  rw [hactiveDet] at hdegree
  norm_num at hdegree
  exact hdegree

/-- A literal nonzero homogeneous complementary vector. -/
theorem firstCoordinate_isStandardLCPSolution :
    IsStandardLCPSolution matrix 0 ![1, 0, 0, 0] := by
  refine ⟨?_, ?_, ?_⟩ <;> intro who <;> fin_cases who <;>
    norm_num [lcpResidual, matrix, Fin.sum_univ_succ]

theorem not_isR0Matrix : ¬IsR0Matrix matrix := by
  intro hR0
  have hzero := hR0 ![1, 0, 0, 0] firstCoordinate_isStandardLCPSolution (0 : Fin 4)
  norm_num at hzero

/-- The zero-diagonal-preserving perturbation at the exact parameter one twentieth. -/
def perturbedMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  matrix - (1 / 20 : ℝ) • offDiagonalOnes (Fin 4)

theorem perturbedMatrix_diagonal_zero (i : Fin 4) : perturbedMatrix i i = 0 := by
  simp [perturbedMatrix, offDiagonalOnes, diagonal_zero]

/-- The determinant remains negative at this explicit positive perturbation. -/
theorem perturbedMatrix_det_eq : perturbedMatrix.det = -129523 / 160000 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [perturbedMatrix, matrix, offDiagonalOnes, Matrix.det_fin_three,
    Fin.sum_univ_succ, Fin.succAbove, Matrix.submatrix]

theorem perturbedMatrix_det_neg : perturbedMatrix.det < 0 := by
  rw [perturbedMatrix_det_eq]
  norm_num

/-- Exact matrix multiplication certifies the displayed rational inverse. -/
theorem perturbedMatrix_inverse_eq : perturbedMatrix⁻¹ = (1 / 129523 : ℝ) •
    !![7240, 7580, 780, 136780; 136780, 7240, 7580, 780;
      780, 136780, 7240, 7580; 7580, 780, 136780, 7240] := by
  apply Matrix.inv_eq_left_inv
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [perturbedMatrix, matrix, offDiagonalOnes, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.one_apply]

theorem perturbedMatrix_inverse_pos (row column : Fin 4) :
    0 < perturbedMatrix⁻¹ row column := by
  rw [perturbedMatrix_inverse_eq]
  fin_cases row <;> fin_cases column <;> norm_num

theorem perturbedMatrix_hasStrictlyPositiveInverse :
    HasStrictlyPositiveInverse perturbedMatrix :=
  ⟨perturbedMatrix_det_neg.ne, perturbedMatrix_inverse_pos⟩

/-- All four opposite entries vanish both before and after the first correction. -/
theorem opposite_entries_inverse_and_first_correction_eq_zero (row : Fin 4) :
    matrix⁻¹ row (![2, 3, 0, 1] row) = 0 ∧
      (matrix⁻¹ * offDiagonalOnes (Fin 4) * matrix⁻¹) row (![2, 3, 0, 1] row) = 0 := by
  rw [inverse_eq]
  fin_cases row <;>
    norm_num [matrix, offDiagonalOnes, Matrix.transpose_apply, Matrix.mul_apply,
      Fin.sum_univ_succ]

/-- The zeroth and first corrections cannot give a strictly positive matrix. -/
theorem not_positive_inverse_add_first_correction :
    ¬HasStrictlyPositiveEntries
      (matrix⁻¹ + matrix⁻¹ * offDiagonalOnes (Fin 4) * matrix⁻¹) := by
  intro hpositive
  obtain ⟨hzero, hfirst⟩ := opposite_entries_inverse_and_first_correction_eq_zero 0
  have hentry := hpositive 0 2
  change 0 < matrix⁻¹ 0 2 + (matrix⁻¹ * offDiagonalOnes (Fin 4) * matrix⁻¹) 0 2 at hentry
  change matrix⁻¹ 0 2 = 0 at hzero
  change (matrix⁻¹ * offDiagonalOnes (Fin 4) * matrix⁻¹) 0 2 = 0 at hfirst
  rw [hzero, hfirst] at hentry
  norm_num at hentry

/-- The second correction fills every remaining entry in this exact boundary test. -/
theorem inverse_add_first_add_second_correction_pos :
    HasStrictlyPositiveEntries
      (matrix⁻¹ + matrix⁻¹ * offDiagonalOnes (Fin 4) * matrix⁻¹ +
        matrix⁻¹ * offDiagonalOnes (Fin 4) * matrix⁻¹ *
          offDiagonalOnes (Fin 4) * matrix⁻¹) := by
  intro row column
  rw [inverse_eq]
  fin_cases row <;> fin_cases column <;>
    norm_num [matrix, offDiagonalOnes, Matrix.transpose_apply, Matrix.mul_apply,
      Fin.sum_univ_succ]

end Math.LinearProgramming.CycleFourNonnegativeInverse
