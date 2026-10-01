import MathUE.LinearProgramming.NonnegativeInverseDegree
import Mathlib.Tactic.FinCases

/-! # A two-coordinate swap: unique inhomogeneous root without R0

The actual offset-minus-one root follows from the canonical nonnegative-inverse
theorem. The separate homogeneous witness shows that this uniqueness does not
imply R0; no degree is assigned to this non-R0 matrix.
-/

noncomputable section

namespace Math.LinearProgramming.SwapTwoNonnegativeInverse

def matrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem det_eq : matrix.det = -1 := by
  norm_num [matrix, Matrix.of_apply, Matrix.det_fin_two]

theorem inverse_eq : matrix⁻¹ = matrix := by
  apply Matrix.inv_eq_left_inv
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [matrix, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem inverse_nonnegative (row column : Fin 2) : 0 ≤ matrix⁻¹ row column := by
  rw [inverse_eq]
  fin_cases row <;> fin_cases column <;> norm_num [matrix, Matrix.of_apply]

theorem inverse_mulVec_one : matrix⁻¹.mulVec (1 : Fin 2 → ℝ) = 1 := by
  rw [inverse_eq]
  ext who
  fin_cases who <;> norm_num [matrix, Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The unique actual LCP root at minus one, without any R0 premise. -/
theorem isStandardLCPSolution_neg_one_iff (root : Fin 2 → ℝ) :
    IsStandardLCPSolution matrix (-1) root ↔ root = 1 := by
  rw [isStandardLCPSolution_neg_one_iff_of_nonnegative_inverse matrix
    (by rw [det_eq]; norm_num) inverse_nonnegative, inverse_mulVec_one]

theorem firstCoordinate_residual :
    lcpResidual matrix 0 ![1, 0] = ![0, 1] := by
  ext who
  fin_cases who <;> norm_num [lcpResidual, matrix, Matrix.of_apply, Fin.sum_univ_succ]

theorem firstCoordinate_isStandardLCPSolution :
    IsStandardLCPSolution matrix 0 ![1, 0] := by
  refine ⟨?_, ?_, ?_⟩
  · intro who
    fin_cases who <;> norm_num
  · intro who
    rw [firstCoordinate_residual]
    fin_cases who <;> norm_num
  · intro who
    rw [firstCoordinate_residual]
    fin_cases who <;> norm_num

theorem firstCoordinate_ne_zero : (![1, 0] : Fin 2 → ℝ) ≠ 0 := by
  intro hzero
  have h := congrFun hzero 0
  norm_num at h

theorem not_isR0Matrix : ¬IsR0Matrix matrix := by
  intro hR0
  have hzero := hR0 ![1, 0] firstCoordinate_isStandardLCPSolution (0 : Fin 2)
  norm_num at hzero

end Math.LinearProgramming.SwapTwoNonnegativeInverse
