import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientNormalCompletion
import UniformEquilibrium.Quitting.Examples.BlockPair.FourPlayerPairedSingleton
import MathUE.LinearProgramming.NonnegativeInverseDegree
import MathUE.LinearProgramming.PositiveInverseR0
import MathUE.LinearProgramming.Examples.PositiveInverseFourMatrices

/-! # The literal three-coordinate response quotient of the paired matrix -/

noncomputable section

namespace GameTheory
namespace PairedResponseQuotient

open Math.LinearProgramming QuittingLCPClassification
open FourPlayerPairedSingleton

/-- The paired owners share coordinate zero; players two and three retain
their own coordinates. -/
def block : Fin 4 → Fin 3 := ![0, 0, 1, 2]

/-- One literal original player in each block. -/
def representative : Fin 3 → Fin 4 := ![0, 2, 3]

theorem block_representative (coordinate : Fin 3) :
    block (representative coordinate) = coordinate := by
  fin_cases coordinate <;> rfl

/-- Row sums, not averages, give the quotient with a nonzero first diagonal. -/
def matrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![3, -1, -1; -2, 0, 3; -2, 3, 0]

theorem quotientMatrix_eq_of_pairedSingletonMatrix
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hmatrix : quittingSingletonMatrix reward = pairedSingletonMatrix) :
    quittingResponseQuotientMatrix reward block representative = matrix := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [quittingResponseQuotientMatrix, quittingSingletonBlockRowSum,
      block, representative, matrix, hmatrix, pairedSingletonMatrix,
      Fin.sum_univ_succ] <;> norm_num

theorem det_eq : matrix.det = -15 := by
  norm_num [matrix, Matrix.det_fin_three]

theorem det_neg : matrix.det < 0 := by
  rw [det_eq]
  norm_num

theorem inverse_eq : matrix⁻¹ = (1 / 15 : ℝ) •
    !![9, 3, 3; 6, 2, 7; 6, 7, 2] := by
  apply Matrix.inv_eq_left_inv
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [matrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem inverse_pos (row column : Fin 3) : 0 < matrix⁻¹ row column := by
  rw [inverse_eq]
  fin_cases row <;> fin_cases column <;> norm_num

theorem hasStrictlyPositiveInverse : HasStrictlyPositiveInverse matrix :=
  ⟨det_neg.ne, inverse_pos⟩

theorem isR0 : IsR0Matrix matrix :=
  isR0Matrix_of_strictlyPositiveInverse matrix hasStrictlyPositiveInverse

theorem degree_eq_neg_one : r0Degree matrix isR0 = -1 := by
  rw [r0Degree_eq_sign_det_of_nonnegative_inverse matrix isR0
    det_neg.ne (fun row column => (inverse_pos row column).le), sign_neg det_neg]
  rfl

theorem degree_ne_one : r0Degree matrix isR0 ≠ 1 := by
  rw [degree_eq_neg_one]
  norm_num

theorem fullMatrix_r0 : IsR0Matrix
    Math.LinearProgramming.PositiveInverseFourMatrices.Paired.matrix :=
  isR0Matrix_of_strictlyPositiveInverse _
    Math.LinearProgramming.PositiveInverseFourMatrices.Paired.hasStrictlyPositiveInverse

theorem fullMatrix_degree_eq_one :
    r0Degree Math.LinearProgramming.PositiveInverseFourMatrices.Paired.matrix
      fullMatrix_r0 = 1 := by
  let full := Math.LinearProgramming.PositiveInverseFourMatrices.Paired.matrix
  have hdet := Math.LinearProgramming.PositiveInverseFourMatrices.Paired.det_pos
  have hinverse := Math.LinearProgramming.PositiveInverseFourMatrices.Paired.inverse_pos
  rw [r0Degree_eq_sign_det_of_nonnegative_inverse full fullMatrix_r0
    hdet.ne' (fun row column => (hinverse row column).le), sign_pos hdet]
  rfl

end PairedResponseQuotient
end GameTheory
