import MathUE.LinearProgramming.PositiveInverseQuantitativePerturbation
import MathUE.DirectedTransport.FiniteInequality.Perturbation
import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseTables
import Mathlib.Tactic.Abel

/-! # Exact inverse and determinant margins on full guarded-crossed reward neighborhoods -/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

open Math.LinearProgramming QuittingLCPClassification
open scoped BigOperators Matrix.Norms.Operator

/-- The packet's printed induced norm of the literal inverse. -/
theorem sourceSingletonMatrix_inverse_operatorNorm : ‖sourceSingletonMatrix⁻¹‖ = 1 := by
  have hrow (row : Fin 4) : ∑ column, ‖sourceSingletonInverse row column‖ = 1 := by
    fin_cases row <;> norm_num [sourceSingletonInverse, Fin.sum_univ_succ]
  rw [sourceSingletonMatrix_inverse]
  apply le_antisymm
  · exact matrix_operator_norm_le_of_rowSum_le _ 1 (by norm_num) (fun row => (hrow row).le)
  · simpa only [hrow 0] using matrix_rowSum_le_operator_norm sourceSingletonInverse 0

/-- Changing raw reward coordinates by δ changes only three entries per singleton row,
with row-sum error at most the packet's `6δ`. -/
theorem singletonMatrix_change_operatorNorm_le_six_mul
    (center other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (error : ℝ)
    (hclose : ∀ terminal who, |other terminal who - center terminal who| ≤ error) :
    ‖quittingSingletonMatrix other - quittingSingletonMatrix center‖ ≤ 6 * error := by
  have hnonnegative : 0 ≤ error := (abs_nonneg _).trans
    (hclose ⟨{0}, Finset.singleton_nonempty 0⟩ 0)
  apply matrix_operator_norm_le_of_rowSum_le _ (6 * error) (by positivity)
  intro row
  have hentry (column : Fin 4) :
      ‖(quittingSingletonMatrix other - quittingSingletonMatrix center) row column‖ ≤
        2 * error := by
    rw [Real.norm_eq_abs]
    exact Maths.FiniteInequality.abs_sub_differences_le _ _ _ _ error
      (hclose _ _) (hclose _ _)
  have hdiagonal : (quittingSingletonMatrix other - quittingSingletonMatrix center) row row = 0 :=
    by simp [quittingSingletonMatrix]
  calc
    _ = ∑ column ∈ Finset.univ.erase row,
        ‖(quittingSingletonMatrix other - quittingSingletonMatrix center) row column‖ := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ row), hdiagonal, norm_zero, add_zero]
    _ ≤ ∑ _column ∈ Finset.univ.erase row, (2 * error) :=
      Finset.sum_le_sum (fun column _ => hentry column)
    _ = 6 * error := by
      simp [Finset.card_erase_of_mem (Finset.mem_univ row)]
      ring

/-- The same literal singleton matrix controls every full reward-table center realizing it. -/
theorem sourceSingletonMatrix_neighborhood
    (center other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hcenter : quittingSingletonMatrix center = sourceSingletonMatrix)
    (error : ℝ) (herror : error < 1 / 100)
    (hclose : ∀ terminal who, |other terminal who - center terminal who| ≤ error) :
    0 < (quittingSingletonMatrix other).det ∧
      (∀ row column, 0 < (quittingSingletonMatrix other)⁻¹ row column) ∧
      ‖(quittingSingletonMatrix other)⁻¹ - sourceSingletonMatrix⁻¹‖ ≤
        6 * error / (1 - 6 * error) := by
  let change := quittingSingletonMatrix other - sourceSingletonMatrix
  have hactual : sourceSingletonMatrix + change = quittingSingletonMatrix other := by
    dsimp [change]
    abel
  have hchange : ‖change‖ ≤ 6 * error := by
    simpa only [change, hcenter] using
      singletonMatrix_change_operatorNorm_le_six_mul center other error hclose
  have hsmall : 6 * error < 1 := by linarith
  have hdet : 0 < sourceSingletonMatrix.det := by rw [sourceSingletonMatrix_det]; norm_num
  have hnorm : ‖sourceSingletonMatrix⁻¹‖ ≤ 1 := sourceSingletonMatrix_inverse_operatorNorm.le
  have hinverse := norm_matrix_inverse_add_sub_le
    sourceSingletonMatrix change hdet.ne' hnorm (6 * error) hsmall hchange
  have hpositive := det_matrix_add_pos_of_inverse_norm_le_one
    sourceSingletonMatrix change hdet hnorm (6 * error) hsmall hchange
  rw [hactual] at hinverse hpositive
  refine ⟨hpositive, ?_, hinverse⟩
  intro row column
  have hentry := (matrix_entry_norm_le_operator_norm
    ((quittingSingletonMatrix other)⁻¹ - sourceSingletonMatrix⁻¹) row column).trans hinverse
  rw [Real.norm_eq_abs] at hentry
  have hgap : 6 * error / (1 - 6 * error) < 2 / 15 := by
    apply (div_lt_iff₀ (by linarith : 0 < 1 - 6 * error)).mpr
    linarith
  have hold : 2 / 15 ≤ sourceSingletonMatrix⁻¹ row column := by
    rw [sourceSingletonMatrix_inverse]
    fin_cases row <;> fin_cases column <;> norm_num [sourceSingletonInverse]
  have h := (abs_le.mp hentry).1
  change -(6 * error / (1 - 6 * error)) ≤
    (quittingSingletonMatrix other)⁻¹ row column - sourceSingletonMatrix⁻¹ row column at h
  linarith

/-- The half-table radius is literal, with every raw reward coordinate free. -/
theorem halfCeiling_inverse_neighborhood_of_coordinate_error
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (error : ℝ) (herror : error < 1 / 100)
    (hclose : ∀ terminal who, |other terminal who - halfCeilingReward terminal who| ≤ error) :
    0 < (quittingSingletonMatrix other).det ∧
      (∀ row column, 0 < (quittingSingletonMatrix other)⁻¹ row column) ∧
      ‖(quittingSingletonMatrix other)⁻¹ - sourceSingletonMatrix⁻¹‖ ≤
        6 * error / (1 - 6 * error) :=
  sourceSingletonMatrix_neighborhood halfCeilingReward other halfCeiling_singletonMatrix
    error herror hclose

/-- The unit-table radius reuses the same matrix and the same resolvent construction. -/
theorem unitCeiling_inverse_neighborhood_of_coordinate_error
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (error : ℝ) (herror : error < 1 / 1000)
    (hclose : ∀ terminal who, |other terminal who - unitCeilingReward terminal who| ≤ error) :
    0 < (quittingSingletonMatrix other).det ∧
      (∀ row column, 0 < (quittingSingletonMatrix other)⁻¹ row column) ∧
      ‖(quittingSingletonMatrix other)⁻¹ - sourceSingletonMatrix⁻¹‖ ≤
        6 * error / (1 - 6 * error) :=
  sourceSingletonMatrix_neighborhood unitCeilingReward other unitCeiling_singletonMatrix
    error (by linarith) hclose

end GameTheory.GuardedCrossedResponseExamples
