import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseStrategic
import MathUE.LinearProgramming.NonnegativeInverseDegree
import MathUE.LinearProgramming.PositiveInverseR0

/-! # Literal row-swap inverse and degree for the crossed singleton matrix -/

noncomputable section

namespace GameTheory

open Math.LinearProgramming QuittingLCPClassification

variable {n : ℕ}

theorem quittingCrossedSingletonMatrix_eq_submatrix
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) :
    quittingCrossedSingletonMatrix reward first second =
      (quittingSingletonMatrix reward).submatrix (Equiv.swap first second) id := by
  rfl

/-- Swapping payoff-recipient rows swaps the columns of the actual inverse. -/
theorem quittingCrossedSingletonMatrix_inverse_eq
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) :
    (quittingCrossedSingletonMatrix reward first second)⁻¹ =
      (quittingSingletonMatrix reward)⁻¹.submatrix id (Equiv.swap first second) := by
  rw [quittingCrossedSingletonMatrix_eq_submatrix]
  simpa [Equiv.refl_apply] using
    Matrix.inv_submatrix_equiv (quittingSingletonMatrix reward)
      (Equiv.swap first second) (Equiv.refl (Fin n))

/-- One exchange of distinct recipient rows reverses the singleton determinant. -/
theorem quittingCrossedSingletonMatrix_det_eq_neg
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (hdistinct : first ≠ second) :
    (quittingCrossedSingletonMatrix reward first second).det =
      -(quittingSingletonMatrix reward).det := by
  rw [quittingCrossedSingletonMatrix_eq_submatrix,
    Matrix.det_permute (Equiv.swap first second), Equiv.Perm.sign_swap hdistinct]
  norm_num

/-- Strict positivity of the full inverse gives the crossed R0 index `−1`. -/
theorem quittingCrossedSingletonMatrix_r0_degree_neg_one_of_positiveInverse
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (hdistinct : first ≠ second)
    (hdet : 0 < (quittingSingletonMatrix reward).det)
    (hinverse : ∀ row column, 0 < (quittingSingletonMatrix reward)⁻¹ row column) :
    ∃ hR0 : IsR0Matrix (quittingCrossedSingletonMatrix reward first second),
      r0Degree (quittingCrossedSingletonMatrix reward first second) hR0 = -1 := by
  let crossed := quittingCrossedSingletonMatrix reward first second
  have hdetCrossed : crossed.det < 0 := by
    rw [quittingCrossedSingletonMatrix_det_eq_neg reward first second hdistinct]
    linarith
  have hinverseCrossed : ∀ row column, 0 < crossed⁻¹ row column := by
    intro row column
    rw [quittingCrossedSingletonMatrix_inverse_eq]
    exact hinverse row ((Equiv.swap first second) column)
  have hR0 : IsR0Matrix crossed :=
    isR0Matrix_of_strictlyPositiveInverse crossed
      ⟨hdetCrossed.ne, hinverseCrossed⟩
  refine ⟨hR0, ?_⟩
  rw [r0Degree_eq_sign_det_of_nonnegative_inverse crossed hR0 hdetCrossed.ne
    (fun row column => (hinverseCrossed row column).le), sign_neg hdetCrossed]
  rfl

/-- The same raw inverse hypothesis gives the full unswapped matrix degree `+1`. -/
theorem quittingSingletonMatrix_r0_degree_one_of_positiveInverse
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (hdet : 0 < (quittingSingletonMatrix reward).det)
    (hinverse : ∀ row column, 0 < (quittingSingletonMatrix reward)⁻¹ row column) :
    ∃ hR0 : IsR0Matrix (quittingSingletonMatrix reward),
      r0Degree (quittingSingletonMatrix reward) hR0 = 1 := by
  let matrix := quittingSingletonMatrix reward
  have hR0 : IsR0Matrix matrix :=
    isR0Matrix_of_strictlyPositiveInverse matrix ⟨hdet.ne', hinverse⟩
  refine ⟨hR0, ?_⟩
  rw [r0Degree_eq_sign_det_of_nonnegative_inverse matrix hR0 hdet.ne'
    (fun row column => (hinverse row column).le), sign_pos hdet]
  rfl

end GameTheory
