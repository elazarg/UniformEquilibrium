import MathUE.LinearProgramming.CyclicChildSharedFixture

/-! # Literal matrix screens for the shared cyclic-child fixture

These are exact failures of the displayed matrix hypotheses. They do not
exclude every possible equilibrium construction using a different criterion.
-/

noncomputable section

namespace Math.CyclicChildJointPhase.SharedFixture

open Matrix Math.LinearProgramming

def childWithout (deleted : Fin 4) : Matrix (Fin 3) (Fin 3) ℝ :=
  matrix.submatrix deleted.succAbove deleted.succAbove

theorem childWithout_zero_eq : childWithout 0 = childMatrix 2 2 2 := by
  funext receiver owner
  fin_cases receiver <;> fin_cases owner <;> rfl

theorem childWithout_zero_inverse_pos (receiver owner : Fin 3) :
    0 < (childWithout 0)⁻¹ receiver owner := by
  rw [childWithout_zero_eq, child_inverse]
  fin_cases receiver <;> fin_cases owner <;> norm_num

theorem childWithout_three_inverse_entry : (childWithout 3)⁻¹ 0 0 = -2 := by
  rw [Matrix.inv_def]
  norm_num [childWithout, matrix_eq, Matrix.det_fin_three, Matrix.adjugate_fin_three,
    Matrix.submatrix, Fin.succAbove, Ring.inverse_eq_inv]

theorem childWithout_two_inverse_entry : (childWithout 2)⁻¹ 0 0 = -2 / 3 := by
  rw [Matrix.inv_def]
  norm_num [childWithout, matrix_eq, Matrix.det_fin_three, Matrix.adjugate_fin_three,
    Matrix.submatrix, Fin.succAbove, Ring.inverse_eq_inv]

theorem childWithout_one_inverse_entry : (childWithout 1)⁻¹ 0 1 = -2 / 3 := by
  rw [Matrix.inv_def]
  norm_num [childWithout, matrix_eq, Matrix.det_fin_three, Matrix.adjugate_fin_three,
    Matrix.submatrix, Fin.succAbove, Ring.inverse_eq_inv]

theorem only_nonnegative_child_inverse (deleted : Fin 4) :
    (∀ receiver owner, 0 ≤ (childWithout deleted)⁻¹ receiver owner) ↔ deleted = 0 := by
  constructor
  · intro hnonnegative
    fin_cases deleted
    · rfl
    · have h := hnonnegative 0 1
      change 0 ≤ (childWithout 1)⁻¹ 0 1 at h
      rw [childWithout_one_inverse_entry] at h
      norm_num at h
    · have h := hnonnegative 0 0
      change 0 ≤ (childWithout 2)⁻¹ 0 0 at h
      rw [childWithout_two_inverse_entry] at h
      norm_num at h
    · have h := hnonnegative 0 0
      change 0 ≤ (childWithout 3)⁻¹ 0 0 at h
      rw [childWithout_three_inverse_entry] at h
      norm_num at h
  · rintro rfl receiver owner
    exact (childWithout_zero_inverse_pos receiver owner).le

theorem full_inverse_entry : matrix⁻¹ 0 2 = -5 / 7 := by
  rw [Matrix.inv_def, matrix_det]
  simp only [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix (n := 3) matrix 0 2]
  norm_num [matrix_eq, Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove]

theorem full_inverse_not_nonnegative : ¬∀ receiver owner, 0 ≤ matrix⁻¹ receiver owner := by
  intro hnonnegative
  have h := hnonnegative 0 2
  rw [full_inverse_entry] at h
  norm_num at h

def passiveInverseRow (deleted : Fin 4) : Fin 3 → ℝ :=
  (fun child => matrix deleted (deleted.succAbove child)) ᵥ* (childWithout deleted)⁻¹

theorem no_nonnegative_deleted_inverse_and_passive_row (deleted : Fin 4) :
    ¬((∀ receiver owner, 0 ≤ (childWithout deleted)⁻¹ receiver owner) ∧
      ∀ child, 0 ≤ passiveInverseRow deleted child) := by
  rintro ⟨hinverse, hrow⟩
  have hdeleted := (only_nonnegative_child_inverse deleted).mp hinverse
  subst deleted
  have hpassive : passiveInverseRow 0 = ![-1 / 7, 5 / 7, 3 / 7] := by
    unfold passiveInverseRow
    rw [childWithout_zero_eq]
    have hroweq : (fun child : Fin 3 => matrix 0 ((0 : Fin 4).succAbove child)) =
        ![1, 1, -1] := by
      funext child
      fin_cases child <;> rfl
    rw [hroweq, pivot_row_inverse]
  have h := hrow 0
  rw [hpassive] at h
  norm_num at h

theorem no_positive_pair (first second : Fin 4) :
    ¬(0 < matrix first second ∧ 0 < matrix second first) := by
  fin_cases first <;> fin_cases second <;> norm_num [matrix_eq]

def pairZeroThree : Matrix (Fin 2) (Fin 2) ℝ := matrix.submatrix ![0, 3] ![0, 3]

theorem pairZeroThree_eq : pairZeroThree = !![0, -1; -1, 0] := by
  funext receiver owner
  fin_cases receiver <;> fin_cases owner <;> norm_num [pairZeroThree, matrix_eq]

theorem pairZeroThree_isR0 : IsR0Matrix pairZeroThree := by
  intro weights hsolution who
  have hzero := hsolution.residual_nonneg 0
  have hone := hsolution.residual_nonneg 1
  have hwzero := hsolution.weight_nonneg 0
  have hwone := hsolution.weight_nonneg 1
  norm_num [lcpResidual, pairZeroThree_eq, Fin.sum_univ_succ] at hzero hone
  fin_cases who
  · change weights 0 = 0
    linarith
  · change weights 1 = 0
    linarith

theorem pairZeroThree_negativeOffset_infeasible :
    ¬StandardLCPSolvable pairZeroThree ![-1, -1] := by
  rintro ⟨weights, hsolution⟩
  have hzero := hsolution.residual_nonneg 0
  have hwone := hsolution.weight_nonneg 1
  norm_num [lcpResidual, pairZeroThree_eq, Fin.sum_univ_succ] at hzero
  linarith

theorem pairZeroThree_not_standardQ : ¬IsStandardQ pairZeroThree := by
  intro hQ
  exact pairZeroThree_negativeOffset_infeasible (hQ ![-1, -1])

end Math.CyclicChildJointPhase.SharedFixture
