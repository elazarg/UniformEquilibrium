import MathUE.LinearProgramming.PositiveInverseOpenness

/-!
# Four-by-four matrices with strictly positive inverses and opposite determinant signs

The first zero-diagonal matrix has determinant minus three and maps a
nonnegative anchor with zero coordinates to a strictly positive inverse image.
The paired zero-diagonal matrix has determinant forty-five and a strictly
positive inverse. These are exact arithmetic fixtures; no game-semantic or
matrix-class comparison is asserted in this module.
-/

noncomputable section

namespace Math.LinearProgramming.PositiveInverseFourMatrices

namespace NegativeDeterminant

/-- The explicit strict-inverse matrix with negative determinant. -/
def matrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 2, 1, -3; -3, 0, 2, 3; -3, 2, 0, 2; 3, -3, -1, 0]

theorem diagonal_zero (i : Fin 4) : matrix i i = 0 := by
  fin_cases i <;> rfl

theorem det_eq : matrix.det = -3 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [matrix, Matrix.det_fin_three, Fin.sum_univ_succ, Fin.succAbove,
    Matrix.submatrix]

theorem det_neg : matrix.det < 0 := by
  rw [det_eq]
  norm_num

/-- The displayed inverse is certified by exact matrix multiplication. -/
theorem inverse_eq : matrix⁻¹ =
    !![6, 4 / 3, 7, 26 / 3; 5, 1, 6, 7; 3, 1, 3, 4; 4, 1, 5, 6] := by
  apply Matrix.inv_eq_left_inv
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [matrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem inverse_pos (row column : Fin 4) : 0 < matrix⁻¹ row column := by
  rw [inverse_eq]
  fin_cases row <;> fin_cases column <;> norm_num

theorem hasStrictlyPositiveInverse : HasStrictlyPositiveInverse matrix :=
  ⟨det_neg.ne, inverse_pos⟩

/-- A nonnegative test anchor with two zero coordinates. -/
def boundaryAnchor : Fin 4 → ℝ := ![0, 2, 0, 3]

theorem boundaryAnchor_nonnegative (i : Fin 4) : 0 ≤ boundaryAnchor i := by
  fin_cases i <;> norm_num [boundaryAnchor]

theorem boundaryAnchor_zero_coordinates : boundaryAnchor 0 = 0 ∧ boundaryAnchor 2 = 0 :=
  ⟨rfl, rfl⟩

/-- Zero coordinates in the anchor still give the displayed positive inverse image. -/
theorem inverse_mulVec_boundaryAnchor :
    matrix⁻¹.mulVec boundaryAnchor = ![86 / 3, 23, 14, 20] := by
  rw [inverse_eq]
  funext i
  fin_cases i <;>
    norm_num [boundaryAnchor, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem inverse_mulVec_boundaryAnchor_pos (i : Fin 4) :
    0 < matrix⁻¹.mulVec boundaryAnchor i := by
  rw [inverse_mulVec_boundaryAnchor]
  fin_cases i <;> norm_num

/-- Each row has a negative entry at this distinct coordinate. -/
def negativeBlocker : Fin 4 → Fin 4 := ![3, 0, 0, 1]

theorem negativeBlocker_ne (i : Fin 4) : negativeBlocker i ≠ i := by
  fin_cases i <;> decide

theorem negativeBlocker_entry (i : Fin 4) : matrix i (negativeBlocker i) < 0 := by
  fin_cases i <;> norm_num [negativeBlocker, matrix]

theorem row_one_negative_iff (column : Fin 4) : matrix 1 column < 0 ↔ column = 0 := by
  fin_cases column <;> norm_num [matrix]

theorem row_two_negative_iff (column : Fin 4) : matrix 2 column < 0 ↔ column = 0 := by
  fin_cases column <;> norm_num [matrix]

/-- Two different vertices have the same unique negative successor, which
excludes a negative Hamiltonian cycle under every relabeling. -/
theorem not_negative_hamiltonianCycle (order : Equiv.Perm (Fin 4)) :
    ¬∀ phase, matrix (order phase) (order (phase + 1)) < 0 := by
  intro hcycle
  have hone : order (order.symm 1 + 1) = 0 := by
    apply (row_one_negative_iff _).mp
    simpa only [order.apply_symm_apply] using hcycle (order.symm 1)
  have htwo : order (order.symm 2 + 1) = 0 := by
    apply (row_two_negative_iff _).mp
    simpa only [order.apply_symm_apply] using hcycle (order.symm 2)
  have hsame : order.symm 1 = order.symm 2 :=
    add_right_cancel (order.injective (hone.trans htwo.symm))
  have himpossible : (1 : Fin 4) = 2 := order.symm.injective hsame
  norm_num at himpossible

/-- A covering six-edge closed walk, with repeated owners zero and three. -/
def coveringWalk : Fin 6 → Fin 4 := ![0, 3, 1, 0, 3, 2]

theorem coveringWalk_edge_negative (phase : Fin 6) :
    matrix (coveringWalk phase) (coveringWalk (phase + 1)) < 0 := by
  fin_cases phase <;> norm_num [coveringWalk, matrix]

theorem coveringWalk_surjective : Function.Surjective coveringWalk := by
  intro player
  fin_cases player
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨1, rfl⟩

end NegativeDeterminant

namespace Paired

/-- The paired strict-inverse matrix with positive determinant. -/
def matrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 3, -1, -1; 3, 0, -1, -1; -1, -1, 0, 3; -1, -1, 3, 0]

theorem diagonal_zero (i : Fin 4) : matrix i i = 0 := by
  fin_cases i <;> rfl

theorem det_eq : matrix.det = 45 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [matrix, Matrix.det_fin_three, Fin.sum_univ_succ, Fin.succAbove,
    Matrix.submatrix]

theorem det_pos : 0 < matrix.det := by
  rw [det_eq]
  norm_num

/-- Diagonal entries are two fifteenths, partner entries seven fifteenths,
and cross-pair entries one fifth. -/
theorem inverse_eq : matrix⁻¹ = (1 / 15 : ℝ) •
    !![2, 7, 3, 3; 7, 2, 3, 3; 3, 3, 2, 7; 3, 3, 7, 2] := by
  apply Matrix.inv_eq_left_inv
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [matrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem inverse_pos (row column : Fin 4) : 0 < matrix⁻¹ row column := by
  rw [inverse_eq]
  fin_cases row <;> fin_cases column <;> norm_num

theorem hasStrictlyPositiveInverse : HasStrictlyPositiveInverse matrix :=
  ⟨det_pos.ne', inverse_pos⟩

end Paired

end Math.LinearProgramming.PositiveInverseFourMatrices
