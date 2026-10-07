import UniformEquilibrium.Quitting.Examples.CrossedMatchingFixture
import MathUE.LinearProgramming.SupportTest
import MathUE.LinearProgramming.NonnegativeInverseDegree
import MathUE.LinearProgramming.CyclicChildSharedFixtureScreens

/-! # Actual singleton matrix and degree of the crossed-matching fixture

The matrix has degree one and a strictly positive inverse. These are source
properties, not obstructions to the uniform payoff already proved separately.
-/

noncomputable section

namespace GameTheory.CrossedMatchingFixture

open Math.LinearProgramming Math.CrossedMatching
open scoped Matrix

def matrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 249 / 40, -1, -1; 53 / 8, 0, -1, -1;
    -1, -1, 0, 53 / 8; -1, -1, 53 / 8, 0]

theorem projectiveMatrix_eq : quittingProjectiveLCPMatrix reward = matrix := by
  ext player owner
  fin_cases player <;> fin_cases owner <;>
    norm_num +decide [quittingProjectiveLCPMatrix, quittingProjectiveSingletonTerminal,
      reward, matrix, Math.FiniteCoalition.binaryCode_finFour]

theorem matrix_det : matrix.det = 33583397 / 20480 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [matrix, Matrix.det_fin_three, Fin.sum_univ_succ, Fin.succAbove,
    Matrix.submatrix]

def principalDeterminants : Fin 15 → ℝ :=
  ![0, 0, -13197 / 320, 0, -1, -1, 257 / 20, 0, -1, -1,
    257 / 20, -2809 / 64, 53 / 4, 53 / 4, 33583397 / 20480]

theorem principal_det_eq (row : Fin 15) :
    (matrix.toSquareBlockProp
      (fun who => who ∈ (Math.Finset.finFourCoalitionRowEquiv row).val)).det =
        principalDeterminants row := by
  classical
  let selected := (Math.Finset.finFourCoalitionRowEquiv row).val
  let selector : Fin 4 → ℝ := fun who => if who ∈ selected then 1 else 0
  have hpredicate (who : Fin 4) : who ∈ selected ↔ 0 < selector who := by
    dsimp only [selector]
    split_ifs <;> simp_all
  have hequal := (det_lcpSelectedMatrix matrix selector).trans
    (Matrix.equiv_block_det matrix hpredicate)
  have hfinite : Finset.Subtype.fintype selected =
      Subtype.fintype (fun who => who ∈ selected) := Subsingleton.elim _ _
  change (matrix.toSquareBlockProp (fun who => who ∈ selected)).det = _
  rw [hfinite, ← hequal, Matrix.det_succ_row_zero]
  fin_cases row <;>
    norm_num [selector, selected, principalDeterminants,
      Math.Finset.finFourCoalitionRowEquiv, Math.Finset.finFourCoalitionOfRow,
      lcpSelectedMatrix, matrix, Matrix.det_fin_three, Fin.sum_univ_succ,
      Fin.succAbove, Matrix.submatrix, Matrix.one_apply]

theorem principal_det_ne_zero (selected : Finset (Fin 4)) (hcard : 2 ≤ selected.card) :
    (matrix.toSquareBlockProp (fun who => who ∈ selected)).det ≠ 0 := by
  have hnonempty : selected.Nonempty := Finset.card_pos.mp (by omega)
  let row := Math.Finset.finFourCoalitionRowEquiv.symm ⟨selected, hnonempty⟩
  have hselected : (Math.Finset.finFourCoalitionRowEquiv row).val = selected := by
    exact congrArg Subtype.val (Math.Finset.finFourCoalitionRowEquiv.apply_symm_apply _)
  rw [← hselected, principal_det_eq]
  rw [← hselected] at hcard
  have hinventory : ∀ index : Fin 15,
      2 ≤ (Math.Finset.finFourCoalitionRowEquiv index).val.card →
        principalDeterminants index ≠ 0 := by
    intro index hlarge
    fin_cases index
    all_goals norm_num [Math.Finset.finFourCoalitionRowEquiv,
      Math.Finset.finFourCoalitionOfRow] at hlarge
    all_goals norm_num [principalDeterminants]
  exact hinventory row hcard

theorem negative_columns (column : Fin 4) : ∃ row : Fin 4, matrix row column < 0 := by
  refine ⟨scheduled column, ?_⟩
  fin_cases column <;> norm_num [scheduled, matrix]

theorem matrix_isR0 : IsR0Matrix matrix :=
  isR0Matrix_of_negative_columns_of_nonsingular_principals matrix
    negative_columns principal_det_ne_zero

theorem matrix_positive_inverse : HasStrictlyPositiveInverse matrix := by
  have hsigns : HasStrictMatchingSigns matrix := by
    rw [← projectiveMatrix_eq]
    exact rawSource.matchingSigns
  apply hasStrictlyPositiveInverse_of_matching_positive_vector matrix hsigns
    (fun _ => 1) (fun _ => by norm_num)
  intro player
  fin_cases player <;>
    norm_num [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem matrix_r0Degree_eq_one : r0Degree matrix matrix_isR0 = 1 := by
  rw [r0Degree_eq_sign_det_of_nonnegative_inverse matrix matrix_isR0
    matrix_positive_inverse.1 (fun row column => (matrix_positive_inverse.2 row column).le),
    matrix_det]
  norm_num

/-- Every distinct nonfavorite pair has the same literal harmful principal matrix. -/
theorem harmful_pair_matrix_eq (player partner : Fin 4)
    (hdistinct : partner ≠ player) (hfavorite : partner ≠ favorite player) :
    matrix.submatrix (![player, partner] : Fin 2 → Fin 4)
      (![player, partner] : Fin 2 → Fin 4) = !![0, -1; -1, 0] := by
  ext row column
  fin_cases player <;> fin_cases partner
  all_goals norm_num at hdistinct
  all_goals norm_num [favorite] at hfavorite
  all_goals fin_cases row <;> fin_cases column <;> norm_num [matrix, Matrix.submatrix]

theorem harmful_pair_isR0 (player partner : Fin 4)
    (hdistinct : partner ≠ player) (hfavorite : partner ≠ favorite player) :
    IsR0Matrix (matrix.submatrix (![player, partner] : Fin 2 → Fin 4)
      (![player, partner] : Fin 2 → Fin 4)) := by
  rw [harmful_pair_matrix_eq player partner hdistinct hfavorite,
    ← Math.CyclicChildJointPhase.SharedFixture.pairZeroThree_eq]
  exact Math.CyclicChildJointPhase.SharedFixture.pairZeroThree_isR0

theorem harmful_pair_negativeOffset_infeasible (player partner : Fin 4)
    (hdistinct : partner ≠ player) (hfavorite : partner ≠ favorite player) :
    ¬StandardLCPSolvable (matrix.submatrix (![player, partner] : Fin 2 → Fin 4)
      (![player, partner] : Fin 2 → Fin 4)) ![-1, -1] := by
  rw [harmful_pair_matrix_eq player partner hdistinct hfavorite,
    ← Math.CyclicChildJointPhase.SharedFixture.pairZeroThree_eq]
  exact Math.CyclicChildJointPhase.SharedFixture.pairZeroThree_negativeOffset_infeasible

theorem harmful_pair_not_standardQ (player partner : Fin 4)
    (hdistinct : partner ≠ player) (hfavorite : partner ≠ favorite player) :
    ¬IsStandardQ (matrix.submatrix (![player, partner] : Fin 2 → Fin 4)
      (![player, partner] : Fin 2 → Fin 4)) := by
  rw [harmful_pair_matrix_eq player partner hdistinct hfavorite,
    ← Math.CyclicChildJointPhase.SharedFixture.pairZeroThree_eq]
  exact Math.CyclicChildJointPhase.SharedFixture.pairZeroThree_not_standardQ

/-- Increasing-order indexing of the actual principal triple. -/
def tripleMatrix (omitted : Fin 4) : Matrix (Fin 3) (Fin 3) ℝ :=
  matrix.submatrix omitted.succAbove omitted.succAbove

theorem triple_inverse_diagonal_neg (omitted : Fin 4) (player : Fin 3) :
    (tripleMatrix omitted)⁻¹ player player < 0 := by
  rw [Matrix.inv_def]
  fin_cases omitted <;> fin_cases player <;>
    norm_num [tripleMatrix, matrix, Matrix.det_fin_three, Matrix.adjugate_fin_three,
      Matrix.submatrix, Fin.succAbove, Ring.inverse_eq_inv]

theorem triple_inverse_not_nonnegative (omitted : Fin 4) :
    ¬∀ row column, 0 ≤ (tripleMatrix omitted)⁻¹ row column := by
  intro hnonnegative
  exact (not_le_of_gt (triple_inverse_diagonal_neg omitted 0)) (hnonnegative 0 0)

theorem projectiveMatrix_harmful_pair_isR0 (player partner : Fin 4)
    (hdistinct : partner ≠ player) (hfavorite : partner ≠ favorite player) :
    IsR0Matrix (Matrix.submatrix (quittingProjectiveLCPMatrix reward)
      (![player, partner] : Fin 2 → Fin 4) (![player, partner] : Fin 2 → Fin 4)) := by
  rw [projectiveMatrix_eq]
  exact harmful_pair_isR0 player partner hdistinct hfavorite

theorem projectiveMatrix_harmful_pair_negativeOffset_infeasible (player partner : Fin 4)
    (hdistinct : partner ≠ player) (hfavorite : partner ≠ favorite player) :
    ¬StandardLCPSolvable (Matrix.submatrix (quittingProjectiveLCPMatrix reward)
      (![player, partner] : Fin 2 → Fin 4) (![player, partner] : Fin 2 → Fin 4)) ![-1, -1] := by
  rw [projectiveMatrix_eq]
  exact harmful_pair_negativeOffset_infeasible player partner hdistinct hfavorite

theorem projectiveMatrix_harmful_pair_not_standardQ (player partner : Fin 4)
    (hdistinct : partner ≠ player) (hfavorite : partner ≠ favorite player) :
    ¬IsStandardQ (Matrix.submatrix (quittingProjectiveLCPMatrix reward)
      (![player, partner] : Fin 2 → Fin 4) (![player, partner] : Fin 2 → Fin 4)) := by
  rw [projectiveMatrix_eq]
  exact harmful_pair_not_standardQ player partner hdistinct hfavorite

theorem projectiveMatrix_triple_inverse_diagonal_neg (omitted : Fin 4) (player : Fin 3) :
    (Matrix.submatrix (quittingProjectiveLCPMatrix reward)
      omitted.succAbove omitted.succAbove)⁻¹ player player < 0 := by
  rw [projectiveMatrix_eq]
  exact triple_inverse_diagonal_neg omitted player

theorem projectiveMatrix_triple_inverse_not_nonnegative (omitted : Fin 4) :
    ¬∀ row column, 0 ≤ (Matrix.submatrix (quittingProjectiveLCPMatrix reward)
      omitted.succAbove omitted.succAbove)⁻¹ row column := by
  rw [projectiveMatrix_eq]
  exact triple_inverse_not_nonnegative omitted

end GameTheory.CrossedMatchingFixture
