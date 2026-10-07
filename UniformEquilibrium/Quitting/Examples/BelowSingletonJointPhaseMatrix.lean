import UniformEquilibrium.Quitting.Examples.BelowSingletonJointPhaseFixture
import UniformEquilibrium.Quitting.Projective.SingletonLCP
import MathUE.LinearProgramming.SupportTest
import MathUE.LinearProgramming.NonnegativeInverseDegree
import MathUE.LinearProgramming.ColumnSumQ
import MathUE.LinearProgramming.PositiveInverseOpenness
import MathUE.LinearProgramming.CyclicChildSharedFixtureScreens

/-! # Actual singleton matrix of the below-singleton fixture

The full matrix is R0, standard Q and has a strictly positive inverse.
All its harmful pair restrictions are not standard Q. These matrix facts
do not obstruct the separately proved uniform-equilibrium payoff.
-/

noncomputable section

namespace GameTheory.BelowSingletonJointPhaseFixture

open Math.LinearProgramming Math.CrossedMatching
open scoped Matrix

def matrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 3, -1, -1; 3, 0, -1, -1; -1, -1, 0, 3; -1, -1, 3, 0]

theorem projectiveMatrix_eq : quittingProjectiveLCPMatrix reward = matrix := by
  ext player owner
  fin_cases player <;> fin_cases owner <;>
    norm_num +decide [quittingProjectiveLCPMatrix, quittingProjectiveSingletonTerminal,
      reward, matrix, Math.FiniteCoalition.binaryCode_finFour]

theorem matrix_det : matrix.det = 45 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [matrix, Matrix.det_fin_three, Fin.sum_univ_succ, Fin.succAbove,
    Matrix.submatrix]

def principalDeterminants : Fin 15 → ℝ :=
  ![0, 0, -9, 0, -1, -1, 6, 0, -1, -1, 6, -9, 6, 6, 45]

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
  have hselected : (Math.Finset.finFourCoalitionRowEquiv row).val = selected :=
    congrArg Subtype.val (Math.Finset.finFourCoalitionRowEquiv.apply_symm_apply _)
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

def inverseMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![2 / 15, 7 / 15, 1 / 5, 1 / 5; 7 / 15, 2 / 15, 1 / 5, 1 / 5;
    1 / 5, 1 / 5, 2 / 15, 7 / 15; 1 / 5, 1 / 5, 7 / 15, 2 / 15]

theorem matrix_inverse_eq : matrix⁻¹ = inverseMatrix := by
  apply Matrix.inv_eq_right_inv
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [matrix, inverseMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply]

theorem matrix_positive_inverse : HasStrictlyPositiveInverse matrix := by
  refine ⟨?_, ?_⟩
  · rw [matrix_det]
    norm_num
  · rw [matrix_inverse_eq]
    intro row column
    fin_cases row <;> fin_cases column <;> norm_num [inverseMatrix]

theorem matrix_r0Degree_eq_one : r0Degree matrix matrix_isR0 = 1 := by
  rw [r0Degree_eq_sign_det_of_nonnegative_inverse matrix matrix_isR0
    matrix_positive_inverse.1 (fun row column => (matrix_positive_inverse.2 row column).le),
    matrix_det]
  norm_num

theorem matrix_standardQ : IsStandardQ matrix := by
  apply isStandardQ_of_r0Degree_ne_zero matrix matrix_isR0
  rw [matrix_r0Degree_eq_one]
  norm_num

/-- Every distinct nonfavorite pair has the literal harmful principal matrix. -/
theorem harmful_pair_matrix_eq_of_not_favorite (player partner : Fin 4)
    (hdistinct : partner ≠ player) (hfavorite : partner ≠ favorite player) :
    matrix.submatrix (![player, partner] : Fin 2 → Fin 4)
      (![player, partner] : Fin 2 → Fin 4) = !![0, -1; -1, 0] := by
  ext row column
  fin_cases player <;> fin_cases partner
  all_goals norm_num at hdistinct
  all_goals norm_num [favorite] at hfavorite
  all_goals fin_cases row <;> fin_cases column <;> norm_num [matrix, Matrix.submatrix]

theorem harmful_pair_not_standardQ_of_not_favorite (player partner : Fin 4)
    (hdistinct : partner ≠ player) (hfavorite : partner ≠ favorite player) :
    ¬IsStandardQ (matrix.submatrix (![player, partner] : Fin 2 → Fin 4)
      (![player, partner] : Fin 2 → Fin 4)) := by
  rw [harmful_pair_matrix_eq_of_not_favorite player partner hdistinct hfavorite]
  apply not_isStandardQ_of_forall_column_sum_nonpos
  intro column
  fin_cases column <;> norm_num [Fin.sum_univ_succ]

theorem harmful_pair_isR0_of_not_favorite (player partner : Fin 4)
    (hdistinct : partner ≠ player) (hfavorite : partner ≠ favorite player) :
    IsR0Matrix (matrix.submatrix (![player, partner] : Fin 2 → Fin 4)
      (![player, partner] : Fin 2 → Fin 4)) := by
  rw [harmful_pair_matrix_eq_of_not_favorite player partner hdistinct hfavorite,
    ← Math.CyclicChildJointPhase.SharedFixture.pairZeroThree_eq]
  exact Math.CyclicChildJointPhase.SharedFixture.pairZeroThree_isR0

def eigenvectors : Fin 4 → Fin 4 → ℝ :=
  ![![1, 1, 1, 1], ![1, 1, -1, -1], ![1, -1, 0, 0], ![0, 0, 1, -1]]

def eigenvalues : Fin 4 → ℝ := ![1, 5, -3, -3]

theorem matrix_mulVec_eigenvector (index : Fin 4) :
    matrix.mulVec (eigenvectors index) = eigenvalues index • eigenvectors index := by
  funext player
  fin_cases index <;> fin_cases player <;>
    norm_num [matrix, eigenvectors, eigenvalues, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Pi.smul_apply, smul_eq_mul]

theorem eigenvectors_ne_zero (index : Fin 4) : eigenvectors index ≠ 0 := by
  intro hzero
  have hfirst := congrFun hzero 0
  have hthird := congrFun hzero 2
  fin_cases index
  all_goals norm_num [eigenvectors] at hfirst
  all_goals norm_num [eigenvectors] at hthird

/-- Every triple is indexed by the omitted player in increasing order. -/
def tripleMatrix (omitted : Fin 4) : Matrix (Fin 3) (Fin 3) ℝ :=
  matrix.submatrix omitted.succAbove omitted.succAbove

def tripleInverseMatrix (omitted : Fin 4) : Matrix (Fin 3) (Fin 3) ℝ :=
  if omitted.val < 2 then
    !![-3 / 2, -1 / 2, -1 / 2; -1 / 2, -1 / 6, 1 / 6; -1 / 2, 1 / 6, -1 / 6]
  else
    !![-1 / 6, 1 / 6, -1 / 2; 1 / 6, -1 / 6, -1 / 2; -1 / 2, -1 / 2, -3 / 2]

theorem triple_inverse_eq (omitted : Fin 4) :
    (tripleMatrix omitted)⁻¹ = tripleInverseMatrix omitted := by
  apply Matrix.inv_eq_right_inv
  ext row column
  fin_cases omitted <;> fin_cases row <;> fin_cases column <;>
    norm_num [tripleMatrix, tripleInverseMatrix, matrix, Matrix.submatrix,
      Matrix.mul_apply, Fin.sum_univ_succ, Fin.succAbove, Matrix.one_apply]

theorem triple_inverse_diagonal_eq (omitted : Fin 4) :
    ∃ player : Fin 3, (tripleMatrix omitted)⁻¹ player player = -1 / 6 := by
  rw [triple_inverse_eq]
  refine ⟨if omitted.val < 2 then 1 else 0, ?_⟩
  fin_cases omitted <;> norm_num [tripleInverseMatrix]

theorem triple_inverse_not_nonnegative (omitted : Fin 4) :
    ¬∀ row column, 0 ≤ (tripleMatrix omitted)⁻¹ row column := by
  obtain ⟨player, hnegative⟩ := triple_inverse_diagonal_eq omitted
  intro hnonnegative
  have hdiagonal := hnonnegative player player
  rw [hnegative] at hdiagonal
  norm_num at hdiagonal

theorem projectiveMatrix_isR0 : IsR0Matrix (quittingProjectiveLCPMatrix reward) := by
  rw [projectiveMatrix_eq]
  exact matrix_isR0

theorem projectiveMatrix_standardQ : IsStandardQ (quittingProjectiveLCPMatrix reward) := by
  rw [projectiveMatrix_eq]
  exact matrix_standardQ

theorem projectiveMatrix_positive_inverse :
    HasStrictlyPositiveInverse (quittingProjectiveLCPMatrix reward) := by
  rw [projectiveMatrix_eq]
  exact matrix_positive_inverse

theorem projectiveMatrix_harmful_pair_not_standardQ (player partner : Fin 4)
    (hdistinct : partner ≠ player) (hfavorite : partner ≠ favorite player) :
    ¬IsStandardQ (Matrix.submatrix (quittingProjectiveLCPMatrix reward)
      (![player, partner] : Fin 2 → Fin 4) (![player, partner] : Fin 2 → Fin 4)) := by
  rw [projectiveMatrix_eq]
  exact harmful_pair_not_standardQ_of_not_favorite player partner hdistinct hfavorite

theorem projectiveMatrix_harmful_pair_isR0 (player partner : Fin 4)
    (hdistinct : partner ≠ player) (hfavorite : partner ≠ favorite player) :
    IsR0Matrix (Matrix.submatrix (quittingProjectiveLCPMatrix reward)
      (![player, partner] : Fin 2 → Fin 4) (![player, partner] : Fin 2 → Fin 4)) := by
  rw [projectiveMatrix_eq]
  exact harmful_pair_isR0_of_not_favorite player partner hdistinct hfavorite

theorem projectiveMatrix_triple_inverse_diagonal_eq (omitted : Fin 4) :
    ∃ player : Fin 3, (Matrix.submatrix (quittingProjectiveLCPMatrix reward)
      omitted.succAbove omitted.succAbove)⁻¹ player player = -1 / 6 := by
  rw [projectiveMatrix_eq]
  exact triple_inverse_diagonal_eq omitted

end GameTheory.BelowSingletonJointPhaseFixture
