import UniformEquilibrium.Quitting.Examples.NegativePremiumCyclicChildFixtures
import UniformEquilibrium.Quitting.Classification.LCP.QuittingRewardAdapter
import MathUE.Finset.FinFourNonemptyCoalitions
import MathUE.LinearProgramming.FiniteSupportDegree
import UniformEquilibrium.Quitting.Cycles.CrossedMatchingPhaseSource

/-! # Actual singleton matrix screens for the negative-premium fixture

All matrix data belong to the literal sixty-coordinate table. These source
comparisons do not exclude its uniform payoff or other strategy classes.
-/

noncomputable section

namespace GameTheory.NegativePremiumCyclicChild.Fixtures

open Math.LinearProgramming QuittingLCPClassification
open scoped Matrix

def matrix : Matrix Player Player ℝ :=
  !![0, 1, 1, -1; -1, 0, -1, 3; -1, 3, 0, -1; -1, -1, 3, 0]

theorem singletonMatrix_eq : quittingSingletonMatrix survivorReward = matrix := by
  ext player owner
  fin_cases player <;> fin_cases owner <;>
    norm_num [quittingSingletonMatrix, survivorReward, quittingSingletonTerminal,
      matrix, Finset.ext_iff, Fin.forall_fin_succ]

theorem matrix_det : matrix.det = 13 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [matrix, Matrix.det_fin_three, Fin.sum_univ_succ, Fin.succAbove,
    Matrix.submatrix]

def principalDeterminants : Fin 15 → ℝ :=
  ![0, 0, 1, 0, 1, 3, -2, 0, -1, 3, -4, 3, 4, 26, 13]

theorem principal_det_eq (row : Fin 15) :
    (matrix.toSquareBlockProp
      (fun who => who ∈ (Math.Finset.finFourCoalitionRowEquiv row).val)).det =
        principalDeterminants row := by
  classical
  let selected := (Math.Finset.finFourCoalitionRowEquiv row).val
  let selector : Player → ℝ := fun who => if who ∈ selected then 1 else 0
  have hpredicate (who : Player) : who ∈ selected ↔ 0 < selector who := by
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

theorem principal_det_ne_zero (selected : Finset Player) (hcard : 2 ≤ selected.card) :
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

theorem negative_columns (column : Player) : ∃ row : Player, matrix row column < 0 := by
  refine ⟨(![1, 3, 1, 0] : Player → Player) column, ?_⟩
  fin_cases column <;> norm_num [matrix]

theorem matrix_isR0 : IsR0Matrix matrix :=
  isR0Matrix_of_negative_columns_of_nonsingular_principals matrix
    negative_columns principal_det_ne_zero

def inverseMatrix : Matrix Player Player ℝ :=
  !![2, 5 / 13, -11 / 13, -7 / 13; 1, 4 / 13, -1 / 13, -3 / 13;
    1, 3 / 13, -4 / 13, 1 / 13; 1, 7 / 13, -5 / 13, -2 / 13]

theorem matrix_inverse : matrix⁻¹ = inverseMatrix := by
  apply Matrix.inv_eq_left_inv
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [matrix, inverseMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem inverse_not_nonnegative : ¬∀ row column, 0 ≤ matrix⁻¹ row column := by
  intro h
  have hentry := h 0 3
  rw [matrix_inverse] at hentry
  norm_num [inverseMatrix] at hentry

/-- No independent column signs can make the actual full inverse positive. -/
theorem inverse_no_positive_column_scaling (scale : Player → ℝ) :
    ¬∀ row column, 0 < matrix⁻¹ row column * scale column := by
  intro h
  have hnegative := h 0 3
  have hpositive := h 2 3
  rw [matrix_inverse] at hnegative hpositive
  norm_num [inverseMatrix] at hnegative hpositive
  linarith

/-- Exact active-system candidates at offset minus one, including rejected supports. -/
def offsetCandidate (support : Finset Player) : Player → ℝ :=
  if support = {0, 1} then ![-1, 1, 0, 0]
  else if support = {0, 2} then ![-1, 0, 1, 0]
  else if support = {0, 3} then ![-1, 0, 0, -1]
  else if support = {1, 2} then ![0, 1 / 3, -1, 0]
  else if support = {1, 3} then ![0, -1, 0, 1 / 3]
  else if support = {2, 3} then ![0, 0, 1 / 3, -1]
  else if support = {0, 1, 2} then ![-5 / 2, -1 / 2, 3 / 2, 0]
  else if support = {0, 1, 3} then ![-7 / 4, 3 / 4, 0, -1 / 4]
  else if support = {0, 2, 3} then ![-1 / 4, 0, 1 / 4, -3 / 4]
  else if support = {1, 2, 3} then ![0, 1 / 2, 1 / 2, 1 / 2]
  else if support = Finset.univ then fun _ => 1
  else fun _ => 0

theorem offsetCandidate_zero (support : Finset Player) (hcard : 2 ≤ support.card)
    (who : Player) (hwho : who ∉ support) : offsetCandidate support who = 0 := by
  fin_cases support <;> fin_cases who <;>
    norm_num [offsetCandidate, Finset.ext_iff, Fin.forall_fin_succ] at *

theorem offsetCandidate_active (support : Finset Player) (hcard : 2 ≤ support.card)
    (who : Player) (hwho : who ∈ support) :
    lcpResidual matrix (-(fun _ => 1)) (offsetCandidate support) who = 0 := by
  fin_cases support <;> fin_cases who <;>
    norm_num [offsetCandidate, lcpResidual, matrix, Finset.ext_iff, Fin.forall_fin_succ,
      Fin.sum_univ_succ] at *

theorem offset_admissible_supports :
    admissibleLCPSupports matrix (fun _ => 1) offsetCandidate = {Finset.univ} := by
  classical
  ext support
  rw [mem_admissibleLCPSupports_iff]
  fin_cases support <;>
    norm_num [offsetCandidate, lcpResidual, matrix, Finset.ext_iff, Fin.forall_fin_succ,
      Fin.sum_univ_succ]

/-- The census is over every actual root, not a supplied finite selection. -/
theorem offsetCandidate_univ : offsetCandidate Finset.univ = fun _ => 1 := by
  funext who
  norm_num [offsetCandidate, Finset.ext_iff, Fin.forall_fin_succ]

theorem offset_solution_iff (root : Player → ℝ) :
    IsStandardLCPSolution matrix (-(fun _ => 1)) root ↔ root = fun _ => 1 := by
  rw [isStandardLCPSolution_iff_exists_admissible_support matrix (fun _ => 1)
    (fun who => by fin_cases who <;> norm_num [matrix]) (fun _ => by norm_num)
    principal_det_ne_zero offsetCandidate offsetCandidate_zero offsetCandidate_active,
    offset_admissible_supports]
  simp only [Finset.mem_singleton, exists_eq_left, offsetCandidate_univ]

theorem matrix_r0Degree_eq_one : r0Degree matrix matrix_isR0 = 1 := by
  classical
  have hselected : lcpSelectedMatrix matrix (fun _ => 1) = matrix := by
    ext row column
    simp [lcpSelectedMatrix]
  have hdet : (matrix.toSquareBlockProp (fun _ => (0 : ℝ) < 1)).det = 13 :=
    ((det_lcpSelectedMatrix matrix (fun _ => 1)).symm.trans
      (congrArg Matrix.det hselected)).trans matrix_det
  have hstrict : ∀ root, IsStandardLCPSolution matrix (-(fun _ => 1)) root →
      ∀ who, root who = 0 → 0 < lcpResidual matrix (-(fun _ => 1)) root who := by
    intro root hroot who hzero
    rw [(offset_solution_iff root).mp hroot] at hzero
    norm_num at hzero
  have hnonsingular : ∀ root, IsStandardLCPSolution matrix (-(fun _ => 1)) root →
      (matrix.toSquareBlockProp (fun who => 0 < root who)).det ≠ 0 := by
    intro root hroot
    rw [(offset_solution_iff root).mp hroot]
    exact hdet ▸ (by norm_num)
  obtain ⟨roots, hroots, hdegree⟩ := exists_finset_r0Degree_eq_sum_sign_det
    matrix matrix_isR0 (-(fun _ => 1)) hstrict hnonsingular
  have hactual : roots = {fun _ => 1} := by
    ext root
    rw [hroots, offset_solution_iff]
    simp only [Finset.mem_singleton]
  rw [hactual, Finset.sum_singleton, hdet] at hdegree
  norm_num at hdegree
  exact hdegree

/-- The actual reward transform tested against the existing raw producers. -/
def affineReindexedReward (label : Player ≃ Player) (scale shift : Payoff Player) : Reward :=
  quittingRewardReindex label (quittingPlayerwiseAffineReward survivorReward scale shift)

theorem affineReindexed_matrix_entry (label : Player ≃ Player) (scale shift : Payoff Player)
    (who owner : Player) :
    quittingProjectiveLCPMatrix (affineReindexedReward label scale shift) who owner =
      scale (label.symm who) * matrix (label.symm who) (label.symm owner) := by
  have hterminal (player : Player) :
      (quittingCoalitionEquiv label).symm (quittingSingletonTerminal player) =
        quittingSingletonTerminal (label.symm player) := by
    apply Subtype.ext
    simp [quittingCoalitionEquiv, quittingSingletonTerminal]
  change scale (label.symm who) *
        survivorReward ((quittingCoalitionEquiv label).symm
          (quittingSingletonTerminal owner)) (label.symm who) + shift (label.symm who) -
      (scale (label.symm who) *
        survivorReward ((quittingCoalitionEquiv label).symm
          (quittingSingletonTerminal who)) (label.symm who) + shift (label.symm who)) = _
  rw [hterminal owner, hterminal who, ← singletonMatrix_eq]
  change _ = scale (label.symm who) *
    (survivorReward (quittingSingletonTerminal (label.symm owner)) (label.symm who) -
      survivorReward (quittingSingletonTerminal (label.symm who)) (label.symm who))
  ring

private theorem weakRawSource_nonpositive_off_favorite {reward : Reward}
    (hraw : PairedCycle.CrossedMatching.WeakRawSource reward) (who owner : Player)
    (hne : owner ≠ Math.CrossedMatching.favorite who) :
    quittingProjectiveLCPMatrix reward who owner ≤ 0 := by
  have hcases : owner = who ∨ owner = Math.CrossedMatching.favorite who ∨
      owner = Math.CrossedMatching.scheduled who ∨ owner = Math.CrossedMatching.other who := by
    fin_cases who <;> fin_cases owner <;>
      simp [Math.CrossedMatching.favorite, Math.CrossedMatching.scheduled,
        Math.CrossedMatching.other]
  rcases hcases with rfl | hfavorite | rfl | rfl
  · simp [quittingProjectiveLCPMatrix]
  · exact (hne hfavorite).elim
  · rw [PairedCycle.CrossedMatching.matrix_entry]
    exact sub_nonpos.mpr (hraw.scheduled_le who)
  · rw [PairedCycle.CrossedMatching.matrix_entry]
    exact sub_nonpos.mpr (hraw.other_le who)

/-- The two positive entries in row zero defeat every relabelled weak matching source. -/
theorem not_weakRawSource_affineReindexed (label : Player ≃ Player)
    (scale shift : Payoff Player) (hscale : ∀ who, 0 < scale who) :
    ¬PairedCycle.CrossedMatching.WeakRawSource (affineReindexedReward label scale shift) := by
  intro hraw
  have hpositive (owner : Player) (hentry : matrix 0 owner = 1) :
      0 < quittingProjectiveLCPMatrix (affineReindexedReward label scale shift)
        (label 0) (label owner) := by
    rw [affineReindexed_matrix_entry]
    simpa only [label.symm_apply_apply, hentry, mul_one] using hscale 0
  have hfirst := hpositive 1 (by norm_num [matrix])
  have hsecond := hpositive 2 (by norm_num [matrix])
  have hfirstEq : label 1 = Math.CrossedMatching.favorite (label 0) := by
    by_contra hne
    exact (not_le_of_gt hfirst) (weakRawSource_nonpositive_off_favorite hraw _ _ hne)
  have hsecondEq : label 2 = Math.CrossedMatching.favorite (label 0) := by
    by_contra hne
    exact (not_le_of_gt hsecond) (weakRawSource_nonpositive_off_favorite hraw _ _ hne)
  have hsame := label.injective (hfirstEq.trans hsecondEq.symm)
  norm_num at hsame

theorem not_rawSource_affineReindexed (label : Player ≃ Player)
    (scale shift : Payoff Player) (hscale : ∀ who, 0 < scale who) :
    ¬PairedCycle.CrossedMatching.RawSource (affineReindexedReward label scale shift) := by
  intro hraw
  apply not_weakRawSource_affineReindexed label scale shift hscale
  exact ⟨fun who => (hraw.favorite_gt who).le, fun who => (hraw.scheduled_lt who).le,
    fun who => (hraw.other_lt who).le, fun who => (hraw.scheduled_join_gt who).le,
    hraw.cap_favorite, hraw.cap_other, hraw.cap_joint⟩

theorem affineReindexed_matrix_inverse (label : Player ≃ Player)
    (scale shift : Payoff Player) (hscale : ∀ who, 0 < scale who) (who owner : Player) :
    (quittingSingletonMatrix (affineReindexedReward label scale shift))⁻¹ who owner =
      inverseMatrix (label.symm who) (label.symm owner) / scale (label.symm owner) := by
  have hmatrix : quittingSingletonMatrix (affineReindexedReward label scale shift) =
      Matrix.reindex label label (Matrix.diagonal scale * matrix) := by
    ext row column
    change quittingProjectiveLCPMatrix (affineReindexedReward label scale shift) row column = _
    rw [affineReindexed_matrix_entry]
    simp [Matrix.reindex_apply, Matrix.diagonal_mul]
  have hdiagonal : (Matrix.diagonal scale)⁻¹ =
      Matrix.diagonal (fun who => (scale who)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    have hproduct : (fun who => (scale who)⁻¹ * scale who) = fun _ => (1 : ℝ) := by
      funext who
      exact inv_mul_cancel₀ (hscale who).ne'
    rw [hproduct]
    exact Matrix.diagonal_one
  rw [hmatrix, Matrix.inv_reindex, Matrix.mul_inv_rev, matrix_inverse, hdiagonal]
  simp [Matrix.reindex_apply, Matrix.mul_diagonal, div_eq_mul_inv]

theorem affineReindexed_inverse_not_nonnegative (label : Player ≃ Player)
    (scale shift : Payoff Player) (hscale : ∀ who, 0 < scale who) :
    ¬∀ row column,
      0 ≤ (quittingSingletonMatrix (affineReindexedReward label scale shift))⁻¹ row column := by
  intro h
  have hentry := h (label 0) (label 3)
  rw [affineReindexed_matrix_inverse label scale shift hscale] at hentry
  simp only [label.symm_apply_apply] at hentry
  have hnegative : inverseMatrix 0 3 / scale 3 < 0 :=
    div_neg_of_neg_of_pos (by norm_num [inverseMatrix]) (hscale 3)
  exact (not_le_of_gt hnegative) hentry

/-- Even after relabeling and positive row scaling, no column signs make the inverse positive. -/
theorem affineReindexed_inverse_no_positive_column_scaling (label : Player ≃ Player)
    (scale shift columnScale : Payoff Player) (hscale : ∀ who, 0 < scale who) :
    ¬∀ row column,
      0 < (quittingSingletonMatrix (affineReindexedReward label scale shift))⁻¹ row column *
        columnScale column := by
  intro h
  have hnegative := h (label 0) (label 3)
  have hpositive := h (label 2) (label 3)
  rw [affineReindexed_matrix_inverse label scale shift hscale] at hnegative hpositive
  simp only [label.symm_apply_apply] at hnegative hpositive
  have hrelation : inverseMatrix 0 3 / scale 3 * columnScale (label 3) =
      -7 * (inverseMatrix 2 3 / scale 3 * columnScale (label 3)) := by
    norm_num [inverseMatrix]
    ring
  rw [hrelation] at hnegative
  nlinarith

end GameTheory.NegativePremiumCyclicChild.Fixtures
