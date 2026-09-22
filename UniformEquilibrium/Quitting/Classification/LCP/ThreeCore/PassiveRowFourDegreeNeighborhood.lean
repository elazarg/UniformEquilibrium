/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.LinearProgramming.SupportTestStability
import MathUE.LinearProgramming.PositiveInverseOpenness
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.PassiveRowFourFixture
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.RawPassiveRowInverseCriterion

/-!
# Degree and neighborhood of the four-player passive-row fixture

The finite support inventory is the exact rational calculation in the
three-player passive-row packet. It is kept separate from the checked
balanced-cycle fixture.
-/

noncomputable section

namespace GameTheory.PassiveRowFourDegreeNeighborhood

open Math.LinearProgramming
open Filter
open scoped Topology

abbrev matrix : Matrix (Fin 4) (Fin 4) ℝ := PassiveRowFourFixture.matrix

def anchor : Fin 4 → ℝ := fun _ => 1

def support : Fin 11 → Finset (Fin 4) :=
  ![{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3},
    {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 2, 3}]

/-- Solutions of the active equations, extended by zero off support. -/
def candidate : Fin 11 → Fin 4 → ℝ :=
  ![![1 / 2, -1, 0, 0], ![-1, 0, 1 / 2, 0], ![-1, 0, 0, -1 / 2],
    ![0, 1 / 2, -1, 0], ![0, 1 / 2, 0, 1], ![0, 0, 1 / 2, 1],
    ![1, 1, 1, 0], ![1, 1, 0, -1], ![-2, 0, -1 / 2, -1],
    ![0, -1 / 2, 1, 2], ![5 / 3, 11 / 3, -7 / 3, -14 / 3]]

/-- Full LCP residual vectors at the active-equation candidates. -/
def residual : Fin 11 → Fin 4 → ℝ :=
  ![![0, 0, -7 / 2, -7 / 2], ![0, -7 / 2, 0, 1],
    ![0, -7 / 2, -1 / 2, 0], ![-7 / 2, 0, 0, -2],
    ![-7 / 2, 0, 1, 0], ![-2, -1 / 2, 0, 0],
    ![0, 0, 0, 2], ![0, 0, -1, 0], ![0, -11 / 2, 0, 0],
    ![-5 / 2, 0, 0, 0], ![0, 0, 0, 0]]

def determinant : Fin 11 → ℝ :=
  ![2, 2, -2, 2, -2, -2, 7, -7, 2, 2, 3]

theorem diagonal_zero (who : Fin 4) : matrix who who = 0 := by
  fin_cases who <;> norm_num [matrix, PassiveRowFourFixture.matrix]

theorem anchor_pos (who : Fin 4) : 0 < anchor who := by
  simp [anchor]

theorem support_complete (selected : Finset (Fin 4)) (hcard : 2 ≤ selected.card) :
    ∃ row : Fin 11, selected = support row := by
  exact (by decide : ∀ selected : Finset (Fin 4), 2 ≤ selected.card →
    ∃ row : Fin 11, selected = support row) selected hcard

theorem candidate_zero_off_support (row : Fin 11) (who : Fin 4)
    (hwho : who ∉ support row) : candidate row who = 0 := by
  fin_cases row <;> fin_cases who <;> simp_all [support, candidate]

theorem residual_eq (row : Fin 11) :
    lcpResidual matrix (-anchor) (candidate row) = residual row := by
  funext who
  fin_cases row <;> fin_cases who <;>
    norm_num [lcpResidual, matrix, PassiveRowFourFixture.matrix,
      anchor, candidate, residual, Fin.sum_univ_succ]

theorem residual_zero_on_support (row : Fin 11) (who : Fin 4)
    (hwho : who ∈ support row) : residual row who = 0 := by
  fin_cases row <;> fin_cases who <;> simp_all [support, residual]

theorem principal_det_eq (row : Fin 11) :
    (matrix.toSquareBlockProp (fun who => who ∈ support row)).det = determinant row := by
  classical
  let selector : Fin 4 → ℝ := fun who => if who ∈ support row then 1 else 0
  have hpredicate (who : Fin 4) : who ∈ support row ↔ 0 < selector who := by
    dsimp only [selector]
    split_ifs <;> simp_all
  have hequal := (det_lcpSelectedMatrix matrix selector).trans
    (Matrix.equiv_block_det matrix hpredicate)
  have hfinite : Finset.Subtype.fintype (support row) =
      Subtype.fintype (fun who => who ∈ support row) := Subsingleton.elim _ _
  rw [hfinite, ← hequal, Matrix.det_succ_row_zero]
  fin_cases row <;>
    norm_num [selector, support, determinant, lcpSelectedMatrix, matrix,
      PassiveRowFourFixture.matrix, Matrix.det_fin_three, Fin.sum_univ_succ,
      Fin.succAbove, Matrix.submatrix, Matrix.one_apply]

theorem principal_det_ne_zero (row : Fin 11) :
    (matrix.toSquareBlockProp (fun who => who ∈ support row)).det ≠ 0 := by
  rw [principal_det_eq]
  fin_cases row <;> norm_num [determinant]

theorem principal_nonsingular (selected : Finset (Fin 4)) (hcard : 2 ≤ selected.card) :
    (matrix.toSquareBlockProp (fun who => who ∈ selected)).det ≠ 0 := by
  obtain ⟨row, rfl⟩ := support_complete selected hcard
  exact principal_det_ne_zero row

theorem negative_columns (column : Fin 4) :
    ∃ row : Fin 4, matrix row column < 0 := by
  fin_cases column
  · exact ⟨3, by norm_num [matrix, PassiveRowFourFixture.matrix]⟩
  · exact ⟨0, by norm_num [matrix, PassiveRowFourFixture.matrix]⟩
  · exact ⟨1, by norm_num [matrix, PassiveRowFourFixture.matrix]⟩
  · exact ⟨0, by norm_num [matrix, PassiveRowFourFixture.matrix]⟩

theorem isR0Matrix : IsR0Matrix matrix :=
  isR0Matrix_of_negative_columns_of_nonsingular_principals
    matrix negative_columns principal_nonsingular

theorem principalInverseCandidate_support_eq (row : Fin 11) :
    principalInverseCandidate matrix anchor (support row) = candidate row := by
  apply principalInverseCandidate_eq_of_supported_linear_system matrix anchor (support row)
    (principal_det_ne_zero row) (candidate row) (candidate_zero_off_support row)
  intro who hwho
  rw [residual_eq]
  exact residual_zero_on_support row who hwho

theorem strict_support_inventory : HasStrictLCPSupportInventory matrix anchor := by
  intro selected hcard
  obtain ⟨row, rfl⟩ := support_complete selected hcard
  rw [principalInverseCandidate_support_eq, residual_eq]
  fin_cases row <;>
    norm_num [support, candidate, residual, Fin.forall_fin_succ, Fin.exists_fin_succ]

theorem support_mem_admissible_iff (row : Fin 11) :
    support row ∈ admissibleLCPSupports matrix anchor
      (principalInverseCandidate matrix anchor) ↔ row = 6 := by
  rw [mem_admissibleLCPSupports_iff, principalInverseCandidate_support_eq, residual_eq]
  fin_cases row <;> norm_num [support, candidate, residual, Fin.forall_fin_succ]

theorem admissible_supports_eq :
    admissibleLCPSupports matrix anchor (principalInverseCandidate matrix anchor) =
      {support 6} := by
  classical
  ext selected
  constructor
  · intro hmem
    obtain ⟨row, rfl⟩ := support_complete selected
      ((mem_admissibleLCPSupports_iff _ _ _ _).mp hmem).1
    rw [support_mem_admissible_iff] at hmem
    simp [hmem]
  · intro hmem
    have hselected : selected = support 6 := by simpa using hmem
    subst selected
    exact (support_mem_admissible_iff 6).mpr rfl

/-- The packet's exact four-player matrix has canonical R0 degree `+1`. -/
theorem r0Degree_eq_one :
    r0Degree matrix isR0Matrix = 1 := by
  rw [r0Degree_eq_sum_admissible_inverse_supports matrix anchor
    diagonal_zero anchor_pos negative_columns principal_nonsingular
    strict_support_inventory.strict_inactive, admissible_supports_eq]
  simp [principal_det_eq, determinant]

/-! ## A common matrix neighborhood for degree and strict passive rows -/

/-- The principal on the selected first three players. -/
def selectedPrincipal (other : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  other.submatrix Fin.castSucc Fin.castSucc

/-- The outside singleton row, indexed by selected owner. -/
def selectedOutsideRow (other : Matrix (Fin 4) (Fin 4) ℝ) : Fin 3 → ℝ :=
  fun owner => other 3 owner.castSucc

/-- The packet's inverse weights on the selected triple. -/
def selectedOutsideWeight (other : Matrix (Fin 4) (Fin 4) ℝ) : Fin 3 → ℝ :=
  Matrix.vecMul (selectedOutsideRow other) (selectedPrincipal other)⁻¹

theorem selectedPrincipal_center :
    selectedPrincipal matrix = PassiveRowFourFixture.childMatrix := rfl

theorem selectedPrincipal_center_strictInverse :
    HasStrictlyPositiveInverse (selectedPrincipal matrix) := by
  rw [selectedPrincipal_center]
  constructor
  · have hdet : PassiveRowFourFixture.childMatrix.det = 7 := by
      norm_num [PassiveRowFourFixture.childMatrix, PassiveRowFourFixture.matrix,
        Matrix.det_fin_three]
    rw [hdet]
    norm_num
  · intro row column
    rw [PassiveRowFourFixture.childMatrix_inverse]
    fin_cases row <;> fin_cases column <;> norm_num

theorem selectedOutsideWeight_center :
    selectedOutsideWeight matrix = ![8 / 7, 2 / 7, 11 / 7] := by
  unfold selectedOutsideWeight
  rw [selectedPrincipal_center, PassiveRowFourFixture.childMatrix_inverse]
  funext column
  fin_cases column <;>
    norm_num [selectedOutsideRow, matrix, PassiveRowFourFixture.matrix,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]

theorem selectedOutsideWeight_center_pos (column : Fin 3) :
    0 < selectedOutsideWeight matrix column := by
  rw [selectedOutsideWeight_center]
  fin_cases column <;> norm_num

private theorem continuous_selectedPrincipal : Continuous selectedPrincipal := by
  exact continuous_id.matrix_submatrix Fin.castSucc Fin.castSucc

private theorem continuous_selectedOutsideRow : Continuous selectedOutsideRow := by
  unfold selectedOutsideRow
  fun_prop

private theorem continuousAt_selectedOutsideWeight :
    ContinuousAt selectedOutsideWeight matrix := by
  have hinverse : ContinuousAt
      (fun other : Matrix (Fin 4) (Fin 4) ℝ => (selectedPrincipal other)⁻¹)
      matrix := by
    apply ContinuousAt.comp _ continuous_selectedPrincipal.continuousAt
    apply continuousAt_matrix_inv
    simpa only [Ring.inverse_eq_inv'] using
      continuousAt_inv₀ selectedPrincipal_center_strictInverse.1
  apply continuousAt_pi.mpr
  intro column
  change ContinuousAt (fun other : Matrix (Fin 4) (Fin 4) ℝ =>
    ∑ owner : Fin 3,
      selectedOutsideRow other owner * (selectedPrincipal other)⁻¹ owner column) matrix
  apply tendsto_finsetSum
  intro owner _
  exact ((continuous_apply owner).continuousAt.comp
      continuous_selectedOutsideRow.continuousAt).mul
    ((continuous_apply_apply owner column).continuousAt.comp hinverse)

/-- R0 degree one and the strict three-player inverse/outsider-row test
persist together on a matrix neighborhood, among zero-diagonal matrices. -/
theorem eventually_degree_one_and_strict_passive_rows :
    ∀ᶠ other : Matrix (Fin 4) (Fin 4) ℝ in 𝓝 matrix,
      (∀ who, other who who = 0) →
        ∃ hR0 : IsR0Matrix other,
          r0Degree other hR0 = 1 ∧
          HasStrictlyPositiveInverse (selectedPrincipal other) ∧
          ∀ column, 0 < selectedOutsideWeight other column := by
  have hstrict : ∀ᶠ other : Matrix (Fin 4) (Fin 4) ℝ in 𝓝 matrix,
      HasStrictlyPositiveInverse (selectedPrincipal other) :=
    continuous_selectedPrincipal.continuousAt.eventually
      (isOpen_hasStrictlyPositiveInverse.mem_nhds selectedPrincipal_center_strictInverse)
  have hweights : ∀ᶠ other : Matrix (Fin 4) (Fin 4) ℝ in 𝓝 matrix,
      ∀ column, 0 < selectedOutsideWeight other column := by
    apply Filter.eventually_all.mpr
    intro column
    exact ((continuous_apply column).continuousAt.comp
      continuousAt_selectedOutsideWeight).eventually_const_lt
        (selectedOutsideWeight_center_pos column)
  filter_upwards [eventually_r0Degree_eq_of_strict_support_inventory
      matrix anchor diagonal_zero anchor_pos negative_columns principal_nonsingular
      strict_support_inventory, hstrict, hweights]
    with other hdegree hpositive hweight
  intro hdiagonal
  obtain ⟨hR0, _, hdegreeEq⟩ := hdegree
  exact ⟨hR0, (hdegreeEq hdiagonal).trans r0Degree_eq_one, hpositive, hweight⟩

/-! ## Pullback to the full terminal reward-table space -/

abbrev Reward := PassiveRowFourFixture.Reward

/-- The singleton-difference matrix of a four-player reward table. -/
def singletonMatrix (reward : Reward) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of (QuittingLCPClassification.normalizedSoloMatrix reward)

theorem singletonMatrix_apply (reward : Reward) (who owner : Fin 4) :
    singletonMatrix reward who owner =
      quittingSoloReward reward owner who - quittingSoloReward reward who who := by
  exact normalizedSoloMatrix_eq_soloReward_sub reward who owner

theorem singletonMatrix_diagonal (reward : Reward) (who : Fin 4) :
    singletonMatrix reward who who = 0 := by
  exact QuittingLCPClassification.normalizedSoloMatrix_diagonal reward who

private theorem continuous_singletonMatrix : Continuous singletonMatrix := by
  apply continuous_matrix
  intro who owner
  change Continuous (fun reward : Reward =>
    quittingSoloReward reward owner who - quittingSoloReward reward who who)
  unfold quittingSoloReward
  fun_prop

/-- Every table realizing the rational matrix lies in a full-dimensional
ambient reward-table neighborhood with degree one and strict inverse rows. -/
theorem eventually_reward_degree_one_and_strict_passive_rows
    (reward : Reward) (hmatrix : singletonMatrix reward = matrix) :
    ∀ᶠ nearby : Reward in 𝓝 reward,
      ∃ hR0 : IsR0Matrix (singletonMatrix nearby),
        r0Degree (singletonMatrix nearby) hR0 = 1 ∧
        HasStrictlyPositiveInverse (selectedPrincipal (singletonMatrix nearby)) ∧
        ∀ column, 0 < selectedOutsideWeight (singletonMatrix nearby) column := by
  have htendsto : Tendsto singletonMatrix (𝓝 reward) (𝓝 matrix) := by
    rw [← hmatrix]
    exact continuous_singletonMatrix.continuousAt
  filter_upwards [htendsto.eventually eventually_degree_one_and_strict_passive_rows]
    with nearby hnear
  exact hnear (singletonMatrix_diagonal nearby)

/-- One literal completion of the displayed singleton-difference matrix;
all other terminal coordinates are set to zero only to name a center. -/
def centerReward : Reward := fun terminal who =>
  ∑ owner : Fin 4,
    if terminal.1 = {owner} then matrix who owner else 0

theorem singletonMatrix_center : singletonMatrix centerReward = matrix := by
  ext who owner
  rw [singletonMatrix_apply]
  fin_cases who <;> fin_cases owner <;>
    norm_num [centerReward, quittingSoloReward, matrix,
      PassiveRowFourFixture.matrix, Fin.sum_univ_succ]

/-- A nonempty open set in the entire reward-table space, not merely the
relative space of zero-diagonal matrices. -/
theorem exists_open_reward_neighborhood :
    ∃ neighborhood : Set Reward,
      IsOpen neighborhood ∧ centerReward ∈ neighborhood ∧
        ∀ reward ∈ neighborhood,
          ∃ hR0 : IsR0Matrix (singletonMatrix reward),
            r0Degree (singletonMatrix reward) hR0 = 1 ∧
            HasStrictlyPositiveInverse (selectedPrincipal (singletonMatrix reward)) ∧
            ∀ column, 0 < selectedOutsideWeight (singletonMatrix reward) column := by
  let good : Set Reward := {reward | ∃ hR0 : IsR0Matrix (singletonMatrix reward),
    r0Degree (singletonMatrix reward) hR0 = 1 ∧
    HasStrictlyPositiveInverse (selectedPrincipal (singletonMatrix reward)) ∧
    ∀ column, 0 < selectedOutsideWeight (singletonMatrix reward) column}
  refine ⟨interior good, isOpen_interior, ?_, ?_⟩
  · apply mem_interior_iff_mem_nhds.mpr
    exact eventually_reward_degree_one_and_strict_passive_rows
      centerReward singletonMatrix_center
  · intro reward hreward
    exact (interior_subset : interior good ⊆ good) hreward

/-! ## The literal raw-H consumer on the open class -/

private def deleted (who : Fin 4) : Prop := who = 3

private instance : DecidablePred deleted :=
  fun who => inferInstanceAs (Decidable (who = 3))

private abbrev Child := {who : Fin 4 // ¬ deleted who}

private def childEquiv : Fin 3 ≃ Child where
  toFun who := ⟨who.castSucc, Fin.castSucc_ne_last who⟩
  invFun who := who.1.castPred (by simpa [deleted] using who.2)
  left_inv who := by simp
  right_inv who := by
    apply Subtype.ext
    exact Fin.castSucc_castPred who.1 (by simpa [deleted] using who.2)

private theorem childMatrix_submatrix (reward : Reward) :
    (PassiveRowInverseCriterion.childMatrix reward deleted).submatrix
      childEquiv childEquiv = selectedPrincipal (singletonMatrix reward) := by
  ext who owner
  rw [Matrix.submatrix_apply, selectedPrincipal, Matrix.submatrix_apply]
  rw [PassiveRowInverseCriterion.childMatrix, Matrix.of_apply,
    normalizedSoloMatrix_eq_soloReward_sub, singletonMatrix_apply]
  simp only [quittingSoloReward]
  rfl

private theorem outsideRow_childEquiv (reward : Reward) (owner : Fin 3) :
    PassiveRowInverseCriterion.outsideRow reward deleted 3 (childEquiv owner) =
      selectedOutsideRow (singletonMatrix reward) owner := by
  change quittingSoloReward reward owner.castSucc 3 - quittingSoloReward reward 3 3 =
    singletonMatrix reward 3 owner.castSucc
  exact (singletonMatrix_apply reward 3 owner.castSucc).symm

private theorem inverseWeight_childEquiv (reward : Reward) (inside : Child) :
    PassiveRowInverseCriterion.inverseWeight reward deleted 3 inside =
      selectedOutsideWeight (singletonMatrix reward) (childEquiv.symm inside) := by
  let T := PassiveRowInverseCriterion.childMatrix reward deleted
  have hinverse := Matrix.inv_submatrix_equiv T childEquiv childEquiv
  rw [childMatrix_submatrix] at hinverse
  have hentry (owner : Fin 3) :
      T⁻¹ (childEquiv owner) inside =
        (selectedPrincipal (singletonMatrix reward))⁻¹ owner
          (childEquiv.symm inside) := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ =>
      M owner (childEquiv.symm inside)) hinverse
    simpa [Matrix.submatrix_apply] using h.symm
  rw [PassiveRowInverseCriterion.inverseWeight, selectedOutsideWeight,
    Matrix.vecMul_apply_eq_sum, Matrix.vecMul_apply_eq_sum]
  rw [← childEquiv.sum_comp (fun owner : Child =>
    PassiveRowInverseCriterion.outsideRow reward deleted 3 owner * T⁻¹ owner inside)]
  apply Finset.sum_congr rfl
  intro owner _
  rw [outsideRow_childEquiv, hentry]

/-- The raw inverse criterion turns each strict-H table in the neighborhood
into an original four-player game with a fixed uniform-equilibrium target. -/
theorem exists_uniformEquilibriumPayoff_of_degree_one_and_strict_passive_rows
    (reward : Reward)
    (hstrict : HasStrictlyPositiveInverse (selectedPrincipal (singletonMatrix reward)))
    (hweight : ∀ column,
      0 < selectedOutsideWeight (singletonMatrix reward) column) :
    ∃ target, (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  have hdet : (PassiveRowInverseCriterion.childMatrix reward deleted).det ≠ 0 := by
    rw [← Matrix.det_submatrix_equiv_self childEquiv]
    rw [childMatrix_submatrix]
    exact hstrict.1
  have hinverse (row column : Child) :
      0 ≤ (PassiveRowInverseCriterion.childMatrix reward deleted)⁻¹ row column := by
    have h := Matrix.inv_submatrix_equiv
      (PassiveRowInverseCriterion.childMatrix reward deleted) childEquiv childEquiv
    rw [childMatrix_submatrix] at h
    have hentry := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ =>
      M (childEquiv.symm row) (childEquiv.symm column)) h
    have hpositive := hstrict.2 (childEquiv.symm row) (childEquiv.symm column)
    rw [Matrix.submatrix_apply] at hentry
    rw [childEquiv.apply_symm_apply, childEquiv.apply_symm_apply] at hentry
    rw [hentry] at hpositive
    exact le_of_lt hpositive
  have houtside (outside : Fin 4) (houtside : deleted outside) (inside : Child) :
      0 ≤ PassiveRowInverseCriterion.inverseWeight reward deleted outside inside := by
    have heq : outside = 3 := houtside
    subst outside
    rw [inverseWeight_childEquiv]
    exact le_of_lt (hweight _)
  have hcard : Fintype.card Child = 3 := by
    exact Fintype.card_congr childEquiv.symm
  exact PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple
    reward deleted hcard hdet hinverse houtside

/-- The packet's nonempty open four-player class has degree `+1` and a
fixed uniform-equilibrium payoff at every reward table in the class. -/
theorem exists_open_degree_one_uniformPayoff_class :
    ∃ neighborhood : Set Reward,
      IsOpen neighborhood ∧ centerReward ∈ neighborhood ∧
        ∀ reward ∈ neighborhood,
          (∃ hR0 : IsR0Matrix (singletonMatrix reward),
            r0Degree (singletonMatrix reward) hR0 = 1) ∧
          ∃ target, (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  obtain ⟨neighborhood, hopen, hcenter, hall⟩ := exists_open_reward_neighborhood
  refine ⟨neighborhood, hopen, hcenter, ?_⟩
  intro reward hreward
  obtain ⟨hR0, hdegree, hstrict, hweight⟩ := hall reward hreward
  exact ⟨⟨hR0, hdegree⟩,
    exists_uniformEquilibriumPayoff_of_degree_one_and_strict_passive_rows
      reward hstrict hweight⟩

end GameTheory.PassiveRowFourDegreeNeighborhood
