import UniformEquilibrium.Quitting.Examples.NegativePremiumCyclicChildFixtureSourceScreens
import UniformEquilibrium.Quitting.Cycles.CyclicChildJointPhaseSingletonExits

/-! # Passive-inverse and scheduled-partner screens for the literal fixture

Every singleton deletion fails a necessary raw passive-inverse test, and the
raw scheduled-partner source fails under every player relabeling and positive
row-affine transform. This is a failure of named raw hypotheses, not an
exclusion of other joint schedules or a uniform payoff.
-/

noncomputable section

namespace GameTheory.NegativePremiumCyclicChild.Fixtures

open QuittingLCPClassification
open scoped Matrix

theorem pivotPartner_premium (partner : Player) (hpartner : partner ≠ 0) :
    survivorReward ⟨{0, partner}, by simp⟩ partner -
      survivorReward (quittingSingletonTerminal partner) partner = -loss := by
  fin_cases partner
  all_goals norm_num at hpartner
  all_goals norm_num [survivorReward, quittingSingletonTerminal, lower, upper, loss,
    Finset.ext_iff, Fin.forall_fin_succ]

/-- The joint-phase raw table's actual child premium is negative in every
possible singleton-row normalization, contradicting its nonnegative eta. -/
theorem not_jointPhaseRawTable_affineReindexed (label : Player ≃ Player)
    (scale shift : Payoff Player) (hscale : ∀ who, 0 < scale who)
    (data : Math.CyclicChildJointPhase.JointPhaseData) (u v ξ R : ℝ) :
    ¬ CyclicChildJointPhase.RawTable data u v ξ R
      (affineReindexedReward label scale shift) := by
  intro table
  have hparameters := cyclicChildRawRows_affineReindexed_parameters
    label scale shift hscale table.singletonRows data.h₁_pos data.h₂_pos data.h₃_pos
  have hpivot := hparameters.1
  have hchildscale := hparameters.2.1
  have hpartner : label.symm 1 ≠ 0 := by
    rw [← hpivot]
    exact fun h => (by decide : (1 : Player) ≠ 0) (label.symm.injective h)
  have hsingle : (quittingCoalitionEquiv label).symm (quittingSingletonTerminal 1) =
      quittingSingletonTerminal (label.symm 1) := by
    apply Subtype.ext
    simp [quittingCoalitionEquiv, quittingSingletonTerminal]
  have hjoint : (quittingCoalitionEquiv label).symm
      (⟨{0, 1}, by simp⟩ : {S : Finset Player // S.Nonempty}) =
      ⟨{0, label.symm 1}, by simp⟩ := by
    apply Subtype.ext
    simp [quittingCoalitionEquiv, hpivot]
  have hpremium : affineReindexedReward label scale shift ⟨{0, 1}, by simp⟩ 1 -
      affineReindexedReward label scale shift (quittingSingletonTerminal 1) 1 = data.η := by
    rw [table.joint, table.singleton_one]
    simp
  change (scale (label.symm 1) * survivorReward
      ((quittingCoalitionEquiv label).symm ⟨{0, 1}, by simp⟩) (label.symm 1) +
      shift (label.symm 1)) -
    (scale (label.symm 1) * survivorReward
      ((quittingCoalitionEquiv label).symm (quittingSingletonTerminal 1)) (label.symm 1) +
      shift (label.symm 1)) = data.η at hpremium
  rw [hsingle, hjoint, hchildscale] at hpremium
  have hequal : data.η = -loss := by
    rw [one_mul, one_mul, add_sub_add_right_eq_sub,
      pivotPartner_premium (label.symm 1) hpartner] at hpremium
    exact hpremium.symm
  have hnonnegative := data.eta_nonneg
  rw [hequal] at hnonnegative
  norm_num [loss] at hnonnegative

/-! ## The actual matrices of all four singleton deletions -/

def deletionIndex (omitted : Player) : Fin 3 → Player :=
  (![![1, 2, 3], ![0, 2, 3], ![0, 1, 3], ![0, 1, 2]] :
    Player → Fin 3 → Player) omitted

abbrev DeletedChild (omitted : Player) := {who : Player // who ≠ omitted}

def deletionEquiv (omitted : Player) : Fin 3 ≃ DeletedChild omitted :=
  finSuccAboveEquiv omitted

theorem deletionEquiv_val (omitted : Player) (who : Fin 3) :
    (deletionEquiv omitted who).val = deletionIndex omitted who := by
  fin_cases omitted <;> fin_cases who <;> decide

def deletionMatrix (omitted : Player) : Matrix (Fin 3) (Fin 3) ℝ :=
  matrix.submatrix (deletionIndex omitted) (deletionIndex omitted)

theorem actual_deletionMatrix_eq (omitted : Player) :
    (PassiveRowInverseCriterion.childMatrix survivorReward (· = omitted)).submatrix
      (deletionEquiv omitted) (deletionEquiv omitted) = deletionMatrix omitted := by
  ext who owner
  rw [Matrix.submatrix_apply, PassiveRowInverseCriterion.childMatrix, Matrix.of_apply,
    normalizedSoloMatrix_eq_soloReward_sub]
  change quittingSingletonMatrix survivorReward (deletionEquiv omitted who).val
    (deletionEquiv omitted owner).val = _
  rw [singletonMatrix_eq, deletionEquiv_val, deletionEquiv_val]
  rfl

def deletionInverse (omitted : Player) : Matrix (Fin 3) (Fin 3) ℝ :=
  match omitted.val with
  | 0 => !![3 / 26, 9 / 26, 1 / 26; 1 / 26, 3 / 26, 9 / 26; 9 / 26, 1 / 26, 3 / 26]
  | 1 => !![3 / 4, -3 / 4, -1 / 4; 1 / 4, -1 / 4, 1 / 4; -3 / 4, -1 / 4, 1 / 4]
  | 2 => !![-3 / 4, -1 / 4, -3 / 4; 3 / 4, 1 / 4, -1 / 4; -1 / 4, 1 / 4, -1 / 4]
  | _ => !![-3 / 2, -3 / 2, 1 / 2; -1 / 2, -1 / 2, 1 / 2; 3 / 2, 1 / 2, -1 / 2]

theorem deletionMatrix_inverse (omitted : Player) :
    (deletionMatrix omitted)⁻¹ = deletionInverse omitted := by
  apply Matrix.inv_eq_left_inv
  ext who owner
  rw [Matrix.mul_apply]
  fin_cases omitted <;> fin_cases who <;> fin_cases owner <;>
    norm_num [deletionMatrix, deletionInverse, deletionIndex, matrix,
      Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem actual_deletionMatrix_inverse_entry (omitted : Player) (who owner : Fin 3) :
    (PassiveRowInverseCriterion.childMatrix survivorReward (· = omitted))⁻¹
        (deletionEquiv omitted who) (deletionEquiv omitted owner) =
      deletionInverse omitted who owner := by
  have hinverse := Matrix.inv_submatrix_equiv
    (PassiveRowInverseCriterion.childMatrix survivorReward (· = omitted))
    (deletionEquiv omitted) (deletionEquiv omitted)
  rw [actual_deletionMatrix_eq, deletionMatrix_inverse] at hinverse
  exact congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M who owner) hinverse.symm

/-- These three packet entries are in the literal original player labels. -/
theorem actual_passive_inverse_negative_entries :
    (PassiveRowInverseCriterion.childMatrix survivorReward (· = (1 : Player)))⁻¹
        ⟨0, by decide⟩ ⟨2, by decide⟩ = -3 / 4 ∧
      (PassiveRowInverseCriterion.childMatrix survivorReward (· = (2 : Player)))⁻¹
        ⟨0, by decide⟩ ⟨0, by decide⟩ = -3 / 4 ∧
      (PassiveRowInverseCriterion.childMatrix survivorReward (· = (3 : Player)))⁻¹
        ⟨0, by decide⟩ ⟨0, by decide⟩ = -3 / 2 := by
  have hfirst := actual_deletionMatrix_inverse_entry 1 0 1
  have hsecond := actual_deletionMatrix_inverse_entry 2 0 0
  have hthird := actual_deletionMatrix_inverse_entry 3 0 0
  norm_num [deletionEquiv, finSuccAboveEquiv, deletionInverse] at hfirst hsecond hthird
  refine ⟨?_, ?_, ?_⟩
  · simpa only [neg_div] using hfirst
  · simpa only [neg_div] using hsecond
  · simpa only [neg_div] using hthird

def transformedDeletionEquiv (label : Player ≃ Player) (omitted : Player) :
    Fin 3 ≃ DeletedChild (label omitted) :=
  (deletionEquiv omitted).trans
    (label.subtypeEquiv (p := fun who => who ≠ omitted)
      (q := fun who => who ≠ label omitted)
      (fun _ => by
        constructor
        · intro hneq heq
          exact hneq (label.injective heq)
        · intro hneq heq
          exact hneq (congrArg label heq)))

theorem transformedDeletionEquiv_val (label : Player ≃ Player) (omitted : Player)
    (who : Fin 3) :
    (transformedDeletionEquiv label omitted who).val = label (deletionIndex omitted who) := by
  change label (deletionEquiv omitted who).val = _
  rw [deletionEquiv_val]

theorem actual_transformed_deletionMatrix_eq (label : Player ≃ Player)
    (scale shift : Payoff Player) (omitted : Player) :
    (PassiveRowInverseCriterion.childMatrix (affineReindexedReward label scale shift)
      (· = label omitted)).submatrix
      (transformedDeletionEquiv label omitted) (transformedDeletionEquiv label omitted) =
      Matrix.diagonal (fun who => scale (deletionIndex omitted who)) * deletionMatrix omitted := by
  ext who owner
  rw [Matrix.submatrix_apply, PassiveRowInverseCriterion.childMatrix, Matrix.of_apply,
    normalizedSoloMatrix_eq_soloReward_sub]
  change quittingSingletonMatrix (affineReindexedReward label scale shift)
    (transformedDeletionEquiv label omitted who).val
    (transformedDeletionEquiv label omitted owner).val = _
  change quittingProjectiveLCPMatrix (affineReindexedReward label scale shift) _ _ = _
  rw [affineReindexed_matrix_entry, transformedDeletionEquiv_val, transformedDeletionEquiv_val]
  simp only [label.symm_apply_apply, Matrix.diagonal_mul, deletionMatrix, Matrix.submatrix_apply]

/-- The inverse of the actual transformed child scales columns by positive reciprocals. -/
theorem actual_transformed_deletionInverse_entry (label : Player ≃ Player)
    (scale shift : Payoff Player) (hscale : ∀ who, 0 < scale who)
    (omitted : Player) (who owner : Fin 3) :
    (PassiveRowInverseCriterion.childMatrix (affineReindexedReward label scale shift)
        (· = label omitted))⁻¹
        (transformedDeletionEquiv label omitted who)
        (transformedDeletionEquiv label omitted owner) =
      deletionInverse omitted who owner / scale (deletionIndex omitted owner) := by
  have hdiagonal : (Matrix.diagonal (fun i => scale (deletionIndex omitted i)))⁻¹ =
      Matrix.diagonal (fun i => (scale (deletionIndex omitted i))⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    have hproduct : (fun i => (scale (deletionIndex omitted i))⁻¹ *
        scale (deletionIndex omitted i)) = fun _ : Fin 3 => (1 : ℝ) := by
      funext i
      exact inv_mul_cancel₀ (hscale _).ne'
    rw [hproduct]
    exact Matrix.diagonal_one
  have hinverse := Matrix.inv_submatrix_equiv
    (PassiveRowInverseCriterion.childMatrix (affineReindexedReward label scale shift)
      (· = label omitted))
    (transformedDeletionEquiv label omitted) (transformedDeletionEquiv label omitted)
  rw [actual_transformed_deletionMatrix_eq, Matrix.mul_inv_rev,
    deletionMatrix_inverse, hdiagonal] at hinverse
  have hentry := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M who owner) hinverse.symm
  simpa only [Matrix.submatrix_apply, Matrix.mul_diagonal, div_eq_mul_inv] using hentry

def deletionOutsideInverse (omitted : Player) : Fin 3 → ℝ :=
  (fun who => matrix omitted (deletionIndex omitted who)) ᵥ* deletionInverse omitted

theorem actual_transformed_outsideRow_entry (label : Player ≃ Player)
    (scale shift : Payoff Player) (omitted : Player) (who : Fin 3) :
    PassiveRowInverseCriterion.outsideRow (affineReindexedReward label scale shift)
        (· = label omitted) (label omitted) (transformedDeletionEquiv label omitted who) =
      scale omitted * matrix omitted (deletionIndex omitted who) := by
  change quittingProjectiveLCPMatrix (affineReindexedReward label scale shift)
    (label omitted) (transformedDeletionEquiv label omitted who).val = _
  rw [affineReindexed_matrix_entry, transformedDeletionEquiv_val]
  simp only [label.symm_apply_apply]

/-- The original outside row and actual inverse give the transported weights. -/
theorem actual_transformed_inverseWeight_entry (label : Player ≃ Player)
    (scale shift : Payoff Player) (hscale : ∀ who, 0 < scale who)
    (omitted : Player) (owner : Fin 3) :
    PassiveRowInverseCriterion.inverseWeight (affineReindexedReward label scale shift)
        (· = label omitted) (label omitted) (transformedDeletionEquiv label omitted owner) =
      scale omitted * deletionOutsideInverse omitted owner /
        scale (deletionIndex omitted owner) := by
  rw [PassiveRowInverseCriterion.inverseWeight, Matrix.vecMul_apply_eq_sum]
  rw [← (transformedDeletionEquiv label omitted).sum_comp]
  simp_rw [actual_transformed_outsideRow_entry,
    actual_transformed_deletionInverse_entry label scale shift hscale]
  rw [deletionOutsideInverse, Matrix.vecMul_apply_eq_sum, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro who _
  ring

/-- Every actual omitted owner fails at least one named raw passive-inverse test.
The label is arbitrary and the row shifts and positive scales are retained. -/
theorem not_passiveInverseTests_affineReindexed (label : Player ≃ Player)
    (scale shift : Payoff Player) (hscale : ∀ who, 0 < scale who) (omitted : Player) :
    ¬ ((∀ who owner : DeletedChild (label omitted),
        0 ≤ (PassiveRowInverseCriterion.childMatrix (affineReindexedReward label scale shift)
          (· = label omitted))⁻¹ who owner) ∧
      ∀ inside : DeletedChild (label omitted),
        0 ≤ PassiveRowInverseCriterion.inverseWeight (affineReindexedReward label scale shift)
          (· = label omitted) (label omitted) inside) := by
  rintro ⟨hchild, houtside⟩
  have hinverse (who owner : Fin 3) :
      0 ≤ deletionInverse omitted who owner / scale (deletionIndex omitted owner) :=
    (hchild (transformedDeletionEquiv label omitted who)
      (transformedDeletionEquiv label omitted owner)).trans_eq
      (actual_transformed_deletionInverse_entry label scale shift hscale omitted who owner)
  have hweight (owner : Fin 3) :
      0 ≤ scale omitted * deletionOutsideInverse omitted owner /
        scale (deletionIndex omitted owner) :=
    (houtside (transformedDeletionEquiv label omitted owner)).trans_eq
      (actual_transformed_inverseWeight_entry label scale shift hscale omitted owner)
  fin_cases omitted
  · have hentry := hweight 0
    have hnegative : scale 0 * deletionOutsideInverse 0 0 /
        scale (deletionIndex 0 0) < 0 := by
      apply div_neg_of_neg_of_pos _ (hscale _)
      apply mul_neg_of_pos_of_neg (hscale 0)
      norm_num [deletionOutsideInverse, deletionInverse, deletionIndex, matrix,
        Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
    exact (not_lt_of_ge hentry) hnegative
  · have hentry := hinverse 0 1
    have hnegative : deletionInverse 1 0 1 / scale (deletionIndex 1 1) < 0 :=
      div_neg_of_neg_of_pos (by norm_num [deletionInverse]) (hscale _)
    exact (not_lt_of_ge hentry) hnegative
  · have hentry := hinverse 0 0
    have hnegative : deletionInverse 2 0 0 / scale (deletionIndex 2 0) < 0 :=
      div_neg_of_neg_of_pos (by norm_num [deletionInverse]) (hscale _)
    exact (not_lt_of_ge hentry) hnegative
  · have hentry := hinverse 0 0
    have hnegative : deletionInverse 3 0 0 / scale (deletionIndex 3 0) < 0 :=
      div_neg_of_neg_of_pos (by norm_num [deletionInverse]) (hscale _)
    exact (not_lt_of_ge hentry) hnegative

/-- Literal all-owner form: no choice of the transformed omitted player succeeds. -/
theorem not_passiveInverseTests_affineReindexed_at (label : Player ≃ Player)
    (scale shift : Payoff Player) (hscale : ∀ who, 0 < scale who) (outside : Player) :
    ¬ ((∀ who owner : DeletedChild outside,
        0 ≤ (PassiveRowInverseCriterion.childMatrix (affineReindexedReward label scale shift)
          (· = outside))⁻¹ who owner) ∧
      ∀ inside : DeletedChild outside,
        0 ≤ PassiveRowInverseCriterion.inverseWeight (affineReindexedReward label scale shift)
          (· = outside) outside inside) := by
  obtain ⟨omitted, rfl⟩ := label.surjective outside
  exact not_passiveInverseTests_affineReindexed label scale shift hscale omitted

end GameTheory.NegativePremiumCyclicChild.Fixtures
