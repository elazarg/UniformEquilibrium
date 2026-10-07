import UniformEquilibrium.Quitting.Examples.NegativePremiumCyclicChildFixtureMatrix
import UniformEquilibrium.Quitting.Cycles.SignedFourCycleRewardAdapter
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.CyclicChildPassiveInverseExit
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.CyclicChildLowDegreeExit

/-! # Further actual raw-source screens for the negative-premium fixture

The literal original-game comparisons defeat the named signed four-clock,
paired-cycle, and cyclic-child exits under every relabeling and positive
row-affine transform. Every cyclic-child raw witness is classified internally;
its resonance gap and negative actual exterior inverse weight are computed.
These are source screens, not an exclusion of other equilibrium policies.
-/

noncomputable section

namespace GameTheory.NegativePremiumCyclicChild.Fixtures

open QuittingLCPClassification

theorem matrix_column_zero_nonpositive (who : Player) : matrix who 0 ≤ 0 := by
  fin_cases who <;> norm_num [matrix]

/-- A predecessor cycle cannot pass through the actual nonpositive column. -/
theorem no_signedFourCycleSingletonData_affineReindexed (label : Player ≃ Player)
    (scale shift : Payoff Player) (hscale : ∀ who, 0 < scale who) :
    ¬Nonempty (SignedFourCycleSingletonData (affineReindexedReward label scale shift)) := by
  rintro ⟨data⟩
  have hclock (index : Player) : (index + 1) + 3 = index := by
    fin_cases index <;> rfl
  have hnonpositive : quittingSingletonMatrix (affineReindexedReward label scale shift)
      (label 0 + 1) (label 0) ≤ 0 := by
    change quittingProjectiveLCPMatrix (affineReindexedReward label scale shift)
      (label 0 + 1) (label 0) ≤ 0
    rw [affineReindexed_matrix_entry]
    simp only [label.symm_apply_apply]
    exact mul_nonpos_of_nonneg_of_nonpos (hscale _).le (matrix_column_zero_nonpositive _)
  have hentry := data.predecessor (label 0 + 1)
  rw [hclock] at hentry
  have hpositive := data.h_pos (label 0 + 1)
  linarith

/-- Two distinct below-own quitters cannot both be the actual unique partner. -/
theorem not_pairedCycleRawRegion_affineReindexed (label : Player ≃ Player)
    (scale shift : Payoff Player) (hscale : ∀ who, 0 < scale who)
    {period : ℕ} (schedule : PairedCycle.Schedule Player period) :
    ¬PairedCycle.RawRegion (affineReindexedReward label scale shift) schedule := by
  intro hregion
  have hbelow (owner : Player) (hentry : matrix 1 owner = -1) :
      affineReindexedReward label scale shift (quittingSingletonTerminal (label owner))
        (label 1) < PairedCycle.singleton (affineReindexedReward label scale shift) (label 1) := by
    apply sub_neg.mp
    change quittingProjectiveLCPMatrix (affineReindexedReward label scale shift)
      (label 1) (label owner) < 0
    rw [affineReindexed_matrix_entry]
    simp only [label.symm_apply_apply, hentry]
    nlinarith [hscale 1]
  have hfirst := hregion.eq_partner_of_singleton_lt (hbelow 0 (by norm_num [matrix]))
  have hsecond := hregion.eq_partner_of_singleton_lt (hbelow 2 (by norm_num [matrix]))
  have hsame := label.injective (hfirst.trans hsecond.symm)
  norm_num at hsame

private theorem matrix_nonzero_column_positive (owner : Player) (howner : owner ≠ 0) :
    ∃ who, who ≠ owner ∧ 0 < matrix who owner := by
  fin_cases owner
  · exact (howner rfl).elim
  · exact ⟨2, by decide, by norm_num [matrix]⟩
  · exact ⟨3, by decide, by norm_num [matrix]⟩
  · exact ⟨1, by decide, by norm_num [matrix]⟩

private theorem matrix_negative_child_rotations (i j k : Player)
    (hi : i ≠ 0) (hj : j ≠ 0) (hk : k ≠ 0)
    (hij : matrix i j < 0) (hjk : matrix j k < 0) (hki : matrix k i < 0) :
    (i = 1 ∧ j = 2 ∧ k = 3) ∨ (i = 2 ∧ j = 3 ∧ k = 1) ∨
      (i = 3 ∧ j = 1 ∧ k = 2) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [matrix] at *

/-- Every possible actual raw witness has one of the three cyclic exterior rows.
The child scales and harms are derived from the reverse-edge normalization. -/
theorem cyclicChildRawRows_affineReindexed_parameters (label : Player ≃ Player)
    (scale shift : Payoff Player) (hscale : ∀ who, 0 < scale who)
    {a b c h₁ h₂ h₃ u v R : ℝ}
    (hrows : CyclicChildSingleton.RawRows a b c h₁ h₂ h₃ u v R
      (affineReindexedReward label scale shift))
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hh₃ : 0 < h₃) :
    label.symm 0 = 0 ∧ scale (label.symm 1) = 1 ∧
      scale (label.symm 2) = 1 ∧ scale (label.symm 3) = 1 ∧
      a = 3 ∧ b = 3 ∧ c = 3 ∧ h₁ = 1 ∧ h₂ = 1 ∧ h₃ = 1 ∧
      ((u = 1 + scale 0 ∧ v = 1 + scale 0 ∧ R = 1 - scale 0) ∨
       (u = 1 + scale 0 ∧ v = 1 - scale 0 ∧ R = 1 + scale 0) ∨
       (u = 1 - scale 0 ∧ v = 1 + scale 0 ∧ R = 1 + scale 0)) := by
  have hmatrix := CyclicChildSingleton.singletonMatrix_eq hrows
  have hentry (who owner : Player) :
      scale (label.symm who) * matrix (label.symm who) (label.symm owner) =
        Math.CyclicChildJointPhase.exteriorMatrix a b c h₁ h₂ h₃
          ![u - 1, v - 1, R - 1] who owner := by
    have h := congrFun (congrFun hmatrix who) owner
    change quittingProjectiveLCPMatrix (affineReindexedReward label scale shift) who owner = _ at h
    rw [affineReindexed_matrix_entry] at h
    exact h
  have h01 := hentry 0 1
  have h02 := hentry 0 2
  have h03 := hentry 0 3
  have h10 := hentry 1 0
  have h12 := hentry 1 2
  have h13 := hentry 1 3
  have h20 := hentry 2 0
  have h21 := hentry 2 1
  have h23 := hentry 2 3
  have h30 := hentry 3 0
  have h31 := hentry 3 1
  have h32 := hentry 3 2
  have hnegative (who : Player) (hwho : who ≠ 0) :
      scale (label.symm who) * matrix (label.symm who) (label.symm 0) < 0 := by
    rw [hentry]
    fin_cases who
    · exact (hwho rfl).elim
    · simpa [Math.CyclicChildJointPhase.exteriorMatrix] using neg_neg_of_pos hh₁
    · simpa [Math.CyclicChildJointPhase.exteriorMatrix] using neg_neg_of_pos hh₂
    · simpa [Math.CyclicChildJointPhase.exteriorMatrix] using neg_neg_of_pos hh₃
  have hpivot : label.symm 0 = 0 := by
    by_contra hnot
    obtain ⟨who, hwho, hpositive⟩ := matrix_nonzero_column_positive _ hnot
    have hlabel : label who ≠ 0 := by
      intro heq
      exact hwho (by simpa using congrArg label.symm heq)
    have hneg := hnegative (label who) hlabel
    simp only [label.symm_apply_apply] at hneg
    exact (not_lt_of_ge (mul_nonneg (hscale who).le hpositive.le)) hneg
  have hchild (who : Player) (hwho : who ≠ 0) : label.symm who ≠ 0 := by
    rw [← hpivot]
    exact fun heq => hwho (label.symm.injective heq)
  have hreverse (i j : Player)
      (heq : scale (label.symm i) * matrix (label.symm i) (label.symm j) = -1) :
      matrix (label.symm i) (label.symm j) < 0 := by
    have hnegativeProduct : scale (label.symm i) *
        matrix (label.symm i) (label.symm j) < 0 := by rw [heq]; norm_num
    by_contra hnot
    exact (not_lt_of_ge (mul_nonneg (hscale _).le (not_lt.mp hnot))) hnegativeProduct
  have hrotations := matrix_negative_child_rotations _ _ _
    (hchild 1 (by decide)) (hchild 2 (by decide)) (hchild 3 (by decide))
    (hreverse 1 2 (by simpa [Math.CyclicChildJointPhase.exteriorMatrix] using h12))
    (hreverse 2 3 (by simpa [Math.CyclicChildJointPhase.exteriorMatrix] using h23))
    (hreverse 3 1 (by simpa [Math.CyclicChildJointPhase.exteriorMatrix] using h31))
  rcases hrotations with ⟨hfirst, hsecond, hthird⟩ |
    ⟨hfirst, hsecond, hthird⟩ | ⟨hfirst, hsecond, hthird⟩
  all_goals
    simp only [hpivot, hfirst, hsecond, hthird] at h01 h02 h03 h10 h12 h13
    simp only [hpivot, hfirst, hsecond, hthird] at h20 h21 h23 h30 h31 h32
    norm_num [matrix, Math.CyclicChildJointPhase.exteriorMatrix] at h01 h02 h03
    norm_num [matrix, Math.CyclicChildJointPhase.exteriorMatrix] at h10 h12 h13
    norm_num [matrix, Math.CyclicChildJointPhase.exteriorMatrix] at h20 h21 h23
    norm_num [matrix, Math.CyclicChildJointPhase.exteriorMatrix] at h30 h31 h32
    simp only [hpivot, hfirst, hsecond, hthird]
    refine ⟨True.intro, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, ?_⟩
  all_goals first
    | exact Or.inl ⟨by linarith, by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith, by linarith⟩)

/-- The exact exterior inverse row retains the three possible cyclic rotations. -/
theorem cyclicChildRawRows_affineReindexed_inverseWeights (label : Player ≃ Player)
    (scale shift : Payoff Player) (hscale : ∀ who, 0 < scale who)
    {a b c h₁ h₂ h₃ u v R : ℝ}
    (hrows : CyclicChildSingleton.RawRows a b c h₁ h₂ h₃ u v R
      (affineReindexedReward label scale shift))
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hh₃ : 0 < h₃) :
    CyclicChildSingleton.outsideInverseWeight a b c u v R =
        ![-5 * scale 0 / 26, 11 * scale 0 / 26, 7 * scale 0 / 26] ∨
      CyclicChildSingleton.outsideInverseWeight a b c u v R =
        ![11 * scale 0 / 26, 7 * scale 0 / 26, -5 * scale 0 / 26] ∨
      CyclicChildSingleton.outsideInverseWeight a b c u v R =
        ![7 * scale 0 / 26, -5 * scale 0 / 26, 11 * scale 0 / 26] := by
  obtain ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, hcases⟩ :=
    cyclicChildRawRows_affineReindexed_parameters label scale shift hscale hrows hh₁ hh₂ hh₃
  rcases hcases with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · left
    rw [CyclicChildSingleton.outsideInverseWeight_eq]
    ext who
    fin_cases who <;> norm_num [Math.CyclicChildJointPhase.gap] <;> ring
  · right; left
    rw [CyclicChildSingleton.outsideInverseWeight_eq]
    ext who
    fin_cases who <;> norm_num [Math.CyclicChildJointPhase.gap] <;> ring
  · right; right
    rw [CyclicChildSingleton.outsideInverseWeight_eq]
    ext who
    fin_cases who <;> norm_num [Math.CyclicChildJointPhase.gap] <;> ring

/-- Every raw witness lies strictly above resonance and has an actual negative
exterior inverse weight, independently of positive pivot scaling. -/
theorem cyclicChildRawRows_affineReindexed_exitObstructions (label : Player ≃ Player)
    (scale shift : Payoff Player) (hscale : ∀ who, 0 < scale who)
    {a b c h₁ h₂ h₃ u v R : ℝ}
    (hrows : CyclicChildSingleton.RawRows a b c h₁ h₂ h₃ u v R
      (affineReindexedReward label scale shift))
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hh₃ : 0 < h₃) :
    R - CyclicChildSingleton.resonance a b c h₁ h₂ h₃ u v = scale 0 ∧
      ∃ who, CyclicChildSingleton.outsideInverseWeight a b c u v R who < 0 := by
  obtain ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, hcases⟩ :=
    cyclicChildRawRows_affineReindexed_parameters label scale shift hscale hrows hh₁ hh₂ hh₃
  rcases hcases with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · constructor
    · norm_num [CyclicChildSingleton.resonance, Math.CyclicChildJointPhase.balanceVector_eq,
        Math.CyclicChildJointPhase.gap]
      ring
    · refine ⟨0, ?_⟩
      rw [CyclicChildSingleton.outsideInverseWeight_eq]
      norm_num [Math.CyclicChildJointPhase.gap]
      nlinarith [hscale 0]
  · constructor
    · norm_num [CyclicChildSingleton.resonance, Math.CyclicChildJointPhase.balanceVector_eq,
        Math.CyclicChildJointPhase.gap]
    · refine ⟨2, ?_⟩
      rw [CyclicChildSingleton.outsideInverseWeight_eq]
      norm_num [Math.CyclicChildJointPhase.gap]
      nlinarith [hscale 0]
  · constructor
    · norm_num [CyclicChildSingleton.resonance, Math.CyclicChildJointPhase.balanceVector_eq,
        Math.CyclicChildJointPhase.gap]
    · refine ⟨1, ?_⟩
      rw [CyclicChildSingleton.outsideInverseWeight_eq]
      norm_num [Math.CyclicChildJointPhase.gap]
      nlinarith [hscale 0]

/-- Both named resonance and below-resonance exits fail for every raw witness. -/
theorem cyclicChildRawRows_affineReindexed_above_resonance (label : Player ≃ Player)
    (scale shift : Payoff Player) (hscale : ∀ who, 0 < scale who)
    {a b c h₁ h₂ h₃ u v R : ℝ}
    (hrows : CyclicChildSingleton.RawRows a b c h₁ h₂ h₃ u v R
      (affineReindexedReward label scale shift))
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hh₃ : 0 < h₃) :
    CyclicChildSingleton.resonance a b c h₁ h₂ h₃ u v < R := by
  have hgap := (cyclicChildRawRows_affineReindexed_exitObstructions
    label scale shift hscale hrows hh₁ hh₂ hh₃).1
  linarith [hscale 0]

/-- The computed obstruction is an actual deleted-child inverse weight. -/
theorem cyclicChildRawRows_affineReindexed_negative_inverseWeight (label : Player ≃ Player)
    (scale shift : Payoff Player) (hscale : ∀ who, 0 < scale who)
    {a b c h₁ h₂ h₃ u v R : ℝ}
    (hrows : CyclicChildSingleton.RawRows a b c h₁ h₂ h₃ u v R
      (affineReindexedReward label scale shift))
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hh₃ : 0 < h₃) :
    ∃ inside : CyclicChildSingleton.Child,
      PassiveRowInverseCriterion.inverseWeight (affineReindexedReward label scale shift)
        CyclicChildSingleton.deleted 0 inside < 0 := by
  obtain ⟨who, hnegative⟩ := (cyclicChildRawRows_affineReindexed_exitObstructions
    label scale shift hscale hrows hh₁ hh₂ hh₃).2
  refine ⟨CyclicChildSingleton.childEquiv who, ?_⟩
  rw [CyclicChildSingleton.deleted_inverseWeight_eq hrows]
  simpa only [Equiv.symm_apply_apply] using hnegative

/-- The named high exit's literal maximum of passive thresholds is also missed. -/
theorem cyclicChildRawRows_affineReindexed_below_passiveThreshold (label : Player ≃ Player)
    (scale shift : Payoff Player) (hscale : ∀ who, 0 < scale who)
    {a b c h₁ h₂ h₃ u v R : ℝ}
    (hrows : CyclicChildSingleton.RawRows a b c h₁ h₂ h₃ u v R
      (affineReindexedReward label scale shift))
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hh₃ : 0 < h₃) :
    R < CyclicChildSingleton.passiveThreshold a b c u v := by
  obtain ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, hcases⟩ :=
    cyclicChildRawRows_affineReindexed_parameters label scale shift hscale hrows hh₁ hh₂ hh₃
  rcases hcases with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · apply lt_of_lt_of_le _ (le_max_left _ _)
    unfold CyclicChildSingleton.passiveThresholdFirst
    norm_num
    linarith [hscale 0]
  · apply lt_of_lt_of_le _ ((le_max_right _ _).trans (le_max_right _ _))
    unfold CyclicChildSingleton.passiveThresholdThird
    norm_num
    linarith [hscale 0]
  · apply lt_of_lt_of_le _ ((le_max_left _ _).trans (le_max_right _ _))
    unfold CyclicChildSingleton.passiveThresholdSecond
    norm_num
    linarith [hscale 0]

end GameTheory.NegativePremiumCyclicChild.Fixtures
