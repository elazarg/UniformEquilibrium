import UniformEquilibrium.Quitting.Classification.WeightedQuittingTrapLeavers
import UniformEquilibrium.Quitting.Classification.PassiveQuittingRewardPerturbation

/-! # All-passive perturbations preserve global floors and strictify leave sums

The same weight vector remains valid for the global participant tests.
Each nonempty proper leave sum decreases by delta times its positive missing
weight sum. No normalization of weights is needed.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem passiveQuittingRewardPerturbation_weightedInsertedPremium
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (delta : ℝ)
    (weight : ι → ℝ) (coalition : Finset ι) :
    quittingWeightedInsertedPremium (passiveQuittingRewardPerturbation reward delta)
        weight coalition = quittingWeightedInsertedPremium reward weight coalition := by
  unfold quittingWeightedInsertedPremium
  apply Finset.sum_congr rfl
  intro player _
  rw [passiveQuittingRewardPerturbation_participant reward delta _ player
    (Finset.mem_insert_self _ _), passiveQuittingRewardPerturbation_singleton]

theorem passiveQuittingRewardPerturbation_globalWeightedFloor_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (delta : ℝ) (weight : ι → ℝ) :
    HasGlobalQuittingWeightedFloor (passiveQuittingRewardPerturbation reward delta) weight ↔
      HasGlobalQuittingWeightedFloor reward weight := by
  simp only [HasGlobalQuittingWeightedFloor,
    passiveQuittingRewardPerturbation_weightedInsertedPremium]

theorem passiveQuittingRewardPerturbation_globalWeightedFloorBox
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (delta bound : ℝ) :
    quittingGlobalWeightedFloorBox (passiveQuittingRewardPerturbation reward delta) bound =
      quittingGlobalWeightedFloorBox reward bound := by
  ext tail
  simp only [quittingGlobalWeightedFloorBox, Set.mem_inter_iff, Set.mem_ofPred_eq,
    passiveQuittingRewardPerturbation_globalWeightedFloor_iff,
    passiveQuittingRewardPerturbation_singleton]

omit [Fintype ι] in
theorem passiveQuittingRewardPerturbation_weightedLeaveSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (delta : ℝ)
    (active : Finset ι) (weight : ι → ℝ)
    (coalition : {S : Finset ι // S.Nonempty}) :
    quittingWeightedLeaveSum (passiveQuittingRewardPerturbation reward delta)
        active weight coalition = quittingWeightedLeaveSum reward active weight coalition -
      delta * ∑ player ∈ active \ coalition.val, weight player := by
  unfold quittingWeightedLeaveSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro player hplayer
  rw [passiveQuittingRewardPerturbation_participant reward delta _ player
      (Finset.mem_insert_self _ _),
    passiveQuittingRewardPerturbation_passive reward delta coalition player
      (Finset.mem_sdiff.mp hplayer).2]
  ring

/-- Weak raw tests become strict using their original per-trap weight
witnesses. Trap membership and global floor validity are exactly preserved. -/
theorem passiveQuittingRewardPerturbation_weightedStrictLeavers_of_weakLeavers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hleavers : HasWeightedQuittingTrapLeavers reward (· ≤ ·))
    (delta : ℝ) (hdelta : 0 < delta) :
    HasWeightedQuittingTrapLeavers (passiveQuittingRewardPerturbation reward delta) (· < ·) := by
  intro active htrap
  obtain ⟨weight, hpositive, houtside, hglobal, hleave⟩ := hleavers active
    ((passiveQuittingRewardPerturbation_trap_iff reward delta active).1 htrap)
  refine ⟨weight, hpositive, houtside, ?_, ?_⟩
  · intro coalition
    rw [passiveQuittingRewardPerturbation_weightedInsertedPremium]
    exact hglobal coalition
  · intro coalition hnonempty hproper
    have hmissing : (active \ coalition).Nonempty := by
      apply Finset.sdiff_nonempty.mpr
      exact not_subset_of_ssubset hproper
    have hsumPositive : 0 < ∑ player ∈ active \ coalition, weight player := by
      apply Finset.sum_pos
      · intro player hplayer
        exact hpositive player (Finset.mem_sdiff.mp hplayer).1
      · exact hmissing
    rw [passiveQuittingRewardPerturbation_weightedLeaveSum]
    have hweak := hleave coalition hnonempty hproper
    have hdrop := mul_pos hdelta hsumPositive
    linarith

end GameTheory
