import MathUE.Finset.FinFourNonemptyCoalitions
import UniformEquilibrium.Quitting.Examples.NegativePremiumCyclicChildFixtures
import UniformEquilibrium.Quitting.Root.PlayerReindex
import UniformEquilibrium.Quitting.Classification.Existence.ConditionalFaceGapRange
import UniformEquilibrium.Quitting.Stationary.ComponentwiseWeightedPotential
import UniformEquilibrium.Quitting.Stationary.SignedInfluenceCycleBalance

/-! # Literal reward-range and influence screens

The complete sixty-coordinate fixture is used here, not only its singleton
matrix. Relabeling preserves the displayed actual membership-gain witnesses.
The named coarse source screens do not exclude broader certificates or policies.
-/

noncomputable section

namespace GameTheory.NegativePremiumCyclicChild.Fixtures

open QuittingSureSetOwnerRepair

theorem survivor_participant_reward_le_upper
    (coalition : {S : Finset Player // S.Nonempty}) (who : Player)
    (hwho : who ∈ coalition.val) : survivorReward coalition who ≤ upper := by
  obtain ⟨row, rfl⟩ := Math.Finset.finFourCoalitionRowEquiv.surjective coalition
  fin_cases row <;> fin_cases who
  all_goals
    norm_num +decide [Math.Finset.finFourCoalitionRowEquiv,
      Math.Finset.finFourCoalitionOfRow] at hwho
  all_goals norm_num +decide [Math.Finset.finFourCoalitionRowEquiv,
    Math.Finset.finFourCoalitionOfRow, survivorReward, lower, upper]

private theorem relabel_setReward (label : Player ≃ Player) (coalition : Finset Player)
    (who : Player) :
    quittingSetReward (quittingRewardReindex label survivorReward)
        (coalition.map label.toEmbedding) (label who) =
      quittingSetReward survivorReward coalition who := by
  by_cases hnonempty : coalition.Nonempty
  · have hmap : (coalition.map label.toEmbedding).Nonempty :=
      Finset.map_nonempty.mpr hnonempty
    have hpullback : (quittingCoalitionEquiv label).symm
        ⟨coalition.map label.toEmbedding, hmap⟩ = ⟨coalition, hnonempty⟩ :=
      (quittingCoalitionEquiv label).left_inv ⟨coalition, hnonempty⟩
    simp only [quittingSetReward, hnonempty, hmap, dite_true,
      quittingRewardReindex_apply, label.symm_apply_apply, hpullback]
  · have hmap : ¬(coalition.map label.toEmbedding).Nonempty := by
      simpa only [Finset.map_nonempty] using hnonempty
    simp only [quittingSetReward, hnonempty, hmap, dite_false]

private theorem relabel_membershipGain (label : Player ≃ Player) (who : Player)
    (background : Finset Player) (hwho : who ∉ background) :
    quittingMembershipGain (quittingRewardReindex label survivorReward)
        (label who) (background.map label.toEmbedding) =
      quittingMembershipGain survivorReward who background := by
  have hmap : label who ∉ background.map label.toEmbedding := by
    simpa only [Finset.mem_map_equiv, label.symm_apply_apply] using hwho
  simp only [quittingMembershipGain, MathUE.binaryJoinGain,
    Finset.erase_eq_of_notMem hwho, Finset.erase_eq_of_notMem hmap]
  have hinsert : (insert who background).map label.toEmbedding =
      insert (label who) (background.map label.toEmbedding) := by
    exact Finset.map_insert label.toEmbedding who background
  rw [← hinsert, relabel_setReward, relabel_setReward]

theorem survivor_membershipGain_one_empty :
    quittingMembershipGain survivorReward 1 ∅ = 1 := by
  norm_num +decide [quittingMembershipGain, MathUE.binaryJoinGain,
    quittingSetReward, survivorReward]

theorem survivor_membershipGain_one_zero :
    quittingMembershipGain survivorReward 1 {0} = 1 - loss := by
  norm_num +decide [quittingMembershipGain, MathUE.binaryJoinGain, quittingSetReward,
    survivorReward, loss, lower, upper]

theorem survivor_membershipGain_one_two :
    quittingMembershipGain survivorReward 1 {2} = 1 := by
  norm_num +decide [quittingMembershipGain, MathUE.binaryJoinGain,
    quittingSetReward, survivorReward]

theorem survivor_membershipGain_one_zero_two :
    quittingMembershipGain survivorReward 1 {0, 2} = 2 - loss := by
  norm_num +decide [quittingMembershipGain, MathUE.binaryJoinGain, quittingSetReward,
    survivorReward, loss, lower, upper]

theorem relabel_pairInfluence_zero_one_empty (label : Player ≃ Player) :
    quittingPairInfluence (quittingRewardReindex label survivorReward)
      (label 0) (label 1) ∅ = -loss := by
  have hzero := relabel_membershipGain label 1 {0} (by decide)
  have hempty := relabel_membershipGain label 1 ∅ (by decide)
  simp only [Finset.map_singleton, Finset.map_empty, Equiv.toEmbedding_apply,
    survivor_membershipGain_one_zero, survivor_membershipGain_one_empty] at hzero hempty
  simp only [quittingPairInfluence, Finset.insert_empty, hzero, hempty]
  ring

theorem relabel_pairInfluence_zero_one_two (label : Player ≃ Player) :
    quittingPairInfluence (quittingRewardReindex label survivorReward)
      (label 0) (label 1) {label 2} = 1 - loss := by
  have hzeroTwo := relabel_membershipGain label 1 {0, 2} (by decide)
  have htwo := relabel_membershipGain label 1 {2} (by decide)
  simp only [Finset.map_insert, Finset.map_singleton, Equiv.toEmbedding_apply,
    survivor_membershipGain_one_zero_two, survivor_membershipGain_one_two] at hzeroTwo htwo
  simp only [quittingPairInfluence, hzeroTwo, htwo]
  ring

/-- Two actual backgrounds have opposite strict influence signs after any relabeling. -/
theorem not_signConsistentQuittingInfluence_relabel (label : Player ≃ Player) :
    ¬SignConsistentQuittingInfluence (quittingRewardReindex label survivorReward) := by
  intro hconsistent
  have hneq : label 0 ≠ label 1 := label.injective.ne (by decide)
  have hother : label 0 ∉ ({label 2} : Finset Player) := by
    simp
  have hwho : label 1 ∉ ({label 2} : Finset Player) := by
    simp
  rcases hconsistent hneq with hpositive | hnegative | habsent
  · have h := hpositive.1 ∅ (by simp) (by simp)
    rw [relabel_pairInfluence_zero_one_empty] at h
    norm_num [loss] at h
  · have h := hnegative.1 {label 2} hother hwho
    rw [relabel_pairInfluence_zero_one_two] at h
    norm_num [loss] at h
  · have h := habsent ∅ (by simp) (by simp)
    rw [relabel_pairInfluence_zero_one_empty] at h
    norm_num [loss] at h

/-- No coefficients can make the actual membership gain affine after relabeling. -/
theorem not_affineQuittingMembershipGain_relabel (label : Player ≃ Player)
    (bias : Payoff Player) (coefficient : Player → Player → ℝ) :
    ¬IsAffineQuittingMembershipGain (quittingRewardReindex label survivorReward)
      bias coefficient := by
  intro haffine
  have hformula (background : Finset Player) (hwho : (1 : Player) ∉ background) :
      quittingMembershipGain survivorReward 1 background = bias (label 1) +
        ∑ other ∈ background.map label.toEmbedding, coefficient (label 1) other := by
    have hmap : label 1 ∉ background.map label.toEmbedding := by
      simpa only [Finset.mem_map_equiv, label.symm_apply_apply] using hwho
    have h := haffine (label 1) (background.map label.toEmbedding) hmap
    rw [← relabel_membershipGain label 1 background hwho]
    simpa only [quittingMembershipGain, MathUE.binaryJoinGain,
      Finset.erase_eq_of_notMem hmap] using h
  have hempty := hformula ∅ (by decide)
  have hzero := hformula {0} (by decide)
  have htwo := hformula {2} (by decide)
  have hzeroTwo := hformula {0, 2} (by decide)
  rw [survivor_membershipGain_one_empty] at hempty
  rw [survivor_membershipGain_one_zero] at hzero
  rw [survivor_membershipGain_one_two] at htwo
  rw [survivor_membershipGain_one_zero_two] at hzeroTwo
  have hneq : label 0 ≠ label 2 := label.injective.ne (by decide)
  simp only [Finset.map_empty, Finset.sum_empty, add_zero] at hempty
  simp only [Finset.map_singleton, Equiv.toEmbedding_apply,
    Finset.sum_singleton] at hzero htwo
  simp only [Finset.map_insert, Finset.map_singleton, Equiv.toEmbedding_apply] at hzeroTwo
  rw [Finset.sum_insert (by simpa only [Finset.mem_singleton] using hneq),
    Finset.sum_singleton] at hzeroTwo
  linarith

/-- Every legal blocker mixture fails the named coarse reward-range source.
Only the particular lower mixture probability needs a validity hypothesis. -/
theorem not_conditionalFaceGapRange_of_valid_blocker_weight_relabel
    (label : Player ≃ Player) (low high : Payoff Player) (blocker : Equiv.Perm Player)
    (quitWithoutLower quitWithoutUpper quitWithLower quitWithUpper : Payoff Player)
    (continueLower continueUpper : Payoff Player)
    (hvalid : low (blocker (label 1)) ∈ Set.Icc (0 : ℝ) 1) :
    ¬IsQuittingConditionalFaceGapRange (quittingRewardReindex label survivorReward)
      low high blocker quitWithoutLower quitWithoutUpper quitWithLower quitWithUpper
      continueLower continueUpper := by
  intro hrange
  have hwithout := (hrange.2.1 (label 1) ∅ (by simp) (by simp)).1
  have hwith := (hrange.2.1 (label 1) ∅ (by simp) (by simp)).2.2.1
  have hwithoutValue : quittingRewardReindex label survivorReward
      ⟨insert (label 1) ∅, Finset.insert_nonempty _ _⟩ (label 1) = 1 := by
    have h := relabel_setReward label {1} 1
    simp [quittingSetReward, survivorReward] at h ⊢
  rw [hwithoutValue] at hwithout
  have hparticipant := survivor_participant_reward_le_upper
    ((quittingCoalitionEquiv label).symm
      ⟨insert (blocker (label 1)) (insert (label 1) ∅), Finset.insert_nonempty _ _⟩) 1
    (by simp [quittingCoalitionEquiv])
  have hwithUpper : quitWithLower (label 1) ≤ upper := by
    exact hwith.trans (by simpa only [quittingRewardReindex_apply,
      label.symm_apply_apply] using hparticipant)
  have hwithoutUpper : quitWithoutLower (label 1) ≤ upper :=
    hwithout.trans (by norm_num [upper])
  have hcontinue := (hrange.2.2.1 (label 1)
    (quittingCoalitionEquiv label ⟨{3}, by simp⟩)
    (by simp [quittingCoalitionEquiv])).2
  have hcontinueValue : quittingRewardReindex label survivorReward
      (quittingCoalitionEquiv label ⟨{3}, by simp⟩) (label 1) = 4 := by
    simp [quittingRewardReindex, survivorReward]
  rw [hcontinueValue] at hcontinue
  have hmixture : (1 - low (blocker (label 1))) * quitWithoutLower (label 1) +
      low (blocker (label 1)) * quitWithLower (label 1) ≤ upper := by
    calc
      _ ≤ (1 - low (blocker (label 1))) * upper +
          low (blocker (label 1)) * upper :=
        add_le_add (mul_le_mul_of_nonneg_left hwithoutUpper (by linarith [hvalid.2]))
          (mul_le_mul_of_nonneg_left hwithUpper hvalid.1)
      _ = upper := by ring
  have hstrict := hrange.2.2.2.1 (label 1)
  norm_num [upper] at hmixture
  linarith

end GameTheory.NegativePremiumCyclicChild.Fixtures
