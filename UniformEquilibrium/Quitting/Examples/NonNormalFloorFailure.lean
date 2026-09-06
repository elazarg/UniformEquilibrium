import UniformEquilibrium.Quitting.Root.AllContinueWeightedRoot
import UniformEquilibrium.Quitting.Punishment.ContinueFloor
import UniformEquilibrium.Quitting.Classification.AbnormalPlayers

/-! # Failure of punishment-floor propagation without normality -/

noncomputable section

namespace GameTheory

open Math.Probability

namespace NonNormalFloorFailure

def reward : {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  fun terminal who ↦ if who ∈ terminal.1 then -1 else 1

def value : Payoff Bool := fun _ ↦ -1 / 2

theorem singletonReward (who : Bool) :
    reward (quittingSingletonTerminal who) who = -1 := by
  simp [reward, quittingSingletonTerminal]

theorem ownerJoinAntitone (who : Bool) :
    QuittingOwnerJoinAntitone reward who := by
  intro quitters hquitters hwho
  simp [reward, hwho]

theorem continueFloor_eq_zero (who : Bool) :
    quittingContinueFloor reward who = 0 := by
  apply le_antisymm (quittingContinueFloor_nonpos reward who)
  unfold quittingContinueFloor quittingBlockContinueFloor
  apply Finset.le_min'
  intro candidate hcandidate
  rcases Finset.mem_insert.mp hcandidate with rfl | hcandidate
  · exact le_rfl
  · obtain ⟨terminal, hterminal, rfl⟩ := Finset.mem_image.mp hcandidate
    have hnot : who ∉ terminal.1 :=
      Finset.disjoint_singleton_right.mp (Finset.mem_filter.mp hterminal).2
    simp [reward, hnot]

theorem punishmentValue_eq_zero (who : Bool) :
    quittingPunishmentValue reward who = 0 := by
  rw [quittingPunishmentValue_eq_continueFloor_of_ownerJoinAntitone
    reward (ownerJoinAntitone who) (by rw [singletonReward]; norm_num)]
  exact continueFloor_eq_zero who

theorem isAbnormal (who : Bool) : IsQuittingAbnormalPlayer reward who := by
  rw [IsQuittingAbnormalPlayer]
  change reward (quittingSingletonTerminal who) who <
    quittingPunishmentValue reward who
  rw [singletonReward, punishmentValue_eq_zero]
  norm_num

theorem allContinue_exactNash :
    IsεQuittingRootNash reward value 0
      (quittingAllContinueRoot : Bool → PMF Bool) := by
  rw [isZeroQuittingRootNash_allContinue_iff_singleton_le]
  intro who
  rw [singletonReward]
  change (-1 : ℝ) ≤ -1 / 2
  norm_num

theorem allContinue_exactBellman :
    quittingRootSuccessorPayoff reward value
      (quittingAllContinueRoot : Bool → PMF Bool) = value :=
  quittingRootSuccessorPayoff_allContinueRoot_eq reward value

theorem constantValue_violates_quarterPunishmentFloor (who : Bool) :
    value who < quittingPunishmentValue reward who - 1 / 4 := by
  rw [punishmentValue_eq_zero]
  simp [value]
  norm_num

theorem allContinue_charge_zero :
    quittingRootAbsorptionMass
      (quittingAllContinueRoot : Bool → PMF Bool) = 0 :=
  quittingRootAbsorptionMass_allContinue_eq_zero

end NonNormalFloorFailure

end GameTheory
