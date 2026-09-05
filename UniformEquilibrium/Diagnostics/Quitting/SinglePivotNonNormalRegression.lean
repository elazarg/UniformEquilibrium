import UniformEquilibrium.Quitting.Punishment.SinglePivotPunishment
import UniformEquilibrium.Quitting.Punishment.ContinueFloor

noncomputable section

namespace GameTheory
namespace SinglePivotNonNormalRegression

open QuittingSureSetOwnerRepair

/-- The second signed boundary table: pivot rewards are unchanged, while the
other player receives `-1` exactly when it belongs to the terminal coalition. -/
def reward : {S : Finset Bool // S.Nonempty} → Payoff Bool := fun terminal who =>
  if who then
    if true ∈ terminal.val then -1 else 0
  else if false ∈ terminal.val then 1 else 0

@[simp] theorem pivot_singleton : reward (quittingSingletonTerminal false) false = 1 := by
  simp [reward, quittingSingletonTerminal]

@[simp] theorem other_singleton : reward (quittingSingletonTerminal true) true = -1 := by
  simp [reward, quittingSingletonTerminal]

theorem other_joinAntitone : QuittingOwnerJoinAntitone reward true := by
  intro quitters hquitters hother
  simp [reward, hother]

theorem other_continueFloor_eq_zero : quittingContinueFloor reward true = 0 := by
  apply le_antisymm (quittingContinueFloor_nonpos reward true)
  unfold quittingContinueFloor quittingBlockContinueFloor
  apply Finset.le_min'
  intro value hvalue
  rcases Finset.mem_insert.mp hvalue with rfl | hvalue
  · exact le_rfl
  · rcases Finset.mem_image.mp hvalue with ⟨terminal, hterminal, rfl⟩
    have hnot : true ∉ terminal.1 :=
      Finset.disjoint_singleton_right.mp (Finset.mem_filter.mp hterminal).2
    simp [reward, hnot]

theorem other_punishment_eq_zero : quittingPunishmentValue reward true = 0 := by
  rw [quittingPunishmentValue_eq_continueFloor_of_ownerJoinAntitone reward
    other_joinAntitone (by simp)]
  exact other_continueFloor_eq_zero

theorem offset_other_eq_neg_one : quittingSinglePivotOffset reward false true = -1 := by
  norm_num [quittingSinglePivotOffset, quittingSoloReward, reward,
    quittingSingletonTerminal]

theorem normalized_other_reward (terminal : {S : Finset Bool // S.Nonempty}) :
    quittingSinglePivotNormalizedReward reward false terminal true =
      if true ∈ terminal.val then 0 else 1 := by
  simp [quittingSinglePivotNormalizedReward, quittingSinglePivotOffset,
    reward, quittingSingletonTerminal]
  split <;> norm_num

theorem normalized_other_joinAntitone :
    QuittingOwnerJoinAntitone (quittingSinglePivotNormalizedReward reward false) true := by
  intro quitters hquitters hother
  rw [normalized_other_reward, normalized_other_reward]
  simp [hother]

theorem normalized_other_continueFloor_eq_zero :
    quittingContinueFloor (quittingSinglePivotNormalizedReward reward false) true = 0 := by
  apply le_antisymm (quittingContinueFloor_nonpos _ true)
  unfold quittingContinueFloor quittingBlockContinueFloor
  apply Finset.le_min'
  intro value hvalue
  rcases Finset.mem_insert.mp hvalue with rfl | hvalue
  · exact le_rfl
  · rcases Finset.mem_image.mp hvalue with ⟨terminal, hterminal, rfl⟩
    have hnot : true ∉ terminal.1 :=
      Finset.disjoint_singleton_right.mp (Finset.mem_filter.mp hterminal).2
    rw [normalized_other_reward]
    simp [hnot]

theorem normalized_other_punishment_eq_zero :
    quittingPunishmentValue (quittingSinglePivotNormalizedReward reward false) true = 0 := by
  rw [quittingPunishmentValue_eq_continueFloor_of_ownerJoinAntitone _
    normalized_other_joinAntitone
      (by simp [normalized_other_reward, quittingSingletonTerminal])]
  exact normalized_other_continueFloor_eq_zero

theorem other_finiteReplyPunishment_eq_neg_one :
    quittingFinitePureReplyPunishmentValue reward true = -1 := by
  rw [quittingFinitePureReplyPunishmentValue_eq_min, other_punishment_eq_zero]
  norm_num [quittingSoloReward, reward, quittingSingletonTerminal]

theorem original_allNever_finiteReply_eq_neg_one :
    quittingFinitePureReplyValue reward (quittingAlwaysContinueProfile reward) true = -1 := by
  rw [quittingFinitePureReplyValue_alwaysContinue]
  norm_num [quittingSoloReward, reward, quittingSingletonTerminal]

theorem normalized_allNever_finiteReply_eq_zero :
    quittingFinitePureReplyValue (quittingSinglePivotNormalizedReward reward false)
      (quittingAlwaysContinueProfile
        (quittingSinglePivotNormalizedReward reward false)) true = 0 := by
  rw [quittingFinitePureReplyValue_alwaysContinue]
  simp [quittingSoloReward, normalized_other_reward]

theorem normalized_allNever_fullCap_eq_zero :
    quittingContinuationBestResponseValue
      (quittingSinglePivotNormalizedReward reward false)
      (quittingAlwaysContinueProfile
        (quittingSinglePivotNormalizedReward reward false)) true = 0 := by
  rw [quittingContinuationBestResponseValue_eq_finitePureReplyValue_of_solo_nonneg,
    normalized_allNever_finiteReply_eq_zero]
  simp [normalized_other_reward, quittingSingletonTerminal]

theorem original_allNever_fullCap_eq_zero :
    quittingContinuationBestResponseValue reward
      (quittingAlwaysContinueProfile reward) true = 0 := by
  rw [quittingContinuationBestResponseValue_quittingAlwaysContinueProfile]
  norm_num [reward, quittingSingletonTerminal]

theorem original_allNever_payoff_zero (who : Bool) :
    quittingTerminalPayoff reward (quittingAlwaysContinueProfile reward) who = 0 :=
  quittingTerminalPayoff_quittingAlwaysContinue reward who

theorem normalized_allNever_payoff_zero (who : Bool) :
    quittingTerminalPayoff (quittingSinglePivotNormalizedReward reward false)
      (quittingAlwaysContinueProfile
        (quittingSinglePivotNormalizedReward reward false)) who = 0 :=
  quittingTerminalPayoff_quittingAlwaysContinue _ who

/-- Never gives the lower bound zero, while the all-Never opponents attain the
matching punishment cap in both the original and normalized tables. -/
theorem allNever_candidates_and_never_lowerBound :
    quittingFinitePureReplyValue reward (quittingAlwaysContinueProfile reward) true = -1 ∧
      quittingPunishmentValue reward true = 0 ∧
      quittingFinitePureReplyValue (quittingSinglePivotNormalizedReward reward false)
        (quittingAlwaysContinueProfile
          (quittingSinglePivotNormalizedReward reward false)) true = 0 ∧
      quittingPunishmentValue (quittingSinglePivotNormalizedReward reward false) true = 0 ∧
      quittingContinuationBestResponseValue reward
        (quittingAlwaysContinueProfile reward) true = 0 ∧
      quittingContinuationBestResponseValue
        (quittingSinglePivotNormalizedReward reward false)
        (quittingAlwaysContinueProfile
          (quittingSinglePivotNormalizedReward reward false)) true = 0 ∧
      quittingTerminalPayoff reward (quittingAlwaysContinueProfile reward) true = 0 ∧
      quittingTerminalPayoff (quittingSinglePivotNormalizedReward reward false)
        (quittingAlwaysContinueProfile
          (quittingSinglePivotNormalizedReward reward false)) true = 0 :=
  ⟨original_allNever_finiteReply_eq_neg_one, other_punishment_eq_zero,
    normalized_allNever_finiteReply_eq_zero, normalized_other_punishment_eq_zero,
    original_allNever_fullCap_eq_zero, normalized_allNever_fullCap_eq_zero,
    original_allNever_payoff_zero true, normalized_allNever_payoff_zero true⟩

/-- Literal failure of the punishment transport when normality is omitted. -/
theorem nonnormal_boundary :
    quittingSoloReward reward true true = -1 ∧
      quittingPunishmentValue reward true = 0 ∧
      quittingFinitePureReplyPunishmentValue reward true = -1 ∧
      quittingPunishmentValue (quittingSinglePivotNormalizedReward reward false) true = 0 ∧
      quittingPunishmentValue (quittingSinglePivotNormalizedReward reward false) true ≠
        (quittingPunishmentValue reward true - quittingSinglePivotOffset reward false true) /
          quittingSoloReward reward false false := by
  refine ⟨by simp [quittingSoloReward, reward],
    other_punishment_eq_zero,
    other_finiteReplyPunishment_eq_neg_one,
    normalized_other_punishment_eq_zero, ?_⟩
  · rw [normalized_other_punishment_eq_zero, other_punishment_eq_zero,
      offset_other_eq_neg_one]
    norm_num [quittingSoloReward, reward, quittingSingletonTerminal]

end SinglePivotNonNormalRegression
end GameTheory
