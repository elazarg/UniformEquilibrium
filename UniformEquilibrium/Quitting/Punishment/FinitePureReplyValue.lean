import UniformEquilibrium.Quitting.Stationary.MinMax
import UniformEquilibrium.Quitting.Terminal.CompactStoppingLawCapUpperBound

/-! # Finite-date reply suprema against complete opponent plans

The responder may choose any finite date, but not Never. Opponents retain
arbitrary complete independent strategies; there is no finite deadline.
-/

noncomputable section

namespace GameTheory

open Set Filter Math.Probability
open QuittingSureSetOwnerRepair
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Supremum over all finite pure stopping dates against the actual opponents. -/
def quittingFinitePureReplyValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) : ℝ :=
  ⨆ time : ℕ, quittingTerminalPayoff reward
    (Function.update profile who (quittingPureTimeBehaviorStrategy reward who (some time))) who

/-- Punishment with complete opponent plans but finite-date responses only. -/
def quittingFinitePureReplyPunishmentValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) : ℝ :=
  ⨅ profile : (quittingGame reward).BehaviorProfile,
    quittingFinitePureReplyValue reward profile who

theorem bddAbove_range_quittingFinitePureReplyPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    BddAbove (Set.range fun time : ℕ ↦ quittingTerminalPayoff reward
      (Function.update profile who (quittingPureTimeBehaviorStrategy reward who (some time)))
      who) := by
  refine ⟨quittingRewardBound reward, ?_⟩
  rintro _ ⟨time, rfl⟩
  exact le_of_abs_le (abs_quittingTerminalPayoff_le reward _ who
    (abs_reward_le_quittingRewardBound reward))

theorem quittingTerminalPayoff_finiteTime_le_finitePureReplyValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) (time : ℕ) :
    quittingTerminalPayoff reward
      (Function.update profile who (quittingPureTimeBehaviorStrategy reward who (some time)))
      who ≤ quittingFinitePureReplyValue reward profile who :=
  le_ciSup (bddAbove_range_quittingFinitePureReplyPayoff reward profile who) time

theorem quittingFinitePureReplyValue_le_bestReplyValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingFinitePureReplyValue reward profile who ≤ quittingBestReplyValue reward profile who :=
  ciSup_le fun time ↦ le_quittingBestReplyValue reward profile who
    (quittingPureTimeBehaviorStrategy reward who (some time))

theorem abs_quittingFinitePureReplyValue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) {bound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |quittingFinitePureReplyValue reward profile who| ≤ bound := by
  apply abs_le.mpr
  constructor
  · exact (neg_le_of_abs_le (abs_quittingTerminalPayoff_le reward _ who hreward)).trans
      (quittingTerminalPayoff_finiteTime_le_finitePureReplyValue reward profile who 0)
  · exact ciSup_le fun time ↦
      le_of_abs_le (abs_quittingTerminalPayoff_le reward _ who hreward)

theorem bddBelow_range_quittingFinitePureReplyValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    BddBelow (Set.range fun profile : (quittingGame reward).BehaviorProfile ↦
      quittingFinitePureReplyValue reward profile who) := by
  refine ⟨-quittingRewardBound reward, ?_⟩
  rintro _ ⟨profile, rfl⟩
  exact neg_le_of_abs_le (abs_quittingFinitePureReplyValue_le reward profile who
    (abs_reward_le_quittingRewardBound reward))

theorem quittingFinitePureReplyPunishmentValue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingFinitePureReplyPunishmentValue reward who ≤
      quittingFinitePureReplyValue reward profile who :=
  ciInf_le (bddBelow_range_quittingFinitePureReplyValue reward who) profile

theorem quittingFinitePureReplyPunishmentValue_le_punishmentValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingFinitePureReplyPunishmentValue reward who ≤ quittingPunishmentValue reward who := by
  letI : Nonempty ((quittingGame reward).BehaviorProfile) :=
    ⟨quittingAlwaysContinueProfile reward⟩
  apply le_ciInf
  intro profile
  exact (quittingFinitePureReplyPunishmentValue_le reward who profile).trans
    (quittingFinitePureReplyValue_le_bestReplyValue reward profile who)

/-- Strict approximation to the finite-only infimum produces actual complete
opponent strategies; no attainment of either extremum is asserted. -/
theorem exists_profile_finitePureReplyValue_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) {value : ℝ}
    (hvalue : quittingFinitePureReplyPunishmentValue reward who < value) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      quittingFinitePureReplyValue reward profile who < value := by
  letI : Nonempty ((quittingGame reward).BehaviorProfile) :=
    ⟨quittingAlwaysContinueProfile reward⟩
  exact exists_lt_of_ciInf_lt hvalue

/-- Every finite date, unlike Never, yields the own singleton against
all-Continue opponents, including negative own singleton rewards. -/
theorem quittingTerminalPayoff_finiteTime_alwaysContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) (time : ℕ) :
    quittingTerminalPayoff reward
      (Function.update (quittingAlwaysContinueProfile reward) who
        (quittingPureTimeBehaviorStrategy reward who (some time))) who =
      quittingSoloReward reward who who := by
  have hprofile : quittingAlwaysContinueProfile reward =
      quittingStationaryProfile reward (quittingPureSetRoot ∅) := by
    rw [quittingPureSetRoot_empty]
    rfl
  rw [hprofile, quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingProfileLiveRoot_stationary]
  have h := quittingRootSequencePureTimeTerminalValue_const_some reward
    (quittingPureSetRoot ∅) who 0 time
  simp only [Nat.zero_add] at h
  rw [h, quittingStationaryFixedOpponentsQuitValue_pureSetRoot,
    quittingStationaryFixedOpponentsContinueReward_pureSetRoot,
    quittingStationaryFixedOpponentsContinueMass_pureSetRoot_of_erase_empty
      (S := ∅) (who := who) (by simp)]
  simp only [Finset.insert_empty, Finset.erase_empty, quittingSetReward_empty,
    quittingSetReward_singleton_eq_soloReward]
  clear h
  induction time with
  | zero => rfl
  | succ time ih => simpa only [quittingStationaryPureTimeValue, one_mul, zero_add] using ih

theorem quittingFinitePureReplyValue_alwaysContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingFinitePureReplyValue reward (quittingAlwaysContinueProfile reward) who =
      quittingSoloReward reward who who := by
  simp only [quittingFinitePureReplyValue, quittingTerminalPayoff_finiteTime_alwaysContinue,
    ciSup_const]

theorem quittingFinitePureReplyPunishmentValue_le_solo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingFinitePureReplyPunishmentValue reward who ≤ quittingSoloReward reward who who := by
  simpa only [quittingFinitePureReplyValue_alwaysContinue] using
    quittingFinitePureReplyPunishmentValue_le reward who (quittingAlwaysContinueProfile reward)

theorem quittingFinitePureReplyValue_eq_compactStoppingLawsOfProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingFinitePureReplyValue reward profile who =
      quittingFinitePureReplyValue reward (quittingCompactStoppingLawProfile reward
        (quittingCompactStoppingLawsOfProfile reward profile)) who := by
  unfold quittingFinitePureReplyValue
  congr 1
  funext time
  exact quittingTerminalPayoff_update_pureTime_eq_compactStoppingLawsOfProfile
    reward profile who (some time)

/-- The signed late-Quit limit is bounded by the finite-date supremum against
the same arbitrary complete opponents. -/
theorem neverPayoff_add_opponentNever_mul_solo_le_finitePureReplyValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff reward (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who none)) who +
      quittingOpponentNeverProduct (quittingCompactStoppingLawsOfProfile reward profile) who *
        reward (quittingSingletonTerminal who) who ≤
      quittingFinitePureReplyValue reward profile who := by
  rw [quittingTerminalPayoff_update_pureTime_eq_compactStoppingLawsOfProfile,
    quittingFinitePureReplyValue_eq_compactStoppingLawsOfProfile]
  apply le_of_tendsto
    (quittingTerminalPayoff_update_finiteTime_tendsto_never_add_opponentNever_mul_singleton
      reward (quittingCompactStoppingLawsOfProfile reward profile) who)
  exact Filter.Eventually.of_forall fun time ↦
    quittingTerminalPayoff_finiteTime_le_finitePureReplyValue reward _ who time

/-- If the own singleton is nonnegative, Never adds nothing to the finite-date
supremum, even when finite response suprema are not attained. -/
theorem quittingContinuationBestResponseValue_eq_finitePureReplyValue_of_solo_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (hsolo : 0 ≤ reward (quittingSingletonTerminal who) who) :
    quittingContinuationBestResponseValue reward profile who =
      quittingFinitePureReplyValue reward profile who := by
  apply le_antisymm
  · rw [quittingContinuationBestResponseValue_eq_compactStoppingLawsOfProfile,
      quittingFinitePureReplyValue_eq_compactStoppingLawsOfProfile]
    have h :=
      quittingCompactStoppingLawProfile_cap_le_finiteBound_add_opponentNeverProduct_mul_negPart
        reward (quittingCompactStoppingLawsOfProfile reward profile) who
        (quittingFinitePureReplyValue reward (quittingCompactStoppingLawProfile reward
          (quittingCompactStoppingLawsOfProfile reward profile)) who)
        (fun time ↦ quittingTerminalPayoff_finiteTime_le_finitePureReplyValue reward _ who time)
    simpa only [max_eq_right (neg_nonpos.mpr hsolo), mul_zero, add_zero] using h
  · exact quittingFinitePureReplyValue_le_bestReplyValue reward profile who

end GameTheory
