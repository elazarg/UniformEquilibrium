import UniformEquilibrium.Quitting.Classification.NonnegativePremiumPunishment
import UniformEquilibrium.Quitting.Classification.QuittingPremiumSupportPeelingOrder
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-! # The literal negative-premium lower-boundary and punishment counterexample -/

noncomputable section

namespace GameTheory.OrderedPremiumNegativeBoundary

open QuittingSureSetOwnerRepair

def singleton : Payoff (Fin 4) := ![1, 0, 0, 0]

/-- The default singleton vector, with only player zero's pair reward changed
to zero and its passive reward at singleton one changed to minus one. -/
def reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal player => if player = 0 then
    if terminal.val = {0, 1} then 0 else if terminal.val = {1} then -1 else 1
  else 0

def root : Fin 4 → PMF Bool := quittingPureSetRoot {0, 1}

@[simp] theorem singleton_selfReward (player : Fin 4) :
    reward (quittingSingletonTerminal player) player = singleton player := by
  fin_cases player <;> norm_num +decide [reward, singleton, quittingSingletonTerminal]

theorem reward_le_singleton (terminal : {S : Finset (Fin 4) // S.Nonempty}) (player : Fin 4) :
    reward terminal player ≤ singleton player := by
  fin_cases player <;> simp [reward, singleton]
  split_ifs <;> norm_num

theorem weakSupportPeeling : HasWeakQuittingPremiumSupportPeeling reward := by
  apply (hasWeakQuittingPremiumSupportPeeling_iff _).mpr
  intro active hactive
  obtain ⟨player, hplayer⟩ := hactive
  refine ⟨player, hplayer, ?_⟩
  intro terminal hterminal _ _
  rw [singleton_selfReward]
  exact reward_le_singleton ⟨terminal, hterminal⟩ player

theorem negative_ownPremium : reward ⟨{0, 1}, by simp⟩ 0 -
    reward (quittingSingletonTerminal 0) 0 = -1 := by
  norm_num +decide [reward, quittingSingletonTerminal]

theorem quitPayoff (tail : Payoff (Fin 4)) (player : Fin 4) :
    quittingRootQuitPayoff reward tail root player = 0 := by
  unfold root
  rw [quittingRootQuitPayoff_pureSetRoot_eq_insert]
  fin_cases player <;> norm_num +decide [quittingSetReward, reward]

theorem continuePayoff (tail : Payoff (Fin 4)) (player : Fin 4) :
    quittingRootContinuePayoff reward tail root player = if player = 0 then -1 else 0 := by
  unfold root
  rw [quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty]
  · fin_cases player <;> norm_num +decide [quittingSetReward, reward]
  · fin_cases player <;> decide

theorem exactRootNash (tail : Payoff (Fin 4)) : IsεQuittingRootNash reward tail 0 root := by
  apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash _ _ _).mp
  intro player
  rw [quittingRootEndpointDifference, quitPayoff, continuePayoff]
  fin_cases player <;> norm_num +decide [root, quittingPureSetRoot, quittingSetAction]

theorem successor_zero (tail : Payoff (Fin 4)) :
    quittingRootSuccessorPayoff reward tail root = 0 := by
  funext player
  rw [quittingRootSuccessorPayoff_eq_endpointMix, quitPayoff, continuePayoff]
  fin_cases player <;> norm_num +decide [root, quittingPureSetRoot, quittingSetAction]

theorem successor_below_singleton (tail : Payoff (Fin 4)) :
    quittingRootSuccessorPayoff reward tail root 0 < reward (quittingSingletonTerminal 0) 0 := by
  rw [successor_zero, singleton_selfReward]
  norm_num [singleton]

theorem participant_zero_nonneg (terminal : {S : Finset (Fin 4) // S.Nonempty})
    (hmember : (0 : Fin 4) ∈ terminal.val) : 0 ≤ reward terminal 0 := by
  have hnot : terminal.val ≠ ({1} : Finset (Fin 4)) := by
    intro heq
    rw [heq] at hmember
    norm_num at hmember
  simp [reward, hnot]
  split_ifs <;> norm_num

theorem zero_le_quitPayoff (opponents : Fin 4 → PMF Bool) :
    0 ≤ quittingRootQuitPayoff reward 0 opponents 0 := by
  rw [quittingRootQuitPayoff_eq_sum_opponentCoalitionMass]
  apply Finset.sum_nonneg
  intro coalition _
  apply mul_nonneg (quittingOpponentCoalitionMass_nonneg opponents 0 coalition)
  simp only [quittingStageCoalitionPayoff, Finset.insert_nonempty, dite_true]
  exact participant_zero_nonneg _ (Finset.mem_insert_self _ _)

/-- Player zero's unrestricted behavioral punishment is exactly zero,
strictly below its own singleton reward one. -/
theorem punishment_zero : quittingPunishmentValue reward 0 = 0 := by
  apply le_antisymm
  · have hupper := quittingPunishmentValue_le_stationaryUnilateralCap reward 0
      (quittingPureSetRoot {1})
    rw [quittingStationaryUnilateralCap_pureSetRoot] at hupper
    norm_num +decide [quittingSetReward, reward] at hupper
    exact hupper
  · rw [quittingPunishmentValue_eq_stationaryPunishmentValue]
    apply le_ciInf
    intro opponents
    apply le_trans ?_ (le_max_left _ _)
    have h := zero_le_quitPayoff opponents
    rwa [quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward (fun _ => opponents) 0 0 0] at h

theorem punishment_strictlyBelowSingleton :
    quittingPunishmentValue reward 0 < reward (quittingSingletonTerminal 0) 0 := by
  rw [punishment_zero, singleton_selfReward]
  norm_num [singleton]

theorem sureExitSet : IsQuittingSureExitSet reward {0, 1} := by
  constructor <;> intro player hplayer <;> fin_cases player <;>
    simp_all +decide [quittingSetReward, reward]

theorem terminalNash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
    (quittingStationaryProfile reward root) :=
  (isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet _ _).mpr sureExitSet

end GameTheory.OrderedPremiumNegativeBoundary
