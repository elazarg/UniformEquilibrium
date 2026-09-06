import UniformEquilibrium.Quitting.Classification.SupportwiseQuittingPremium
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-! # A semipositive global weight does not imply supportwise balance -/

noncomputable section

namespace GameTheory.SemipositiveGlobalWeightCounterexample

open GameTheory
open QuittingSureSetOwnerRepair

def singleton : Payoff (Fin 3) := fun player => if player = 0 then 1 else 0

def reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3) :=
  fun terminal =>
    if terminal.val = {1, 2}
    then fun player => if player = 0 then 2 else 1
    else singleton

def weight : Fin 3 → ℝ := fun player => if player = 0 then 1 else 0

def root : Fin 3 → PMF Bool := quittingPureSetRoot {1, 2}

@[simp] theorem singleton_selfReward (player : Fin 3) :
    reward (quittingSingletonTerminal player) player = singleton player := by
  fin_cases player <;>
    norm_num +decide [reward, singleton, quittingSingletonTerminal]

theorem weight_nonneg (player : Fin 3) : 0 ≤ weight player := by
  fin_cases player <;> norm_num [weight]

theorem weight_not_strictlyPositive : ¬∀ player, 0 < weight player := by
  intro h
  have hzero := h 1
  norm_num [weight] at hzero

theorem semipositiveGlobalWeight_participantPremium_nonpos
    (terminal : Finset (Fin 3)) (hterminal : terminal.Nonempty) :
    (∑ player ∈ terminal, weight player *
      (reward ⟨terminal, hterminal⟩ player -
        reward (quittingSingletonTerminal player) player)) ≤ 0 := by
  by_cases hpair : terminal = {1, 2}
  · subst terminal
    simp_rw [singleton_selfReward]
    norm_num +decide [weight, reward, singleton]
  · simp_rw [singleton_selfReward]
    simp [reward, hpair]

theorem not_supportwiseBalance :
    ¬IsSupportwiseBalancedQuittingPremiumTable reward := by
  intro hbalanced
  obtain ⟨localWeight, hnonneg, _hsupport, hsum, hpremium⟩ :=
    hbalanced ({1, 2} : Finset (Fin 3)) (by simp)
  have h := hpremium ({1, 2} : Finset (Fin 3)) (by simp)
    (fun _ hmem => hmem)
  rw [Finset.sum_insert
    (by decide : (1 : Fin 3) ∉ ({2} : Finset (Fin 3))),
    Finset.sum_singleton] at hsum h
  simp_rw [singleton_selfReward] at h
  norm_num +decide [reward, singleton] at h
  linarith

@[simp] theorem root_quitProbability (player : Fin 3) :
    (root player true).toReal = if player = 0 then 0 else 1 := by
  fin_cases player <;>
    simp [root, quittingPureSetRoot, quittingSetAction]

@[simp] theorem root_continueProbability (player : Fin 3) :
    (root player false).toReal = if player = 0 then 1 else 0 := by
  fin_cases player <;>
    simp [root, quittingPureSetRoot, quittingSetAction]

@[simp] theorem root_absorptionMass :
    quittingRootAbsorptionMass root = 1 := by
  exact quittingRootAbsorptionMass_pureSetRoot_of_nonempty (by simp)

theorem quitPayoff (tail : Payoff (Fin 3)) (player : Fin 3) :
    quittingRootQuitPayoff reward tail root player = 1 := by
  unfold root
  rw [quittingRootQuitPayoff_pureSetRoot_eq_insert]
  fin_cases player <;> simp [quittingSetReward, reward, singleton]

theorem continuePayoff (tail : Payoff (Fin 3)) (player : Fin 3) :
    quittingRootContinuePayoff reward tail root player =
      if player = 0 then 2 else 0 := by
  unfold root
  fin_cases player
  · rw [quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty]
    · norm_num [quittingSetReward, reward]
    · simp
  · rw [quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty]
    · norm_num +decide [quittingSetReward, reward, singleton]
    · simp
  · rw [quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty]
    · simp [quittingSetReward, reward, singleton]
    · decide

/-- The sure pair root is exact Nash against every continuation annotation. -/
theorem exactRootNash (tail : Payoff (Fin 3)) :
    IsεQuittingRootNash reward tail 0 root := by
  apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward tail root).mp
  intro player
  rw [quittingRootEndpointDifference]
  rw [quitPayoff, continuePayoff]
  fin_cases player <;> norm_num

theorem inactive_strictlyPrefersContinue (tail : Payoff (Fin 3)) :
    quittingRootQuitPayoff reward tail root 0 <
      quittingRootContinuePayoff reward tail root 0 := by
  rw [quitPayoff, continuePayoff]
  norm_num

theorem active_quitPayoff_strictlyAboveSingleton (player : Fin 3)
    (hactive : player = 1 ∨ player = 2) (tail : Payoff (Fin 3)) :
    reward (quittingSingletonTerminal player) player <
      quittingRootQuitPayoff reward tail root player := by
  rcases hactive with rfl | rfl <;>
    simp [quitPayoff, singleton]

end GameTheory.SemipositiveGlobalWeightCounterexample
