import UniformEquilibrium.Quitting.Classification.ProductLowQuittingPremium
import UniformEquilibrium.Quitting.Classification.QuittingPremiumReward
import UniformEquilibrium.Quitting.Stationary.SingletonStationaryRoot
import MathUE.Probability

/-! # Pure-coalition low premiums do not imply product-low premiums -/

noncomputable section

namespace GameTheory.PureCoalitionLowProductFailure

open GameTheory Math.Probability Math.PMFProduct

def premium (terminal : Finset (Fin 3)) : Payoff (Fin 3) :=
  if terminal = {0, 1} then ![2, -1, 0]
  else if terminal = {1, 2} then ![0, 2, -1]
  else if terminal = {0, 2} then ![-1, 0, 2]
  else 0

def reward
    (passive : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3)) :
    {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3) :=
  rewardOfOwnPremium 0 premium passive

def halfRoot : Fin 3 → PMF Bool := fun _ =>
  quittingHazardCoin (1 / 2) (by norm_num) (by norm_num)

@[simp] theorem premium_singleton (player : Fin 3) :
    premium {player} player = 0 := by
  fin_cases player <;> simp +decide [premium]

@[simp] theorem reward_singleton
    (passive : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3))
    (player : Fin 3) :
    reward passive (quittingSingletonTerminal player) player = 0 := by
  unfold reward rewardOfOwnPremium
  simp [quittingSingletonTerminal]

/-- Every pure nonempty coalition contains a participant with nonpositive
own premium. -/
theorem everyPureCoalition_has_low_participant
    (terminal : Finset (Fin 3)) (hterminal : terminal.Nonempty) :
    ∃ player ∈ terminal, premium terminal player ≤ 0 := by
  by_cases h01 : terminal = {0, 1}
  · subst terminal
    exact ⟨1, by simp, by norm_num [premium]⟩
  by_cases h12 : terminal = {1, 2}
  · subst terminal
    refine ⟨2, by simp, ?_⟩
    change (-1 : ℝ) ≤ 0
    norm_num
  by_cases h02 : terminal = {0, 2}
  · subst terminal
    exact ⟨0, by simp, by norm_num [premium, h01, h12]⟩
  obtain ⟨player, hplayer⟩ := hterminal
  exact ⟨player, hplayer, by simp [premium, h01, h12, h02]⟩

@[simp] theorem halfRoot_quitProbability (player : Fin 3) :
    (halfRoot player true).toReal = 1 / 2 := by
  simp [halfRoot, quittingHazardCoin]

@[simp] theorem halfRoot_continueProbability (player : Fin 3) :
    (halfRoot player false).toReal = 1 / 2 := by
  rw [pmfBool_false_toReal, halfRoot_quitProbability]
  norm_num

@[simp] theorem halfRoot_absorptionMass :
    quittingRootAbsorptionMass halfRoot = 7 / 8 := by
  unfold quittingRootAbsorptionMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    Fin.prod_univ_three]
  norm_num

/-- At the half-hazard product root every pure-Quit endpoint premium is
strictly positive and equals one quarter. -/
theorem halfRoot_quitPremium
    (passive : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3))
    (player : Fin 3) :
    quittingRootQuitPayoff (reward passive) 0 halfRoot player -
      reward passive (quittingSingletonTerminal player) player = 1 / 4 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin3]
  fin_cases player <;>
    simp +decide [reward, rewardOfOwnPremium, premium, quittingRootPayoff,
      quittingQuitters, halfRoot, quittingHazardCoin,
      Math.Probability.expect_eq_sum] <;>
    norm_num

/-- The table therefore fails product-low premiums although every pure
coalition has a low participant. -/
theorem not_hasProductLowQuittingPremium
    (passive : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3)) :
    ¬HasProductLowQuittingPremium (reward passive) := by
  intro hlow
  obtain ⟨player, _hactive, hquit⟩ := hlow halfRoot (by norm_num)
  have hpremium := halfRoot_quitPremium passive player
  linarith

end GameTheory.PureCoalitionLowProductFailure
