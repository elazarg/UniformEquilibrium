import UniformEquilibrium.Quitting.Classification.QuittingPremiumReward
import UniformEquilibrium.Quitting.Root.OpponentCoalitionPayoff

/-! # A literal two-player hazard-weighted premium boundary -/

noncomputable section

namespace GameTheory.FinTwoHazardWeightedPremiumBoundary

def premium (terminal : Finset (Fin 2)) (player : Fin 2) : ℝ :=
  if terminal = Finset.univ then if player = 0 then 1 else -1 else 0

def reward : {S : Finset (Fin 2) // S.Nonempty} → Payoff (Fin 2) :=
  rewardOfOwnPremium 0 premium (fun _ _ => 0)

def root (player : Fin 2) : PMF Bool :=
  if player = 0 then
    quittingHazardCoin (1 / 4) (by norm_num) (by norm_num)
  else
    quittingHazardCoin (3 / 4) (by norm_num) (by norm_num)

def weight (_player : Fin 2) : ℝ := 1 / 2

theorem weight_nonneg (player : Fin 2) : 0 ≤ weight player := by
  norm_num [weight]

theorem weight_sum_one : (∑ player : Fin 2, weight player) = 1 := by
  norm_num [weight, Fin.sum_univ_two]

@[simp] theorem root_zero_quit : (root 0 true).toReal = 1 / 4 := by
  simp [root, quittingHazardCoin_true_toReal]

@[simp] theorem root_one_quit : (root 1 true).toReal = 3 / 4 := by
  simp [root, quittingHazardCoin_true_toReal]

@[simp] theorem root_zero_continue : (root 0 false).toReal = 3 / 4 := by
  simp [root, quittingHazardCoin_false_toReal]
  norm_num +decide

@[simp] theorem root_one_continue : (root 1 false).toReal = 1 / 4 := by
  simp [root, quittingHazardCoin_false_toReal]
  norm_num +decide

theorem singleton_payoff_zero (player : Fin 2) :
    reward (quittingSingletonTerminal player) player = 0 := by
  fin_cases player <;>
    norm_num +decide [reward, rewardOfOwnPremium, premium,
      quittingSingletonTerminal]

theorem full_premium_zero :
    reward ⟨Finset.univ, Finset.univ_nonempty⟩ 0 -
        reward (quittingSingletonTerminal 0) 0 = 1 := by
  norm_num +decide [reward, rewardOfOwnPremium, premium,
    quittingSingletonTerminal]

theorem full_premium_one :
    reward ⟨Finset.univ, Finset.univ_nonempty⟩ 1 -
        reward (quittingSingletonTerminal 1) 1 = -1 := by
  norm_num +decide [reward, rewardOfOwnPremium, premium,
    quittingSingletonTerminal]

theorem quitPremium_zero :
    quittingRootQuitPayoff reward 0 root 0 -
        reward (quittingSingletonTerminal 0) 0 = 3 / 4 := by
  rw [quittingRootQuitPayoff_eq_sum_opponentCoalitionMass]
  have herase : Finset.univ.erase (0 : Fin 2) = {1} := by decide
  have hpowerset : ({1} : Finset (Fin 2)).powerset = {∅, {1}} := by decide
  rw [herase, hpowerset]
  simp [herase, root, reward, rewardOfOwnPremium, premium,
    quittingOpponentCoalitionMass, quittingStageCoalitionPayoff,
    quittingSingletonTerminal]
  norm_num +decide

theorem quitPremium_one :
    quittingRootQuitPayoff reward 0 root 1 -
        reward (quittingSingletonTerminal 1) 1 = -1 / 4 := by
  rw [quittingRootQuitPayoff_eq_sum_opponentCoalitionMass]
  have herase : Finset.univ.erase (1 : Fin 2) = {0} := by decide
  have hpowerset : ({0} : Finset (Fin 2)).powerset = {∅, {0}} := by decide
  rw [herase, hpowerset]
  simp [herase, root, reward, rewardOfOwnPremium, premium,
    quittingOpponentCoalitionMass, quittingStageCoalitionPayoff,
    quittingSingletonTerminal]
  norm_num +decide

/-- Equal weighting sees a strictly positive unweighted average premium. -/
theorem plain_weighted_premium_pos :
    0 < weight 0 *
        (quittingRootQuitPayoff reward 0 root 0 -
          reward (quittingSingletonTerminal 0) 0) +
      weight 1 *
        (quittingRootQuitPayoff reward 0 root 1 -
          reward (quittingSingletonTerminal 1) 1) := by
  rw [quitPremium_zero, quitPremium_one]
  norm_num [weight]

/-- The same premiums, multiplied by the actual Quit hazards, cancel exactly. -/
theorem hazard_weighted_premium_zero :
    (root 0 true).toReal *
        (quittingRootQuitPayoff reward 0 root 0 -
          reward (quittingSingletonTerminal 0) 0) +
      (root 1 true).toReal *
        (quittingRootQuitPayoff reward 0 root 1 -
          reward (quittingSingletonTerminal 1) 1) = 0 := by
  rw [root_zero_quit, root_one_quit, quitPremium_zero, quitPremium_one]
  norm_num

/-- Multiplying additionally by the normalized equal support weights keeps
the hazard-weighted premium at zero. -/
theorem equally_hazard_weighted_premium_zero :
    weight 0 * (root 0 true).toReal *
        (quittingRootQuitPayoff reward 0 root 0 -
          reward (quittingSingletonTerminal 0) 0) +
      weight 1 * (root 1 true).toReal *
        (quittingRootQuitPayoff reward 0 root 1 -
          reward (quittingSingletonTerminal 1) 1) = 0 := by
  rw [root_zero_quit, root_one_quit, quitPremium_zero, quitPremium_one]
  norm_num [weight]

end GameTheory.FinTwoHazardWeightedPremiumBoundary
