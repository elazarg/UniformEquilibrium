import UniformEquilibrium.Quitting.Classification.Existence.TwoPlayerPremiumCoreUniformPayoff
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # A strict-leave premium core outside the product-low class

This literal table has a uniform-equilibrium payoff and fails product-low.
No further matrix, response-partition, or child-certificate separation is claimed.
-/

noncomputable section

namespace GameTheory.TwoPlayerPremiumCoreStrictLeave

def coalitionCode (coalition : Finset (Fin 4)) : ℕ :=
  (if 0 ∈ coalition then 1 else 0) + (if 1 ∈ coalition then 2 else 0) +
    (if 2 ∈ coalition then 4 else 0) + (if 3 ∈ coalition then 8 else 0)

def reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal => match coalitionCode terminal.val with
    | 1 => ![1, -1, -1, -1]
    | 2 => ![0, 0, 2, -1]
    | 3 => ![1, 0, -1, -1]
    | 4 => ![0, -1, 0, 2]
    | 5 => ![1, -1, 0, -1]
    | 6 => ![0, 0, 0, 1]
    | 7 => ![1, 0, 0, -1]
    | 8 => ![4, 2, -1, 0]
    | 9 => ![2, -1, -1, 1]
    | 10 => ![4, 0, 1, 0]
    | 11 => ![1, 0, -1, 0]
    | 12 => ![4, 1, 0, 0]
    | 13 => ![1, -1, 0, 0]
    | 14 => ![4, 0, 0, 0]
    | 15 => ![1, 0, 0, 0]
    | _ => 0

@[simp] theorem reward_singleton (player : Fin 4) :
    reward (quittingSingletonTerminal player) player =
      (![1, 0, 0, 0] : Payoff (Fin 4)) player := by
  fin_cases player <;>
    norm_num +decide [reward, coalitionCode, quittingSingletonTerminal]

theorem reward_abs_le_four
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (player : Fin 4) :
    |reward terminal player| ≤ 4 := by
  fin_cases terminal <;> fin_cases player <;>
    norm_num +decide [reward, coalitionCode]

theorem singleton_nonnegative (player : Fin 4) :
    0 ≤ reward (quittingSingletonTerminal player) player := by
  rw [reward_singleton]
  fin_cases player <;> norm_num

theorem nonnegativePremium : HasNonnegativeOwnQuittingPremium reward := by
  intro terminal player hmem
  rw [reward_singleton]
  fin_cases terminal <;> fin_cases player <;>
    norm_num +decide [reward, coalitionCode] at *

theorem outside_constantParticipantReward
    (player : Fin 4) (hfirst : player ≠ 0) (hsecond : player ≠ 3)
    (terminal : {S : Finset (Fin 4) // S.Nonempty})
    (hmem : player ∈ terminal.val) :
    reward terminal player = reward (quittingSingletonTerminal player) player := by
  rw [reward_singleton]
  fin_cases terminal <;> fin_cases player <;>
    norm_num +decide [reward, coalitionCode] at *

theorem strictLeave :
    reward ⟨{0, 3}, by simp⟩ 0 < reward (quittingSingletonTerminal 3) 0 := by
  norm_num +decide [reward, coalitionCode, quittingSingletonTerminal]

theorem exists_uniformEquilibriumPayoff :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_twoPlayerPremiumCore_strictLeave
    reward nonnegativePremium singleton_nonnegative 0 3 (by decide)
    outside_constantParticipantReward strictLeave

def halfCoin : PMF Bool :=
  quittingHazardCoin (1 / 2) (by norm_num) (by norm_num)

@[simp] theorem halfCoin_quitProbability :
    (halfCoin true).toReal = 1 / 2 := by
  exact quittingHazardCoin_true_toReal _ _ _

/-- Only the two premium-core players are active. No Nash property is asserted. -/
def halfCoreRoot : Fin 4 → PMF Bool :=
  PairedCycle.root 0 3 halfCoin halfCoin

@[simp] theorem halfCoreRoot_absorptionMass :
    quittingRootAbsorptionMass halfCoreRoot = 3 / 4 := by
  rw [halfCoreRoot, PairedCycle.absorptionMass_root (by decide)]
  norm_num [Math.PairedAffine.absorption]

theorem halfCoreRoot_quit_first (tail : Payoff (Fin 4)) :
    quittingRootQuitPayoff reward tail halfCoreRoot 0 = 3 / 2 := by
  rw [halfCoreRoot, PairedCycle.rootQuit_first reward tail (by decide)]
  norm_num +decide [Math.PairedAffine.activeValue, reward, coalitionCode,
    quittingSingletonTerminal]

theorem halfCoreRoot_quit_second (tail : Payoff (Fin 4)) :
    quittingRootQuitPayoff reward tail halfCoreRoot 3 = 1 / 2 := by
  rw [halfCoreRoot, PairedCycle.rootQuit_second reward tail (by decide)]
  norm_num +decide [Math.PairedAffine.activeValue, reward, coalitionCode,
    quittingSingletonTerminal]

theorem halfCoreRoot_outside_inactive
    (player : Fin 4) (hfirst : player ≠ 0) (hsecond : player ≠ 3) :
    (halfCoreRoot player true).toReal = 0 := by
  unfold halfCoreRoot
  rw [PairedCycle.root_outside hfirst hsecond]
  simp

theorem not_hasProductLowQuittingPremium :
    ¬ HasProductLowQuittingPremium reward := by
  intro hlow
  obtain ⟨player, hactive, hquit⟩ :=
    hlow halfCoreRoot (by rw [halfCoreRoot_absorptionMass]; norm_num)
  by_cases hfirst : player = 0
  · subst player
    rw [halfCoreRoot_quit_first, reward_singleton] at hquit
    norm_num at hquit
  · by_cases hsecond : player = 3
    · subst player
      rw [halfCoreRoot_quit_second, reward_singleton] at hquit
      norm_num at hquit
    · rw [halfCoreRoot_outside_inactive player hfirst hsecond] at hactive
      exact (lt_irrefl 0) hactive

end GameTheory.TwoPlayerPremiumCoreStrictLeave
