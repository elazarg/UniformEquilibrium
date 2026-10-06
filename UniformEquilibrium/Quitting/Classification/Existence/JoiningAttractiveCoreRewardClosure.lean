import UniformEquilibrium.Quitting.Classification.Existence.JoiningAttractiveCoreUniformPayoff
import UniformEquilibrium.Quitting.Classification.JoiningAttractiveCorePassivePerturbation
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityRewardRobustness

/-! # Weak attractive-core insertion comparisons by actual reward closure

Localized passive decreases preserve the exact computed core and own
singletons. Positive decreases strictify the printed weak comparisons.
Canonical reward closure yields one fixed original-game payoff target.
-/

noncomputable section

namespace GameTheory

theorem exists_uniformEquilibriumPayoff_of_weakJoiningAttractive_core
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsingleton : ∀ player, 0 ≤ reward (quittingSingletonTerminal player) player)
    (hcard : (quittingPremiumCore reward).card = 3)
    (hattractive : HasWeakJoiningAttractivePremiumCore reward) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables
  intro delta hdelta
  let nearby := joiningAttractiveCorePassivePerturbation reward delta
  refine ⟨nearby, ?_, ?_⟩
  · intro terminal player
    exact (abs_joiningAttractiveCorePassivePerturbation_sub_le
      reward delta terminal player).trans (by rw [abs_of_pos hdelta])
  · apply exists_uniformEquilibriumPayoff_of_joiningAttractive_core nearby
    · intro player
      change 0 ≤ joiningAttractiveCorePassivePerturbation reward delta
        (quittingSingletonTerminal player) player
      rw [joiningAttractiveCorePassivePerturbation_singleton]
      exact hsingleton player
    · change (quittingPremiumCore
        (joiningAttractiveCorePassivePerturbation reward delta)).card = 3
      rw [joiningAttractiveCorePassivePerturbation_core]
      exact hcard
    · exact joiningAttractiveCorePassivePerturbation_strict_of_weak
        reward hattractive delta hdelta

end GameTheory
