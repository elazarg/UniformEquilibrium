import UniformEquilibrium.Quitting.Classification.Existence.WeightedQuittingTrapLeaversUniformPayoff
import UniformEquilibrium.Quitting.Classification.WeightedQuittingTrapPassivePerturbation
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityRewardRobustness

/-! # Weak weighted raw tests yield one fixed original uniform payoff

The canonical reward-closure theorem passes from strict nearby reward tables
to one original fixed target. There is no weak analytic potential-exclusion claim.
-/

noncomputable section

namespace GameTheory

theorem exists_uniformEquilibriumPayoff_of_weightedTrap_weakLeave
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsingleton : ∀ player, 0 ≤ reward (quittingSingletonTerminal player) player)
    (hleavers : HasWeightedQuittingTrapLeavers reward (· ≤ ·)) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables
  intro delta hdelta
  let nearby := passiveQuittingRewardPerturbation reward delta
  refine ⟨nearby, ?_, ?_⟩
  · intro terminal player
    exact (abs_passiveQuittingRewardPerturbation_sub_le reward delta terminal player).trans
      (by rw [abs_of_pos hdelta])
  · apply exists_uniformEquilibriumPayoff_of_weightedTrap_strictLeave nearby
      (fun player => by
        change 0 ≤ passiveQuittingRewardPerturbation reward delta
          (quittingSingletonTerminal player) player
        rw [passiveQuittingRewardPerturbation_singleton]
        exact hsingleton player)
    exact passiveQuittingRewardPerturbation_weightedStrictLeavers_of_weakLeavers
      reward hleavers delta hdelta

end GameTheory
