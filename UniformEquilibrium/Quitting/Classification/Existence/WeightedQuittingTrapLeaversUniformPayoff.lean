import UniformEquilibrium.Quitting.Classification.WeightedQuittingTrapLeaversSmoothDrift
import UniformEquilibrium.Quitting.Classification.Existence.BoundaryDifferentiablePotentialUniformPayoff

/-! # Actual four-player uniform payoffs from strict weighted raw tests -/

noncomputable section

namespace GameTheory

theorem exists_uniformEquilibriumPayoff_of_weightedTrap_strictLeave
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsingleton : ∀ player, 0 ≤ reward (quittingSingletonTerminal player) player)
    (hleavers : HasWeightedQuittingTrapLeavers reward (· < ·)) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply exists_uniformEquilibriumPayoff_of_continuous_boundaryDifferentiable_potential_exclusion
    reward hsingleton
  intro potential hcontinuous hdiff
  exact not_isQuittingFullExactRootPotential_of_weightedTrap_strictLeave reward hleavers
    (M := quittingRewardBound reward) (bound := quittingRewardBound reward + 2)
    (abs_reward_le_quittingRewardBound reward) (by linarith) potential
    hcontinuous.continuousOn hdiff

end GameTheory
