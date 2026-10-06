import UniformEquilibrium.Quitting.Projective.SelectedSingletonSublevelReturnSmoothDrift
import UniformEquilibrium.Quitting.Classification.Existence.BoundaryDifferentiablePotentialUniformPayoff

/-! # Conditional Fin4 payoff compiler for chosen singleton-sublevel return

Raw signed-pair, boxed-charge, and mixed-trap producers are separate obligations.
The return hypothesis here is not presented as their completed source adapter.
-/

noncomputable section

namespace GameTheory

theorem exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn_on_subbox
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsingleton : ∀ player, 0 ≤ reward (quittingSingletonTerminal player) player)
    (bound : ℝ) (hbound : quittingRewardBound reward < bound)
    (hlarge : bound ≤ quittingRewardBound reward + 2)
    (hreturn : HasBoxedSelectedSingletonSublevelReturn reward bound) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply exists_uniformEquilibriumPayoff_of_continuous_boundaryDifferentiable_potential_exclusion
    reward hsingleton
  intro potential hcontinuous hdiff hpotential
  apply not_isQuittingFullExactRootPotential_of_selectedSingletonSublevelReturn reward
    (M := quittingRewardBound reward) (bound := bound)
    (abs_reward_le_quittingRewardBound reward) hbound hreturn potential
    hcontinuous.continuousOn _ (hpotential.mono_box hlarge)
  intro point hpoint
  exact hdiff point ⟨⟨hpoint.1.1, fun player => (hpoint.1.2 player).trans hlarge⟩, hpoint.2⟩

theorem exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsingleton : ∀ player, 0 ≤ reward (quittingSingletonTerminal player) player)
    (hreturn : HasBoxedSelectedSingletonSublevelReturn reward (quittingRewardBound reward + 2)) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn_on_subbox reward
    hsingleton (quittingRewardBound reward + 2) (by linarith) le_rfl hreturn

end GameTheory
