import UniformEquilibrium.Quitting.Classification.CommonQuittingPremiumLeaverSmoothDrift
import UniformEquilibrium.Quitting.Classification.Existence.BoundaryDifferentiablePotentialUniformPayoff

/-! # Four-player uniform payoff for signed strict common leavers -/

noncomputable section

namespace GameTheory

theorem exists_uniformEquilibriumPayoff_of_commonLeaver_strictLeave
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsingleton : ∀ player, 0 ≤ reward (quittingSingletonTerminal player) player)
    (player : Fin 4) (hcommon : IsCommonQuittingPremiumLeaver reward player)
    (hleave : ∀ (coalition : Finset (Fin 4)) (hcoalition : coalition.Nonempty),
      coalition ⊆ (quittingPremiumCore reward).erase player →
        reward ⟨insert player coalition, Finset.insert_nonempty _ _⟩ player <
          reward ⟨coalition, hcoalition⟩ player) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply exists_uniformEquilibriumPayoff_of_continuous_boundaryDifferentiable_potential_exclusion
    reward hsingleton
  intro potential hcontinuous hdiff
  exact not_isQuittingFullExactRootPotential_of_commonLeaver_strictLeave
    reward player hcommon hleave (M := quittingRewardBound reward)
    (bound := quittingRewardBound reward + 2) (abs_reward_le_quittingRewardBound reward)
    (by linarith) potential hcontinuous.continuousOn hdiff

end GameTheory
