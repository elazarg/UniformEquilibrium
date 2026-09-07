import UniformEquilibrium.Quitting.Classification.NonnegativeProductLowForwardPackets
import UniformEquilibrium.Quitting.Classification.NonnegativePremiumPunishment

/-! # Punishment-floor restoration and semantic consumption of ordered-premium packets -/

noncomputable section

namespace GameTheory

/-- Nonnegative singleton levels restore punishment floors in the same
fixed-radius weighted packets supplied by nonnegative support peeling. -/
theorem hasAbsorptionWeightedFiniteForwardPackets_of_nonnegative_weakSupportPeeling
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    (hpeeling : HasWeakQuittingPremiumSupportPeeling reward)
    (hsingleton : ∀ player, 0 ≤ reward (quittingSingletonTerminal player) player)
    (rewardBound : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound) :
    HasAbsorptionWeightedFiniteForwardPackets reward (rewardBound + 2) := by
  have hboundNonneg : 0 ≤ rewardBound := (abs_nonneg _).trans
    (hreward (quittingSingletonTerminal 0) 0)
  have hbound : 0 < rewardBound + 2 := by linarith
  exact (hasFloorFreeAbsorptionWeightedFiniteForwardPackets_iff_weighted reward hbound
    (fun terminal player => (hreward terminal player).trans (by linarith))
    (fun player => isQuittingNormalPlayer_of_singleton_nonneg reward player (hsingleton player))).mp
      (hasFloorFreeAbsorptionWeightedFiniteForwardPackets_of_nonnegative_weakSupportPeeling
        reward hnonnegative hpeeling rewardBound hreward)

/-- The charged-packet route independently yields one fixed uniform payoff
for the NN support-peeling class. This route uses smooth-capacity exclusion,
not the periodic approximate-equilibrium producer. -/
theorem exists_uniformEquilibriumPayoff_of_nonnegative_weakSupportPeeling_viaForwardPackets
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    (hpeeling : HasWeakQuittingPremiumSupportPeeling reward)
    (hsingleton : ∀ player, 0 ≤ reward (quittingSingletonTerminal player) player) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  let rewardBound := quittingRewardBound reward
  have hboundNonneg : 0 ≤ rewardBound := quittingRewardBound_nonneg reward
  have hbound : 0 < rewardBound + 2 := by linarith
  exact quittingGame_exists_uniformEquilibriumPayoff_of_absorptionWeightedPackets
    reward (rewardBound + 2) hbound
    (fun terminal player => (abs_reward_le_quittingRewardBound reward terminal player).trans
      (by linarith))
    (hasAbsorptionWeightedFiniteForwardPackets_of_nonnegative_weakSupportPeeling
      reward hnonnegative hpeeling hsingleton rewardBound
        (abs_reward_le_quittingRewardBound reward))

end GameTheory
