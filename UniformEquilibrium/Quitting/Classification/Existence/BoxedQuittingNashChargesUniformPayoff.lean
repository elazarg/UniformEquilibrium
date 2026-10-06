import UniformEquilibrium.Quitting.Classification.BoxedQuittingNashChargeReturn
import UniformEquilibrium.Quitting.Classification.Existence.SelectedSingletonSublevelReturnUniformPayoff

/-! # Actual Fin4 payoff producer from boxed Nash charges

The reward bound is a coordinate bound, not the canonical sum of absolute
rewards. Strict finite trap margins choose one common box internally. No root,
strategy, selected-return certificate, or favorable successor is supplied.
-/

noncomputable section

namespace GameTheory

theorem exists_uniformEquilibriumPayoff_of_boxedQuittingNashCharges
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsingleton : ∀ player, 0 ≤ reward (quittingSingletonTerminal player) player)
    (M : ℝ) (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hcharges : HasBoxedQuittingNashCharges reward M) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  let base := min M (quittingRewardBound reward)
  have hbaseReward : ∀ terminal player, |reward terminal player| ≤ base := by
    intro terminal player
    exact le_min (hreward terminal player)
      (abs_reward_le_quittingRewardBound reward terminal player)
  have hbaseCharges : HasBoxedQuittingNashCharges reward base :=
    hcharges.mono_bound reward (min_le_left _ _)
  obtain ⟨bound, hbound, hupper, hboxCharges⟩ :=
    exists_common_box_of_boxedQuittingNashCharges reward base hbaseCharges
  apply exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn_of_reward_bound
    reward hsingleton base bound hbaseReward hbound
      (hupper.le.trans (add_le_add_left (min_le_right M (quittingRewardBound reward)) 2))
  exact hasBoxedSelectedSingletonSublevelReturn_of_boxedQuittingNashCharges
    reward hbaseReward hboxCharges

end GameTheory
