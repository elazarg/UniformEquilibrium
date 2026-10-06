import UniformEquilibrium.Quitting.Classification.BoxedQuittingNashChargeReturn
import UniformEquilibrium.Quitting.Classification.Existence.SelectedSingletonSublevelReturnUniformPayoff
import UniformEquilibrium.Quitting.Root.NashExistence
import UniformEquilibrium.Quitting.Root.BelowSingletonRootAbsorption

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
  intro tail hbox hbelow
  obtain ⟨player, hplayer⟩ := hbelow
  obtain ⟨root, hnash⟩ := exists_isZeroQuittingRootNash (reward := reward) tail
  have hgap : 0 < reward (quittingSingletonTerminal player) player - tail player := by
    change tail player < reward (quittingSingletonTerminal player) player at hplayer
    linarith
  have hbase := quittingRewardCoordinateBound_nonneg_of_player reward player hbaseReward
  have habsorption := belowSingleton_exactRoot_absorptionMass_lowerBound
    reward tail root player hgap hbaseReward (by linarith) hnash
  have hpositive : 0 < quittingRootAbsorptionMass root :=
    (div_pos hgap (by positivity)).trans_le habsorption
  refine ⟨root, hnash, ?_⟩
  exact exists_successor_le_singleton_of_boxedQuittingNashCharges
    reward bound hboxCharges tail hbox root hnash hpositive

end GameTheory
