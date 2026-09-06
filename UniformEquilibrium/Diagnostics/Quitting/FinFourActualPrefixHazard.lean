import UniformEquilibrium.Quitting.Paths.ActualExactPrefixBlock
import UniformEquilibrium.Diagnostics.Quitting.FinFourUnboundedExactBlockHazardCapacity

/-! # Bounded actual-prefix hazard under failure of a Fin4 uniform payoff -/

noncomputable section

namespace GameTheory

open Math.Probability

/-- Failure of a Fin4 uniform payoff bounds every actual nested exact-prefix
marginal-hazard partial sum by one common constant. -/
theorem finFour_exists_uniform_actualExactPrefix_hazard_bound_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → Fin 4 → PMF Bool)
    (hnested : ∀ n, profiles (n + 1) =
      quittingRootThenContinuationProfile reward (roots n) (profiles n))
    (hexact : ∀ n, IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward (profiles n) player)
      0 (roots n)) :
    ∃ bound : ℝ, ∀ horizon,
      (∑ time ∈ Finset.range horizon,
        ∑ player, (roots time player true).toReal) ≤ bound := by
  have hcapacity :=
    finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff
      reward hnot
  rw [hasBoundedFiniteExactNashBellmanHazardCapacity_iff] at hcapacity
  obtain ⟨bound, hbound⟩ := hcapacity
  refine ⟨max bound 0, fun horizon => ?_⟩
  cases horizon with
  | zero => simp
  | succ horizon =>
      have hpositive : 0 < horizon + 1 := by omega
      rw [← quittingActualPrefixHazardBlock_hazardCharge
        reward profiles roots hnested hexact (horizon + 1) hpositive]
      exact (hbound (quittingActualPrefixHazardBlock reward profiles roots
        hnested hexact (horizon + 1) hpositive)).trans (le_max_left _ _)

/-- Hence the actual marginal-hazard series is summable; this conclusion is
derived from capacity rather than accepted as source data. -/
theorem finFour_summable_actualExactPrefix_hazard_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → Fin 4 → PMF Bool)
    (hnested : ∀ n, profiles (n + 1) =
      quittingRootThenContinuationProfile reward (roots n) (profiles n))
    (hexact : ∀ n, IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward (profiles n) player)
      0 (roots n)) :
    Summable (fun time => ∑ player, (roots time player true).toReal) := by
  obtain ⟨bound, hbound⟩ :=
    finFour_exists_uniform_actualExactPrefix_hazard_bound_of_no_uniformPayoff
      reward hnot profiles roots hnested hexact
  apply summable_of_sum_range_le (c := bound)
  · intro time
    exact Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  · exact hbound


end GameTheory
