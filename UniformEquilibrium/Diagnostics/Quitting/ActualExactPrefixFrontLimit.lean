import UniformEquilibrium.Diagnostics.Quitting.FinFourActualPrefixHazard
import UniformEquilibrium.Quitting.Paths.ActualPrefixAllContinueLimit
import UniformEquilibrium.Quitting.Paths.ActualPrefixPayoffLimit

/-! # Actual exact-prefix front limit from the original source -/

noncomputable section
namespace GameTheory

open Filter Math.Probability
open scoped Topology

/-- Failure of a uniform payoff and an actual nested exact-root recursion
produce one payoff limit.  Every fixed reverse-front coordinate converges to
that same payoff and to the all-Continue root; the limiting root is exact and
its Bellman successor fixes the limit. -/
theorem finFour_actualExactPrefix_frontLimit_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → Fin 4 → PMF Bool)
    (hnested : ∀ time, profiles (time + 1) =
      quittingRootThenContinuationProfile reward (roots time) (profiles time))
    (hexact : ∀ time, IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward (profiles time) player)
      0 (roots time)) :
    ∃ limit : Payoff (Fin 4),
      (∀ player, Tendsto
        (fun time => quittingTerminalPayoff reward (profiles time) player)
        atTop (nhds (limit player))) ∧
      (∀ offset,
        Tendsto (fun depth =>
          quittingSimplexOfRoot (roots (depth - (offset + 1)))) atTop
          (nhds (quittingSimplexOfRoot
            (quittingAllContinueRoot : Fin 4 → PMF Bool))) ∧
        ∀ player, Tendsto (fun depth =>
          quittingTerminalPayoff reward
            (profiles (depth - (offset + 1))) player) atTop
          (nhds (limit player))) ∧
      IsεQuittingRootNash reward limit 0
        (quittingAllContinueRoot : Fin 4 → PMF Bool) ∧
      quittingRootSuccessorPayoff reward limit
        (quittingAllContinueRoot : Fin 4 → PMF Bool) = limit := by
  have hhazard :=
    finFour_summable_actualExactPrefix_hazard_of_no_uniformPayoff
      reward hnot profiles roots hnested hexact
  obtain ⟨limit, hpayoff⟩ :=
    exists_tendsto_terminalPayoff_of_nested_of_summable_marginalHazard
      reward profiles roots (M := quittingRewardBound reward)
        (abs_reward_le_quittingRewardBound reward) hnested hhazard
  have hlimit :=
    allContinue_exactNash_and_fixedPoint_of_tendsto_terminalPayoff
      reward profiles roots limit hpayoff hhazard hexact
  refine ⟨limit, hpayoff, fun offset => ⟨?_, ?_⟩, hlimit⟩
  · exact tendsto_reversePrefix_frontRoot_allContinue roots hhazard offset
  · intro player
    exact (hpayoff player).comp (Filter.tendsto_sub_atTop_nat (offset + 1))

end GameTheory
