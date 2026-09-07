import UniformEquilibrium.Quitting.Cycles.PairedCycleFin4Source
import UniformEquilibrium.Quitting.Cycles.PairedCycleAffineEquilibrium

/-! # The literal transformed infinite Fin4 paired profile -/

noncomputable section

namespace GameTheory.PairedCycle

open Math.PairedAffine

/-- Applied to the q and zero certificate furnished by the fixed-menu source,
this certifies that very transformed infinite profile and its fixed target. -/
theorem fin4Pivot_infinite_exact_of_selected
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hregion : RawRegion reward fin4Schedule) (q : Fin 4 → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap fin4Schedule.partner (singleton reward)
      (partnerReward reward fin4Schedule) (jointReward reward fin4Schedule)
      (quietRows reward fin4Schedule) q player = 0) :
    (∀ initial start,
      (quittingGame (fin4PivotReward reward)).IsεAsymptoticNash
        (quittingTerminalPayoff (fin4PivotReward reward)) 0
        (quittingRootSequenceProfile (fin4PivotReward reward)
          (quittingCyclicRootSequence (cycle fin4Schedule q hq) initial) start)) ∧
    quittingTerminalPayoff (fin4PivotReward reward)
        (quittingCyclicBehaviorProfile (fin4PivotReward reward) (cycle fin4Schedule q hq) 0) =
      fin4PivotValue reward q hq ∧
    (quittingGame (fin4PivotReward reward)).IsUniformEquilibriumPayoff none
      (fin4PivotValue reward q hq) := by
  refine ⟨?_, ?_, ?_⟩
  · intro initial start
    exact affine_allSuffix_isExactNash_of_selected reward fin4Schedule hregion q hq
      hinterior hzero (fin4PivotScale reward) (fin4PivotShift reward)
      (fin4PivotScale_pos reward hregion) initial start
  · funext player
    rw [quittingTerminalPayoff_cyclicBehaviorProfile]
    exact affine_value reward fin4Schedule q hq
      (fun player => by linarith [(hinterior player).1])
      (fin4PivotScale reward) (fin4PivotShift reward) 0 player
  · exact affine_isUniformPayoff_of_selected reward fin4Schedule hregion q hq
      hinterior hzero (fin4PivotScale reward) (fin4PivotShift reward)
      (fin4PivotScale_pos reward hregion) 0

end GameTheory.PairedCycle
