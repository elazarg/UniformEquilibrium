import UniformEquilibrium.Quitting.Classification.MixedSignTripleCoreSelectedReturn
import UniformEquilibrium.Quitting.Classification.Existence.SelectedSingletonSublevelReturnUniformPayoff
import UniformEquilibrium.Quitting.Root.PureSetNashSureExit

/-! # Actual Fin4 payoff from the strict mixed-sign triple equality stratum

All source derivatives, tie avoidance and selected return are produced from
the printed reward comparisons. An actual pure positive-pair root is handled
by its unrestricted sure-exit payoff. The final input contains no root oracle.
-/

noncomputable section

namespace GameTheory

theorem exists_uniformEquilibriumPayoff_of_mixedSignTriple_core
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsingleton : ∀ player, 0 ≤ reward (quittingSingletonTerminal player) player)
    {first second third : Fin 4}
    (hcore : quittingPremiumCore reward = {first, second, third})
    (hjoining : HasMixedSignTripleJoining reward first second third) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  classical
  by_cases hpure : ∃ tail : Payoff (Fin 4), IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second (PMF.pure true) (PMF.pure true))
  · obtain ⟨tail, hnash⟩ := hpure
    exact ⟨_, isUniformEquilibriumPayoff_pairReward_of_purePairNash reward tail
      hjoining.pairwise_distinct.1 hnash⟩
  · apply exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn reward hsingleton
    apply hasBoxedSelectedSingletonSublevelReturn_of_mixedSignTriple_core reward hcore hjoining
    intro tail hnash
    exact hpure ⟨tail, hnash⟩

end GameTheory
