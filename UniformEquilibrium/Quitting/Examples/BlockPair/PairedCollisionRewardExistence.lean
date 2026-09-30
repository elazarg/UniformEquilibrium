/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Examples.BlockPair.PairedCollisionRewardExits
import UniformEquilibrium.Quitting.Examples.BlockPair.PairedCollisionRewardPeriodic

/-!
# Uniform-equilibrium payoff existence for every real paired collision parameter

The same literal raw reward table is used in all four overlapping branches.
This existence conclusion does not assert the separate packet obligations for
exact censored clock laws, explicit finite-horizon constants, or class separation.
-/

noncomputable section

namespace GameTheory.PairedCollisionReward

/-- The internally selected stationary hazard has the packet's opponent-survival bound. -/
theorem stationaryOpponentMass_bound {q : ℝ}
    (hq : q ∈ Set.Ioo ((1 : ℝ) / 100) (1 / 2)) :
    stationaryOpponentMass q ≤ ((99 : ℝ) / 100) ^ 3 := by
  unfold stationaryOpponentMass
  exact pow_le_pow_left₀ (by linarith [hq.2] : 0 ≤ 1 - q)
    (by linarith [hq.1] : 1 - q ≤ 99 / 100) 3

/-- Every real input parameter has a fixed uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff (c : ℝ) :
    ∃ payoff : Payoff Player,
      (quittingGame (reward c)).IsUniformEquilibriumPayoff none payoff := by
  by_cases hc1 : c ≤ 1
  · exact exists_uniformPayoff_of_le_one hc1
  · by_cases hc2 : c ≤ 2
    · obtain ⟨rates, hpayoff⟩ := exists_periodicUniformPayoff
        (show c ∈ Set.Icc (1 : ℝ) 2 from ⟨(lt_of_not_ge hc1).le, hc2⟩)
      exact ⟨rates.phaseAValue, hpayoff⟩
    · by_cases hc4 : c ≤ 4
      · obtain ⟨q, _hq, hpayoff⟩ := exists_stationaryUniformPayoff
          (lt_of_not_ge hc2).le hc4
        exact ⟨fun _ => stationaryQuitValue c q, hpayoff⟩
      · exact ⟨surePairValue c, surePair_isUniformEquilibriumPayoff
          (lt_of_not_ge hc4).le⟩

end GameTheory.PairedCollisionReward
