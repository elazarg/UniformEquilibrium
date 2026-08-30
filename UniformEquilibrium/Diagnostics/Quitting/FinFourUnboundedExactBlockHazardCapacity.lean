/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.FullSupportProjectiveQBarResidual
import UniformEquilibrium.Quitting.Classification.Existence.AllNormalUnboundedExactBlockHazardCapacity

/-!
# Fin4 unbounded exact-block hazard capacity

The quantitative full-support hard residual available under failure of a
Fin4 uniform payoff makes every player punishment-normal.  Consequently the
generic all-normal capacity theorem turns unbounded exact-block hazard
capacity in the canonical Nash--Bellman box into a uniform-equilibrium
payoff.  Contrapositively, a Fin4 counterexample has bounded exact-block
hazard capacity in that box.

This does not produce unbounded capacity, identify a numerical capacity
bound, or bound source-trace capacity.
-/

noncomputable section

namespace GameTheory

open Math.Probability

/-- Four-player unbounded exact-block hazard capacity in the canonical reward
box gives a uniform-equilibrium payoff. -/
theorem finFour_exists_uniformEquilibriumPayoff_of_unboundedExactBlockHazardCapacity
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hcapacity : HasUnboundedFiniteExactNashBellmanHazardCapacity reward
      (quittingNashBellmanBox (quittingRewardBound reward))) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hnot
  obtain ⟨residual⟩ :=
    nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff
      reward (abs_reward_le_quittingRewardBound reward) hnot
  exact hnot
    (exists_uniformEquilibriumPayoff_of_unboundedExactBlockHazardCapacity_of_allNormal
      reward (quittingNashBellmanBox (quittingRewardBound reward))
      (quittingNashBellmanBox_isCompact (quittingRewardBound reward))
      hcapacity residual.all_punishmentNormal)

/-- Contrapositive Fin4 capstone: absence of a uniform-equilibrium payoff
forces bounded exact Nash--Bellman hazard capacity in the canonical box. -/
theorem finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    HasBoundedFiniteExactNashBellmanHazardCapacity reward
      (quittingNashBellmanBox (quittingRewardBound reward)) := by
  by_contra hunbounded
  exact hnot
    (finFour_exists_uniformEquilibriumPayoff_of_unboundedExactBlockHazardCapacity
      reward hunbounded)

end GameTheory
