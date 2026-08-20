/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.ThreeBranchDisjunction

/-!
# A negative solo endpoint produces an isolated negative cycle

A positive-rate solo stationary row which is exact endpoint Nash against its
singleton payoff vector is a self-consistent absorbing period-one block.  If
the owner's singleton payoff is negative, this block belongs to the isolated
negative branch of the cyclic classification.

This implication is intrinsic to the quitting game.  It assumes no
counterexample regime or asymptotic limit.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A positive-rate solo endpoint equilibrium with a negative owner produces
an isolated-negative absorbing period-one Nash--Bellman block. -/
theorem hasIsolatedNegativeAbsorbingQuittingCycle_of_soloEndpointNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool)
    (hpositive : 0 < (hazard true).toReal)
    (hnash : IsεQuittingRootEndpointNash reward
      (quittingSoloReward reward owner) 0
      (quittingSoloStationaryRoot owner hazard))
    (hnegative : quittingSoloReward reward owner owner < 0) :
    HasIsolatedNegativeAbsorbingQuittingCycle reward := by
  let value : Payoff ι := quittingSoloReward reward owner
  let root : ι → PMF Bool := quittingSoloStationaryRoot owner hazard
  let block : QuittingFiniteNashBellmanPath ι 1 :=
    quittingRowBlock value root
  have hvalueBound : ∀ who, |value who| ≤ quittingRewardBound reward := by
    intro who
    exact abs_reward_le_quittingRewardBound reward
      (quittingSingletonTerminal owner) who
  have hsuccessor : value =
      quittingRootSuccessorPayoff reward value root := by
    exact (quittingRootSuccessorPayoff_soloStationaryRoot_self
      reward owner hazard).symm
  have habsorption : 0 < quittingRootAbsorptionMass root := by
    dsimp only [root]
    rw [quittingRootAbsorptionMass_soloStationaryRoot]
    exact hpositive
  have hblock : IsQuittingCyclicContinuationBlock reward value 1 block :=
    quittingRowBlock_isQuittingCyclicContinuationBlock
      reward value root hvalueBound hsuccessor hnash habsorption
  have hisolated : IsQuittingIsolatedWindow
      (quittingFiniteNashBellmanPathRoots 1 block) owner 1 := by
    intro time htime
    have htimeZero : time = 0 := by omega
    subst time
    rw [quittingFiniteNashBellmanPathRoots_of_lt 1 block 0 (by omega)]
    dsimp only [block]
    rw [quittingRootOfSimplex_quittingRowBlock]
    exact (isQuittingIsolatedRoot_iff_exists_soloStationaryRoot
      root owner).2 ⟨hazard, rfl⟩
  exact ⟨value, 0, block, owner, hblock, hisolated, hnegative⟩

end GameTheory
