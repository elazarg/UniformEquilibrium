/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorInfiniteOrbit
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanQuitEndpointLimit

/-!
# Quantitative limit bounds for punishment-floor infinite orbits

Successive prescribed values along an exact punishment-floor orbit move by at
most the current absorption mass. Every orbit value dominates the punishment
floor, and the next value dominates the solo reward up to the current
opponent-absorption hazard.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingPunishmentFloorInfiniteOrbit

variable (orbit : QuittingPunishmentFloorInfiniteOrbit reward)

/-- Every coordinate of every orbit annotation lies in the canonical reward
interval. -/
theorem abs_value_le_quittingRewardBound (time : ℕ) (who : ι) :
    |orbit.value time who| ≤ quittingRewardBound reward := by
  have hmem : orbit.value time ∈ Set.Icc
      (fun _ : ι => -quittingRewardBound reward)
      (fun _ : ι => quittingRewardBound reward) := orbit.value_mem time
  exact abs_le.mpr ⟨hmem.1 who, hmem.2 who⟩

/-- Consecutive orbit annotations differ coordinatewise by at most twice the
reward bound times the stage's absorption mass. -/
theorem abs_value_succ_sub_le_two_mul_absorptionMass (time : ℕ) (who : ι) :
    |orbit.value (time + 1) who - orbit.value time who| ≤
      2 * quittingRewardBound reward *
        quittingRootAbsorptionMass (orbit.roots time) := by
  rw [orbit.policy time]
  exact abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
    reward (orbit.value time) (orbit.roots time) who
    (quittingRewardBound reward)
    (abs_reward_le_quittingRewardBound reward)
    (orbit.abs_value_le_quittingRewardBound time who)

/-- Every orbit annotation dominates the behavioral punishment floor. -/
theorem punishmentValue_le_value (time : ℕ) (who : ι) :
    quittingPunishmentValue reward who ≤ orbit.value time who :=
  quittingPunishmentValue_le_finitePrefixValue
    (orbit.toFinitePrefix time) time le_rfl who

/-- Each successor annotation is at least the player's solo reward minus the
current opponent-absorption error. -/
theorem soloReward_sub_opponentHazard_le_value_succ (time : ℕ) (who : ι) :
    quittingSoloReward reward who who -
        2 * quittingRewardBound reward *
          quittingRootOpponentAbsorptionMass (orbit.roots time) who ≤
      orbit.value (time + 1) who := by
  have hest :=
    abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
      reward (orbit.value time) (orbit.roots time) who
      (quittingRewardBound reward)
      (abs_reward_le_quittingRewardBound reward)
  have hquit := quittingRootQuitPayoff_le_successor_of_isZeroNash
    reward (orbit.value time) (orbit.roots time) who (orbit.exactNash time)
  have hsucc : orbit.value (time + 1) who =
      quittingRootSuccessorPayoff reward (orbit.value time)
        (orbit.roots time) who :=
    congrFun (orbit.policy time) who
  have hsolo : quittingSoloReward reward who who =
      reward (quittingSingletonTerminal who) who := rfl
  have hpair := abs_le.mp hest
  rw [hsolo]
  linarith [hpair.1, hquit, hsucc]

end QuittingPunishmentFloorInfiniteOrbit

end GameTheory
