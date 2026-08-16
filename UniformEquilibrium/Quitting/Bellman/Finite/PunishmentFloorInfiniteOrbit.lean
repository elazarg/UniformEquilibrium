/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorFinitePrefix

/-!
# Infinite punishment-floor Nash--Bellman orbits

This module owns arbitrary infinite exact Nash--Bellman orbits in the
punishment-floor carrier and their finite truncations.  It imposes no choice
rule, counterexample assumption, or global charge bound.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- An arbitrary infinite exact Nash--Bellman orbit in the canonical box,
anchored coordinatewise above the behavioral punishment floor. -/
structure QuittingPunishmentFloorInfiniteOrbit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  roots : ℕ → ι → PMF Bool
  value : ℕ → Payoff ι
  value_mem : ∀ time,
    value time ∈ quittingPunishmentFloorForwardCarrier reward
  anchor_floor : ∀ who,
    quittingPunishmentValue reward who ≤ value 0 who
  policy : ∀ time,
    value (time + 1) =
      quittingRootSuccessorPayoff reward (value time) (roots time)
  exactNash : ∀ time,
    IsεQuittingRootNash reward (value time) 0 (roots time)

namespace QuittingPunishmentFloorInfiniteOrbit

variable (orbit : QuittingPunishmentFloorInfiniteOrbit reward)

/-- Cumulative absorption mass before a finite horizon. -/
def partialAbsorption (horizon : ℕ) : ℝ :=
  ∑ time ∈ Finset.range horizon,
    quittingRootAbsorptionMass (orbit.roots time)

/-- Every finite truncation is an exact punishment-floor prefix certificate. -/
def toFinitePrefix (horizon : ℕ) :
    QuittingPunishmentFloorFinitePrefix reward where
  roots := orbit.roots
  value := orbit.value
  horizon := horizon
  value_mem := fun time _ => orbit.value_mem time
  anchor_floor := orbit.anchor_floor
  policy := fun time _ => orbit.policy time
  exactNash := fun time _ => orbit.exactNash time

@[simp] theorem toFinitePrefix_charge (horizon : ℕ) :
    (orbit.toFinitePrefix horizon).charge = orbit.partialAbsorption horizon :=
  rfl

theorem absorptionMass_nonneg (time : ℕ) :
    0 ≤ quittingRootAbsorptionMass (orbit.roots time) := by
  unfold quittingRootAbsorptionMass
  linarith [quittingStationaryContinueMass_le_one (orbit.roots time)]

/-- A player's quit probability is bounded by the probability that at least
one player quits. -/
theorem quitProbability_le_absorptionMass (time : ℕ) (who : ι) :
    (orbit.roots time who true).toReal ≤
      quittingRootAbsorptionMass (orbit.roots time) := by
  have hcontinue :=
    quittingStationaryContinueMass_le_ownContinueProbability
      (orbit.roots time) who
  have hsum := quittingRoot_continueProbability_add_quitProbability
    (orbit.roots time) who
  unfold quittingRootAbsorptionMass
  linarith

theorem quitProbability_nonneg (time : ℕ) (who : ι) :
    0 ≤ (orbit.roots time who true).toReal :=
  ENNReal.toReal_nonneg

end QuittingPunishmentFloorInfiniteOrbit
end GameTheory
