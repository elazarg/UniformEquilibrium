/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ProbabilityMassFunction.Simplex
import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Punishment.OwnerSoloCertification
import UniformEquilibrium.Quitting.Punishment.SoloQuitterEquilibrium

/-!
# Nonclosedness at the diffuse stationarily generated boundary

Positive-live product roots form a nonclosed region at the all-Continue
boundary.  More importantly, literal terminal payoff and terminal Nash are
not continuous under coordinatewise convergence there.

The one-player family below makes the obstruction exact.  The player quits
with probability `1 / (n + 2)` each stage.  Every profile is an exact
behavioral Nash equilibrium with terminal payoff one, and every root has
positive all-Continue mass.  The roots nevertheless converge coordinatewise
to pure Continue, whose stationary profile has payoff zero and is not Nash.

This does **not** refute compactification of the corrected Simon branch: the
example already has stationary equilibria at every positive hazard.  It does
show that selecting a pointwise limit of roots or behavior profiles cannot be
the compactification proof.  A valid proof must retain terminal semantics,
for example in `QuittingTerminalSemanticPair`, and then decode the limiting
semantic data to an actual stationary or well-supported absorbing witness.
-/

noncomputable section

namespace GameTheory
namespace StationarilyGeneratedCompactnessObstruction

open Filter StochasticGame
open QuittingSureSetOwnerRepair
open scoped Topology

/-- The one-player terminal table with reward one whenever the player quits. -/
def reward : {S : Finset PUnit // S.Nonempty} → Payoff PUnit :=
  fun _ _ ↦ 1

/-- A positive hazard tending to zero. -/
def rate (n : ℕ) : ℝ := ((n : ℝ) + 2)⁻¹

theorem rate_pos (n : ℕ) : 0 < rate n := by
  unfold rate
  positivity

theorem rate_le_one (n : ℕ) : rate n ≤ 1 := by
  rw [rate, inv_le_one₀ (by positivity)]
  norm_cast
  omega

/-- The Boolean hazard with displayed Quit probability `rate n`. -/
def hazard (n : ℕ) : PMF Bool :=
  Math.ProbabilityMassFunction.bernoulliBool (rate n) (rate_pos n).le
    (rate_le_one n)

@[simp] theorem hazard_true_toReal (n : ℕ) :
    (hazard n true).toReal = rate n := by
  simp [hazard]

@[simp] theorem hazard_false_toReal (n : ℕ) :
    (hazard n false).toReal = 1 - rate n := by
  simp [hazard]

/-- The stationary product root carrying the vanishing positive hazard. -/
def root (n : ℕ) : PUnit → PMF Bool :=
  quittingSoloStationaryRoot PUnit.unit (hazard n)

/-- The corresponding stationary behavior profile. -/
def profile (n : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (root n)

/-- The limit root is all-Continue. -/
def limitRoot : PUnit → PMF Bool := quittingPureSetRoot ∅

/-- The limit stationary profile is the all-Continue profile. -/
def limitProfile : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward limitRoot

/-- Every approximating root remains live with positive one-stage
probability. -/
theorem root_continueMass_pos (n : ℕ) :
    0 < quittingStationaryContinueMass (root n) := by
  rw [root, quittingStationaryContinueMass_solo, hazard_false_toReal]
  have hrate := rate_le_one n
  have hstrict : rate n < 1 := by
    rw [rate, inv_lt_one₀ (by positivity)]
    norm_cast
    omega
  linarith

/-- The displayed Quit probabilities tend to zero. -/
theorem tendsto_rate_zero : Tendsto rate atTop (nhds 0) := by
  apply tendsto_inv_atTop_zero.comp
  exact tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop

/-- The product roots converge coordinatewise to all-Continue. -/
theorem tendsto_root_coordinate (player : PUnit) (action : Bool) :
    Tendsto (fun n ↦ (root n player action).toReal) atTop
      (nhds ((limitRoot player action).toReal)) := by
  cases player
  cases action with
  | false =>
      have h := (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).sub tendsto_rate_zero
      simpa [root, limitRoot] using h
  | true =>
      simpa [root, limitRoot] using tendsto_rate_zero

/-- Every positive-hazard approximant has terminal payoff one. -/
@[simp] theorem terminalPayoff_profile (n : ℕ) :
    quittingTerminalPayoff reward (profile n) PUnit.unit = 1 := by
  rw [profile, root, quittingTerminalPayoff_soloStationary reward
    PUnit.unit PUnit.unit (hazard n)]
  · simp [quittingSoloReward, reward]
  · simpa using rate_pos n

/-- Every positive-hazard approximant is an exact behavioral Nash
equilibrium. -/
theorem profile_isExactNash (n : ℕ) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 (profile n) := by
  apply isεAsymptoticNash_soloStationary_exact reward PUnit.unit (hazard n)
  · simpa using rate_pos n
  · simp [quittingSoloReward, reward]
  · intro other hother
    exact False.elim (hother (Subsingleton.elim other PUnit.unit))

/-- The all-Continue limit profile has terminal payoff zero. -/
@[simp] theorem terminalPayoff_limitProfile :
    quittingTerminalPayoff reward limitProfile PUnit.unit = 0 := by
  rw [limitProfile]
  exact quittingTerminalPayoff_pureSetRoot reward ∅ PUnit.unit

/-- Quitting at the first stage against the limit profile pays one. -/
@[simp] theorem terminalPayoff_limitProfile_quitNow :
    quittingTerminalPayoff reward
        (Function.update limitProfile PUnit.unit
          (quittingPureTimeBehaviorStrategy reward PUnit.unit (some 0)))
        PUnit.unit = 1 := by
  unfold limitProfile limitRoot
  rw [quittingTerminalPayoff_update_pureSetRoot_quitNow]
  simp [quittingSetReward, reward]

/-- Exact terminal Nash is not closed under this coordinatewise root limit. -/
theorem limitProfile_not_isExactNash :
    ¬(quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 limitProfile := by
  intro hnash
  have hdeviation := hnash PUnit.unit
    (quittingPureTimeBehaviorStrategy reward PUnit.unit (some 0))
  rw [terminalPayoff_limitProfile_quitNow, terminalPayoff_limitProfile,
    add_zero] at hdeviation
  norm_num at hdeviation

/-- Literal terminal payoffs do not converge to the payoff of the
coordinatewise limiting profile. -/
theorem not_tendsto_terminalPayoff_to_limit :
    ¬Tendsto (fun n ↦ quittingTerminalPayoff reward (profile n) PUnit.unit)
      atTop (nhds (quittingTerminalPayoff reward limitProfile PUnit.unit)) := by
  simp only [terminalPayoff_profile, terminalPayoff_limitProfile]
  rw [tendsto_const_nhds_iff]
  norm_num

end StationarilyGeneratedCompactnessObstruction
end GameTheory
