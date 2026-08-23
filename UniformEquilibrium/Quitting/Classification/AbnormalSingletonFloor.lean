/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.AbnormalPlayers
import UniformEquilibrium.Quitting.Boundary.Exceptional.TailFallback

/-!
# Singleton floors of abnormal players

An abnormal player's punishment value is weakly below that player's payoff in
every other owner's singleton row.  The proof is entirely in the production
semantics: test the punishment infimum against stationary rows in which the
other owner quits at a vanishing positive rate.  No literature minmax adapter
is used.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every other singleton row pays an abnormal player at least her behavioral
punishment value. -/
theorem quittingPunishmentValue_le_soloReward_of_abnormal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {abnormal owner : ι}
    (habnormal : IsQuittingAbnormalPlayer reward abnormal)
    (hne : abnormal ≠ owner) :
    quittingPunishmentValue reward abnormal ≤
      quittingSoloReward reward owner abnormal := by
  let rate : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hratePos : ∀ n, 0 < rate n := by
    intro n
    dsimp only [rate]
    positivity
  have hrateOne : ∀ n, rate n ≤ 1 := by
    intro n
    dsimp only [rate]
    apply (div_le_one (by positivity)).2
    exact_mod_cast (show (1 : ℕ) ≤ n + 1 by omega)
  have hrateVanish : Tendsto rate atTop (nhds 0) := by
    simpa only [rate] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (nhds 0))
  let hazard : ℕ → PMF Bool := fun n =>
    quittingHazardCoin (rate n) (hratePos n).le (hrateOne n)
  have hmix : Tendsto
      (fun n =>
        (1 - rate n) * quittingSoloReward reward abnormal abnormal +
          rate n * quittingSingletonCollisionReward reward owner abnormal)
      atTop (nhds (quittingSoloReward reward abnormal abnormal)) := by
    convert ((tendsto_const_nhds.sub hrateVanish).mul
      tendsto_const_nhds).add (hrateVanish.mul tendsto_const_nhds) using 1
    all_goals ring_nf
  have hcap : Tendsto
      (fun n => quittingStationaryUnilateralCap reward
        (quittingSoloStationaryRoot owner (hazard n)) abnormal)
      atTop
      (nhds (max (quittingSoloReward reward abnormal abnormal)
        (quittingSoloReward reward owner abnormal))) := by
    apply (hmix.max tendsto_const_nhds).congr'
    filter_upwards [] with n
    rw [quittingStationaryUnilateralCap_solo_other reward hne
      (hazard n) (by simp [hazard, hratePos n]),
      quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
        reward hne]
    simp [hazard]
  have hpunishment : quittingPunishmentValue reward abnormal ≤
      max (quittingSoloReward reward abnormal abnormal)
        (quittingSoloReward reward owner abnormal) := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hcap
    filter_upwards [] with n
    exact quittingPunishmentValue_le_stationaryUnilateralCap
      reward abnormal
        (quittingSoloStationaryRoot owner (hazard n))
  have habnormal' : quittingSoloReward reward abnormal abnormal <
      quittingPunishmentValue reward abnormal := by
    simpa [IsQuittingAbnormalPlayer, quittingSoloSelfPayoff,
      quittingSoloReward, quittingSingletonTerminal] using habnormal
  rcases max_cases (quittingSoloReward reward abnormal abnormal)
      (quittingSoloReward reward owner abnormal) with hmax | hmax
  · rw [hmax.1] at hpunishment
    linarith
  · rwa [hmax.1] at hpunishment

end GameTheory
