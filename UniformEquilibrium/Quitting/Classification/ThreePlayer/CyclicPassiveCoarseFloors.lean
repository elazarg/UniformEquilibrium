/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.ThreePlayer.CyclicCompiler

/-!
# Exact passive coarse floors for a right singleton cycle

An arbitrary signed row is applied to the existing three active surplus
vectors. Each phase tests one row coordinate against a strictly positive
surplus. Thus all three affine coarse floors hold exactly when that row is
nonnegative. This is a criterion for these particular constructed coarse
values, not a necessity claim about arbitrary ambient equilibria.
-/

noncomputable section

namespace GameTheory

/-- Passive affine phase values with arbitrary real weights. No row
factorization or nonnegativity hypothesis is built into this definition. -/
def rightPassiveCoarse (reward : QuittingReward3) (baseline : ℝ)
    (weight : Fin 3 → ℝ) (phase : Fin 3) : ℝ :=
  baseline + ∑ who : Fin 3,
    weight who * (rightCoarse reward phase who - quittingSoloReward reward who who)

/-- The phase-zero passive target is the singleton baseline plus the weight
at player one times that phase's sole positive active surplus. -/
theorem rightPassiveCoarse_zero (reward : QuittingReward3) (baseline : ℝ)
    (weight : Fin 3 → ℝ) :
    rightPassiveCoarse reward baseline weight 0 =
      baseline + weight 1 * (rightS reward * rightAlpha reward) := by
  rw [rightPassiveCoarse, Fin.sum_univ_three]
  change baseline +
    (weight 0 * (quittingSoloReward reward 0 0 - quittingSoloReward reward 0 0) +
      weight 1 * ((1 - rightAlpha reward) * quittingSoloReward reward 1 1 +
        rightAlpha reward * quittingSoloReward reward 0 1 - quittingSoloReward reward 1 1) +
      weight 2 * (quittingSoloReward reward 2 2 - quittingSoloReward reward 2 2)) = _
  unfold rightS
  ring

/-- Phase one has its active surplus at player two. -/
theorem rightPassiveCoarse_one (reward : QuittingReward3) (baseline : ℝ)
    (weight : Fin 3 → ℝ) :
    rightPassiveCoarse reward baseline weight 1 =
      baseline + weight 2 * (rightU reward * rightBeta reward) := by
  rw [rightPassiveCoarse, Fin.sum_univ_three]
  change baseline +
    (weight 0 * (quittingSoloReward reward 0 0 - quittingSoloReward reward 0 0) +
      weight 1 * (quittingSoloReward reward 1 1 - quittingSoloReward reward 1 1) +
      weight 2 * ((1 - rightBeta reward) * quittingSoloReward reward 2 2 +
        rightBeta reward * quittingSoloReward reward 1 2 - quittingSoloReward reward 2 2)) = _
  unfold rightU
  ring

/-- Phase two has its active surplus at player zero. -/
theorem rightPassiveCoarse_two (reward : QuittingReward3) (baseline : ℝ)
    (weight : Fin 3 → ℝ) :
    rightPassiveCoarse reward baseline weight 2 =
      baseline + weight 0 * (rightQ reward * rightGamma reward) := by
  rw [rightPassiveCoarse, Fin.sum_univ_three]
  change baseline +
    (weight 0 * ((1 - rightGamma reward) * quittingSoloReward reward 0 0 +
        rightGamma reward * quittingSoloReward reward 2 0 - quittingSoloReward reward 0 0) +
      weight 1 * (quittingSoloReward reward 1 1 - quittingSoloReward reward 1 1) +
      weight 2 * (quittingSoloReward reward 2 2 - quittingSoloReward reward 2 2)) = _
  unfold rightQ
  ring

/-- For the explicit right cycle, its three passive affine coarse floors
hold if and only if every row weight is nonnegative. The baseline is unrestricted. -/
theorem rightPassiveCoarse_floor_iff {reward : QuittingReward3}
    (cycle : RightSingletonCycle reward) (baseline : ℝ) (weight : Fin 3 → ℝ) :
    (∀ phase, baseline ≤ rightPassiveCoarse reward baseline weight phase) ↔
      ∀ who, 0 ≤ weight who := by
  have hQ := (right_gaps_pos cycle).2.1
  have hS := (right_gaps_pos cycle).2.2.2.1
  have hU := (right_gaps_pos cycle).2.2.2.2.2
  obtain ⟨halpha, hbeta, hgamma⟩ := right_rates_pos cycle
  have hfirst := mul_pos hS halpha
  have hsecond := mul_pos hU hbeta
  have hthird := mul_pos hQ hgamma
  constructor
  · intro hfloors who
    have hzero := hfloors 0
    have hone := hfloors 1
    have htwo := hfloors 2
    rw [rightPassiveCoarse_zero] at hzero
    rw [rightPassiveCoarse_one] at hone
    rw [rightPassiveCoarse_two] at htwo
    fin_cases who
    · change 0 ≤ weight (0 : Fin 3)
      exact (mul_nonneg_iff_of_pos_right hthird).mp (by linarith)
    · change 0 ≤ weight (1 : Fin 3)
      exact (mul_nonneg_iff_of_pos_right hfirst).mp (by linarith)
    · change 0 ≤ weight (2 : Fin 3)
      exact (mul_nonneg_iff_of_pos_right hsecond).mp (by linarith)
  · intro hweight phase
    fin_cases phase
    · change baseline ≤ rightPassiveCoarse reward baseline weight (0 : Fin 3)
      rw [rightPassiveCoarse_zero]
      exact le_add_of_nonneg_right (mul_nonneg (hweight 1) hfirst.le)
    · change baseline ≤ rightPassiveCoarse reward baseline weight (1 : Fin 3)
      rw [rightPassiveCoarse_one]
      exact le_add_of_nonneg_right (mul_nonneg (hweight 2) hsecond.le)
    · change baseline ≤ rightPassiveCoarse reward baseline weight (2 : Fin 3)
      rw [rightPassiveCoarse_two]
      exact le_add_of_nonneg_right (mul_nonneg (hweight 0) hthird.le)

end GameTheory
