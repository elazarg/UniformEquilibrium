/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.DiscreteHazardStopping

/-!
# Survival-weighted coboundaries for varying hazards

These identities are the finite-horizon algebra behind chronological
rare-activation and reset arguments.  The hazard may vary at every date; the
survival product is therefore retained explicitly rather than replaced by a
constant geometric factor.
-/

noncomputable section

open scoped BigOperators

namespace Math.Probability.DiscreteHazard.ScalarHazard

/-- A varying-hazard coboundary telescopes after weighting by preceding
survival. -/
theorem sum_survival_mul_coboundary_eq
    (hazard : ScalarHazard) (value : ℕ → ℝ) (start fuel : ℕ) :
    (∑ offset ∈ Finset.range fuel,
        hazard.survival start offset *
          (value (start + offset) -
            (1 - hazard.stop (start + offset)) * value (start + offset + 1))) =
      value start - hazard.survival start fuel * value (start + fuel) := by
  induction fuel with
  | zero => simp [survival_zero]
  | succ fuel ih =>
      rw [Finset.sum_range_succ, ih, survival_succ]
      rw [show start + fuel + 1 = start + (fuel + 1) by omega]
      ring

/-- The ordinary finite difference is a survival-weighted coboundary plus an
explicit remainder carrying the varying hazard. -/
theorem sum_survival_mul_difference_eq_coboundary_sub_remainder
    (hazard : ScalarHazard) (value : ℕ → ℝ) (start fuel : ℕ) :
    (∑ offset ∈ Finset.range fuel,
        hazard.survival start offset *
          (value (start + offset) - value (start + offset + 1))) =
      value start - hazard.survival start fuel * value (start + fuel) -
        ∑ offset ∈ Finset.range fuel,
          hazard.survival start offset * hazard.stop (start + offset) *
            value (start + offset + 1) := by
  have hdecompose :
      (∑ offset ∈ Finset.range fuel,
          hazard.survival start offset *
            (value (start + offset) - value (start + offset + 1))) =
        (∑ offset ∈ Finset.range fuel,
            hazard.survival start offset *
              (value (start + offset) -
                (1 - hazard.stop (start + offset)) *
                  value (start + offset + 1))) -
          ∑ offset ∈ Finset.range fuel,
            hazard.survival start offset * hazard.stop (start + offset) *
              value (start + offset + 1) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro offset hoffset
    ring
  rw [hdecompose, sum_survival_mul_coboundary_eq]

/-- A bounded value sequence has a bounded survival-weighted hazard
remainder. -/
theorem abs_sum_survival_mul_hazard_value_le
    (hazard : ScalarHazard) (value : ℕ → ℝ) (bound : ℝ)
    (hvalue : ∀ time, |value time| ≤ bound)
    (start fuel : ℕ) :
    |∑ offset ∈ Finset.range fuel,
        hazard.survival start offset * hazard.stop (start + offset) *
          value (start + offset + 1)| ≤
      bound * (1 - hazard.survival start fuel) := by
  have hterm : ∀ offset,
      |hazard.survival start offset * hazard.stop (start + offset) *
          value (start + offset + 1)| ≤
        bound * (hazard.survival start offset *
          hazard.stop (start + offset)) := by
    intro offset
    rw [abs_mul, abs_mul]
    calc
      |hazard.survival start offset| * |hazard.stop (start + offset)| *
            |value (start + offset + 1)| ≤
          hazard.survival start offset * hazard.stop (start + offset) * bound := by
        rw [abs_of_nonneg (survival_nonneg hazard start offset),
          abs_of_nonneg (hazard.stop_nonneg _)]
        exact mul_le_mul_of_nonneg_left (hvalue _)
          (mul_nonneg (survival_nonneg hazard start offset)
            (hazard.stop_nonneg _))
      _ = bound * (hazard.survival start offset *
          hazard.stop (start + offset)) := by ring
  calc
    |∑ offset ∈ Finset.range fuel,
        hazard.survival start offset * hazard.stop (start + offset) *
          value (start + offset + 1)| ≤
        ∑ offset ∈ Finset.range fuel,
          |hazard.survival start offset * hazard.stop (start + offset) *
            value (start + offset + 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ offset ∈ Finset.range fuel,
          bound * (hazard.survival start offset *
            hazard.stop (start + offset)) :=
      Finset.sum_le_sum fun offset hoffset => hterm offset
    _ = bound * (1 - hazard.survival start fuel) := by
      rw [← Finset.mul_sum, sum_survival_mul_stop]

end Math.Probability.DiscreteHazard.ScalarHazard
