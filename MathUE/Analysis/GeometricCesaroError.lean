import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Cesàro error from a geometric pointwise bound -/

namespace Math

open scoped BigOperators

/-- Averaging a geometric absolute error costs at most its infinite geometric sum.
The bound's nonnegativity follows from the actual error estimate at time zero. -/
theorem abs_cesaro_sub_le_of_geometric_error
    (sequence : ℕ → ℝ) (target : ℝ) {bound ratio : ℝ}
    (hratio0 : 0 ≤ ratio) (hratio1 : ratio < 1)
    (herror : ∀ time, |sequence time - target| ≤ bound * ratio ^ time)
    (horizon : ℕ) (hhorizon : 0 < horizon) :
    |(horizon : ℝ)⁻¹ * (∑ time ∈ Finset.range horizon, sequence time) - target| ≤
      bound / ((1 - ratio) * (horizon : ℝ)) := by
  have hbound : 0 ≤ bound := by
    simpa only [pow_zero, mul_one] using (abs_nonneg _).trans (herror 0)
  have hhorizonNe : (horizon : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hhorizon)
  have hrearrange : (horizon : ℝ)⁻¹ *
      (∑ time ∈ Finset.range horizon, sequence time) - target =
      (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon, (sequence time - target) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_sub,
      ← mul_assoc, inv_mul_cancel₀ hhorizonNe, one_mul]
  have hgeometric : (∑ time ∈ Finset.range horizon, ratio ^ time) ≤ (1 - ratio)⁻¹ := by
    have hpartial := (summable_geometric_of_lt_one hratio0 hratio1).sum_le_tsum
      (Finset.range horizon) (fun time _ => pow_nonneg hratio0 time)
    simpa only [tsum_geometric_of_lt_one hratio0 hratio1] using hpartial
  rw [hrearrange, abs_mul, abs_of_nonneg (by positivity)]
  calc
    (horizon : ℝ)⁻¹ * |∑ time ∈ Finset.range horizon, (sequence time - target)| ≤
        (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon, |sequence time - target| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon, bound * ratio ^ time :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun time _ => herror time)
        (by positivity)
    _ = (horizon : ℝ)⁻¹ * (bound * ∑ time ∈ Finset.range horizon, ratio ^ time) := by
      rw [← Finset.mul_sum]
    _ ≤ (horizon : ℝ)⁻¹ * (bound * (1 - ratio)⁻¹) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgeometric hbound)
        (by positivity)
    _ = bound / ((1 - ratio) * (horizon : ℝ)) := by
      rw [div_eq_mul_inv, mul_inv_rev]
      ring

end Math
