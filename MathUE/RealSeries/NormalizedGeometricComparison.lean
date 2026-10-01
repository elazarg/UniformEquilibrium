import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Ring

/-! # Two-sided normalized geometric comparison with a summable clock -/

namespace Math.RealSeries

open scoped BigOperators

/-- A stagewise absolute error transfers to the normalized geometric series.
The actual clock is retained; no positivity or regularity of the stage rewards
is required. Summability of the payoff series follows from the same bound. -/
theorem abs_normalized_geometric_sub_le_clock
    (discount value bound : ℝ) (payoff clock : ℕ → ℝ)
    (hdiscount : 0 ≤ discount) (hdiscountOne : discount < 1)
    (hclock : Summable (fun time => discount ^ time * clock time))
    (herror : ∀ time, |payoff time - value| ≤ bound * clock time) :
    |(1 - discount) * ∑' time, discount ^ time * payoff time - value| ≤
      bound * (1 - discount) * ∑' time, discount ^ time * clock time := by
  let error := fun time => discount ^ time * (payoff time - value)
  have hdom : Summable (fun time => bound * (discount ^ time * clock time)) :=
    hclock.mul_left bound
  have hpointwise : ∀ time, ‖error time‖ ≤ bound * (discount ^ time * clock time) := by
    intro time
    dsimp only [error]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hdiscount time)]
    simpa only [mul_assoc, mul_left_comm] using
      mul_le_mul_of_nonneg_left (herror time) (pow_nonneg hdiscount time)
  have hsError : Summable error := hdom.of_norm_bounded hpointwise
  have hsConst : Summable (fun time : ℕ => discount ^ time * value) :=
    (summable_geometric_of_lt_one hdiscount hdiscountOne).mul_right value
  have hsplit :
      (∑' time : ℕ, discount ^ time * payoff time) =
        (∑' time, error time) + ∑' time : ℕ, discount ^ time * value := by
    rw [← hsError.tsum_add hsConst]
    apply tsum_congr
    intro time
    dsimp only [error]
    ring
  have hconst :
      (1 - discount) * (∑' time : ℕ, discount ^ time * value) = value := by
    rw [tsum_mul_right, tsum_geometric_of_lt_one hdiscount hdiscountOne, ← mul_assoc,
      mul_inv_cancel₀ (sub_ne_zero.mpr (ne_of_gt hdiscountOne)), one_mul]
  have hrewrite :
      (1 - discount) * (∑' time : ℕ, discount ^ time * payoff time) - value =
        (1 - discount) * ∑' time, error time := by
    rw [hsplit, mul_add, hconst]
    ring
  have hsum := tsum_of_norm_bounded hdom.hasSum hpointwise
  rw [Real.norm_eq_abs, tsum_mul_left] at hsum
  rw [hrewrite, abs_mul, abs_of_nonneg (sub_nonneg.mpr hdiscountOne.le)]
  calc
    (1 - discount) * |∑' time, error time| ≤
        (1 - discount) * (bound * ∑' time, discount ^ time * clock time) :=
      mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hdiscountOne.le)
    _ = bound * (1 - discount) * ∑' time, discount ^ time * clock time := by ring

end Math.RealSeries
