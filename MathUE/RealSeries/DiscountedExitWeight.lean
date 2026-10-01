import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! # The normalized discounted weight of an exit at a finite date -/

namespace Math.RealSeries

open scoped BigOperators Classical

/-- Exit at date t first pays at stage t+1 under the zero-live-stage convention. -/
theorem normalized_geometric_exit_weight
    (discount value : ℝ) (hdiscount : 0 ≤ discount) (hdiscountOne : discount < 1)
    (exit : ℕ) :
    (1 - discount) * ∑' stage : ℕ,
        discount ^ stage * (if exit < stage then value else 0) =
      discount ^ (exit + 1) * value := by
  have hs : Summable (fun stage : ℕ =>
      discount ^ stage * (if exit < stage then value else 0)) := by
    refine ((summable_geometric_of_lt_one hdiscount hdiscountOne).mul_right |value|).of_norm_bounded
      ?_
    intro stage
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hdiscount stage)]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hdiscount stage)
    split_ifs
    · exact le_rfl
    · simpa only [abs_zero] using abs_nonneg value
  have hprefix :
      (∑ stage ∈ Finset.range (exit + 1),
        discount ^ stage * (if exit < stage then value else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro stage hstage
    have hnot : ¬ exit < stage := by
      have := Finset.mem_range.mp hstage
      omega
    simp only [ite_eq_right hnot, mul_zero]
  have htail :
      (∑' stage : ℕ, discount ^ (stage + (exit + 1)) *
        (if exit < stage + (exit + 1) then value else 0)) =
      discount ^ (exit + 1) * ∑' stage : ℕ, discount ^ stage * value := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro stage
    rw [ite_eq_left (by omega), pow_add]
    ring
  have hsplit := hs.sum_add_tsum_nat_add (exit + 1)
  rw [hprefix, zero_add, htail] at hsplit
  rw [← hsplit, tsum_mul_right, tsum_geometric_of_lt_one hdiscount hdiscountOne]
  have hnonzero : 1 - discount ≠ 0 := sub_ne_zero.mpr (ne_of_gt hdiscountOne)
  calc
    (1 - discount) * (discount ^ (exit + 1) * ((1 - discount)⁻¹ * value)) =
        discount ^ (exit + 1) * ((1 - discount) * (1 - discount)⁻¹) * value := by ring
    _ = discount ^ (exit + 1) * value := by rw [mul_inv_cancel₀ hnonzero, mul_one]

end Math.RealSeries
