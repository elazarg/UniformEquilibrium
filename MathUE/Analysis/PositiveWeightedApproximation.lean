import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Positive finite averages with near/far error control -/

namespace Math

open scoped BigOperators

/-- A near/far estimate for a positive finite average using a squared-distance moment. -/
theorem sum_weight_mul_abs_le_of_near_and_sq_moment {Index : Type*}
    (indices : Finset Index) (weight distance error : Index → ℝ)
    (nearBound globalBound momentBound threshold : ℝ)
    (hweight : ∀ index ∈ indices, 0 ≤ weight index)
    (hmass : ∑ index ∈ indices, weight index = 1)
    (hnearBound : 0 ≤ nearBound) (hthreshold : 0 < threshold)
    (hglobal : ∀ index ∈ indices, |error index| ≤ globalBound)
    (hnear : ∀ index ∈ indices, distance index < threshold → |error index| ≤ nearBound)
    (hmoment : ∑ index ∈ indices, weight index * distance index ^ 2 ≤ momentBound) :
    ∑ index ∈ indices, weight index * |error index| ≤
      nearBound + globalBound * momentBound / threshold ^ 2 := by
  obtain ⟨index, hindex⟩ := Finset.nonempty_of_sum_ne_zero (by rw [hmass]; exact one_ne_zero)
  have hglobalBound : 0 ≤ globalBound := (abs_nonneg (error index)).trans (hglobal index hindex)
  have hthresholdSq : 0 < threshold ^ 2 := sq_pos_of_pos hthreshold
  have hpointwise (index : Index) (hindex : index ∈ indices) :
      |error index| ≤ nearBound + globalBound / threshold ^ 2 * distance index ^ 2 := by
    by_cases hclose : distance index < threshold
    · exact (hnear index hindex hclose).trans
        (le_add_of_nonneg_right (mul_nonneg (div_nonneg hglobalBound hthresholdSq.le)
          (sq_nonneg _)))
    · have hfar : threshold ≤ distance index := le_of_not_gt hclose
      have hsquare : threshold ^ 2 ≤ distance index ^ 2 := by
        nlinarith [sq_nonneg (distance index - threshold)]
      have hscale : globalBound ≤ globalBound / threshold ^ 2 * distance index ^ 2 := by
        have := mul_le_mul_of_nonneg_left hsquare
          (div_nonneg hglobalBound hthresholdSq.le)
        simpa only [div_mul_cancel₀ _ hthresholdSq.ne'] using this
      exact (hglobal index hindex).trans (hscale.trans (le_add_of_nonneg_left hnearBound))
  calc
    _ ≤ ∑ index ∈ indices,
        weight index * (nearBound + globalBound / threshold ^ 2 * distance index ^ 2) :=
      Finset.sum_le_sum fun index hindex ↦
        mul_le_mul_of_nonneg_left (hpointwise index hindex) (hweight index hindex)
    _ = nearBound + globalBound / threshold ^ 2 *
        ∑ index ∈ indices, weight index * distance index ^ 2 := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
        mul_left_comm (weight _) (globalBound / threshold ^ 2), ← Finset.mul_sum, hmass,
        one_mul]
    _ ≤ nearBound + globalBound / threshold ^ 2 * momentBound := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hmoment (div_nonneg hglobalBound hthresholdSq.le))
    _ = _ := by ring

/-- The corresponding near/far estimate for the error of an actual weighted average. -/
theorem abs_sum_weight_mul_sub_target_le_of_near_and_sq_moment {Index : Type*}
    (indices : Finset Index) (weight distance sample : Index → ℝ)
    (target nearBound globalBound momentBound threshold : ℝ)
    (hweight : ∀ index ∈ indices, 0 ≤ weight index)
    (hmass : ∑ index ∈ indices, weight index = 1)
    (hnearBound : 0 ≤ nearBound) (hthreshold : 0 < threshold)
    (hglobal : ∀ index ∈ indices, |sample index - target| ≤ globalBound)
    (hnear : ∀ index ∈ indices, distance index < threshold →
      |sample index - target| ≤ nearBound)
    (hmoment : ∑ index ∈ indices, weight index * distance index ^ 2 ≤ momentBound) :
    |(∑ index ∈ indices, weight index * sample index) - target| ≤
      nearBound + globalBound * momentBound / threshold ^ 2 := by
  calc
    _ = |∑ index ∈ indices, weight index * (sample index - target)| := by
      congr 1
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, one_mul]
    _ ≤ ∑ index ∈ indices, |weight index * (sample index - target)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ index ∈ indices, weight index * |sample index - target| := by
      apply Finset.sum_congr rfl
      intro index hindex
      rw [abs_mul, abs_of_nonneg (hweight index hindex)]
    _ ≤ _ := sum_weight_mul_abs_le_of_near_and_sq_moment indices weight distance
      (fun index ↦ sample index - target) nearBound globalBound momentBound threshold
      hweight hmass hnearBound hthreshold hglobal hnear hmoment

end Math
