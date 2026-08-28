/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Tail averages and telescoping forward differences

This file records two elementary real-analysis tools for summable nonnegative
weights.  A vanishing error remains vanishing after normalization by every
positive tail of the weights, and a convergent scalar sequence is the sum of
its summable future forward increments.
-/

noncomputable section

namespace Math

open Filter

/-- Multiplying a summable nonnegative weight by a scalar sequence tending to
zero preserves summability. -/
theorem summable_weight_mul_of_nonneg_of_tendsto_zero
    (weight error : ℕ → ℝ)
    (hweight0 : ∀ time, 0 ≤ weight time)
    (hweight : Summable weight)
    (herror : Tendsto error atTop (nhds 0)) :
    Summable (fun time ↦ weight time * error time) := by
  obtain ⟨bound, hbound⟩ :=
    (Metric.isBounded_range_of_tendsto error herror).exists_norm_le
  have hbound0 : 0 ≤ bound :=
    (norm_nonneg (error 0)).trans (hbound (error 0) ⟨0, rfl⟩)
  apply Summable.of_norm_bounded (hweight.mul_left bound)
  intro time
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hweight0 time)]
  calc
    weight time * |error time| ≤ weight time * bound :=
      mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using
          hbound (error time) ⟨time, rfl⟩)
        (hweight0 time)
    _ = bound * weight time := mul_comm _ _

/-- A vanishing scalar error remains vanishing after averaging against every
positive summable tail of nonnegative weights. -/
theorem weightedTailAverage_tendsto_zero
    (weight error : ℕ → ℝ)
    (hweight0 : ∀ time, 0 ≤ weight time)
    (hweight : Summable weight)
    (htailPos : ∀ start, 0 < ∑' offset, weight (start + offset))
    (herror : Tendsto error atTop (nhds 0)) :
    Tendsto (fun start ↦
      (∑' offset, weight (start + offset) * error (start + offset)) /
        ∑' offset, weight (start + offset)) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop] at herror ⊢
  intro tolerance htolerance
  have hhalf : 0 < tolerance / 2 := half_pos htolerance
  obtain ⟨cutoff, hcutoff⟩ := herror (tolerance / 2) hhalf
  refine ⟨cutoff, fun start hstart ↦ ?_⟩
  have hshift : Summable (fun offset ↦ weight (start + offset)) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff start).2 hweight
  have hpoint : ∀ offset,
      |weight (start + offset) * error (start + offset)| ≤
        (tolerance / 2) * weight (start + offset) := by
    intro offset
    have hindex : cutoff ≤ start + offset := hstart.trans (Nat.le_add_right start offset)
    have hsmall := hcutoff (start + offset) hindex
    rw [Real.dist_eq, sub_zero] at hsmall
    rw [abs_mul, abs_of_nonneg (hweight0 _)]
    nlinarith [hweight0 (start + offset)]
  have hmajor : Summable (fun offset ↦
      (tolerance / 2) * weight (start + offset)) :=
    hshift.mul_left _
  have hweightedNorm : Summable (fun offset ↦
      |weight (start + offset) * error (start + offset)|) :=
    hmajor.of_nonneg_of_le (fun _ ↦ abs_nonneg _) hpoint
  have hnorm :
      |∑' offset, weight (start + offset) * error (start + offset)| ≤
        ∑' offset,
          |weight (start + offset) * error (start + offset)| := by
    simpa only [Real.norm_eq_abs] using
      (norm_tsum_le_tsum_norm
        (f := fun offset ↦ weight (start + offset) * error (start + offset))
        (by simpa only [Real.norm_eq_abs] using hweightedNorm))
  have habsSum :
      (∑' offset,
        |weight (start + offset) * error (start + offset)|) ≤
          (tolerance / 2) * ∑' offset, weight (start + offset) := by
    calc
      (∑' offset,
          |weight (start + offset) * error (start + offset)|) ≤
          ∑' offset, (tolerance / 2) * weight (start + offset) :=
        hweightedNorm.tsum_le_tsum hpoint hmajor
      _ = (tolerance / 2) * ∑' offset, weight (start + offset) := by
        rw [tsum_mul_left]
  have hratio :
      |(∑' offset, weight (start + offset) * error (start + offset)) /
          ∑' offset, weight (start + offset)| ≤ tolerance / 2 := by
    rw [abs_div, abs_of_pos (htailPos start)]
    exact (div_le_iff₀ (htailPos start)).2 (hnorm.trans habsSum)
  rw [Real.dist_eq, sub_zero]
  exact hratio.trans_lt (half_lt_self htolerance)

/-- A convergent scalar sequence is the sum of all its summable future
forward increments. -/
theorem hasSum_forwardDifference
    (value : ℕ → ℝ) (limit : ℝ)
    (hvalue : Tendsto value atTop (nhds limit)) (start : ℕ)
    (hincrements : Summable (fun offset ↦
      value (start + offset + 1) - value (start + offset))) :
    HasSum (fun offset ↦
      value (start + offset + 1) - value (start + offset))
      (limit - value start) := by
  apply (hincrements.hasSum_iff_tendsto_nat).2
  have hshift := hvalue.comp (tendsto_add_atTop_nat start)
  have hsub := hshift.sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ value start) atTop
      (nhds (value start)))
  convert hsub using 1
  ext horizon
  have htelescope := Finset.sum_range_sub'
    (fun offset ↦ value (start + offset)) horizon
  have hneg := congrArg Neg.neg htelescope
  simpa [Finset.sum_neg_distrib, Nat.add_assoc, Nat.add_comm] using hneg

end Math
