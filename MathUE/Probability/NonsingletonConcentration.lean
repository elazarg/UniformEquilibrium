/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.MeanInequalities

/-!
# Sharp concentration from a finite root-mass budget

This file isolates the game-independent real-power calculation behind
nonsingleton stopping-clock concentration.  If the sum of the `k`-th roots
of nonnegative masses is at most one, some mass is at least the total mass
to the exponent `k / (k - 1)`.
-/

open scoped BigOperators

namespace Math.Probability

/-- A finite nonnegative family with `k`-th-root budget at most one has an
atom of size at least `total ^ (k / (k - 1))`. -/
theorem finite_exists_rpow_ratio_le_of_sum_root_le_one
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (mass : Index → ℝ) (k : ℝ)
    (hindices : indices.Nonempty) (hk : 1 < k)
    (hmass : ∀ index ∈ indices, 0 ≤ mass index)
    (hroot : ∑ index ∈ indices, mass index ^ (1 / k) ≤ 1) :
    ∃ peak ∈ indices,
      (∑ index ∈ indices, mass index) ^ (k / (k - 1)) ≤ mass peak := by
  obtain ⟨peak, hpeak, hmax⟩ :=
    Finset.exists_max_image indices mass hindices
  refine ⟨peak, hpeak, ?_⟩
  have hk0 : 0 < k := lt_trans zero_lt_one hk
  have hkne : k ≠ 0 := hk0.ne'
  have hk1 : 0 < k - 1 := sub_pos.mpr hk
  have hq : 0 < (k - 1) / k := div_pos hk1 hk0
  have hqnonneg : 0 ≤ (k - 1) / k := hq.le
  have hpeak_nonneg : 0 ≤ mass peak := hmass peak hpeak
  have hsum_nonneg : 0 ≤ ∑ index ∈ indices, mass index :=
    Finset.sum_nonneg hmass
  have hfactor : ∀ index ∈ indices,
      mass index = mass index ^ (1 / k) *
        mass index ^ ((k - 1) / k) := by
    intro index hindex
    have hm := hmass index hindex
    rw [← Real.rpow_add_of_nonneg hm (by positivity) hqnonneg]
    convert (Real.rpow_one (mass index)).symm using 2
    field_simp
    ring
  have hsum : (∑ index ∈ indices, mass index) ≤
      mass peak ^ ((k - 1) / k) := by
    calc
      (∑ index ∈ indices, mass index) =
          ∑ index ∈ indices,
            mass index ^ (1 / k) *
              mass index ^ ((k - 1) / k) := by
        apply Finset.sum_congr rfl
        exact hfactor
      _ ≤ ∑ index ∈ indices,
          mass index ^ (1 / k) *
            mass peak ^ ((k - 1) / k) := by
        apply Finset.sum_le_sum
        intro index hindex
        apply mul_le_mul_of_nonneg_left
        · exact Real.rpow_le_rpow (hmass index hindex)
            (hmax index hindex) hqnonneg
        · exact Real.rpow_nonneg (hmass index hindex) _
      _ = (∑ index ∈ indices, mass index ^ (1 / k)) *
          mass peak ^ ((k - 1) / k) := by
        rw [Finset.sum_mul]
      _ ≤ mass peak ^ ((k - 1) / k) := by
        have hp := Real.rpow_nonneg hpeak_nonneg ((k - 1) / k)
        nlinarith
  have hinv : 0 < k / (k - 1) := div_pos hk0 hk1
  have hraised := Real.rpow_le_rpow hsum_nonneg hsum hinv.le
  calc
    (∑ index ∈ indices, mass index) ^ (k / (k - 1)) ≤
        (mass peak ^ ((k - 1) / k)) ^ (k / (k - 1)) := hraised
    _ = mass peak := by
      rw [← Real.rpow_mul hpeak_nonneg]
      convert Real.rpow_one (mass peak) using 2
      field_simp

end Math.Probability
