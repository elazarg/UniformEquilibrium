/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Finite weighted selection

A positive nonnegative weighted total has a positive-weight coordinate whose
score is at least the normalized weighted score. The division-free form is
useful when the weights have already been cleared of denominators.
-/

namespace MathUE

/-- A finite nonnegative weighted sum is bounded by the total weight times
one score in the positive support. -/
theorem exists_weight_pos_and_weightedSum_le_total_mul
    {α : Type} [Fintype α] [Nonempty α]
    (weight score : α → ℝ) (total : ℝ)
    (weight_nonneg : ∀ index, 0 ≤ weight index)
    (sum_weight : ∑ index, weight index = total)
    (total_pos : 0 < total) :
    ∃ index, 0 < weight index ∧
      (∑ other, weight other * score other) ≤ total * score index := by
  classical
  let support := Finset.univ.filter fun index => 0 < weight index
  have support_nonempty : support.Nonempty := by
    by_contra hempty
    have hnonpos : ∀ index, weight index ≤ 0 := by
      intro index
      have hnotMem : index ∉ support := by
        rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
        simp
      simpa [support] using hnotMem
    have hzero : ∀ index, weight index = 0 := fun index =>
      le_antisymm (hnonpos index) (weight_nonneg index)
    have : total = 0 := by
      rw [← sum_weight]
      simp [hzero]
    linarith
  obtain ⟨index, hindex, hmax⟩ :=
    Finset.exists_max_image support score support_nonempty
  have hindex_pos : 0 < weight index :=
    (Finset.mem_filter.mp hindex).2
  refine ⟨index, hindex_pos, ?_⟩
  calc
    (∑ other, weight other * score other) ≤
        ∑ other, weight other * score index := by
      apply Finset.sum_le_sum
      intro other _
      by_cases hother : 0 < weight other
      · exact mul_le_mul_of_nonneg_left
          (hmax other (Finset.mem_filter.mpr
            ⟨Finset.mem_univ other, hother⟩)) (weight_nonneg other)
      · have hzero : weight other = 0 :=
          le_antisymm (le_of_not_gt hother) (weight_nonneg other)
        simp [hzero]
    _ = total * score index := by
      rw [← Finset.sum_mul, sum_weight]

/-- Substituting the name of the weighted sum gives the usual cleared
weighted-cell extraction statement. -/
theorem exists_weight_pos_and_total_mul_score_ge
    {α : Type} [Fintype α] [Nonempty α]
    (weight score : α → ℝ) (total weighted : ℝ)
    (weight_nonneg : ∀ index, 0 ≤ weight index)
    (sum_weight : ∑ index, weight index = total)
    (weighted_eq : ∑ index, weight index * score index = weighted)
    (total_pos : 0 < total) :
    ∃ index, 0 < weight index ∧ weighted ≤ total * score index := by
  obtain ⟨index, hweight, hbound⟩ :=
    exists_weight_pos_and_weightedSum_le_total_mul
      weight score total weight_nonneg sum_weight total_pos
  exact ⟨index, hweight, weighted_eq ▸ hbound⟩

end MathUE
