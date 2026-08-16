/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Real.Basic

/-!
# Strict upper bounds for finite products

A finite product is strictly below one when one displayed factor is strictly
below one and every other factor lies in `[0, 1]`. No lower bound is needed on
the strict witness itself. The statement allows zero factors, which is
essential at closed probability boundaries.
-/

namespace Math.Finset

open scoped BigOperators

/-- A product is strictly below one when one factor is strictly below one and
all remaining factors lie in `[0, 1]`. -/
theorem prod_lt_one_of_mem
    {Index : Type*}
    (indices : Finset Index) (factor : Index → ℝ)
    (witness : Index) (hwitness : witness ∈ indices)
    (hfactor_nonneg : ∀ index ∈ indices, index ≠ witness → 0 ≤ factor index)
    (hfactor_le_one : ∀ index ∈ indices, index ≠ witness → factor index ≤ 1)
    (hwitness_lt_one : factor witness < 1) :
    (∏ index ∈ indices, factor index) < 1 := by
  classical
  have hrest_nonneg :
      0 ≤ ∏ index ∈ indices.erase witness, factor index := by
    apply Finset.prod_nonneg
    intro index hindex
    exact hfactor_nonneg index (Finset.mem_of_mem_erase hindex)
      (Finset.ne_of_mem_erase hindex)
  have hrest_le_one :
      (∏ index ∈ indices.erase witness, factor index) ≤ 1 := by
    apply Finset.prod_le_one
    · intro index hindex
      exact hfactor_nonneg index (Finset.mem_of_mem_erase hindex)
        (Finset.ne_of_mem_erase hindex)
    · intro index hindex
      exact hfactor_le_one index (Finset.mem_of_mem_erase hindex)
        (Finset.ne_of_mem_erase hindex)
  have hmul :
      factor witness * (∏ index ∈ indices.erase witness, factor index) < 1 := by
    by_cases hwitness_nonneg : 0 ≤ factor witness
    · calc
        factor witness * (∏ index ∈ indices.erase witness, factor index) ≤
            factor witness * 1 :=
          mul_le_mul_of_nonneg_left hrest_le_one hwitness_nonneg
        _ < 1 := by simpa using hwitness_lt_one
    · have hwitness_nonpos : factor witness ≤ 0 := le_of_lt (lt_of_not_ge hwitness_nonneg)
      have hproduct_nonpos :
          factor witness * (∏ index ∈ indices.erase witness, factor index) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hwitness_nonpos hrest_nonneg
      exact hproduct_nonpos.trans_lt zero_lt_one
  have hsplit := Finset.mul_prod_erase indices factor hwitness
  exact hsplit.symm ▸ hmul

end Math.Finset
