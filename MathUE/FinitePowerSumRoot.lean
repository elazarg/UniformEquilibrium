/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Roots of finite power sums

An elementary intermediate-value interface for finite polynomials presented
as indexed power sums.  It is useful when the constant coefficient is
negative and the sum of all coefficients is positive.
-/

noncomputable section

namespace Math

/-- A finite power sum with coefficients indexed from zero. -/
def finitePowerSum {n : ℕ} (coefficient : Fin (n + 1) → ℝ) (x : ℝ) : ℝ :=
  ∑ i, coefficient i * x ^ i.val

@[simp] theorem finitePowerSum_zero {n : ℕ} (coefficient : Fin (n + 1) → ℝ) :
    finitePowerSum coefficient 0 = coefficient 0 := by
  rw [finitePowerSum, Fin.sum_univ_succ]
  simp

@[simp] theorem finitePowerSum_one {n : ℕ} (coefficient : Fin (n + 1) → ℝ) :
    finitePowerSum coefficient 1 = ∑ i, coefficient i := by
  simp [finitePowerSum]

theorem continuous_finitePowerSum {n : ℕ} (coefficient : Fin (n + 1) → ℝ) :
    Continuous (finitePowerSum coefficient) := by
  unfold finitePowerSum
  fun_prop

/-- A finite power sum whose constant coefficient is negative and whose total
coefficient sum is positive has a root strictly between zero and one. -/
theorem exists_finitePowerSum_root_mem_Ioo {n : ℕ}
    (coefficient : Fin (n + 1) → ℝ)
    (hconstant : coefficient 0 < 0)
    (htotal : 0 < ∑ i, coefficient i) :
    ∃ s ∈ Set.Ioo (0 : ℝ) 1, finitePowerSum coefficient s = 0 := by
  apply intermediate_value_Ioo zero_le_one
    (continuous_finitePowerSum coefficient).continuousOn
  simpa using And.intro hconstant htotal

end Math
