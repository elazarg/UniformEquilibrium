/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.ProbabilityMassFunction
import Mathlib.Probability.Distributions.Uniform

/-!
# Boolean probability mass functions

Elementary rigidity facts for probability mass functions on `Bool`.
-/

namespace Math.ProbabilityMassFunction

open Math.Probability

/-- Expectation of a real-valued function under the uniform Boolean PMF. -/
@[simp] theorem expect_uniformOfFintype_bool (f : Bool → ℝ) :
    expect (PMF.uniformOfFintype Bool) f = (f false + f true) / 2 := by
  rw [expect_eq_sum, Fintype.sum_bool]
  norm_num [PMF.uniformOfFintype_apply]
  ring

/-- A Boolean probability mass function with zero real mass at `true` is the
Dirac mass at `false`. -/
theorem eq_pure_false_of_apply_true_toReal_eq_zero
    (marginal : PMF Bool) (htrueReal : (marginal true).toReal = 0) :
    marginal = PMF.pure false := by
  apply eq_of_forall_toReal_eq
  intro action
  have hsum := Math.Probability.pmf_toReal_sum_one marginal
  rw [Fintype.sum_bool, htrueReal, zero_add] at hsum
  cases action
  · simpa [PMF.pure_apply] using hsum
  · simpa [PMF.pure_apply] using htrueReal

end Math.ProbabilityMassFunction
