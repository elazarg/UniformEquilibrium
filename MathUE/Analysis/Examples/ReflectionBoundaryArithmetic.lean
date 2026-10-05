import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

/-! # Scalar boundaries for adaptive box reflection

These are exact arithmetic fixtures, not counterexamples to any theorem.
They isolate the adaptive cap and nonnegative-singleton requirements.
-/

namespace Math.ReflectionBoundaryArithmetic

theorem allowed_reflection_endpoint : (2 : ℝ) * 0 - 3 = -3 := by norm_num

theorem fixed_cap_reflection_outside :
    (2 : ℝ) * 3 - 1 / 2 = 11 / 2 ∧ (3 : ℝ) < 11 / 2 := by norm_num

theorem signed_singleton_reflection_outside :
    (2 : ℝ) * (-1) - 3 = -5 ∧ (-5 : ℝ) < -3 := by norm_num

theorem unsigned_multiaffine_partial_positive :
    (((2 / 3 : ℝ) * 1 - (1 - 2 / 3) * 1 - (2 / 3) * (1 / 10)) / 6) = 2 / 45 ∧
      (0 : ℝ) < 2 / 45 := by norm_num

end Math.ReflectionBoundaryArithmetic
