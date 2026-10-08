import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Scalar likelihood bounds for signed conditioning

The same two-sided bound applies to finite laws and measurable probability laws.
It uses only a positive event mass at most one and the closed signed radius.
-/

namespace Math.Probability

theorem signedConditioningLikelihood_bounds (eventMass : ℝ)
    (hmass : 0 < eventMass) (hmassOne : eventMass ≤ 1)
    (parameter : ℝ) (hparameter : |parameter| ≤ min (1 / 2 : ℝ) (eventMass / 2))
    (event : Prop) [Decidable event] :
    (1 / 2 : ℝ) ≤ (1 - parameter) + (if event then parameter / eventMass else 0) ∧
      (1 - parameter) + (if event then parameter / eventMass else 0) ≤ 3 / 2 := by
  have hhalf : |parameter| ≤ (1 / 2 : ℝ) := hparameter.trans (min_le_left _ _)
  have hehalf : |parameter| ≤ eventMass / 2 := hparameter.trans (min_le_right _ _)
  by_cases hevent : event
  · rw [ite_eq_left hevent]
    have hcoefficient : 0 ≤ 1 / eventMass - 1 := by
      apply sub_nonneg.mpr
      apply (le_div_iff₀ hmass).mpr
      simpa only [one_mul] using hmassOne
    have hcoefficientUpper : 1 / eventMass - 1 ≤ 1 / eventMass := by linarith
    have hproduct : |parameter * (1 / eventMass - 1)| ≤ (1 / 2 : ℝ) := by
      calc
        |parameter * (1 / eventMass - 1)| =
            |parameter| * (1 / eventMass - 1) := by
          rw [abs_mul, abs_of_nonneg hcoefficient]
        _ ≤ |parameter| * (1 / eventMass) :=
          mul_le_mul_of_nonneg_left hcoefficientUpper (abs_nonneg parameter)
        _ = |parameter| / eventMass := by ring
        _ ≤ 1 / 2 := (div_le_iff₀ hmass).mpr (by linarith)
    have hidentity : (1 - parameter) + parameter / eventMass =
        1 + parameter * (1 / eventMass - 1) := by ring
    rw [hidentity]
    constructor <;> linarith [(abs_le.mp hproduct).1, (abs_le.mp hproduct).2]
  · rw [ite_eq_right hevent, add_zero]
    constructor <;> linarith [(abs_le.mp hhalf).1, (abs_le.mp hhalf).2]

end Math.Probability
