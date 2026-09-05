import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # Equality of pushforward laws from equality on support -/

namespace Math.Probability

/-- Two maps that agree on the support of a PMF have the same pushforward. -/
theorem pmf_map_eq_of_eq_on_support {α β : Type*}
    (law : PMF α) (first second : α → β)
    (heq : ∀ source, source ∈ law.support → first source = second source) :
    law.map first = law.map second := by
  classical
  apply PMF.ext
  intro outcome
  simp only [PMF.map_apply]
  apply tsum_congr
  intro source
  by_cases hzero : law source = 0
  · simp [hzero]
  · rw [heq source hzero]

end Math.Probability
