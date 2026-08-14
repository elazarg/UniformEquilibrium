import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace Math

open Function

/-- If a square preconditioned derivative is within operator norm one of the
identity, then the preconditioner is injective.  Finite dimensionality is used
only after proving `A.comp J` injective: it turns this into surjectivity, hence
surjectivity of `A`, and then injectivity of `A`. -/
theorem ContinuousLinearMap.injective_of_norm_one_sub_comp_lt_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A J : E →L[ℝ] E) (hnear : ‖1 - A.comp J‖ < 1) :
    Injective A := by
  have hcompInjective : Injective (A.comp J) := by
    intro first second heq
    have hzero : (A.comp J) (first - second) = 0 := by
      rw [map_sub, heq, sub_self]
    have hfixed : (1 - A.comp J) (first - second) = first - second := by
      change (first - second) - (A.comp J) (first - second) = first - second
      rw [hzero, sub_zero]
    have hopNorm := (1 - A.comp J).le_opNorm (first - second)
    rw [hfixed] at hopNorm
    by_cases hdifference : first - second = 0
    · exact sub_eq_zero.mp hdifference
    · have hnormPositive : 0 < ‖first - second‖ :=
        norm_pos_iff.mpr hdifference
      have hstrict : ‖1 - A.comp J‖ * ‖first - second‖ <
          ‖first - second‖ := by
        exact (mul_lt_iff_lt_one_left hnormPositive).mpr hnear
      exact False.elim (not_lt_of_ge hopNorm hstrict)
  have hcompSurjective : Surjective (A.comp J) :=
    LinearMap.injective_iff_surjective.mp hcompInjective
  have hASurjective : Surjective A := by
    intro target
    obtain ⟨source, hsource⟩ := hcompSurjective target
    change A (J source) = target at hsource
    exact ⟨J source, hsource⟩
  exact LinearMap.injective_iff_surjective.mpr hASurjective

end Math
