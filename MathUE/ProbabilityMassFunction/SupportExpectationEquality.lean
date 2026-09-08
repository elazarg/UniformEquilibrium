import MathUE.ProbabilityMassFunction

/-!
# Equality in finite-PMF expectation comparison

Only supported values are ordered. Equality of the expectations then forces
equality at every supported point, including when some atoms have zero mass.
-/

namespace Math.ProbabilityMassFunction

/-- Equality in a supportwise finite expectation comparison is pointwise on the support. -/
theorem expect_eq_iff_eq_on_support_of_le_on_support
    {Ω : Type*} [Finite Ω] (mass : PMF Ω) (lower upper : Ω → ℝ)
    (hle : ∀ point ∈ mass.support, lower point ≤ upper point) :
    Math.Probability.expect mass lower = Math.Probability.expect mass upper ↔
      ∀ point ∈ mass.support, lower point = upper point := by
  classical
  letI : Fintype Ω := Fintype.ofFinite Ω
  constructor
  · intro hequal
    have hnonneg (point : Ω) :
        0 ≤ (mass point).toReal * (upper point - lower point) := by
      by_cases hzero : mass point = 0
      · simp [hzero]
      · exact mul_nonneg ENNReal.toReal_nonneg
          (sub_nonneg.mpr (hle point ((PMF.mem_support_iff mass point).mpr hzero)))
    have hsum : ∑ point, (mass point).toReal * (upper point - lower point) = 0 := by
      rw [Math.Probability.expect_eq_sum, Math.Probability.expect_eq_sum] at hequal
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, hequal, sub_self]
    intro point hsupport
    have hterm : (mass point).toReal * (upper point - lower point) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun index _ => hnonneg index)).mp hsum
        point (Finset.mem_univ point)
    have hmass : 0 < (mass point).toReal :=
      ENNReal.toReal_pos ((PMF.mem_support_iff mass point).mp hsupport)
        (mass.apply_ne_top point)
    have hgap : upper point - lower point = 0 :=
      (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hmass)
    exact (sub_eq_zero.mp hgap).symm
  · exact expect_congr_on_support mass lower upper

/-- A supported upper bound is saturated in expectation exactly when every supported value is. -/
theorem expect_eq_const_iff_eq_on_support_of_le_on_support
    {Ω : Type*} [Finite Ω] (mass : PMF Ω) (value : Ω → ℝ) (bound : ℝ)
    (hle : ∀ point ∈ mass.support, value point ≤ bound) :
    Math.Probability.expect mass value = bound ↔
      ∀ point ∈ mass.support, value point = bound := by
  simpa only [Math.Probability.expect_const] using
    expect_eq_iff_eq_on_support_of_le_on_support mass value (fun _ => bound) hle

/-- A supported nonnegative observable has zero expectation exactly when it vanishes there. -/
theorem expect_eq_zero_iff_eq_zero_on_support_of_nonneg_on_support
    {Ω : Type*} [Finite Ω] (mass : PMF Ω) (value : Ω → ℝ)
    (hnonneg : ∀ point ∈ mass.support, 0 ≤ value point) :
    Math.Probability.expect mass value = 0 ↔
      ∀ point ∈ mass.support, value point = 0 := by
  have h := expect_eq_iff_eq_on_support_of_le_on_support
    mass (fun _ => 0) value hnonneg
  rw [Math.Probability.expect_const] at h
  constructor
  · intro hequal point hsupport
    exact (h.mp hequal.symm point hsupport).symm
  · intro hzero
    exact (h.mpr (fun point hsupport => (hzero point hsupport).symm)).symm

end Math.ProbabilityMassFunction
