import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! # A quantitative inverse for a linear-plus-square-root error bound -/

namespace Math

/-- On a bounded positive-gap scale, a linear-plus-square-root comparison
forces the displayed quadratic lower bound on the source error. -/
theorem gap_sq_div_le_of_linear_sqrt_bound
    (scale bound gap error : ℝ)
    (hscale : scale ≤ bound) (hgap : 0 < gap) (hgapBound : gap ≤ 2 * bound)
    (herror : 0 ≤ error)
    (hcomparison : gap ≤ (scale + 2 * bound) * error + 2 * bound * Real.sqrt error) :
    gap ^ 2 / (16 * bound ^ 2) ≤ error := by
  have hbound : 0 < bound := by linarith
  by_contra hnot
  have hsmall : error < gap ^ 2 / (16 * bound ^ 2) := lt_of_not_ge hnot
  have hthreshold : gap ^ 2 / (16 * bound ^ 2) ≤ gap / (8 * bound) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_nonneg (by positivity : 0 ≤ 8 * bound * gap)
      (sub_nonneg.mpr hgapBound)]
  have hlinear : 8 * bound * error < gap := by
    have h := (lt_div_iff₀ (by positivity : 0 < 8 * bound)).mp (hsmall.trans_le hthreshold)
    nlinarith
  have hthresholdSq : gap ^ 2 / (16 * bound ^ 2) = (gap / (4 * bound)) ^ 2 := by
    field_simp
    ring
  have hsqrt : Real.sqrt error < gap / (4 * bound) := by
    apply (Real.sqrt_lt herror (by positivity)).mpr
    rwa [← hthresholdSq]
  have hsqrt' := (lt_div_iff₀ (by positivity : 0 < 4 * bound)).mp hsqrt
  have hscale' := mul_le_mul_of_nonneg_right hscale herror
  nlinarith

end Math
