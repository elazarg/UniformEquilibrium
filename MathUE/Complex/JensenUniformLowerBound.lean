module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Complex.CauchyIntegral

/-! # A uniform lower bound for logarithmic circle averages

This is the Jensen lower-bound step in Milnor, *Dynamics in One Complex
Variable*, Appendix A.3 (the radial uniqueness theorem):
https://legacy-www.math.harvard.edu/archive/118r_spring_05/docs/milnor.pdf

We retain the center order and leading coefficient, so the center may be a zero.
The bound is explicit and works throughout any positive-radius terminal annulus.
The identically-zero function also satisfies this bound under `Real.log 0 = 0`;
radial uniqueness requires a separate almost-everywhere logarithmic upper bound
for a nonzero analytic function. No boundary-limit assertion is made here.
-/

public section

namespace Math.ComplexAnalysis

open Set Metric MeromorphicOn Real

theorem center_terms_le_circleAverage_log_norm {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (closedBall c r)) :
    (divisor f (closedBall c r) c : ℝ) * Real.log r +
        Real.log ‖meromorphicTrailingCoeffAt f c‖ ≤
      circleAverage (fun z => Real.log ‖f z‖) c r := by
  have hmer : MeromorphicOn f (closedBall c |r|) := by
    simpa only [abs_of_pos hr] using hf.meromorphicOn
  have hjensen := MeromorphicOn.circleAverage_log_norm hr.ne' hmer
  rw [abs_of_pos hr] at hjensen
  rw [hjensen]
  have hsum : 0 ≤ ∑ᶠ z, (divisor f (closedBall c r) z : ℝ) *
      Real.log (r * ‖c - z‖⁻¹) := by
    apply finsum_nonneg
    intro z
    by_cases hz : z ∈ closedBall c r
    · by_cases heq : z = c
      · simp [heq]
      · have hn : 0 < ‖c - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm heq))
        have hnorm : ‖c - z‖ ≤ r := by
          simpa only [mem_closedBall, dist_eq_norm'] using hz
        apply mul_nonneg (by exact_mod_cast hf.divisor_nonneg z)
        rw [← div_eq_mul_inv]
        exact Real.log_nonneg ((one_le_div hn).mpr hnorm)
    · simp only [(divisor f (closedBall c r)).apply_eq_zero_of_notMem hz,
        Int.cast_zero, zero_mul, le_refl]
  linarith

theorem uniform_lower_bound_circleAverage_log_norm {f : ℂ → ℂ} {c : ℂ}
    {inner outer : ℝ} (hinner : 0 < inner)
    (hf : DifferentiableOn ℂ f (ball c outer))
    {r : ℝ} (hir : inner ≤ r) (hro : r < outer) :
    ((meromorphicOrderAt f c).untop₀ : ℝ) * Real.log inner +
        Real.log ‖meromorphicTrailingCoeffAt f c‖ ≤
      circleAverage (fun z => Real.log ‖f z‖) c r := by
  have hr : 0 < r := hinner.trans_le hir
  have har : AnalyticOnNhd ℂ f (closedBall c r) :=
    (hf.analyticOnNhd isOpen_ball).mono (closedBall_subset_ball hro)
  have horder : divisor f (closedBall c r) c = (meromorphicOrderAt f c).untop₀ :=
    har.meromorphicOn.divisor_apply (mem_closedBall_self hr.le)
  have hnonneg : (0 : ℝ) ≤ ((meromorphicOrderAt f c).untop₀ : ℝ) := by
    rw [← horder]
    exact_mod_cast har.divisor_nonneg c
  have hlog : Real.log inner ≤ Real.log r := Real.log_le_log hinner hir
  have hbound := center_terms_le_circleAverage_log_norm hr har
  rw [horder] at hbound
  have hmul := mul_le_mul_of_nonneg_left hlog hnonneg
  linarith

end Math.ComplexAnalysis
