module

public import MathUE.Complex.JensenUniformLowerBound
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Radial uniqueness for bounded holomorphic functions

Known proof: Milnor, *Dynamics in One Complex Variable*, Appendix A.3,
https://legacy-www.math.harvard.edu/archive/118r_spring_05/docs/milnor.pdf.
We use Fatou's equivalent integral formulation of the measured-small-set step.

The radii may be any sequence in a terminal annulus: convergence of the radii
is not used. Vanishing along this sequence on a positive-measure set of angles
forces the analytic function to vanish. In particular the result applies to
radial limits at the boundary. Circle zeros are removed almost everywhere
before logarithmic divergence is used; `Real.log 0` is never treated as minus
infinity. This is not a boundary-extension or Jordan-curve theorem.
-/

public section

namespace Math.ComplexAnalysis

open Set Filter Metric Complex Real MeasureTheory MeromorphicOn
open scoped _root_.Topology ENNReal

theorem eqOn_zero_of_radial_sequence_zero_of_norm_le_one
    {f : ℂ → ℂ} {c : ℂ} {inner outer : ℝ} {radii : ℕ → ℝ}
    (hinner : 0 < inner) (hradii : ∀ n, inner ≤ radii n ∧ radii n < outer)
    (hf : DifferentiableOn ℂ f (ball c outer))
    (hbound : ∀ z ∈ ball c outer, ‖f z‖ ≤ 1)
    {angles : Set ℝ}
    (hpositive : (volume.restrict (Ioc 0 (2 * π))) angles ≠ 0)
    (hzero : ∀ θ ∈ angles,
      Tendsto (fun n => f (circleMap c (radii n) θ)) atTop (𝓝 0)) :
    EqOn f 0 (ball c outer) := by
  classical
  by_contra hnotzero
  let μ := volume.restrict (Ioc 0 (2 * π))
  let loss : ℕ → ℝ → ℝ := fun n θ => -Real.log ‖f (circleMap c (radii n) θ)‖
  let mass : ℕ → ℝ → ℝ≥0∞ := fun n θ => ENNReal.ofReal (loss n θ)
  have hrpos : ∀ n, 0 < radii n := fun n => hinner.trans_le (hradii n).1
  have hcircle : ∀ n θ, circleMap c (radii n) θ ∈ ball c outer := by
    intro n θ
    exact (closedBall_subset_ball (hradii n).2)
      (sphere_subset_closedBall (circleMap_mem_sphere c (hrpos n).le θ))
  have hcontinuous : ∀ n, Continuous (fun θ => f (circleMap c (radii n) θ)) := by
    intro n
    exact hf.continuousOn.comp_continuous (continuous_circleMap c (radii n)) (hcircle n)
  have hmeas : ∀ n, Measurable (mass n) := by
    intro n
    exact ENNReal.measurable_ofReal.comp
      ((Real.measurable_log.comp (hcontinuous n).norm.measurable).neg)
  have hnonneg : ∀ n θ, 0 ≤ loss n θ := by
    intro n θ
    exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) (hbound _ (hcircle n θ)))
  have hint : ∀ n, Integrable (loss n) μ := by
    intro n
    have har : AnalyticOnNhd ℂ f (closedBall c (radii n)) :=
      (hf.analyticOnNhd isOpen_ball).mono (closedBall_subset_ball (hradii n).2)
    have hmer := (har.mono sphere_subset_closedBall).meromorphicOn
    have hc := hmer.circleIntegrable_log_norm_of_nonneg (hrpos n).le
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by positivity : (0 : ℝ) ≤ 2 * π)).mp hc).neg
  let lower : ℝ := ((meromorphicOrderAt f c).untop₀ : ℝ) * Real.log inner +
    Real.log ‖meromorphicTrailingCoeffAt f c‖
  have hlower : ∀ n, lower ≤ circleAverage (fun z => Real.log ‖f z‖) c (radii n) :=
    fun n => uniform_lower_bound_circleAverage_log_norm hinner hf
      (hradii n).1 (hradii n).2
  have hintegral : ∀ n, ∫ θ, loss n θ ∂μ ≤ -(2 * π) * lower := by
    intro n
    have h := hlower n
    rw [circleAverage_def, smul_eq_mul,
      intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)] at h
    have hmul := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 * π)
    have hpi : (2 * π : ℝ) ≠ 0 := by positivity
    rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul] at hmul
    change ∫ θ, -(Real.log ‖f (circleMap c (radii n) θ)‖) ∂μ ≤ _
    rw [integral_neg]
    linarith
  have hmass : ∀ n, ∫⁻ θ, mass n θ ∂μ ≤ ENNReal.ofReal (-(2 * π) * lower) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (ae_of_all μ (hnonneg n))]
    exact ENNReal.ofReal_le_ofReal (hintegral n)
  have hfatou : ∫⁻ θ, liminf (fun n => mass n θ) atTop ∂μ ≤
      ENNReal.ofReal (-(2 * π) * lower) := by
    apply (lintegral_liminf_le hmeas).trans
    exact liminf_le_of_frequently_le' (Eventually.of_forall hmass).frequently
  have hfinite : ∀ᵐ θ ∂μ, liminf (fun n => mass n θ) atTop < ∞ :=
    ae_lt_top (Measurable.liminf hmeas)
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfatou)
  have hanalytic := hf.analyticOnNhd isOpen_ball
  have hdiscrete := (hanalytic.eqOn_zero_or_eventually_ne_zero_of_preconnected
    (convex_ball c outer).isPreconnected).resolve_left hnotzero
  have hnonzero : ∀ n, ∀ᵐ θ ∂μ, f (circleMap c (radii n) θ) ≠ 0 := by
    intro n
    have hsphere : ∀ᶠ z in codiscreteWithin (sphere c |radii n|), f z ≠ 0 := by
      apply codiscreteWithin_mono _ hdiscrete
      rw [abs_of_pos (hrpos n)]
      exact sphere_subset_closedBall.trans (closedBall_subset_ball (hradii n).2)
    exact ae_restrict_le_codiscreteWithin measurableSet_Ioc
      (codiscreteWithin_mono (subset_univ _)
        (circleMap_preimage_codiscrete (hrpos n).ne' hsphere))
  have hnotAngles : ∀ᵐ θ ∂μ, θ ∉ angles := by
    filter_upwards [hfinite, ae_all_iff.mpr hnonzero] with θ hfin hne hθ
    have hnorm : Tendsto (fun n => ‖f (circleMap c (radii n) θ)‖) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨by simpa using (hzero θ hθ).norm,
        Eventually.of_forall (fun n => norm_pos_iff.mpr (hne n))⟩
    have hlog := tendsto_neg_atTop_iff.mpr (Real.tendsto_log_nhdsGT_zero.comp hnorm)
    have htop : Tendsto (fun n => mass n θ) atTop (𝓝 ∞) :=
      ENNReal.tendsto_ofReal_atTop.comp hlog
    simp only [htop.liminf_eq, lt_self_iff_false] at hfin
  apply hpositive
  simpa only [ae_iff, Classical.not_not, Set.ofPred_mem_eq, μ] using hnotAngles

theorem eqOn_zero_of_bounded_radial_sequence_zero
    {f : ℂ → ℂ} {c : ℂ} {inner outer bound : ℝ} {radii : ℕ → ℝ}
    (hinner : 0 < inner) (hradii : ∀ n, inner ≤ radii n ∧ radii n < outer)
    (hf : DifferentiableOn ℂ f (ball c outer))
    (hbound : ∀ z ∈ ball c outer, ‖f z‖ ≤ bound)
    {angles : Set ℝ}
    (hpositive : (volume.restrict (Ioc 0 (2 * π))) angles ≠ 0)
    (hzero : ∀ θ ∈ angles,
      Tendsto (fun n => f (circleMap c (radii n) θ)) atTop (𝓝 0)) :
    EqOn f 0 (ball c outer) := by
  let scale : ℝ := max 1 bound
  have hscale : 0 < scale := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hscaleC : (scale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hscale.ne'
  have hnormalized : ∀ z ∈ ball c outer, ‖f z / (scale : ℂ)‖ ≤ 1 := by
    intro z hz
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hscale]
    exact (div_le_one hscale).mpr ((hbound z hz).trans (le_max_right _ _))
  have hlimits : ∀ θ ∈ angles,
      Tendsto (fun n => f (circleMap c (radii n) θ) / (scale : ℂ)) atTop (𝓝 0) := by
    intro θ hθ
    simpa only [zero_div] using (hzero θ hθ).div_const (scale : ℂ)
  have hvanish := eqOn_zero_of_radial_sequence_zero_of_norm_le_one
    hinner hradii (hf.div_const (scale : ℂ)) hnormalized hpositive hlimits
  intro z hz
  exact (div_eq_zero_iff.mp (hvanish hz)).resolve_right hscaleC

end Math.ComplexAnalysis
