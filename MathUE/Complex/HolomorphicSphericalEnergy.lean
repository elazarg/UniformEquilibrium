module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.Topology.Algebra.Module.Determinant

/-! # Actual spherical-density energy in a complex-valued chart

This supplies the analytic area calculation used in Milnor §§15.1–15.2:
https://legacy-www.math.harvard.edu/archive/118r_spring_05/docs/milnor.pdf

The real Jacobian is derived from the complex derivative. Injectivity and the
weighted change-of-variables theorem identify the energy with the actual image
density integral. Integrability of the density supplies finiteness; its exact
total value is not needed. This is a complex-valued chart theorem, not a theorem
about a chart containing infinity, spherical curve length, or boundary extension.
-/

public section

noncomputable section

namespace Math.ComplexAnalysis

open MeasureTheory Set
open scoped ENNReal

@[expose] def sphericalDensity (z : ℂ) : ℝ := 4 / (1 + ‖z‖ ^ 2) ^ 2

@[expose] def sphericalDerivativeSpeed (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  2 * ‖deriv f z‖ / (1 + ‖f z‖ ^ 2)

theorem sphericalDensity_nonneg (z : ℂ) : 0 ≤ sphericalDensity z := by
  unfold sphericalDensity
  positivity

theorem integrable_sphericalDensity : Integrable sphericalDensity := by
  have h := (integrable_rpow_neg_one_add_norm_sq
    (E := ℂ) (μ := volume) (r := 4)
    (by norm_num [Complex.finrank_real_complex])).const_mul (4 : ℝ)
  convert h using 1
  funext z
  norm_num [sphericalDensity, Real.rpow_neg, Real.rpow_two, div_eq_mul_inv]

theorem lintegral_sphericalDensity_lt_top :
    (∫⁻ z : ℂ, ENNReal.ofReal (sphericalDensity z)) < ∞ := by
  rw [← ofReal_integral_eq_lintegral_ofReal integrable_sphericalDensity
    (Filter.Eventually.of_forall sphericalDensity_nonneg)]
  exact ENNReal.ofReal_lt_top

/-- The determinant is computed, not supplied as an extra derivative hypothesis. -/
theorem det_complex_derivative_as_real (value : ℂ) :
    ((ContinuousLinearMap.toSpanSingleton ℂ value).restrictScalars ℝ).det =
      ‖value‖ ^ 2 := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]

theorem sphericalDerivativeSpeed_sq (f : ℂ → ℂ) (z : ℂ) :
    sphericalDerivativeSpeed f z ^ 2 = ‖deriv f z‖ ^ 2 * sphericalDensity (f z) := by
  unfold sphericalDerivativeSpeed sphericalDensity
  have hdenom : 1 + ‖f z‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp [hdenom]
  ring

/-- Exact weighted image formula on every measurable part of the open domain. -/
theorem spherical_energy_eq_image_integral
    {f : ℂ → ℂ} {U S : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    (hS : MeasurableSet S) (hSU : S ⊆ U) :
    (∫⁻ z in S, ENNReal.ofReal (sphericalDerivativeSpeed f z ^ 2)) =
      ∫⁻ w in f '' S, ENNReal.ofReal (sphericalDensity w) := by
  have hderiv (z : ℂ) (hz : z ∈ S) : HasFDerivWithinAt f
      ((ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)).restrictScalars ℝ) S z :=
    ((hf z (hSU hz)).differentiableAt (hU.mem_nhds (hSU hz))).hasDerivAt.hasFDerivAt
      |>.restrictScalars ℝ |>.hasFDerivWithinAt
  have hchange := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
    hderiv (hinj.mono hSU) (fun w => ENNReal.ofReal (sphericalDensity w))
  rw [hchange]
  apply setLIntegral_congr_fun hS
  intro z _
  dsimp only
  rw [det_complex_derivative_as_real, abs_of_nonneg (sq_nonneg _),
    sphericalDerivativeSpeed_sq, ENNReal.ofReal_mul (sq_nonneg _)]

theorem spherical_energy_le_total_density
    {f : ℂ → ℂ} {U S : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    (hS : MeasurableSet S) (hSU : S ⊆ U) :
    (∫⁻ z in S, ENNReal.ofReal (sphericalDerivativeSpeed f z ^ 2)) ≤
      ∫⁻ w : ℂ, ENNReal.ofReal (sphericalDensity w) := by
  rw [spherical_energy_eq_image_integral hU hf hinj hS hSU]
  exact setLIntegral_le_lintegral _ _

theorem spherical_energy_lt_top
    {f : ℂ → ℂ} {U S : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    (hS : MeasurableSet S) (hSU : S ⊆ U) :
    (∫⁻ z in S, ENNReal.ofReal (sphericalDerivativeSpeed f z ^ 2)) < ∞ :=
  (spherical_energy_le_total_density hU hf hinj hS hSU).trans_lt
    lintegral_sphericalDensity_lt_top

end Math.ComplexAnalysis
