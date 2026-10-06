module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.Tactic.Module

/-! # Normalized stereographic speed and actual chordal displacement

Milnor's spherical line element is `2 |dz| / (1 + |z|²)`. The pinned
stereographic chart uses twice the usual plane coordinate; this file inserts
that factor explicitly and derives the speed from the actual derivative.
Source: Milnor, *Dynamics in One Complex Variable*, §§1 and 15,
https://legacy-www.math.harvard.edu/archive/118r_spring_05/docs/milnor.pdf

The displacement bound is an actual interval-integral theorem, not a supplied
curve-length certificate. Neither completeness nor finite dimension is needed.
Landing endpoints, infinity-chart transitions and crosscuts are separate work.
-/

public section

noncomputable section

namespace Math.NormalizedSphereChart

open Metric Set MeasureTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (pole : E) (plane : ℂ →ₗᵢ[ℝ] E)

@[expose] def chart (hpole : ‖pole‖ = 1)
    (horthogonal : ∀ z, ⟪pole, plane z⟫_ℝ = 0) (z : ℂ) : sphere (0 : E) 1 :=
  stereoInvFun hpole ⟨(2 : ℝ) • plane z, by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    simp only [inner_smul_right, horthogonal z, mul_zero]⟩

theorem coe_chart (hpole : ‖pole‖ = 1)
    (horthogonal : ∀ z, ⟪pole, plane z⟫_ℝ = 0) (z : ℂ) :
    (chart pole plane hpole horthogonal z : E) =
      pole + (2 / (1 + ‖z‖ ^ 2)) • (plane z - pole) := by
  have hden : 1 + ‖z‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hdenFour : 4 * ‖z‖ ^ 2 + 4 ≠ 0 := ne_of_gt (by positivity)
  have hfirst : (4 * ‖z‖ ^ 2 + 4)⁻¹ * (4 * 2) = 2 / (1 + ‖z‖ ^ 2) := by
    field_simp [hden, hdenFour]
    ring
  have hsecond : (4 * ‖z‖ ^ 2 + 4)⁻¹ * (4 * ‖z‖ ^ 2 - 4) =
      1 - 2 / (1 + ‖z‖ ^ 2) := by
    field_simp [hden, hdenFour]
    ring
  change (‖(2 : ℝ) • plane z‖ ^ 2 + 4)⁻¹ •
      ((4 : ℝ) • ((2 : ℝ) • plane z) + (‖(2 : ℝ) • plane z‖ ^ 2 - 4) • pole) = _
  simp only [norm_smul,
    Real.norm_eq_abs, plane.norm_map, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num, smul_add, smul_smul,
    hfirst, hsecond]
  module

@[expose] def chartDerivative (z : ℂ) : ℂ →L[ℝ] E :=
  (2 / (1 + ‖z‖ ^ 2)) • plane.toContinuousLinearMap +
    ((-4 / (1 + ‖z‖ ^ 2) ^ 2) • innerSL ℝ z).smulRight (plane z - pole)

theorem chartDerivative_apply (z h : ℂ) :
    chartDerivative pole plane z h =
      (2 / (1 + ‖z‖ ^ 2)) • plane h +
        (-4 * ⟪z, h⟫_ℝ / (1 + ‖z‖ ^ 2) ^ 2) • (plane z - pole) := by
  simp only [chartDerivative, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, LinearIsometry.coe_toContinuousLinearMap, smul_eq_mul]
  congr 1
  congr 1
  ring

theorem hasFDerivAt_coe_chart (hpole : ‖pole‖ = 1)
    (horthogonal : ∀ z, ⟪pole, plane z⟫_ℝ = 0) (z : ℂ) :
    HasFDerivAt (fun w => (chart pole plane hpole horthogonal w : E))
      (chartDerivative pole plane z) z := by
  have hden : 1 + ‖z‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hscalar : HasDerivAt (fun t : ℝ => 2 / (1 + t))
      (-2 / (1 + ‖z‖ ^ 2) ^ 2) (‖z‖ ^ 2) := by
    simpa only [id_eq, mul_zero, zero_mul, zero_sub, mul_one] using
      (hasDerivAt_const (‖z‖ ^ 2) (2 : ℝ)).fun_div
        ((hasDerivAt_id (‖z‖ ^ 2)).const_add 1) hden
  have hscalarNorm := hscalar.comp_hasFDerivAt z (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hscalarNorm' : HasFDerivAt (fun w : ℂ => 2 / (1 + ‖w‖ ^ 2))
      ((-4 / (1 + ‖z‖ ^ 2) ^ 2) • innerSL ℝ z) z := by
    have hmap : (-2 / (1 + ‖z‖ ^ 2) ^ 2) • (2 • innerSL ℝ z) =
        (-4 / (1 + ‖z‖ ^ 2) ^ 2) • innerSL ℝ z := by
      rw [two_smul, smul_add, ← add_smul]
      congr 1
      ring
    rw [hmap] at hscalarNorm
    simpa only [Function.comp_def] using hscalarNorm
  have hvector := (plane.toContinuousLinearMap.hasFDerivAt (x := z)).sub_const pole
  have hresult := (hscalarNorm'.smul hvector).const_add pole
  convert! hresult using 1
  funext w
  exact coe_chart pole plane hpole horthogonal w

theorem norm_chartDerivative (hpole : ‖pole‖ = 1)
    (horthogonal : ∀ z, ⟪pole, plane z⟫_ℝ = 0) (z h : ℂ) :
    ‖chartDerivative pole plane z h‖ = 2 * ‖h‖ / (1 + ‖z‖ ^ 2) := by
  have hden : 1 + ‖z‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hnorm : ‖plane z - pole‖ ^ 2 = ‖z‖ ^ 2 + 1 := by
    rw [norm_sub_sq_real, plane.norm_map, real_inner_comm, horthogonal z, hpole]
    ring
  have hinner : ⟪plane h, plane z - pole⟫_ℝ = ⟪z, h⟫_ℝ := by
    have horthh : ⟪plane h, pole⟫_ℝ = 0 := by
      rw [real_inner_comm]
      exact horthogonal h
    rw [inner_sub_right, plane.inner_map_map, horthh, sub_zero]
    exact real_inner_comm _ _
  have hsquare : ‖chartDerivative pole plane z h‖ ^ 2 =
      (2 * ‖h‖ / (1 + ‖z‖ ^ 2)) ^ 2 := by
    rw [chartDerivative_apply, norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, plane.norm_map,
      hnorm, real_inner_smul_left, real_inner_smul_right, hinner]
    field_simp [hden]
    ring
  have hnonneg : 0 ≤ 2 * ‖h‖ / (1 + ‖z‖ ^ 2) := by positivity
  nlinarith [norm_nonneg (chartDerivative pole plane z h)]

@[expose] def curveSpeed (curve : ℝ → ℂ) (time : ℝ) : ℝ :=
  2 * ‖deriv curve time‖ / (1 + ‖curve time‖ ^ 2)

theorem norm_deriv_chart_curve (hpole : ‖pole‖ = 1)
    (horthogonal : ∀ z, ⟪pole, plane z⟫_ℝ = 0)
    {curve : ℝ → ℂ} {time : ℝ} (hcurve : DifferentiableAt ℝ curve time) :
    ‖deriv (fun t => (chart pole plane hpole horthogonal (curve t) : E)) time‖ =
      curveSpeed curve time := by
  have heq := ((hasFDerivAt_coe_chart pole plane hpole horthogonal (curve time)).comp_hasDerivAt
    time hcurve.hasDerivAt).deriv
  simp only [Function.comp_def] at heq
  rw [heq]
  exact norm_chartDerivative pole plane hpole horthogonal _ _

theorem dist_chart_curve_le_integral_speed (hpole : ‖pole‖ = 1)
    (horthogonal : ∀ z, ⟪pole, plane z⟫_ℝ = 0)
    {curve : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hcontinuous : ContinuousOn curve (Icc a b))
    (hdifferentiable : DifferentiableOn ℝ curve (Ioo a b))
    (hintegrable : IntervalIntegrable (curveSpeed curve) volume a b) :
    dist (chart pole plane hpole horthogonal (curve b))
        (chart pole plane hpole horthogonal (curve a)) ≤
      ∫ t in a..b, curveSpeed curve t := by
  have hchartContinuous : Continuous (fun z => (chart pole plane hpole horthogonal z : E)) :=
    continuous_iff_continuousAt.mpr fun z =>
      (hasFDerivAt_coe_chart pole plane hpole horthogonal z).continuousAt
  have hd : DifferentiableOn ℝ
      (fun t => (chart pole plane hpole horthogonal (curve t) : E)) (Ioo a b) := by
    intro t ht
    exact (hasFDerivAt_coe_chart pole plane hpole horthogonal (curve t)).differentiableAt
      |>.comp_differentiableWithinAt t (hdifferentiable t ht)
  have hbound : ∀ᵐ t, t ∈ Ioo a b →
      ‖deriv (fun s => (chart pole plane hpole horthogonal (curve s) : E)) t‖ ≤
        curveSpeed curve t := Filter.Eventually.of_forall fun t ht =>
    (norm_deriv_chart_curve pole plane hpole horthogonal
      ((hdifferentiable t ht).differentiableAt (isOpen_Ioo.mem_nhds ht))).le
  simpa only [Subtype.dist_eq, dist_eq_norm, Function.comp_def] using
    norm_sub_le_integral_of_norm_deriv_le_of_le hab
      (hchartContinuous.comp_continuousOn hcontinuous) hd hbound hintegrable

end Math.NormalizedSphereChart
