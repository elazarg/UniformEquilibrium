module

public import MathUE.Complex.CanonicalComplexSphere
public import MathUE.Complex.HolomorphicRectangleLengthArea
public import MathUE.Complex.HolomorphicUnitLineSphereSpeed
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # Actual almost-everywhere radial landing in the sphere

Milnor §15.3 applies length-area to logarithmic coordinates. On an angular
strip narrower than a full turn the exponential is injective, so the actual
weighted image formula supplies finite energy. Slice integrability and the
actual spherical unit-line theorem then produce landing values. No boundedness
of the original holomorphic function or finite complex endpoint is assumed.
Source: https://legacy-www.math.harvard.edu/archive/118r_spring_05/docs/milnor.pdf

This is the complex-valued interior-chart case. Distinct endpoint fibers,
crosscuts, Jordan separation and continuous boundary extension are not asserted.
-/

public section

noncomputable section

namespace Math.ComplexAnalysis

open Complex Filter MeasureTheory Metric Set
open scoped ENNReal Topology

@[expose] def logarithmicStrip (width : ℝ) : Set ℂ :=
  {w | 0 < w.re ∧ w.re < width ∧ 0 < w.im}

@[expose] def logarithmicDiskMap (angle : ℝ) (w : ℂ) : ℂ :=
  Complex.exp ((angle : ℂ) * I) * Complex.exp (w * I)

theorem isOpen_logarithmicStrip (width : ℝ) : IsOpen (logarithmicStrip width) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im))

theorem logarithmicDiskMap_mem_ball {width angle : ℝ} {w : ℂ}
    (hw : w ∈ logarithmicStrip width) : logarithmicDiskMap angle w ∈ ball 0 1 := by
  rw [mem_ball_zero_iff]
  simp only [logarithmicDiskMap, norm_mul, Complex.norm_exp, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, I_re, I_im, mul_zero,
    sub_zero, zero_sub, Real.exp_zero, one_mul, mul_one]
  exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hw.2.2)

theorem logarithmicDiskMap_injOn {width : ℝ} (hwidth : width < 2 * Real.pi)
    (angle : ℝ) : InjOn (logarithmicDiskMap angle) (logarithmicStrip width) := by
  intro z hz w hw heq
  have hexp : Complex.exp (z * I) = Complex.exp (w * I) :=
    mul_left_cancel₀ (Complex.exp_ne_zero _) heq
  have hshift : Complex.exp (z * I - (Real.pi : ℂ) * I) =
      Complex.exp (w * I - (Real.pi : ℂ) * I) := by
    rw [Complex.exp_sub, Complex.exp_sub, hexp]
  have hzlower : -Real.pi < (z * I - (Real.pi : ℂ) * I).im := by
    simp only [Complex.sub_im, Complex.mul_im, I_im, I_re, mul_one, mul_zero,
      add_zero, Complex.ofReal_re]
    linarith [hz.1]
  have hzupper : (z * I - (Real.pi : ℂ) * I).im ≤ Real.pi := by
    simp only [Complex.sub_im, Complex.mul_im, I_im, I_re, mul_one, mul_zero,
      add_zero, Complex.ofReal_re]
    linarith [hz.2.1]
  have hwlower : -Real.pi < (w * I - (Real.pi : ℂ) * I).im := by
    simp only [Complex.sub_im, Complex.mul_im, I_im, I_re, mul_one, mul_zero,
      add_zero, Complex.ofReal_re]
    linarith [hw.1]
  have hwupper : (w * I - (Real.pi : ℂ) * I).im ≤ Real.pi := by
    simp only [Complex.sub_im, Complex.mul_im, I_im, I_re, mul_one, mul_zero,
      add_zero, Complex.ofReal_re]
    linarith [hw.2.1]
  have hcancel : z * I - (Real.pi : ℂ) * I = w * I - (Real.pi : ℂ) * I :=
    Complex.exp_inj_of_neg_pi_lt_of_le_pi hzlower hzupper hwlower hwupper hshift
  have hmul : z * I = w * I := by linear_combination hcancel
  exact mul_right_cancel₀ I_ne_zero hmul

theorem differentiable_logarithmicDiskMap (angle : ℝ) :
    Differentiable ℂ (logarithmicDiskMap angle) := by
  exact (Complex.differentiable_exp.comp (differentiable_id.mul_const I)).const_mul _

theorem openComplexSquare_subset_logarithmicStrip (width : ℝ) :
    openComplexSquare width ⊆ logarithmicStrip width := by
  rintro w ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
  exact ⟨hx.1, hx.2, hy.1⟩

theorem logarithmicDiskMap_unitLine (angle x time : ℝ) :
    logarithmicDiskMap angle (complexUnitLine (x : ℂ) I time) =
      (Real.exp (-time) : ℂ) * Complex.exp (((angle + x : ℝ) : ℂ) * I) := by
  rw [logarithmicDiskMap, Complex.ofReal_exp, Complex.ofReal_add]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [complexUnitLine, Complex.real_smul, Complex.ofReal_neg]
  ring_nf
  simp only [I_sq]
  ring

/-- A logarithmic square gives finite actual speed for almost every radial direction. -/
theorem logarithmic_slice_finite_ae
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1)) (hinj : InjOn g (ball 0 1))
    {width : ℝ} (hwidth : width < 2 * Real.pi) (angle : ℝ) :
    ∀ᵐ (x : ℝ) ∂volume.restrict (Ioo 0 width),
      (∫⁻ t in Ioo 0 width, ENNReal.ofReal
        (sphericalDerivativeSpeed (fun w => g (logarithmicDiskMap angle w))
          (complexUnitLine (x : ℂ) I t))) < ∞ := by
  let f : ℂ → ℂ := fun w => g (logarithmicDiskMap angle w)
  have hf : DifferentiableOn ℂ f (logarithmicStrip width) :=
    hg.comp (differentiable_logarithmicDiskMap angle).differentiableOn
      (fun _ hw => logarithmicDiskMap_mem_ball hw)
  have hi : InjOn f (logarithmicStrip width) :=
    hinj.comp (logarithmicDiskMap_injOn hwidth angle)
      (fun _ hw => logarithmicDiskMap_mem_ball hw)
  have hae := chart_slice_finite_ae (isOpen_logarithmicStrip width) hf hi
    (openComplexSquare_subset_logarithmicStrip width)
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with x hx hxmem
  rw [chart_slice_eq_actual (openComplexSquare_subset_logarithmicStrip width) hxmem] at hx
  have heq (t : ℝ) : complexUnitLine (x : ℂ) I t =
      Complex.measurableEquivRealProd.symm (x, t) := by
    apply Complex.ext <;> simp [complexUnitLine, Complex.real_smul]
  simpa only [heq] using hx

theorem tendsto_neg_log_nhdsLT_one :
    Tendsto (fun r : ℝ => -Real.log r) (𝓝[<] 1) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hlog : Tendsto Real.log (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      simpa only [Real.log_one] using
        ((Real.continuousAt_log (x := 1) one_ne_zero).tendsto.mono_left
          nhdsWithin_le_nhds)
    simpa only [neg_zero] using hlog.neg
  · filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r from
        nhdsWithin_le_nhds (eventually_gt_nhds zero_lt_one))] with r hr hpositive
    exact neg_pos.mpr (Real.log_neg hpositive hr)

/-- The actual unbounded holomorphic map has sphere-valued radial limits for
almost every offset in every angular interval of width less than a full turn. -/
theorem exists_sphere_radial_limit_ae
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1)) (hinj : InjOn g (ball 0 1))
    {width : ℝ} (hpositive : 0 < width) (hwidth : width < 2 * Real.pi) (angle : ℝ) :
    ∀ᵐ (x : ℝ) ∂volume.restrict (Ioo 0 width), ∃ endpoint : ComplexSphere.Sphere,
      Tendsto (fun r : ℝ => ComplexSphere.chart
        (g ((r : ℂ) * Complex.exp (((angle + x : ℝ) : ℂ) * I))))
        (𝓝[<] 1) (𝓝 endpoint) := by
  have hfinite := logarithmic_slice_finite_ae hg hinj hwidth angle
  filter_upwards [hfinite, ae_restrict_mem measurableSet_Ioo] with x hx hxmem
  have hf : DifferentiableOn ℂ (fun w => g (logarithmicDiskMap angle w))
      (logarithmicStrip width) :=
    hg.comp (differentiable_logarithmicDiskMap angle).differentiableOn
      (fun _ hw => logarithmicDiskMap_mem_ball hw)
  have hline : MapsTo (complexUnitLine (x : ℂ) I) (Ioo 0 width)
      (logarithmicStrip width) := by
    intro t ht
    simpa [complexUnitLine, logarithmicStrip, Complex.real_smul] using
      (show 0 < x ∧ x < width ∧ 0 < t from ⟨hxmem.1, hxmem.2, ht.1⟩)
  obtain ⟨left, right, hleft, _⟩ := exists_sphere_endpoint_limits_holomorphic_unitLine
    ComplexSphere.pole ComplexSphere.plane ComplexSphere.norm_pole
    ComplexSphere.pole_orthogonal_plane (isOpen_logarithmicStrip width) hf
    Complex.norm_I hpositive hline hx.ne
  refine ⟨left, ?_⟩
  have hcomposed := hleft.comp tendsto_neg_log_nhdsLT_one
  apply hcomposed.congr'
  filter_upwards [(show ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r from
    nhdsWithin_le_nhds (eventually_gt_nhds zero_lt_one))] with r hr
  simp only [Function.comp_def, logarithmicDiskMap_unitLine, neg_neg, Real.exp_log hr]
  rfl

/-- Countably many overlapping translated windows give the paper-facing
almost-everywhere statement on all real angles. -/
theorem exists_sphere_radial_limit_ae_real
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1)) (hinj : InjOn g (ball 0 1)) :
    ∀ᵐ θ : ℝ, ∃ endpoint : ComplexSphere.Sphere,
      Tendsto (fun r : ℝ => ComplexSphere.chart
        (g ((r : ℂ) * Complex.exp ((θ : ℂ) * I)))) (𝓝[<] 1) (𝓝 endpoint) := by
  let P : ℝ → Prop := fun θ => ∃ endpoint : ComplexSphere.Sphere,
    Tendsto (fun r : ℝ => ComplexSphere.chart
      (g ((r : ℂ) * Complex.exp ((θ : ℂ) * I)))) (𝓝[<] 1) (𝓝 endpoint)
  have hwindows (n : ℤ) : ∀ᵐ θ : ℝ, θ - n ∈ Ioo (0 : ℝ) 2 → P θ := by
    have hwindow := exists_sphere_radial_limit_ae hg hinj
      (width := 2) (by norm_num) (by linarith [Real.pi_gt_three]) (n : ℝ)
    have hwhole : ∀ᵐ x : ℝ, x ∈ Ioo (0 : ℝ) 2 → P ((n : ℝ) + x) :=
      (ae_restrict_iff' measurableSet_Ioo).mp hwindow
    have htranslated := (measurePreserving_add_left volume (-(n : ℝ)))
      |>.quasiMeasurePreserving.ae hwhole
    filter_upwards [htranslated] with θ hθ hmem
    have hsub : -(n : ℝ) + θ = θ - n := by ring
    have hsum : (n : ℝ) + (-(n : ℝ) + θ) = θ := by ring
    rw [hsum] at hθ
    exact hθ (hsub.symm ▸ hmem)
  have hall : ∀ᵐ θ : ℝ, ∀ n : ℤ, θ - n ∈ Ioo (0 : ℝ) 2 → P θ :=
    ae_all_iff.mpr hwindows
  filter_upwards [hall] with θ hθ
  apply hθ (⌊θ⌋ - 1)
  have hfloor := Int.floor_le θ
  have hupper := Int.lt_floor_add_one θ
  constructor <;> push_cast <;> linarith

end Math.ComplexAnalysis
