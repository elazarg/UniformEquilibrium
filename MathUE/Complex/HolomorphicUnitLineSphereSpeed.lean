module

public import MathUE.Analysis.NormalizedSphereChartSpeed
public import MathUE.Analysis.FiniteIntegralCurveLanding
public import MathUE.Complex.HolomorphicSphericalEnergy
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Actual holomorphic unit-line speed in the normalized sphere chart

Milnor's length-area argument uses horizontal and vertical unit-speed lines.
Here the line derivative and the spherical speed identity are derived from
holomorphicity, not supplied as a curve-length hypothesis. The ambient sphere
may be infinite dimensional; completeness is not needed for displacement.
Source: Milnor, *Dynamics in One Complex Variable*, §§1 and 15,
https://legacy-www.math.harvard.edu/archive/118r_spring_05/docs/milnor.pdf

This is a finite-chart displacement theorem. Landing endpoints, including the
chart pole, require the separate finite-integral extension argument.
-/

public section

noncomputable section

namespace Math.ComplexAnalysis

open MeasureTheory Metric Set
open scoped InnerProductSpace
open scoped ENNReal
open scoped Topology

@[expose] def complexUnitLine (origin direction : ℂ) (time : ℝ) : ℂ :=
  origin + time • direction

theorem hasDerivAt_complexUnitLine (origin direction : ℂ) (time : ℝ) :
    HasDerivAt (complexUnitLine origin direction) direction time := by
  have h := ((hasDerivAt_id time).smul_const direction).const_add origin
  simp only [one_smul] at h
  convert! h using 1

theorem hasDerivAt_holomorphic_unitLine
    {f : ℂ → ℂ} {origin direction : ℂ} {time : ℝ}
    (hf : DifferentiableAt ℂ f (complexUnitLine origin direction time)) :
    HasDerivAt (fun t => f (complexUnitLine origin direction t))
      (direction * deriv f (complexUnitLine origin direction time)) time := by
  have h := (hf.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt time
    (hasDerivAt_complexUnitLine origin direction time)
  simp only [Function.comp_def] at h
  convert! h using 1

theorem curveSpeed_holomorphic_unitLine
    {f : ℂ → ℂ} {origin direction : ℂ} {time : ℝ}
    (hdirection : ‖direction‖ = 1)
    (hf : DifferentiableAt ℂ f (complexUnitLine origin direction time)) :
    NormalizedSphereChart.curveSpeed (fun t => f (complexUnitLine origin direction t))
        time = sphericalDerivativeSpeed f (complexUnitLine origin direction time) := by
  unfold NormalizedSphereChart.curveSpeed sphericalDerivativeSpeed
  rw [(hasDerivAt_holomorphic_unitLine hf).deriv, norm_mul, hdirection, one_mul]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem dist_sphere_holomorphic_unitLine_le_integral
    (pole : E) (plane : ℂ →ₗᵢ[ℝ] E) (hpole : ‖pole‖ = 1)
    (horthogonal : ∀ z, ⟪pole, plane z⟫_ℝ = 0)
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {origin direction : ℂ} (hdirection : ‖direction‖ = 1)
    {a b : ℝ} (hab : a ≤ b)
    (hline : MapsTo (complexUnitLine origin direction) (Icc a b) U)
    (hintegrable : IntervalIntegrable
      (fun t => sphericalDerivativeSpeed f (complexUnitLine origin direction t))
      volume a b) :
    dist (NormalizedSphereChart.chart pole plane hpole horthogonal
        (f (complexUnitLine origin direction b)))
      (NormalizedSphereChart.chart pole plane hpole horthogonal
        (f (complexUnitLine origin direction a))) ≤
      ∫ t in a..b, sphericalDerivativeSpeed f (complexUnitLine origin direction t) := by
  have hdiff (t : ℝ) (ht : t ∈ Icc a b) :
      DifferentiableAt ℂ f (complexUnitLine origin direction t) :=
    (hf _ (hline ht)).differentiableAt (hU.mem_nhds (hline ht))
  have hcurve (t : ℝ) (ht : t ∈ Icc a b) :
      DifferentiableAt ℝ (fun s => f (complexUnitLine origin direction s)) t :=
    (hasDerivAt_holomorphic_unitLine (hdiff t ht)).differentiableAt
  have heq : Set.EqOn
      (NormalizedSphereChart.curveSpeed (fun t => f (complexUnitLine origin direction t)))
      (fun t => sphericalDerivativeSpeed f (complexUnitLine origin direction t)) (Icc a b) :=
    fun t ht => curveSpeed_holomorphic_unitLine hdirection (hdiff t ht)
  have hae : ∀ᵐ t ∂volume.restrict (uIoc a b),
      NormalizedSphereChart.curveSpeed (fun s => f (complexUnitLine origin direction s)) t =
        sphericalDerivativeSpeed f (complexUnitLine origin direction t) := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    exact heq ((uIoc_of_le hab ▸ ht).imp le_of_lt id)
  have hint := hintegrable.congr_ae (Filter.EventuallyEq.symm hae)
  have hbound := NormalizedSphereChart.dist_chart_curve_le_integral_speed
    pole plane hpole horthogonal hab
    (fun t ht => (hcurve t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hcurve t ⟨ht.1.le, ht.2.le⟩).differentiableWithinAt) hint
  rw [intervalIntegral.integral_congr_ae_restrict hae] at hbound
  exact hbound

/-- Finite actual spherical speed produces both landing values, possibly at
the chart pole. Nothing is asserted about a finite complex endpoint. -/
theorem exists_sphere_landing_holomorphic_unitLine [CompleteSpace E]
    (pole : E) (plane : ℂ →ₗᵢ[ℝ] E) (hpole : ‖pole‖ = 1)
    (horthogonal : ∀ z, ⟪pole, plane z⟫_ℝ = 0)
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {origin direction : ℂ} (hdirection : ‖direction‖ = 1)
    {a b : ℝ} (hab : a < b)
    (hline : MapsTo (complexUnitLine origin direction) (Ioo a b) U)
    (hintegrable : IntegrableOn
      (fun t => sphericalDerivativeSpeed f (complexUnitLine origin direction t))
      (Ioo a b)) :
    ∃ landing : Icc a b → sphere (0 : E) 1, UniformContinuous landing ∧
      ∀ t : Ioo a b, landing ⟨t, t.property.1.le, t.property.2.le⟩ =
        NormalizedSphereChart.chart pole plane hpole horthogonal
          (f (complexUnitLine origin direction t)) := by
  let speed : ℝ → ℝ := fun t =>
    sphericalDerivativeSpeed f (complexUnitLine origin direction t)
  let curve : Ioo a b → sphere (0 : E) 1 := fun t =>
    NormalizedSphereChart.chart pole plane hpole horthogonal
      (f (complexUnitLine origin direction t))
  have hnonnegative (t : ℝ) : 0 ≤ speed t := by
    dsimp [speed, sphericalDerivativeSpeed]
    positivity
  have hfinite : (∫⁻ t in Ioo a b, ENNReal.ofReal (speed t)) ≠ ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hintegrable
      (Filter.Eventually.of_forall hnonnegative)]
    exact ENNReal.ofReal_ne_top
  have hordered (s t : Ioo a b) (hst : (s : ℝ) ≤ t) :
      edist (curve s) (curve t) ≤
        ∫⁻ r in uIoc (s : ℝ) (t : ℝ), ENNReal.ofReal (speed r)
          ∂volume.restrict (Ioo a b) := by
    have hsub : Icc (s : ℝ) (t : ℝ) ⊆ Ioo a b := fun r hr =>
      ⟨s.property.1.trans_le hr.1, hr.2.trans_lt t.property.2⟩
    have hsuboc : Ioc (s : ℝ) (t : ℝ) ⊆ Ioo a b :=
      fun r hr => hsub ⟨hr.1.le, hr.2⟩
    have hint : IntervalIntegrable speed volume (s : ℝ) (t : ℝ) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).mpr
        (hintegrable.mono_set hsuboc)
    have hbound := dist_sphere_holomorphic_unitLine_le_integral
      pole plane hpole horthogonal hU hf hdirection hst
      (fun r hr => hline (hsub hr)) hint
    rw [uIoc_of_le hst, Measure.restrict_restrict_of_subset hsuboc]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (hintegrable.mono_set hsuboc) (Filter.Eventually.of_forall hnonnegative)]
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    simpa only [curve, dist_comm, intervalIntegral.integral_of_le hst] using hbound
  have hchord (s t : Ioo a b) : edist (curve s) (curve t) ≤
      ∫⁻ r in uIoc (s : ℝ) (t : ℝ), ENNReal.ofReal (speed r)
        ∂volume.restrict (Ioo a b) := by
    rcases le_total (s : ℝ) (t : ℝ) with hst | hts
    · exact hordered s t hst
    · simpa only [edist_comm, uIoc_comm] using hordered t s hts
  let : CompleteSpace (sphere (0 : E) 1) := isClosed_sphere.isComplete.completeSpace_coe
  exact FiniteIntegralCurve.exists_landing_of_edist_le_lintegral hab
    Measure.restrict_le_self hfinite hchord

/-- The finite ENNReal integral formulation derives its real integrability
from local holomorphicity; no measurability of the arbitrary outside values is used. -/
theorem exists_sphere_landing_holomorphic_unitLine_of_lintegral_ne_top [CompleteSpace E]
    (pole : E) (plane : ℂ →ₗᵢ[ℝ] E) (hpole : ‖pole‖ = 1)
    (horthogonal : ∀ z, ⟪pole, plane z⟫_ℝ = 0)
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {origin direction : ℂ} (hdirection : ‖direction‖ = 1)
    {a b : ℝ} (hab : a < b)
    (hline : MapsTo (complexUnitLine origin direction) (Ioo a b) U)
    (hfinite : (∫⁻ t in Ioo a b,
      ENNReal.ofReal (sphericalDerivativeSpeed f (complexUnitLine origin direction t))) ≠ ∞) :
    ∃ landing : Icc a b → sphere (0 : E) 1, UniformContinuous landing ∧
      ∀ t : Ioo a b, landing ⟨t, t.property.1.le, t.property.2.le⟩ =
        NormalizedSphereChart.chart pole plane hpole horthogonal
          (f (complexUnitLine origin direction t)) := by
  have hspeed : ContinuousOn (sphericalDerivativeSpeed f) U := by
    have hderiv := (hf.analyticOnNhd hU).deriv.continuousOn
    unfold sphericalDerivativeSpeed
    exact (continuousOn_const.mul hderiv.norm).div
      (continuousOn_const.add (hf.continuousOn.norm.pow 2)) (fun z _ => by positivity)
  have hlineContinuous : Continuous (complexUnitLine origin direction) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_complexUnitLine origin direction t).continuousAt
  have hmeas := (hspeed.comp hlineContinuous.continuousOn hline).aestronglyMeasurable
    (μ := volume) measurableSet_Ioo
  have hnonnegative : ∀ᵐ t ∂volume.restrict (Ioo a b),
      0 ≤ sphericalDerivativeSpeed f (complexUnitLine origin direction t) :=
    Filter.Eventually.of_forall fun t => by
      unfold sphericalDerivativeSpeed
      positivity
  exact exists_sphere_landing_holomorphic_unitLine pole plane hpole horthogonal hU hf
    hdirection hab hline
    ((lintegral_ofReal_ne_top_iff_integrable hmeas hnonnegative).mp hfinite)

/-- Literal right and left landing limits in the sphere, with no finite-chart
restriction on either produced endpoint. -/
theorem exists_sphere_endpoint_limits_holomorphic_unitLine [CompleteSpace E]
    (pole : E) (plane : ℂ →ₗᵢ[ℝ] E) (hpole : ‖pole‖ = 1)
    (horthogonal : ∀ z, ⟪pole, plane z⟫_ℝ = 0)
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {origin direction : ℂ} (hdirection : ‖direction‖ = 1)
    {a b : ℝ} (hab : a < b)
    (hline : MapsTo (complexUnitLine origin direction) (Ioo a b) U)
    (hfinite : (∫⁻ t in Ioo a b,
      ENNReal.ofReal (sphericalDerivativeSpeed f (complexUnitLine origin direction t))) ≠ ∞) :
    ∃ left right : sphere (0 : E) 1,
      Filter.Tendsto (fun t => NormalizedSphereChart.chart pole plane hpole horthogonal
        (f (complexUnitLine origin direction t))) (𝓝[>] a) (𝓝 left) ∧
      Filter.Tendsto (fun t => NormalizedSphereChart.chart pole plane hpole horthogonal
        (f (complexUnitLine origin direction t))) (𝓝[<] b) (𝓝 right) := by
  obtain ⟨landing, hcontinuous, hagrees⟩ :=
    exists_sphere_landing_holomorphic_unitLine_of_lintegral_ne_top
      pole plane hpole horthogonal hU hf hdirection hab hline hfinite
  exact ⟨landing ⟨a, le_rfl, hab.le⟩, landing ⟨b, hab.le, le_rfl⟩,
    FiniteIntegralCurve.endpoint_limits_of_extension hab hcontinuous.continuous hagrees⟩

end Math.ComplexAnalysis
