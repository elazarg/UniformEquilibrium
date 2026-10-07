module

public import MathUE.Complex.HolomorphicRadialLandingFibers
public import MathUE.Complex.HolomorphicRectangleLengthArea
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Order.Filter.Finite
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Topology.Path
public import Mathlib.Topology.Order.ExtendFrom

/-! # Local ingredients for short spherical image arcs

Milnor §§15.2–15.4 select two radial sides and one transverse side using
localized actual spherical energy. The localization below is derived from
the univalent map, rather than assumed as a small-energy certificate.
Endpoint exclusions use null fibers and allow the north pole.

Source: Milnor, *Dynamics in One Complex Variable*, §§15.2–15.4,
https://legacy-www.math.harvard.edu/archive/118r_spring_05/docs/milnor.pdf

The local analytic ingredients do not assert a nested disjoint arc sequence,
Jordan separation, or continuous extension on the whole disk boundary.
-/

public section
noncomputable section

namespace Math.ComplexAnalysis

open Complex Filter MeasureTheory Metric Set
open scoped ENNReal Topology

/-- Actual finite spherical energy can be made small near any point, including
a point outside the open source domain. No behavior outside that domain is used. -/
theorem exists_ball_spherical_energy_lt
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    (center : ℂ) {ε : ℝ≥0∞} (hε : ε ≠ 0) {radius : ℝ} (hradius : 0 < radius) :
    ∃ r ∈ Ioo 0 radius,
      (∫⁻ z in ball center r ∩ U,
        ENNReal.ofReal (sphericalDerivativeSpeed f z ^ 2)) < ε := by
  have hfinite := spherical_energy_lt_top hU hf hinj hU.measurableSet
    (Subset.rfl : U ⊆ U)
  obtain ⟨δ, hδ, hsmall⟩ :=
    exists_pos_setLIntegral_lt_of_measure_lt hfinite.ne hε
  obtain ⟨V, hpoint, hV, hvolume⟩ :=
    ({center} : Set ℂ).exists_isOpen_lt_of_lt (μ := volume) δ (by simpa using hδ)
  obtain ⟨s, hs, hsV⟩ := Metric.mem_nhds_iff.mp
    (hV.mem_nhds (hpoint (mem_singleton center)))
  let r := min s radius / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrs : r < s := by dsimp [r]; linarith [min_le_left s radius]
  have hrradius : r < radius := by dsimp [r]; linarith [min_le_right s radius]
  refine ⟨r, ⟨hr, hrradius⟩, ?_⟩
  have hmeasure : (volume.restrict U) (ball center r) < δ :=
    (Measure.restrict_apply_le _ _).trans_lt
      ((measure_mono ((ball_subset_ball hrs.le).trans hsV)).trans_lt hvolume)
  have h := hsmall (ball center r) hmeasure
  simpa only [Measure.restrict_restrict measurableSet_ball] using h

/-- Almost every direction lands on the actual image frontier while avoiding
any specified finite collection of spherical values. No measurability of the
individual landing fibers is needed. -/
theorem exists_sphere_radial_frontier_limit_ae_avoiding
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1)) (hinj : InjOn g (ball 0 1))
    (forbidden : Finset ComplexSphere.Sphere) :
    ∀ᵐ θ : ℝ, ∃ endpoint ∈ frontier (ComplexSphere.chart '' (g '' ball 0 1)),
      endpoint ∉ forbidden ∧
      Tendsto (fun r : ℝ => ComplexSphere.chart
        (g ((r : ℂ) * Complex.exp ((θ : ℂ) * I)))) (𝓝[<] 1) (𝓝 endpoint) := by
  have havoids (p : ComplexSphere.Sphere) :
      ∀ᵐ θ : ℝ, ¬Tendsto (fun r : ℝ => ComplexSphere.chart
        (g ((r : ℂ) * Complex.exp ((θ : ℂ) * I)))) (𝓝[<] 1) (𝓝 p) := by
    exact ae_iff.mpr (by simpa only [not_not] using
      spherical_radial_fiber_measure_zero hg hinj p)
  have hall := (eventually_all_finset forbidden).mpr (fun p _ => havoids p)
  filter_upwards [exists_sphere_radial_frontier_limit_ae hg hinj, hall] with θ hθ havoid
  obtain ⟨endpoint, hfrontier, hlimit⟩ := hθ
  exact ⟨endpoint, hfrontier, fun hmem => havoid endpoint hmem hlimit, hlimit⟩

private theorem exists_short_slice_in_band_of_ae
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite ν]
    {speed : X × Y → ℝ≥0∞} (hspeed : Measurable speed)
    (hfinite : (∫⁻ point, speed point ^ 2 ∂μ.prod ν) ≠ ∞)
    {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) {band : Set X}
    (hlarge : ν univ / 4 < μ band) :
    ∃ x ∈ band, P x ∧
      (∫⁻ y, speed (x, y) ∂ν) ≤ ENNReal.ofReal
        (2 * Real.sqrt (∫⁻ point, speed point ^ 2 ∂μ.prod ν).toReal) := by
  by_cases hzero : (∫⁻ point, speed point ^ 2 ∂μ.prod ν) = 0
  · have hslices := RectangleLengthArea.slice_eq_zero_ae_of_energy_zero
      (μ := μ) (ν := ν) hspeed hzero
    have hpositive : μ band ≠ 0 := (lt_of_le_of_lt zero_le hlarge).ne'
    obtain ⟨x, hx, hPx, hslice⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      hpositive (ae_restrict_of_ae (hP.and hslices))
    exact ⟨x, hx, hPx, by rw [hslice]; exact zero_le⟩
  · have hlong := RectangleLengthArea.measure_two_sqrt_energy_le_quarter
      (μ := μ) (ν := ν) hspeed hzero hfinite
    by_contra hnot
    have hsubset : band ≤ᵐ[μ] {x | ENNReal.ofReal
        (2 * Real.sqrt (∫⁻ point, speed point ^ 2 ∂μ.prod ν).toReal) ≤
          ∫⁻ y, speed (x, y) ∂ν} := by
      filter_upwards [hP] with x hx hmem
      exact (lt_of_not_ge (fun hle => hnot ⟨x, hmem, hx, hle⟩)).le
    exact hlarge.not_ge ((measure_mono_ae hsubset).trans hlong)

/-- Short radial sides can be selected in any angular band occupying more
than a quarter of the square. In particular the two opposite half-bands
remain available after excluding finitely many spherical endpoint values.
The energy is the actual energy of the logarithmic pullback. -/
theorem exists_short_logarithmic_slice_avoiding
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1)) (hinj : InjOn g (ball 0 1))
    {width : ℝ} (hwidth : width < 2 * Real.pi) (angle : ℝ)
    (forbidden : Finset ComplexSphere.Sphere) {band : Set ℝ}
    (hband : band ⊆ Ioo 0 width)
    (hlarge : ENNReal.ofReal width / 4 < (volume.restrict (Ioo 0 width)) band) :
    ∃ x ∈ band, ∃ endpoint ∈ frontier (ComplexSphere.chart '' (g '' ball 0 1)),
      endpoint ∉ forbidden ∧
      Tendsto (fun r : ℝ => ComplexSphere.chart
        (g ((r : ℂ) * Complex.exp (((angle + x : ℝ) : ℂ) * I))))
        (𝓝[<] 1) (𝓝 endpoint) ∧
      (∫⁻ t in Ioo 0 width, ENNReal.ofReal
        (sphericalDerivativeSpeed (fun w => g (logarithmicDiskMap angle w))
          (complexUnitLine (x : ℂ) I t))) ≤
        ENNReal.ofReal (2 * Real.sqrt
          (chartSquareEnergy (fun w => g (logarithmicDiskMap angle w))
            (logarithmicStrip width) width).toReal) := by
  let f : ℂ → ℂ := fun w => g (logarithmicDiskMap angle w)
  let μ := volume.restrict (Ioo (0 : ℝ) width)
  let energy := chartSquareEnergy f (logarithmicStrip width) width
  let threshold := ENNReal.ofReal (2 * Real.sqrt energy.toReal)
  let slice := fun x => ∫⁻ t in Ioo 0 width,
    chartRectangleSpeed f (logarithmicStrip width) (x, t)
  let P : ℝ → Prop := fun x =>
    ∃ endpoint ∈ frontier (ComplexSphere.chart '' (g '' ball 0 1)),
      endpoint ∉ forbidden ∧
      Tendsto (fun r : ℝ => ComplexSphere.chart
        (g ((r : ℂ) * Complex.exp (((angle + x : ℝ) : ℂ) * I))))
        (𝓝[<] 1) (𝓝 endpoint)
  have hP : ∀ᵐ x ∂μ, P x := ae_restrict_of_ae
    ((measurePreserving_add_left volume angle).quasiMeasurePreserving.ae
      (exists_sphere_radial_frontier_limit_ae_avoiding hg hinj forbidden))
  have hf : DifferentiableOn ℂ f (logarithmicStrip width) :=
    hg.comp (differentiable_logarithmicDiskMap angle).differentiableOn
      (fun _ hw => logarithmicDiskMap_mem_ball hw)
  have hi : InjOn f (logarithmicStrip width) :=
    hinj.comp (logarithmicDiskMap_injOn hwidth angle)
      (fun _ hw => logarithmicDiskMap_mem_ball hw)
  have hselected : ∃ x ∈ band, P x ∧ slice x ≤ threshold :=
    exists_short_slice_in_band_of_ae
      (measurable_chartRectangleSpeed (isOpen_logarithmicStrip width) hf)
      (chartSquareEnergy_lt_top (isOpen_logarithmicStrip width) hf hi
        (openComplexSquare_subset_logarithmicStrip width)).ne hP
      (by simpa only [Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero] using hlarge)
  obtain ⟨x, hx, ⟨endpoint, hfrontier, havoid, hlimit⟩, hslice⟩ := hselected
  refine ⟨x, hx, endpoint, hfrontier, havoid, hlimit, ?_⟩
  change (∫⁻ t in Ioo 0 width,
    chartRectangleSpeed f (logarithmicStrip width) (x, t)) ≤ threshold at hslice
  rw [chart_slice_eq_actual (openComplexSquare_subset_logarithmicStrip width)
    (hband hx)] at hslice
  have heq (t : ℝ) : complexUnitLine (x : ℂ) I t =
      Complex.measurableEquivRealProd.symm (x, t) := by
    apply Complex.ext <;> simp [complexUnitLine, Complex.real_smul]
  simpa only [heq] using hslice

theorem chartSquareEnergy_comp_add_const
    {f : ℂ → ℂ} {U : Set ℂ} {width : ℝ} (shift : ℂ)
    (hcontained : openComplexSquare width ⊆ U) :
    chartSquareEnergy (fun z => f (z + shift)) U width =
      ∫⁻ z in (fun w => w + shift) '' openComplexSquare width,
        ENNReal.ofReal (sphericalDerivativeSpeed f z ^ 2) := by
  rw [chartSquareEnergy_eq_actual_energy hcontained]
  have hspeed (z : ℂ) :
      sphericalDerivativeSpeed (fun w => f (w + shift)) z =
        sphericalDerivativeSpeed f (z + shift) := by
    simp only [sphericalDerivativeSpeed, deriv_comp_add_const]
  simp_rw [hspeed]
  exact (measurePreserving_add_right volume shift).setLIntegral_comp_emb
    (Homeomorph.addRight shift).isClosedEmbedding.measurableEmbedding
    (fun z => ENNReal.ofReal (sphericalDerivativeSpeed f z ^ 2))
    (openComplexSquare width)

private def rectangleArc (left right height : ℝ) (t : ℝ) : ℂ :=
  if t ≤ 1 then (left : ℂ) + ((height * t : ℝ) : ℂ) * I
  else if t ≤ 2 then
    ((left + (right - left) * (t - 1) : ℝ) : ℂ) + (height : ℂ) * I
  else (right : ℂ) + ((height * (3 - t) : ℝ) : ℂ) * I

private theorem continuous_rectangleArc (left right height : ℝ) :
    Continuous (rectangleArc left right height) := by
  unfold rectangleArc
  apply Continuous.if_le (by fun_prop) ?_ continuous_id continuous_const
  · intro t ht
    change t = 1 at ht
    subst t
    norm_num
  · apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
    intro t ht
    change t = 2 at ht
    subst t
    push_cast
    ring

private theorem rectangleArc_endpoints (left right height : ℝ) :
    rectangleArc left right height 0 = (left : ℂ) ∧
      rectangleArc left right height 3 = (right : ℂ) := by
  norm_num [rectangleArc]

private theorem rectangleArc_coordinates
    {left right height : ℝ} (hlr : left < right) (hh : 0 < height)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 3) :
    (rectangleArc left right height t).re ∈ Icc left right ∧
      (rectangleArc left right height t).im ∈ Icc 0 height := by
  unfold rectangleArc
  split_ifs with hfirst hsecond <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, I_re, I_im, mul_one, mul_zero,
      sub_zero, add_zero, zero_add]
  · constructor
    · exact ⟨le_rfl, hlr.le⟩
    · constructor <;> nlinarith [ht.1]
  · constructor
    · constructor <;> nlinarith
    · exact ⟨hh.le, le_rfl⟩
  · constructor
    · exact ⟨hlr.le, le_rfl⟩
    · constructor <;> nlinarith [ht.2]

private theorem rectangleArc_im_pos
    {left right height : ℝ} (hh : 0 < height)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 3) :
    0 < (rectangleArc left right height t).im := by
  unfold rectangleArc
  split_ifs <;>
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, I_re, I_im, mul_one, mul_zero, add_zero, zero_add]
  · exact mul_pos hh ht.1
  · exact hh
  · exact mul_pos hh (sub_pos.mpr ht.2)

private theorem rectangleArc_injOn
    {left right height : ℝ} (hlr : left < right) (hh : 0 < height) :
    InjOn (rectangleArc left right height) (Icc (0 : ℝ) 3) := by
  intro s hs t ht heq
  have hre := congrArg Complex.re heq
  have him := congrArg Complex.im heq
  dsimp only [rectangleArc] at hre him
  split_ifs at hre him <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, I_re, I_im, mul_one, mul_zero,
      sub_zero, add_zero, zero_add] at hre him <;>
    nlinarith

private theorem logarithmicDiskMap_injOn_closed_upper_strip
    {width : ℝ} (hwidth : width < 2 * Real.pi) (angle : ℝ) :
    InjOn (logarithmicDiskMap angle)
      {z : ℂ | 0 < z.re ∧ z.re < width ∧ 0 ≤ z.im} := by
  intro z hz w hw heq
  have hz' : z + I ∈ logarithmicStrip width := by
    simpa only [logarithmicStrip, mem_ofPred_eq, Complex.add_re, Complex.add_im,
      I_re, I_im, add_zero] using
      (show 0 < z.re ∧ z.re < width ∧ 0 < z.im + 1 from
        ⟨hz.1, hz.2.1, by linarith [hz.2.2]⟩)
  have hw' : w + I ∈ logarithmicStrip width := by
    simpa only [logarithmicStrip, mem_ofPred_eq, Complex.add_re, Complex.add_im,
      I_re, I_im, add_zero] using
      (show 0 < w.re ∧ w.re < width ∧ 0 < w.im + 1 from
        ⟨hw.1, hw.2.1, by linarith [hw.2.2]⟩)
  have hshift : logarithmicDiskMap angle (z + I) =
      logarithmicDiskMap angle (w + I) := by
    simpa only [logarithmicDiskMap, add_mul, Complex.exp_add, mul_assoc] using
      congrArg (fun value => value * Complex.exp (I * I)) heq
  exact add_right_cancel (logarithmicDiskMap_injOn hwidth angle hz' hw' hshift)

private theorem exists_rectangle_source_path
    {left right height width : ℝ} (hleft : 0 < left) (hlr : left < right)
    (hright : right < width) (hheight : 0 < height)
    (hwidth : width < 2 * Real.pi) (angle : ℝ) :
    ∃ source : Path (Complex.exp (((angle + left : ℝ) : ℂ) * I))
        (Complex.exp (((angle + right : ℝ) : ℂ) * I)),
      Function.Injective source ∧
      (∀ t : unitInterval, (t : ℝ) ∈ Ioo 0 1 → source t ∈ ball 0 1) ∧
      ∀ t : unitInterval, source t = logarithmicDiskMap angle
        (rectangleArc left right height (3 * (t : ℝ))) := by
  let curve : ℝ → ℂ := fun t => logarithmicDiskMap angle
    (rectangleArc left right height (3 * t))
  have hc : Continuous curve :=
    (differentiable_logarithmicDiskMap angle).continuous.comp
      ((continuous_rectangleArc left right height).comp (by fun_prop))
  have hzero : curve 0 = Complex.exp (((angle + left : ℝ) : ℂ) * I) := by
    simp only [curve, mul_zero, (rectangleArc_endpoints left right height).1]
    simpa [complexUnitLine] using logarithmicDiskMap_unitLine angle left 0
  have hone : curve 1 = Complex.exp (((angle + right : ℝ) : ℂ) * I) := by
    simp only [curve, mul_one, (rectangleArc_endpoints left right height).2]
    simpa [complexUnitLine] using logarithmicDiskMap_unitLine angle right 0
  let source := Path.ofLine hc.continuousOn hzero hone
  have htime (t : unitInterval) : 3 * (t : ℝ) ∈ Icc (0 : ℝ) 3 := by
    constructor <;> linarith [t.property.1, t.property.2]
  have hstrip (t : unitInterval) :
      0 < (rectangleArc left right height (3 * (t : ℝ))).re ∧
      (rectangleArc left right height (3 * (t : ℝ))).re < width ∧
      0 ≤ (rectangleArc left right height (3 * (t : ℝ))).im := by
    have hc := rectangleArc_coordinates hlr hheight (htime t)
    exact ⟨hleft.trans_le hc.1.1, hc.1.2.trans_lt hright, hc.2.1⟩
  refine ⟨source, ?_, ?_, fun _ => rfl⟩
  · intro s t heq
    have hrect := logarithmicDiskMap_injOn_closed_upper_strip hwidth angle
      (hstrip s) (hstrip t) heq
    have htimeEq := rectangleArc_injOn hlr hheight (htime s) (htime t) hrect
    apply Subtype.ext
    linarith
  · intro t ht
    apply logarithmicDiskMap_mem_ball (width := width)
    refine ⟨(hstrip t).1, (hstrip t).2.1, ?_⟩
    apply rectangleArc_im_pos hheight
    constructor <;> linarith [ht.1, ht.2]

private theorem exists_injective_image_path
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hinj : InjOn g (ball 0 1)) {a b : ℂ} (source : Path a b)
    (hsource : Function.Injective source)
    (hinside : ∀ t : unitInterval, (t : ℝ) ∈ Ioo 0 1 → source t ∈ ball 0 1)
    {p q : ComplexSphere.Sphere}
    (hp : p ∈ frontier (ComplexSphere.chart '' (g '' ball 0 1)))
    (hq : q ∈ frontier (ComplexSphere.chart '' (g '' ball 0 1)))
    (hpq : p ≠ q)
    (hleft : Tendsto (fun t : ℝ => ComplexSphere.chart (g (source.extend t)))
      (𝓝[>] 0) (𝓝 p))
    (hright : Tendsto (fun t : ℝ => ComplexSphere.chart (g (source.extend t)))
      (𝓝[<] 1) (𝓝 q)) :
    ∃ image : Path p q, Function.Injective image ∧
      ∀ t : unitInterval, (t : ℝ) ∈ Ioo 0 1 →
        image t = ComplexSphere.chart (g (source t)) := by
  let φ : ℝ → ComplexSphere.Sphere := fun t =>
    ComplexSphere.chart (g (source.extend t))
  have hmap : MapsTo source.extend (Ioo (0 : ℝ) 1) (ball 0 1) := by
    intro t ht
    rw [Path.extend_extends' source ⟨t, ht.1.le, ht.2.le⟩]
    exact hinside ⟨t, ht.1.le, ht.2.le⟩ ht
  have hcontinuous : ContinuousOn φ (Ioo (0 : ℝ) 1) :=
    ComplexSphere.isEmbedding_chart.continuous.comp_continuousOn
      (hg.continuousOn.comp source.extend.continuous.continuousOn hmap)
  let image : Path p q := Path.ofLine
    (continuousOn_Icc_extendFrom_Ioo hcontinuous hleft hright)
    (eq_lim_at_left_extendFrom_Ioo zero_lt_one hleft)
    (eq_lim_at_right_extendFrom_Ioo zero_lt_one hright)
  have hagrees (t : unitInterval) (ht : (t : ℝ) ∈ Ioo 0 1) :
      image t = ComplexSphere.chart (g (source t)) := by
    change extendFrom (Ioo (0 : ℝ) 1) φ (t : ℝ) = _
    rw [extendFrom_extends hcontinuous _ ht]
    exact congrArg (fun z => ComplexSphere.chart (g z))
      (Path.extend_extends' source t)
  have hopenComplex : IsOpen (g '' ball 0 1) := by
    simpa only [range_domRestrict] using
      (isOpenMap_domRestrict_of_holomorphic_injOn isOpen_ball hg hinj).isOpen_range
  have hopenChart : IsOpen (range ComplexSphere.chart) := by
    rw [ComplexSphere.range_chart]
    exact isClosed_singleton.isOpen_compl
  have hopen : IsOpen (ComplexSphere.chart '' (g '' ball 0 1)) :=
    ComplexSphere.isEmbedding_chart.isInducing.isOpenMap hopenChart _ hopenComplex
  have hpnot : p ∉ ComplexSphere.chart '' (g '' ball 0 1) := by
    simpa only [hopen.interior_eq] using hp.2
  have hqnot : q ∉ ComplexSphere.chart '' (g '' ball 0 1) := by
    simpa only [hopen.interior_eq] using hq.2
  have hmem (t : unitInterval) (ht : (t : ℝ) ∈ Ioo 0 1) :
      image t ∈ ComplexSphere.chart '' (g '' ball 0 1) := by
    rw [hagrees t ht]
    exact ⟨_, ⟨_, hinside t ht, rfl⟩, rfl⟩
  have hcases (t : unitInterval) :
      t = 0 ∨ t = 1 ∨ (t : ℝ) ∈ Ioo 0 1 := by
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc t.property with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr h)
  refine ⟨image, ?_, hagrees⟩
  intro s t heq
  rcases hcases s with rfl | rfl | hs
  · rcases hcases t with rfl | rfl | ht
    · rfl
    · exact False.elim (hpq (by simpa using heq))
    · exact False.elim (hpnot (by simpa only [← heq, Path.source] using hmem t ht))
  · rcases hcases t with rfl | rfl | ht
    · exact False.elim (hpq (by simpa using heq.symm))
    · rfl
    · exact False.elim (hqnot (by simpa only [← heq, Path.target] using hmem t ht))
  · rcases hcases t with rfl | rfl | ht
    · exact False.elim (hpnot (by simpa only [heq, Path.source] using hmem s hs))
    · exact False.elim (hqnot (by simpa only [heq, Path.target] using hmem s hs))
    · rw [hagrees s hs, hagrees t ht] at heq
      exact hsource (hinj (hinside s hs) (hinside t ht)
        (ComplexSphere.isEmbedding_chart.injective heq))

private theorem exists_short_horizontal_chart_slice
    {f : ℂ → ℂ} {U : Set ℂ} {width : ℝ} (hwidth : 0 < width)
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    (hcontained : openComplexSquare width ⊆ U) :
    ∃ height ∈ Ioo 0 width,
      (∫⁻ x in Ioo 0 width, ENNReal.ofReal
        (sphericalDerivativeSpeed f (complexUnitLine ((height : ℂ) * I) 1 x))) ≤
      ENNReal.ofReal (2 * Real.sqrt (chartSquareEnergy f U width).toReal) := by
  let μ := volume.restrict (Ioo (0 : ℝ) width)
  let speed := chartRectangleSpeed f U
  have hswap :
      (∫⁻ point, speed point.swap ^ 2 ∂μ.prod μ) = chartSquareEnergy f U width :=
    lintegral_prod_swap (μ := μ) (ν := μ) (fun point => speed point ^ 2)
  have hfinite : (∫⁻ point, speed point.swap ^ 2 ∂μ.prod μ) ≠ ∞ := by
    rw [hswap]
    exact (chartSquareEnergy_lt_top hU hf hinj hcontained).ne
  have hlarge : μ univ / 4 < μ univ := by
    change volume.restrict (Ioo (0 : ℝ) width) univ / 4 <
      volume.restrict (Ioo (0 : ℝ) width) univ
    rw [Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero]
    rw [ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    simpa only [one_mul, mul_one, mul_comm] using ENNReal.mul_lt_mul_left
      (ENNReal.ofReal_pos.mpr hwidth).ne' ENNReal.ofReal_ne_top
      (show (1 : ℝ≥0∞) < 4 by norm_num)
  obtain ⟨height, _, hh, hshort⟩ := exists_short_slice_in_band_of_ae
    ((measurable_chartRectangleSpeed hU hf).comp measurable_swap)
    hfinite (ae_restrict_mem measurableSet_Ioo) hlarge
  simp only [Function.comp_def] at hshort
  change (∫⁻ x, speed (height, x).swap ∂μ) ≤
    ENNReal.ofReal (2 * Real.sqrt
      (∫⁻ point, speed point.swap ^ 2 ∂μ.prod μ).toReal) at hshort
  rw [hswap] at hshort
  refine ⟨height, hh, ?_⟩
  have heq :
      (∫⁻ x in Ioo 0 width, speed (x, height)) =
      ∫⁻ x in Ioo 0 width, ENNReal.ofReal
        (sphericalDerivativeSpeed f (complexUnitLine ((height : ℂ) * I) 1 x)) := by
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro x hx
    have hmem := hcontained ⟨(x, height), ⟨hx, hh⟩, rfl⟩
    change U.indicator _ (Complex.measurableEquivRealProd.symm (x, height)) = _
    rw [indicator_of_mem hmem]
    congr 2
    apply Complex.ext <;> simp [complexUnitLine, Complex.real_smul]
  rw [← heq]
  exact hshort

private theorem exists_logarithmic_three_sides
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hinj : InjOn g (ball 0 1)) {width : ℝ} (hwidth : 0 < width)
    (hwidthPi : width < 2 * Real.pi) (angle : ℝ)
    (forbidden : Finset ComplexSphere.Sphere) :
    ∃ left ∈ Ioo 0 (width / 2), ∃ right ∈ Ioo (width / 2) width,
      ∃ height ∈ Ioo 0 width, ∃ p q : ComplexSphere.Sphere,
        p ∈ frontier (ComplexSphere.chart '' (g '' ball 0 1)) ∧
        q ∈ frontier (ComplexSphere.chart '' (g '' ball 0 1)) ∧
        p ∉ forbidden ∧ q ∉ forbidden ∧ p ≠ q ∧
        Tendsto (fun r : ℝ => ComplexSphere.chart
          (g ((r : ℂ) * Complex.exp (((angle + left : ℝ) : ℂ) * I))))
          (𝓝[<] 1) (𝓝 p) ∧
        Tendsto (fun r : ℝ => ComplexSphere.chart
          (g ((r : ℂ) * Complex.exp (((angle + right : ℝ) : ℂ) * I))))
          (𝓝[<] 1) (𝓝 q) ∧
        (∫⁻ t in Ioo 0 width, ENNReal.ofReal
          (sphericalDerivativeSpeed (fun w => g (logarithmicDiskMap angle w))
            (complexUnitLine (left : ℂ) I t))) ≤
          ENNReal.ofReal (2 * Real.sqrt
            (chartSquareEnergy (fun w => g (logarithmicDiskMap angle w))
              (logarithmicStrip width) width).toReal) ∧
        (∫⁻ t in Ioo 0 width, ENNReal.ofReal
          (sphericalDerivativeSpeed (fun w => g (logarithmicDiskMap angle w))
            (complexUnitLine (right : ℂ) I t))) ≤
          ENNReal.ofReal (2 * Real.sqrt
            (chartSquareEnergy (fun w => g (logarithmicDiskMap angle w))
              (logarithmicStrip width) width).toReal) ∧
        (∫⁻ x in Ioo 0 width, ENNReal.ofReal
          (sphericalDerivativeSpeed (fun w => g (logarithmicDiskMap angle w))
            (complexUnitLine ((height : ℂ) * I) 1 x))) ≤
          ENNReal.ofReal (2 * Real.sqrt
            (chartSquareEnergy (fun w => g (logarithmicDiskMap angle w))
              (logarithmicStrip width) width).toReal) := by
  classical
  have hleftBand : Ioo (0 : ℝ) (width / 2) ⊆ Ioo 0 width := by
    intro x hx
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hrightBand : Ioo (width / 2) width ⊆ Ioo 0 width := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hquarter : ENNReal.ofReal width / 4 < ENNReal.ofReal (width / 2) := by
    have heq : ENNReal.ofReal width / 4 = ENNReal.ofReal (width / 4) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
      norm_num
    rw [heq]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < width / 2)).mpr
      (by linarith)
  have hleftLarge : ENNReal.ofReal width / 4 <
      (volume.restrict (Ioo (0 : ℝ) width)) (Ioo 0 (width / 2)) := by
    rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr hleftBand,
      Real.volume_Ioo, sub_zero]
    exact hquarter
  have hrightLarge : ENNReal.ofReal width / 4 <
      (volume.restrict (Ioo (0 : ℝ) width)) (Ioo (width / 2) width) := by
    rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr hrightBand,
      Real.volume_Ioo, show width - width / 2 = width / 2 by ring]
    exact hquarter
  obtain ⟨left, hleft, p, hp, hpavoid, hplimit, hleftShort⟩ :=
    exists_short_logarithmic_slice_avoiding hg hinj hwidthPi angle forbidden
      hleftBand hleftLarge
  obtain ⟨right, hright, q, hq, hqavoid, hqlimit, hrightShort⟩ :=
    exists_short_logarithmic_slice_avoiding hg hinj hwidthPi angle (insert p forbidden)
      hrightBand hrightLarge
  let f : ℂ → ℂ := fun w => g (logarithmicDiskMap angle w)
  have hf : DifferentiableOn ℂ f (logarithmicStrip width) :=
    hg.comp (differentiable_logarithmicDiskMap angle).differentiableOn
      (fun _ hw => logarithmicDiskMap_mem_ball hw)
  have hi : InjOn f (logarithmicStrip width) :=
    hinj.comp (logarithmicDiskMap_injOn hwidthPi angle)
      (fun _ hw => logarithmicDiskMap_mem_ball hw)
  obtain ⟨height, hheight, hhorizontal⟩ := exists_short_horizontal_chart_slice
    hwidth (isOpen_logarithmicStrip width) hf hi
    (openComplexSquare_subset_logarithmicStrip width)
  have hpq : p ≠ q := by
    intro heq
    apply hqavoid
    rw [← heq]
    exact Finset.mem_insert_self _ _
  exact ⟨left, hleft, right, hright, height, hheight, p, q,
    hp, hq, hpavoid, fun hmem => hqavoid (Finset.mem_insert_of_mem hmem),
    hpq, hplimit, hqlimit, hleftShort, hrightShort, hhorizontal⟩

private theorem exists_small_logarithmic_square
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hinj : InjOn g (ball 0 1)) (angle : ℝ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ width ∈ Ioo (0 : ℝ) 1,
      chartSquareEnergy (fun w => g (logarithmicDiskMap (angle - width / 2) w))
        (logarithmicStrip width) width < ε ∧
      ∀ z : ℂ, z.re ∈ Icc 0 width → z.im ∈ Icc 0 width →
        dist (logarithmicDiskMap (angle - width / 2) z)
          (Complex.exp ((angle : ℂ) * I)) < δ := by
  let f : ℂ → ℂ := fun w => g (logarithmicDiskMap (angle - 1) w)
  have htwo : (2 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hf : DifferentiableOn ℂ f (logarithmicStrip 2) :=
    hg.comp (differentiable_logarithmicDiskMap (angle - 1)).differentiableOn
      (fun _ hw => logarithmicDiskMap_mem_ball hw)
  have hi : InjOn f (logarithmicStrip 2) :=
    hinj.comp (logarithmicDiskMap_injOn htwo (angle - 1))
      (fun _ hw => logarithmicDiskMap_mem_ball hw)
  have hcenter : logarithmicDiskMap (angle - 1) (1 : ℂ) =
      Complex.exp ((angle : ℂ) * I) := by
    simpa [complexUnitLine] using logarithmicDiskMap_unitLine (angle - 1) 1 0
  obtain ⟨η, hη, hclose⟩ := Metric.continuousAt_iff.mp
    ((differentiable_logarithmicDiskMap (angle - 1)).continuous.continuousAt
      (x := (1 : ℂ))) δ hδ
  obtain ⟨r, hr, henergy⟩ := exists_ball_spherical_energy_lt
    (isOpen_logarithmicStrip 2) hf hi (1 : ℂ) hε (lt_min hη zero_lt_one)
  let width := r / 4
  have hw : width ∈ Ioo (0 : ℝ) 1 := by
    dsimp [width]
    constructor <;> linarith [hr.1, hr.2, min_le_right η 1]
  let shift : ℂ := ((1 - width / 2 : ℝ) : ℂ)
  have htranslate (z : ℂ) : logarithmicDiskMap (angle - width / 2) z =
      logarithmicDiskMap (angle - 1) (z + shift) := by
    unfold logarithmicDiskMap
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    dsimp [shift]
    push_cast
    ring
  have hnear (z : ℂ) (hx : z.re ∈ Icc 0 width) (hy : z.im ∈ Icc 0 width) :
      z + shift ∈ ball (1 : ℂ) r := by
    rw [mem_ball, dist_eq_norm]
    have hxabs : |z.re - width / 2| ≤ width / 2 := abs_le.mpr (by
      constructor <;> linarith [hx.1, hx.2])
    have hyabs : |z.im| ≤ width := by
      rw [abs_of_nonneg hy.1]
      exact hy.2
    have hnorm := Complex.norm_le_abs_re_add_abs_im (z + shift - 1)
    have hre : (z + shift - 1).re = z.re - width / 2 := by
      simp only [shift, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
        Complex.one_re]
      ring
    have him : (z + shift - 1).im = z.im := by simp [shift]
    rw [hre, him] at hnorm
    have hsum : ‖z + shift - 1‖ ≤ width / 2 + width :=
      hnorm.trans (add_le_add hxabs hyabs)
    dsimp [width] at hsum
    linarith [hr.1]
  refine ⟨width, hw, ?_, ?_⟩
  · have hfun : (fun w => g (logarithmicDiskMap (angle - width / 2) w)) =
        (fun w => f (w + shift)) := funext fun w => congrArg g (htranslate w)
    rw [hfun, chartSquareEnergy_comp_add_const shift
      (openComplexSquare_subset_logarithmicStrip width)]
    apply lt_of_le_of_lt (lintegral_mono_set ?_) henergy
    rintro _ ⟨z, ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩, rfl⟩
    refine ⟨hnear _ ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩, ?_⟩
    simp only [logarithmicStrip, Set.mem_ofPred_eq, shift,
      Complex.measurableEquivRealProd_symm_apply, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, add_zero]
    exact ⟨by linarith [hw.2, hx.1], by linarith [hw.2, hx.2], hy.1⟩
  · intro z hx hy
    rw [htranslate, ← hcenter]
    apply hclose
    have hdistance : dist (z + shift) (1 : ℂ) < r := hnear z hx hy
    exact hdistance.trans (hr.2.trans_le (min_le_left η 1))

private theorem logarithmic_unitLine_tendsto_of_radial
    {g : ℂ → ℂ} {angle x : ℝ} {endpoint : ComplexSphere.Sphere}
    (hlimit : Tendsto (fun r : ℝ => ComplexSphere.chart
      (g ((r : ℂ) * Complex.exp (((angle + x : ℝ) : ℂ) * I))))
      (𝓝[<] 1) (𝓝 endpoint)) :
    Tendsto (fun t : ℝ => ComplexSphere.chart
      (g (logarithmicDiskMap angle (complexUnitLine (x : ℂ) I t))))
      (𝓝[>] 0) (𝓝 endpoint) := by
  have hradius : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[>] 0) (𝓝[<] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun t : ℝ => Real.exp (-t)) := by fun_prop
      have ht := hc.continuousAt (x := (0 : ℝ))
      simpa only [neg_zero, Real.exp_zero] using
        ht.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)
  simpa only [Function.comp_def, logarithmicDiskMap_unitLine] using hlimit.comp hradius

private theorem rectangle_image_endpoint_limits
    {g : ℂ → ℂ} {left right height angle : ℝ} (hh : 0 < height)
    {a b : ℂ} (source : Path a b)
    (hsource : ∀ t : unitInterval, source t = logarithmicDiskMap angle
      (rectangleArc left right height (3 * (t : ℝ))))
    {p q : ComplexSphere.Sphere}
    (hp : Tendsto (fun r : ℝ => ComplexSphere.chart
      (g ((r : ℂ) * Complex.exp (((angle + left : ℝ) : ℂ) * I))))
      (𝓝[<] 1) (𝓝 p))
    (hq : Tendsto (fun r : ℝ => ComplexSphere.chart
      (g ((r : ℂ) * Complex.exp (((angle + right : ℝ) : ℂ) * I))))
      (𝓝[<] 1) (𝓝 q)) :
    Tendsto (fun t : ℝ => ComplexSphere.chart (g (source.extend t)))
      (𝓝[>] 0) (𝓝 p) ∧
    Tendsto (fun t : ℝ => ComplexSphere.chart (g (source.extend t)))
      (𝓝[<] 1) (𝓝 q) := by
  have hleftTime : Tendsto (fun t : ℝ => height * (3 * t))
      (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun t : ℝ => height * (3 * t)) := by fun_prop
      simpa only [mul_zero] using hc.continuousAt.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos hh (mul_pos (by norm_num) ht)
  have hrightTime : Tendsto (fun t : ℝ => height * (3 - 3 * t))
      (𝓝[<] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun t : ℝ => height * (3 - 3 * t)) := by fun_prop
      simpa only [mul_one, sub_self, mul_zero] using hc.continuousAt.tendsto.mono_left
        (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change t < 1 at ht
      exact mul_pos hh (by linarith)
  constructor
  · apply ((logarithmic_unitLine_tendsto_of_radial hp).comp hleftTime).congr'
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 / 3 from
        nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 3)))]
      with t ht hsmall
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.le, by linarith⟩
    rw [Path.extend_extends' source ⟨t, htI⟩, hsource]
    simp only [Function.comp_def, rectangleArc, ite_eq_left (show 3 * t ≤ 1 by linarith),
      complexUnitLine, Complex.real_smul]
  · apply ((logarithmic_unitLine_tendsto_of_radial hq).comp hrightTime).congr'
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ t : ℝ in 𝓝[<] 1, 2 / 3 < t from
        nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (2 : ℝ) / 3 < 1)))]
      with t ht hlarge
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith, ht.le⟩
    rw [Path.extend_extends' source ⟨t, htI⟩, hsource]
    simp only [Function.comp_def, rectangleArc,
      ite_eq_right (show ¬3 * t ≤ 1 by linarith),
      ite_eq_right (show ¬3 * t ≤ 2 by linarith),
      complexUnitLine, Complex.real_smul]

private theorem ediam_image_Icc_le_of_open_chords
    {X : Type*} [PseudoEMetricSpace X] {f : unitInterval → X}
    (hf : Continuous f) {a b : unitInterval} (hab : a < b)
    {bound : ℝ≥0∞}
    (hbound : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, edist (f s) (f t) ≤ bound) :
    Metric.ediam (f '' Icc a b) ≤ bound := by
  calc
    Metric.ediam (f '' Icc a b) =
        Metric.ediam (f '' closure (Ioo a b)) := by rw [closure_Ioo hab.ne]
    _ ≤ Metric.ediam (closure (f '' Ioo a b)) :=
      Metric.ediam_mono (image_closure_subset_closure_image hf)
    _ = Metric.ediam (f '' Ioo a b) := Metric.ediam_closure _
    _ ≤ bound := by
      apply Metric.ediam_le
      rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
      exact hbound s hs t ht

private theorem rectangle_image_ediam_le
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {left right height width : ℝ} (hleft : 0 < left) (hlr : left < right)
    (hright : right < width) (hheight : 0 < height) (hheightWidth : height < width)
    (hcontained : openComplexSquare width ⊆ U)
    {p q : ComplexSphere.Sphere} (image : Path p q)
    (hformula : ∀ t : unitInterval, (t : ℝ) ∈ Ioo 0 1 →
      image t = ComplexSphere.chart (f (rectangleArc left right height (3 * (t : ℝ)))))
    {bound : ℝ≥0∞} (hbound : bound ≠ ∞)
    (hleftShort : (∫⁻ t in Ioo 0 width, ENNReal.ofReal
      (sphericalDerivativeSpeed f (complexUnitLine (left : ℂ) I t))) ≤ bound)
    (hrightShort : (∫⁻ t in Ioo 0 width, ENNReal.ofReal
      (sphericalDerivativeSpeed f (complexUnitLine (right : ℂ) I t))) ≤ bound)
    (hhorizontal : (∫⁻ x in Ioo 0 width, ENNReal.ofReal
      (sphericalDerivativeSpeed f (complexUnitLine ((height : ℂ) * I) 1 x))) ≤ bound) :
    Metric.ediam (range image) ≤ bound + bound + bound := by
  have hvertical (x : ℝ) (hx : x ∈ Ioo 0 width) :
      MapsTo (complexUnitLine (x : ℂ) I) (Ioo 0 width) U := by
    intro t ht
    have heq : complexUnitLine (x : ℂ) I t =
        Complex.measurableEquivRealProd.symm (x, t) := by
      apply Complex.ext <;> simp [complexUnitLine, Complex.real_smul]
    rw [heq]
    exact hcontained ⟨(x, t), ⟨hx, ht⟩, rfl⟩
  have hhorizontalLine : MapsTo (complexUnitLine ((height : ℂ) * I) 1)
      (Ioo 0 width) U := by
    intro x hx
    have heq : complexUnitLine ((height : ℂ) * I) 1 x =
        Complex.measurableEquivRealProd.symm (x, height) := by
      apply Complex.ext <;> simp [complexUnitLine, Complex.real_smul]
    rw [heq]
    exact hcontained ⟨(x, height), ⟨hx, hheight, hheightWidth⟩, rfl⟩
  have hleftLine := hvertical left ⟨hleft, hlr.trans hright⟩
  have hrightLine := hvertical right ⟨hleft.trans hlr, hright⟩
  have hleftInt := integrableOn_sphericalDerivativeSpeed_unitLine_of_lintegral_ne_top
    hU hf hleftLine (ne_top_of_le_ne_top hbound hleftShort)
  have hrightInt := integrableOn_sphericalDerivativeSpeed_unitLine_of_lintegral_ne_top
    hU hf hrightLine (ne_top_of_le_ne_top hbound hrightShort)
  have hhorizontalInt := integrableOn_sphericalDerivativeSpeed_unitLine_of_lintegral_ne_top
    hU hf hhorizontalLine (ne_top_of_le_ne_top hbound hhorizontal)
  let cut₁ : unitInterval := ⟨1 / 3, by norm_num, by norm_num⟩
  let cut₂ : unitInterval := ⟨2 / 3, by norm_num, by norm_num⟩
  have hcut₁ : (0 : unitInterval) < cut₁ := by change (0 : ℝ) < 1 / 3; norm_num
  have hcuts : cut₁ < cut₂ := by change (1 : ℝ) / 3 < 2 / 3; norm_num
  have hcut₂ : cut₂ < (1 : unitInterval) := by change (2 : ℝ) / 3 < 1; norm_num
  have hL : Metric.ediam (image '' Icc 0 cut₁) ≤ bound := by
    apply ediam_image_Icc_le_of_open_chords image.continuous hcut₁
    intro s hs t ht
    change (0 : ℝ) < (s : ℝ) ∧ (s : ℝ) < 1 / 3 at hs
    change (0 : ℝ) < (t : ℝ) ∧ (t : ℝ) < 1 / 3 at ht
    have heq (u : unitInterval) (hu : (u : ℝ) ∈ Ioo 0 (1 / 3)) :
        image u = ComplexSphere.chart
          (f (complexUnitLine (left : ℂ) I (height * (3 * (u : ℝ))))) := by
      rw [hformula u ⟨hu.1, by linarith [hu.2]⟩]
      simp only [rectangleArc, ite_eq_left (show 3 * (u : ℝ) ≤ 1 by linarith [hu.2]),
        complexUnitLine, Complex.real_smul]
    have hs' : height * (3 * (s : ℝ)) ∈ Ioo 0 width := by
      constructor <;> nlinarith [hs.1, hs.2]
    have ht' : height * (3 * (t : ℝ)) ∈ Ioo 0 width := by
      constructor <;> nlinarith [ht.1, ht.2]
    rw [heq s hs, heq t ht]
    exact (edist_sphere_holomorphic_unitLine_le_lintegral
      ComplexSphere.pole ComplexSphere.plane ComplexSphere.norm_pole
      ComplexSphere.pole_orthogonal_plane hU hf (by simp) hleftLine hleftInt
      ⟨_, hs'⟩ ⟨_, ht'⟩).trans ((setLIntegral_le_lintegral _ _).trans hleftShort)
  have hM : Metric.ediam (image '' Icc cut₁ cut₂) ≤ bound := by
    apply ediam_image_Icc_le_of_open_chords image.continuous hcuts
    intro s hs t ht
    change (1 : ℝ) / 3 < (s : ℝ) ∧ (s : ℝ) < 2 / 3 at hs
    change (1 : ℝ) / 3 < (t : ℝ) ∧ (t : ℝ) < 2 / 3 at ht
    have heq (u : unitInterval) (hu : (u : ℝ) ∈ Ioo (1 / 3) (2 / 3)) :
        image u = ComplexSphere.chart (f (complexUnitLine ((height : ℂ) * I) 1
          (left + (right - left) * (3 * (u : ℝ) - 1)))) := by
      rw [hformula u ⟨by linarith [hu.1], by linarith [hu.2]⟩]
      simp only [rectangleArc, ite_eq_right (show ¬3 * (u : ℝ) ≤ 1 by linarith [hu.1]),
        ite_eq_left (show 3 * (u : ℝ) ≤ 2 by linarith [hu.2]),
        complexUnitLine, Complex.real_smul, mul_one, add_comm]
    have hs' : left + (right - left) * (3 * (s : ℝ) - 1) ∈ Ioo 0 width := by
      constructor <;> nlinarith [hs.1, hs.2]
    have ht' : left + (right - left) * (3 * (t : ℝ) - 1) ∈ Ioo 0 width := by
      constructor <;> nlinarith [ht.1, ht.2]
    rw [heq s hs, heq t ht]
    exact (edist_sphere_holomorphic_unitLine_le_lintegral
      ComplexSphere.pole ComplexSphere.plane ComplexSphere.norm_pole
      ComplexSphere.pole_orthogonal_plane hU hf (by simp) hhorizontalLine hhorizontalInt
      ⟨_, hs'⟩ ⟨_, ht'⟩).trans ((setLIntegral_le_lintegral _ _).trans hhorizontal)
  have hR : Metric.ediam (image '' Icc cut₂ 1) ≤ bound := by
    apply ediam_image_Icc_le_of_open_chords image.continuous hcut₂
    intro s hs t ht
    change (2 : ℝ) / 3 < (s : ℝ) ∧ (s : ℝ) < 1 at hs
    change (2 : ℝ) / 3 < (t : ℝ) ∧ (t : ℝ) < 1 at ht
    have heq (u : unitInterval) (hu : (u : ℝ) ∈ Ioo (2 / 3) 1) :
        image u = ComplexSphere.chart
          (f (complexUnitLine (right : ℂ) I (height * (3 - 3 * (u : ℝ))))) := by
      rw [hformula u ⟨by linarith [hu.1], hu.2⟩]
      simp only [rectangleArc, ite_eq_right (show ¬3 * (u : ℝ) ≤ 1 by linarith [hu.1]),
        ite_eq_right (show ¬3 * (u : ℝ) ≤ 2 by linarith [hu.1]),
        complexUnitLine, Complex.real_smul]
    have hs' : height * (3 - 3 * (s : ℝ)) ∈ Ioo 0 width := by
      constructor <;> nlinarith [hs.1, hs.2]
    have ht' : height * (3 - 3 * (t : ℝ)) ∈ Ioo 0 width := by
      constructor <;> nlinarith [ht.1, ht.2]
    rw [heq s hs, heq t ht]
    exact (edist_sphere_holomorphic_unitLine_le_lintegral
      ComplexSphere.pole ComplexSphere.plane ComplexSphere.norm_pole
      ComplexSphere.pole_orthogonal_plane hU hf (by simp) hrightLine hrightInt
      ⟨_, hs'⟩ ⟨_, ht'⟩).trans ((setLIntegral_le_lintegral _ _).trans hrightShort)
  have hcover : range image =
      (image '' Icc 0 cut₁ ∪ image '' Icc cut₁ cut₂) ∪ image '' Icc cut₂ 1 := by
    apply Subset.antisymm
    · rintro _ ⟨t, rfl⟩
      by_cases ht : t ≤ cut₁
      · exact Or.inl (Or.inl ⟨t, ⟨t.property.1, ht⟩, rfl⟩)
      · by_cases ht' : t ≤ cut₂
        · exact Or.inl (Or.inr ⟨t, ⟨(not_le.mp ht).le, ht'⟩, rfl⟩)
        · exact Or.inr ⟨t, ⟨(not_le.mp ht').le, t.property.2⟩, rfl⟩
    · rintro _ ((⟨t, _, rfl⟩ | ⟨t, _, rfl⟩) | ⟨t, _, rfl⟩) <;> exact mem_range_self t
  have hmeet₁ : ((image '' Icc 0 cut₁) ∩ (image '' Icc cut₁ cut₂)).Nonempty :=
    ⟨image cut₁, ⟨cut₁, ⟨hcut₁.le, le_rfl⟩, rfl⟩,
      ⟨cut₁, ⟨le_rfl, hcuts.le⟩, rfl⟩⟩
  have hmeet₂ : ((image '' Icc 0 cut₁ ∪ image '' Icc cut₁ cut₂) ∩
      (image '' Icc cut₂ 1)).Nonempty :=
    ⟨image cut₂, Or.inr ⟨cut₂, ⟨hcuts.le, le_rfl⟩, rfl⟩,
      ⟨cut₂, ⟨le_rfl, hcut₂.le⟩, rfl⟩⟩
  rw [hcover]
  exact (Metric.ediam_union_le hmeet₂).trans
    (add_le_add ((Metric.ediam_union_le hmeet₁).trans (add_le_add hL hM)) hR)

/-- A local embedded three-side arc with actual small spherical image. The two
boundary arguments lie in opposite bands around the prescribed argument.
Neither boundary injectivity nor boundedness of the original map is assumed.
This is a local arc, not a nested crosscut sequence or a separation theorem. -/
theorem exists_short_embedded_spherical_image_arc
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hinj : InjOn g (ball 0 1)) (angle : ℝ)
    {sourceTolerance imageTolerance : ℝ}
    (hsourceTolerance : 0 < sourceTolerance) (himageTolerance : 0 < imageTolerance)
    (forbidden : Finset ComplexSphere.Sphere) :
    ∃ width ∈ Ioo (0 : ℝ) 1,
      ∃ left ∈ Ioo (angle - width / 2) angle,
      ∃ right ∈ Ioo angle (angle + width / 2),
      ∃ p q : ComplexSphere.Sphere,
      ∃ source : Path (Complex.exp ((left : ℂ) * I))
        (Complex.exp ((right : ℂ) * I)), ∃ image : Path p q,
        Topology.IsClosedEmbedding source ∧ Topology.IsClosedEmbedding image ∧
        p ∈ frontier (ComplexSphere.chart '' (g '' ball 0 1)) ∧
        q ∈ frontier (ComplexSphere.chart '' (g '' ball 0 1)) ∧
        p ∉ forbidden ∧ q ∉ forbidden ∧ p ≠ q ∧
        (∀ t : unitInterval, (t : ℝ) ∈ Ioo 0 1 →
          source t ∈ ball 0 1 ∧ image t = ComplexSphere.chart (g (source t))) ∧
        (∀ t : unitInterval,
          dist (source t) (Complex.exp ((angle : ℂ) * I)) < sourceTolerance) ∧
        Metric.ediam (range source) < ENNReal.ofReal sourceTolerance ∧
        Metric.ediam (range image) < ENNReal.ofReal imageTolerance := by
  classical
  have henergyPositive : ENNReal.ofReal ((imageTolerance / 12) ^ 2) ≠ 0 := by
    positivity
  obtain ⟨width, hw, henergy, hclose⟩ := exists_small_logarithmic_square
    hg hinj angle henergyPositive (show 0 < sourceTolerance / 4 by positivity)
  have hwidthPi : width < 2 * Real.pi := by linarith [hw.2, Real.pi_gt_three]
  let offset := angle - width / 2
  let f : ℂ → ℂ := fun w => g (logarithmicDiskMap offset w)
  let energy := chartSquareEnergy f (logarithmicStrip width) width
  let bound := ENNReal.ofReal (2 * Real.sqrt energy.toReal)
  obtain ⟨left, hl, right, hr, height, hh, p, q, hp, hq, hpavoid, hqavoid,
      hpq, hplimit, hqlimit, hleftShort, hrightShort, hhorizontal⟩ :=
    exists_logarithmic_three_sides hg hinj hw.1 hwidthPi offset forbidden
  have hlr : left < right := hl.2.trans hr.1
  obtain ⟨source, hsourceInj, hinside, hsource⟩ :=
    exists_rectangle_source_path hl.1 hlr hr.2 hh.1 hwidthPi offset
  have hlimits := rectangle_image_endpoint_limits hh.1 source hsource hplimit hqlimit
  obtain ⟨image, himageInj, hagrees⟩ := exists_injective_image_path
    hg hinj source hsourceInj hinside hp hq hpq hlimits.1 hlimits.2
  have hf : DifferentiableOn ℂ f (logarithmicStrip width) :=
    hg.comp (differentiable_logarithmicDiskMap offset).differentiableOn
      (fun _ hz => logarithmicDiskMap_mem_ball hz)
  have hformula (t : unitInterval) (ht : (t : ℝ) ∈ Ioo 0 1) :
      image t = ComplexSphere.chart (f (rectangleArc left right height (3 * (t : ℝ)))) := by
    rw [hagrees t ht, hsource t]
  have himageBound : Metric.ediam (range image) ≤ bound + bound + bound :=
    rectangle_image_ediam_le (isOpen_logarithmicStrip width) hf hl.1 hlr hr.2 hh.1 hh.2
      (openComplexSquare_subset_logarithmicStrip width) image hformula
      ENNReal.ofReal_ne_top hleftShort hrightShort hhorizontal
  have he : energy < ENNReal.ofReal ((imageTolerance / 12) ^ 2) := henergy
  have hefinite : energy ≠ ∞ := ne_top_of_lt he
  have hereal : energy.toReal < (imageTolerance / 12) ^ 2 := by
    have h := (ENNReal.toReal_lt_toReal hefinite ENNReal.ofReal_ne_top).mpr he
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using h
  have hsqrt : Real.sqrt energy.toReal < imageTolerance / 12 :=
    (Real.sqrt_lt ENNReal.toReal_nonneg (by positivity)).mpr hereal
  have hboundSmall : bound + bound + bound < ENNReal.ofReal imageTolerance := by
    have hn : 0 ≤ 2 * Real.sqrt energy.toReal := by positivity
    change ENNReal.ofReal _ + ENNReal.ofReal _ + ENNReal.ofReal _ < _
    rw [← ENNReal.ofReal_add hn hn, ← ENNReal.ofReal_add (add_nonneg hn hn) hn]
    exact (ENNReal.ofReal_lt_ofReal_iff himageTolerance).mpr (by linarith)
  have hsourceClose (t : unitInterval) :
      dist (source t) (Complex.exp ((angle : ℂ) * I)) < sourceTolerance / 4 := by
    have ht : 3 * (t : ℝ) ∈ Icc (0 : ℝ) 3 := by
      constructor <;> linarith [t.property.1, t.property.2]
    have hc := rectangleArc_coordinates hlr hh.1 ht
    rw [hsource t]
    exact hclose _ ⟨le_trans hl.1.le hc.1.1, hc.1.2.trans hr.2.le⟩
      ⟨hc.2.1, hc.2.2.trans hh.2.le⟩
  have hsourceBound : Metric.ediam (range source) ≤
      ENNReal.ofReal (sourceTolerance / 2) := by
    apply Metric.ediam_le
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    have htri := dist_triangle_right (source s) (source t)
      (Complex.exp ((angle : ℂ) * I))
    linarith [hsourceClose s, hsourceClose t]
  have hleftBand : offset + left ∈ Ioo (angle - width / 2) angle := by
    dsimp [offset]
    constructor <;> linarith [hl.1, hl.2]
  have hrightBand : offset + right ∈ Ioo angle (angle + width / 2) := by
    dsimp [offset]
    constructor <;> linarith [hr.1, hr.2]
  refine ⟨width, hw, offset + left, hleftBand, offset + right, hrightBand,
    p, q, source, image, source.continuous.isClosedEmbedding hsourceInj,
    image.continuous.isClosedEmbedding himageInj, hp, hq, hpavoid, hqavoid, hpq,
    ?_, ?_, ?_, himageBound.trans_lt hboundSmall⟩
  · exact fun t ht => ⟨hinside t ht, hagrees t ht⟩
  · intro t
    linarith [hsourceClose t]
  · exact hsourceBound.trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hsourceTolerance).mpr (by linarith))

end Math.ComplexAnalysis
