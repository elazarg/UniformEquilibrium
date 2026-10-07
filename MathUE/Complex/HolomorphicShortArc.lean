module

public import MathUE.Complex.HolomorphicRadialLandingFibers
public import MathUE.Complex.HolomorphicRectangleLengthArea
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Order.Filter.Finite
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Convex.PathConnected
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
  have hselected : ∃ x ∈ band, P x ∧ slice x ≤ threshold := by
    by_cases hzero : energy = 0
    · have hslices := RectangleLengthArea.slice_eq_zero_ae_of_energy_zero
        (μ := μ) (ν := μ)
        (measurable_chartRectangleSpeed (isOpen_logarithmicStrip width) hf) hzero
      have hpositive : μ band ≠ 0 := (lt_of_le_of_lt zero_le hlarge).ne'
      obtain ⟨x, hx, hPx, hslice⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
        hpositive (ae_restrict_of_ae (hP.and hslices))
      exact ⟨x, hx, hPx, by change slice x = 0 at hslice; rw [hslice]; exact zero_le⟩
    · have hlong := chart_long_slices_le_quarter (isOpen_logarithmicStrip width) hf hi
        (openComplexSquare_subset_logarithmicStrip width) hzero
      by_contra hnot
      have hsubset : band ≤ᵐ[μ] {x | threshold ≤ slice x} := by
        filter_upwards [hP] with x hx hmem
        exact (lt_of_not_ge (fun hle => hnot ⟨x, hmem, hx, hle⟩)).le
      exact hlarge.not_ge ((measure_mono_ae hsubset).trans hlong)
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

private theorem injective_path_trans
    {X : Type*} [TopologicalSpace X] {a b c : X}
    (left : Path a b) (right : Path b c)
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hmeet : ∀ s t, left s = right t → s = 1 ∧ t = 0) :
    Function.Injective (left.trans right) := by
  intro s t heq
  rw [Path.trans_apply, Path.trans_apply] at heq
  split_ifs at heq with hs ht ht
  · have h := congrArg Subtype.val (hleft heq)
    apply Subtype.ext
    dsimp only at h
    linarith
  · obtain ⟨hleftEnd, hrightEnd⟩ := hmeet _ _ heq
    have hl := congrArg Subtype.val hleftEnd
    have hr := congrArg Subtype.val hrightEnd
    change (2 : ℝ) * (s : ℝ) = 1 at hl
    change (2 : ℝ) * (t : ℝ) - 1 = 0 at hr
    apply Subtype.ext
    linarith
  · obtain ⟨hleftEnd, hrightEnd⟩ := hmeet _ _ heq.symm
    have hl := congrArg Subtype.val hleftEnd
    have hr := congrArg Subtype.val hrightEnd
    change (2 : ℝ) * (t : ℝ) = 1 at hl
    change (2 : ℝ) * (s : ℝ) - 1 = 0 at hr
    apply Subtype.ext
    linarith
  · have h := congrArg Subtype.val (hright heq)
    apply Subtype.ext
    dsimp only at h
    linarith

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

end Math.ComplexAnalysis
