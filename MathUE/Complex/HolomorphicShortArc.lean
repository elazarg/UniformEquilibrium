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

end Math.ComplexAnalysis
