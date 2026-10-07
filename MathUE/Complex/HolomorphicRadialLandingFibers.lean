module

public import MathUE.Complex.HolomorphicRadialFrontier
public import MathUE.Complex.UnivalentDiskBoundedization
public import MathUE.Complex.RadialSequenceUniqueness
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Separation.Basic

/-! # Null fibers of actual spherical radial landing

Milnor §15.3: square-root/Möbius boundedization and the Riesz uniqueness
theorem exclude positive-measure fibers of every fixed spherical endpoint.
The finite-target polynomial retains the actual algebraic boundedization;
the pole case uses compact chart images, not a finite complex endpoint.
No measurability of the landing set is assumed. This is not a crosscut,
Jordan separation, or continuous boundary-extension theorem.
-/

public section
noncomputable section
namespace Math.ComplexSphere

open Metric Set Filter
open scoped Topology InnerProductSpace

theorem range_chart : range chart = {north}ᶜ := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    exact chart_ne_north z
  · intro p hp
    obtain ⟨w, hw⟩ :=
      (range_stereographic_symm norm_pole (by simpa using norm_pole)).symm ▸ hp
    have hwzero : (WithLp.ofLp (w : Ambient)).2 = 0 := by
      have h := Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property
      simpa [pole, WithLp.prod_inner_apply] using h
    refine ⟨(WithLp.ofLp (w : Ambient)).1 / 2, ?_⟩
    have hscaled : (2 : ℝ) • plane ((WithLp.ofLp (w : Ambient)).1 / 2) =
        (w : Ambient) := by
      apply (WithLp.linearEquiv 2 ℝ (ℂ × ℝ)).injective
      apply Prod.ext
      · change (2 : ℝ) • ((WithLp.ofLp (w : Ambient)).1 / 2) =
          (WithLp.ofLp (w : Ambient)).1
        norm_num [Complex.real_smul]
        ring
      · change (2 : ℝ) * 0 = (WithLp.ofLp (w : Ambient)).2
        simpa only [mul_zero] using hwzero.symm
    change stereoInvFun norm_pole _ = p
    change stereoInvFun norm_pole w = p at hw
    rw [← hw]
    congr 1
    exact Subtype.ext hscaled

theorem norm_tendsto_atTop_of_chart_tendsto_north
    {ι : Type*} {l : Filter ι} {f : ι → ℂ}
    (h : Tendsto (fun i => chart (f i)) l (𝓝 north)) :
    Tendsto (fun i => ‖f i‖) l atTop := by
  apply Filter.tendsto_atTop.2
  intro R
  have hball : IsCompact (closedBall (0 : ℂ) R) := isCompact_closedBall _ _
  have hc : IsCompact (chart '' closedBall (0 : ℂ) R) :=
    hball.image isEmbedding_chart.continuous
  have hn : north ∉ chart '' closedBall (0 : ℂ) R := by
    rintro ⟨z, _, hz⟩
    exact chart_ne_north z hz
  filter_upwards [h (hc.isClosed.isOpen_compl.mem_nhds hn)] with i hi
  have hout : f i ∉ closedBall (0 : ℂ) R := by
    intro hmem
    exact hi ⟨f i, hmem, rfl⟩
  exact (lt_of_not_ge (by simpa [mem_closedBall, dist_zero_right] using hout)).le

end Math.ComplexSphere
namespace Math.ComplexAnalysis

open Complex Filter Function MeasureTheory Metric Set
open scoped Topology ENNReal

private def fiberRadii (n : ℕ) : ℝ := 1 - ((n : ℝ) + 2)⁻¹

private theorem fiberRadii_bounds (n : ℕ) :
    (1 / 2 : ℝ) ≤ fiberRadii n ∧ fiberRadii n < 1 := by
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have hupper : ((n : ℝ) + 2)⁻¹ ≤ (2 : ℝ)⁻¹ :=
    (inv_le_inv₀ hden (by norm_num)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hpositive := inv_pos.mpr hden
  dsimp [fiberRadii]
  constructor <;> norm_num at hupper ⊢ <;> linarith

private theorem fiberRadii_tendsto :
    Tendsto fiberRadii atTop (𝓝[<] 1) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
      apply Filter.tendsto_atTop.2
      intro R
      filter_upwards [(tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop) (eventually_ge_atTop R)] with n hn
      change R ≤ (n : ℝ) at hn
      linarith
    have hinv := tendsto_inv_atTop_zero.comp hden
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
    simp only [Function.comp_def, sub_zero] at h
    convert! h using 1
  · exact Eventually.of_forall fun n => (fiberRadii_bounds n).2

theorem eqOn_zero_of_bounded_radial_limit_zero
    {H : ℂ → ℂ} (hH : DifferentiableOn ℂ H (ball 0 1))
    {B : ℝ} (hbound : ∀ z ∈ ball 0 1, ‖H z‖ ≤ B)
    {angles : Set ℝ}
    (hpositive : (volume.restrict (Ioc 0 (2 * Real.pi))) angles ≠ 0)
    (hzero : ∀ θ ∈ angles,
      Tendsto (fun r : ℝ => H ((r : ℂ) * Complex.exp ((θ : ℂ) * I)))
        (𝓝[<] 1) (𝓝 0)) :
    EqOn H 0 (ball 0 1) := by
  apply eqOn_zero_of_bounded_radial_sequence_zero
    (inner := 1 / 2) (radii := fiberRadii) (by norm_num)
    fiberRadii_bounds hH hbound hpositive
  intro θ hθ
  simpa [circleMap, Function.comp_def] using (hzero θ hθ).comp fiberRadii_tendsto

theorem bounded_radial_zero_fiber_measure_zero
    {H : ℂ → ℂ} (hH : DifferentiableOn ℂ H (ball 0 1))
    {B : ℝ} (hbound : ∀ z ∈ ball 0 1, ‖H z‖ ≤ B)
    (hnonzero : ¬EqOn H 0 (ball 0 1)) :
    (volume.restrict (Ioc 0 (2 * Real.pi)))
      {θ : ℝ | Tendsto
        (fun r : ℝ => H ((r : ℂ) * Complex.exp ((θ : ℂ) * I)))
        (𝓝[<] 1) (𝓝 0)} = 0 := by
  by_contra hpositive
  exact hnonzero (eqOn_zero_of_bounded_radial_limit_zero hH hbound hpositive
    (fun _ h => h))
theorem tendsto_boundedization_zero_of_norm_atTop
    {ι : Type*} {l : Filter ι} {g F : ι → ℂ} {a b : ℂ} {c : ℝ}
    (hc : 0 < c)
    (hrelation : ∀ᶠ i in l, g i = a + (b + (c : ℂ) / F i) ^ 2)
    (hescape : Tendsto (fun i => ‖g i‖) l atTop) :
    Tendsto F l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let M : ℝ := ‖a‖ + (‖b‖ + c / ε) ^ 2
  filter_upwards [hrelation, hescape (eventually_gt_atTop M)] with i hi hlarge
  rw [dist_zero_right]
  by_contra! hF
  have hnorm : ‖(c : ℂ) / F i‖ ≤ c / ε := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    exact div_le_div_of_nonneg_left hc.le hε hF
  have hterm : ‖b + (c : ℂ) / F i‖ ≤ ‖b‖ + c / ε := by
    have htriangle := norm_add_le b ((c : ℂ) / F i)
    linarith
  have hupper : ‖g i‖ ≤ M := by
    rw [hi]
    calc
      ‖a + (b + (c : ℂ) / F i) ^ 2‖ ≤
          ‖a‖ + ‖(b + (c : ℂ) / F i) ^ 2‖ := norm_add_le _ _
      _ = ‖a‖ + ‖b + (c : ℂ) / F i‖ ^ 2 := by rw [norm_pow]
      _ ≤ M := by
        have hpow := pow_le_pow_left₀ (norm_nonneg _) hterm 2
        dsimp [M]
        linarith
  exact (not_le_of_gt hlarge) hupper

private theorem eventually_radial_mem_ball (θ : ℝ) :
    ∀ᶠ r : ℝ in 𝓝[<] 1,
      (r : ℂ) * Complex.exp ((θ : ℂ) * I) ∈ ball 0 1 := by
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r from
      nhdsWithin_le_nhds (eventually_gt_nhds zero_lt_one))] with r hr hpos
  rw [mem_ball_zero_iff, norm_mul]
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, Complex.norm_exp] using hr

private def finiteFiberPolynomial (a b : ℂ) (c : ℝ) (y : ℂ) : Polynomial ℂ :=
  Polynomial.C (y - a) * Polynomial.X ^ 2 -
    (Polynomial.C b * Polynomial.X + Polynomial.C (c : ℂ)) ^ 2

private theorem finiteFiberPolynomial_ne_zero (a b y : ℂ) {c : ℝ} (hc : 0 < c) :
    finiteFiberPolynomial a b c y ≠ 0 := by
  intro h
  have hzero := congrArg (fun P : Polynomial ℂ => P.eval 0) h
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  simp [finiteFiberPolynomial, hcC] at hzero

private theorem finiteFiber_not_eqOn_zero
    {F : ℂ → ℂ} (hinj : InjOn F (ball 0 1)) (a b y : ℂ) {c : ℝ} (hc : 0 < c) :
    ¬EqOn (fun z => (y - a) * F z ^ 2 - (b * F z + (c : ℂ)) ^ 2) 0 (ball 0 1) := by
  intro hzero
  have hinfinite : (F '' ball (0 : ℂ) 1).Infinite :=
    (infinite_of_mem_nhds (0 : ℂ) (ball_mem_nhds _ zero_lt_one)).image hinj
  apply hinfinite
  apply (Polynomial.finite_setOfPred_isRoot (finiteFiberPolynomial_ne_zero a b y hc)).subset
  rintro _ ⟨z, hz, rfl⟩
  simpa [Polynomial.IsRoot, finiteFiberPolynomial] using hzero hz

private theorem finiteFiber_bounded
    {F : ℂ → ℂ} (hbound : ∀ z ∈ ball 0 1, ‖F z‖ ≤ 1)
    (a b y : ℂ) {c : ℝ} (hc : 0 ≤ c) :
    ∀ z ∈ ball 0 1,
      ‖(y - a) * F z ^ 2 - (b * F z + (c : ℂ)) ^ 2‖ ≤
        ‖y - a‖ + (‖b‖ + c) ^ 2 := by
  intro z hz
  calc
    ‖(y - a) * F z ^ 2 - (b * F z + (c : ℂ)) ^ 2‖ ≤
        ‖(y - a) * F z ^ 2‖ + ‖(b * F z + (c : ℂ)) ^ 2‖ := norm_sub_le _ _
    _ = ‖y - a‖ * ‖F z‖ ^ 2 + ‖b * F z + (c : ℂ)‖ ^ 2 := by
      rw [norm_mul, norm_pow, norm_pow]
    _ ≤ ‖y - a‖ * 1 ^ 2 + (‖b‖ * 1 + c) ^ 2 := by
      have hsum : ‖b * F z + (c : ℂ)‖ ≤ ‖b‖ * 1 + c := by
        calc
          _ ≤ ‖b * F z‖ + ‖(c : ℂ)‖ := norm_add_le _ _
          _ = ‖b‖ * ‖F z‖ + c := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
          _ ≤ _ := by gcongr; exact hbound z hz
      gcongr
      exact hbound z hz
    _ = _ := by ring
private theorem finiteFiber_tendsto_zero
    {g F : ℂ → ℂ} {a b y : ℂ} {c : ℝ}
    (hdata : ∀ z ∈ ball 0 1, F z ≠ 0 ∧ ‖F z‖ < 1 ∧
      g z = a + (b + (c : ℂ) / F z) ^ 2)
    {θ : ℝ}
    (hlimit : Tendsto
      (fun r : ℝ => g ((r : ℂ) * Complex.exp ((θ : ℂ) * I)))
      (𝓝[<] 1) (𝓝 y)) :
    Tendsto (fun r : ℝ =>
      (y - a) * F ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) ^ 2 -
        (b * F ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) + (c : ℂ)) ^ 2)
      (𝓝[<] 1) (𝓝 0) := by
  let radial : ℝ → ℂ := fun r => (r : ℂ) * Complex.exp ((θ : ℂ) * I)
  have hvanish : Tendsto (fun r => y - g (radial r)) (𝓝[<] 1) (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := y)).sub hlimit
  have hbounded : IsBoundedUnder (· ≤ ·) (𝓝[<] 1)
      (norm ∘ fun r => F (radial r) ^ 2) := by
    apply isBoundedUnder_of_eventually_le (a := 1)
    filter_upwards [eventually_radial_mem_ball θ] with r hr
    simpa only [Function.comp_def, norm_pow, one_pow] using
      pow_le_pow_left₀ (norm_nonneg _) (hdata _ hr).2.1.le 2
  have hproduct := hvanish.zero_mul_isBoundedUnder_le hbounded
  apply hproduct.congr'
  filter_upwards [eventually_radial_mem_ball θ] with r hr
  obtain ⟨hF, _, hrelation⟩ := hdata _ hr
  dsimp [radial]
  rw [hrelation]
  field_simp [hF]
  ring

theorem spherical_radial_fiber_measure_zero_one_turn
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1)) (hinj : InjOn g (ball 0 1))
    (p : ComplexSphere.Sphere) :
    (volume.restrict (Ioc 0 (2 * Real.pi)))
      {θ : ℝ | Tendsto
        (fun r : ℝ => ComplexSphere.chart
          (g ((r : ℂ) * Complex.exp ((θ : ℂ) * I))))
        (𝓝[<] 1) (𝓝 p)} = 0 := by
  obtain ⟨a, b, c, F, hc, hF, hiF, hdata⟩ :=
    exists_algebraic_boundedization_of_holomorphic_injOn hg hinj
  by_cases hp : p = ComplexSphere.north
  · subst p
    have hFnonzero : ¬EqOn F 0 (ball 0 1) := by
      intro hzero
      exact (hdata 0 (mem_ball_self zero_lt_one)).1 (hzero (mem_ball_self zero_lt_one))
    apply measure_mono_null _ (bounded_radial_zero_fiber_measure_zero hF
      (fun z hz => (hdata z hz).2.1.le) hFnonzero)
    intro θ hθ
    apply tendsto_boundedization_zero_of_norm_atTop hc
    · filter_upwards [eventually_radial_mem_ball θ] with r hr
      exact (hdata _ hr).2.2
    · exact ComplexSphere.norm_tendsto_atTop_of_chart_tendsto_north hθ
  · obtain ⟨y, rfl⟩ : p ∈ range ComplexSphere.chart := by
      rw [ComplexSphere.range_chart]
      exact hp
    let H : ℂ → ℂ := fun z =>
      (y - a) * F z ^ 2 - (b * F z + (c : ℂ)) ^ 2
    have hH : DifferentiableOn ℂ H (ball 0 1) :=
      ((hF.pow 2).const_mul (y - a)).sub
        (((hF.const_mul b).add_const (c : ℂ)).pow 2)
    have hbound := finiteFiber_bounded (fun z hz => (hdata z hz).2.1.le) a b y hc.le
    have hnonzero := finiteFiber_not_eqOn_zero hiF a b y hc
    apply measure_mono_null _ (bounded_radial_zero_fiber_measure_zero hH hbound hnonzero)
    intro θ hθ
    exact finiteFiber_tendsto_zero hdata
      (ComplexSphere.isEmbedding_chart.tendsto_nhds_iff.mpr hθ)
/-- Every fixed spherical endpoint has a null angular landing fiber on the
whole real line, including the north pole. No measurability hypothesis is
imposed on the landing set. -/
theorem spherical_radial_fiber_measure_zero
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1)) (hinj : InjOn g (ball 0 1))
    (p : ComplexSphere.Sphere) :
    volume {θ : ℝ | Tendsto
      (fun r : ℝ => ComplexSphere.chart
        (g ((r : ℂ) * Complex.exp ((θ : ℂ) * I))))
      (𝓝[<] 1) (𝓝 p)} = 0 := by
  let P : ℝ → Prop := fun θ => ¬Tendsto
    (fun r : ℝ => ComplexSphere.chart
      (g ((r : ℂ) * Complex.exp ((θ : ℂ) * I))))
    (𝓝[<] 1) (𝓝 p)
  have hwindows (n : ℤ) : ∀ᵐ θ : ℝ, θ - n ∈ Ioo (0 : ℝ) 2 → P θ := by
    let rotation : ℂ → ℂ := fun z => Complex.exp ((n : ℂ) * I) * z
    have hunit : ‖Complex.exp ((n : ℂ) * I)‖ = 1 := by simp [Complex.norm_exp]
    have hmaps : MapsTo rotation (ball 0 1) (ball 0 1) := by
      intro z hz
      simpa only [rotation, mem_ball_zero_iff, norm_mul, hunit, one_mul] using hz
    have hrot : DifferentiableOn ℂ (fun z => g (rotation z)) (ball 0 1) :=
      hg.comp (differentiable_id.const_mul _).differentiableOn hmaps
    have hrotInj : InjOn (fun z => g (rotation z)) (ball 0 1) :=
      hinj.comp (mul_right_injective₀ (Complex.exp_ne_zero _)).injOn hmaps
    have hnull := spherical_radial_fiber_measure_zero_one_turn hrot hrotInj p
    have hturn : ∀ᵐ (θ : ℝ) ∂volume.restrict (Ioc 0 (2 * Real.pi)),
        ¬Tendsto (fun r : ℝ => ComplexSphere.chart
          (g (rotation ((r : ℂ) * Complex.exp ((θ : ℂ) * I)))))
          (𝓝[<] 1) (𝓝 p) := by
      simpa only [ae_iff, Classical.not_not, Set.ofPred_mem_eq] using hnull
    have hsub : Ioo (0 : ℝ) 2 ⊆ Ioc 0 (2 * Real.pi) :=
      fun θ hθ => ⟨hθ.1, hθ.2.le.trans (by linarith [Real.pi_gt_three])⟩
    have hsmall := hturn.filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
    have heq (θ r : ℝ) : rotation ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) =
        (r : ℂ) * Complex.exp (((n : ℝ) + θ : ℝ) * I) := by
      simp only [rotation, Complex.ofReal_add, Complex.ofReal_intCast,
        add_mul, Complex.exp_add]
      ring
    have hwhole : ∀ᵐ θ : ℝ, θ ∈ Ioo (0 : ℝ) 2 → P ((n : ℝ) + θ) := by
      apply (ae_restrict_iff' measurableSet_Ioo).mp
      simpa only [heq] using hsmall
    have htranslated := (measurePreserving_add_left volume (-(n : ℝ)))
      |>.quasiMeasurePreserving.ae hwhole
    filter_upwards [htranslated] with θ hθ hmem
    have hsub : -(n : ℝ) + θ = θ - n := by ring
    have hsum : (n : ℝ) + (-(n : ℝ) + θ) = θ := by ring
    rw [hsum] at hθ
    exact hθ (hsub.symm ▸ hmem)
  have hall : ∀ᵐ θ : ℝ, ∀ n : ℤ, θ - n ∈ Ioo (0 : ℝ) 2 → P θ :=
    ae_all_iff.mpr hwindows
  have hglobal : ∀ᵐ θ : ℝ, P θ := by
    filter_upwards [hall] with θ hθ
    apply hθ (⌊θ⌋ - 1)
    have hfloor := Int.floor_le θ
    have hupper := Int.lt_floor_add_one θ
    constructor <;> push_cast <;> linarith
  simpa only [P, ae_iff, Classical.not_not, Set.ofPred_mem_eq] using hglobal

end Math.ComplexAnalysis
