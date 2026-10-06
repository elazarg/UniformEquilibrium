module

public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Holomorphic inverses without a nonvanishing-derivative premise

Known proof source: Berkeley complex analysis Lecture 24 (April 24, 2026),
the inverse-mapping proposition and its proof:
https://math.berkeley.edu/~avizeff/complex_analysis_S26/lecture_24.html

Open mapping constructs continuity of the actual inverse. Isolated critical
points give differentiability of the inverse on punctured neighborhoods;
continuity removes these singularities. The chain rule then rules out critical
points. We use the pinned open mapping theorem, not other claims in those notes.
No connectedness, boundary regularity, or supplied inverse continuity is required.
-/

public section

namespace Math.ComplexAnalysis

open Set Filter Metric Function Complex
open scoped _root_.Topology

private theorem not_eventually_constant_of_injOn {U : Set ℂ} {f : ℂ → ℂ}
    (hinj : InjOn f U) {a : ℂ} (hU : U ∈ 𝓝 a) :
    ¬∀ᶠ z in 𝓝 a, f z = f a := by
  intro hc
  have hfalse : ∀ᶠ z in 𝓝[≠] a, False := by
    filter_upwards [hc.filter_mono nhdsWithin_le_nhds,
      nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with z hz hzU hne
    exact hne (hinj hzU (mem_of_mem_nhds hU) hz)
  obtain ⟨_, h⟩ := hfalse.exists
  exact h

theorem isOpenMap_domRestrict_of_holomorphic_injOn {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hfd : DifferentiableOn ℂ f U) (hinj : InjOn f U) :
    IsOpenMap (U.domRestrict f) := by
  intro s hs
  change IsOpen ((f ∘ Subtype.val) '' s)
  rw [Set.image_comp]
  apply isOpen_iff_mem_nhds.mpr
  rintro w ⟨z, ⟨v, hv, rfl⟩, rfl⟩
  have hanalytic := (hfd.analyticOnNhd hU) v v.property
  have hopen := hanalytic.eventually_constant_or_nhds_le_map_nhds.resolve_left
      (not_eventually_constant_of_injOn hinj (hU.mem_nhds v.property))
  exact hopen (image_mem_map ((hU.isOpenMap_subtype_val s hs).mem_nhds ⟨v, hv, rfl⟩))

private theorem eventually_deriv_ne_of_injOn {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hfd : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    {a : ℂ} (ha : a ∈ U) : ∀ᶠ z in 𝓝[≠] a, deriv f z ≠ 0 := by
  have hanalytic := ((hfd.analyticOnNhd hU) a ha).deriv
  apply hanalytic.eventually_eq_zero_or_eventually_ne_zero.resolve_left
  intro hzero
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hzero.and (hU.mem_nhds ha))
  have hsub : ball a r ⊆ U := fun z hz => (hball hz).2
  have hconstant : ∀ᶠ z in 𝓝 a, f z = f a := by
    filter_upwards [ball_mem_nhds a hr] with z hz
    exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball a r).isPreconnected
      (hfd.mono hsub) (fun w hw => (hball hw).1) hz (mem_ball_self hr)
  exact not_eventually_constant_of_injOn hinj (hU.mem_nhds ha) hconstant

theorem differentiableOn_invFunOn_of_holomorphic_injOn {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hfd : DifferentiableOn ℂ f U) (hinj : InjOn f U) :
    DifferentiableOn ℂ (invFunOn f U) (f '' U) := by
  let g := invFunOn f U
  have hopenMap := isOpenMap_domRestrict_of_holomorphic_injOn hU hfd hinj
  have hV : IsOpen (f '' U) := by
    simpa only [range_domRestrict] using hopenMap.isOpen_range
  have hgc : ContinuousOn g (f '' U) :=
    hopenMap.continuousOn_image_of_leftInvOn hinj.leftInvOn_invFunOn
  have hright : ∀ w ∈ f '' U, f (g w) = w := fun w hw => invFunOn_eq hw
  have hmaps : ∀ w ∈ f '' U, g w ∈ U := fun w hw => invFunOn_mem hw
  intro a ha
  have hga := hgc.continuousAt (hV.mem_nhds ha)
  have hderiv := eventually_deriv_ne_of_injOn hU hfd hinj (hmaps a ha)
  have hnear : ∀ᶠ z in 𝓝 (g a), z ≠ g a → deriv f z ≠ 0 := by
    simpa only [mem_compl_iff, mem_singleton_iff] using
      (eventually_nhdsWithin_iff.mp hderiv)
  have hpunctured : ∀ᶠ w in 𝓝[≠] a, DifferentiableAt ℂ g w := by
    filter_upwards [(hga.eventually hnear).filter_mono nhdsWithin_le_nhds,
      nhdsWithin_le_nhds (hV.mem_nhds ha),
      self_mem_nhdsWithin] with w hw hwV hwne
    have hgwne : g w ≠ g a := by
      intro heq
      exact hwne ((hright w hwV).symm.trans ((congrArg f heq).trans (hright a ha)))
    have hidentity : ∀ᶠ y in 𝓝 w, f (g y) = y := by
      filter_upwards [hV.mem_nhds hwV] with y hy
      exact hright y hy
    exact (HasDerivAt.of_local_left_inverse (hgc.continuousAt (hV.mem_nhds hwV))
      (hfd.differentiableAt (hU.mem_nhds (hmaps w hwV))).hasDerivAt
      (hw hgwne) hidentity).differentiableAt
  exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    hpunctured hga).differentiableAt.differentiableWithinAt

theorem deriv_ne_zero_of_holomorphic_injOn {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hfd : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    {a : ℂ} (ha : a ∈ U) : deriv f a ≠ 0 := by
  have hopenMap := isOpenMap_domRestrict_of_holomorphic_injOn hU hfd hinj
  have hV : IsOpen (f '' U) := by
    simpa only [range_domRestrict] using hopenMap.isOpen_range
  have hgd := differentiableOn_invFunOn_of_holomorphic_injOn hU hfd hinj
  have hchain := (hgd.differentiableAt (hV.mem_nhds ⟨a, ha, rfl⟩)).hasDerivAt.comp a
    (hfd.differentiableAt (hU.mem_nhds ha)).hasDerivAt
  have heq : (fun z => invFunOn f U (f z)) =ᶠ[𝓝 a] id := by
    filter_upwards [hU.mem_nhds ha] with z hz
    exact hinj.leftInvOn_invFunOn hz
  have hproduct := (hchain.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_id a)
  intro hzero
  simp only [hzero, mul_zero, zero_ne_one] at hproduct

end Math.ComplexAnalysis
