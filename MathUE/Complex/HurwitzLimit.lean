/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache-2.0; see LICENSES/APACHE_2_0.txt.
Authors: Yury Kudryashov

Adapted from the Hurwitz and injective-limit proofs in
https://github.com/urkud/mathlib4/tree/d43061d911b1aeae0788591da437a3b115098962
under Mathlib/Analysis/Complex/RiemannMapping.lean (PR33505).
-/
module

public import MathUE.Complex.CircleArgumentPrinciple
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! # Zero-free and injective locally uniform limits

The zero-free limit is either identically zero or zero-free on the open
preconnected domain. The injective limit is either constant or injective.
The filter is nontrivial and countably generated, as in the supplied proof.
These results do not assert existence of a compact family or an extremal map.
-/

public section

namespace Math.ComplexAnalysis

open Complex Set Metric Filter Function
open scoped _root_.Topology Real

theorem eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn
    {ι : Type*} {U : Set ℂ} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hopen : IsOpen U) (hconnected : IsPreconnected U)
    (hzeroFree : ∀ᶠ i in l, ∀ x ∈ U, F i x ≠ 0)
    (hanalytic : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U)
    (hlimit : TendstoLocallyUniformlyOn F f l U) :
    EqOn f 0 U ∨ ∀ x ∈ U, f x ≠ 0 := by
  have hfd : DifferentiableOn ℂ f U := hlimit.differentiableOn hanalytic hopen
  rw [or_iff_not_imp_left]
  intro hnotzero center hcenter hfcenter
  obtain hlocalzero | hlocalnonzero :=
    (hfd.analyticAt (hopen.mem_nhds hcenter)).eventually_eq_zero_or_eventually_ne_zero
  · exact hnotzero ((hfd.analyticOnNhd hopen).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hconnected hcenter hlocalzero)
  · obtain ⟨radius, hradius, hball, hboundary⟩ : ∃ radius > 0,
        closedBall center radius ⊆ U ∧ ∀ w ∈ sphere center radius, f w ≠ 0 := by
      rw [eventually_nhdsWithin_iff] at hlocalnonzero
      obtain ⟨radius, hradius, hnear⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp
        (hlocalnonzero.and (hopen.eventually_mem hcenter))
      refine ⟨radius, hradius, fun w hw => (hnear hw).2, fun w hw => ?_⟩
      exact (hnear (sphere_subset_closedBall hw)).1 (ne_of_mem_sphere hw hradius.ne')
    have hsphere : sphere center radius ⊆ U := sphere_subset_closedBall.trans hball
    have hlog : TendstoUniformlyOn (fun i => logDeriv (F i)) (logDeriv f) l
        (sphere center radius) := by
      simp only [logDeriv]
      have hderiv := (hlimit.deriv hanalytic hopen).mono hsphere
      rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
        (isCompact_sphere center radius)]
      exact hderiv.fun_div₀ (hlimit.mono hsphere)
        ((hfd.analyticOnNhd hopen).deriv.continuousOn.mono hsphere)
        (hfd.continuousOn.mono hsphere) hboundary
    have hintegrals : Tendsto (fun i => ∮ z in C(center, radius), logDeriv (F i) z) l
        (𝓝 (∮ z in C(center, radius), logDeriv f z)) := by
      apply hlog.tendsto_circleIntegral_of_continuousOn hradius.le
      filter_upwards [hzeroFree, hanalytic] with i hi hd
      exact ((hd.analyticOnNhd hopen).deriv.continuousOn.mono hsphere).div
        (hd.continuousOn.mono hsphere) (fun x hx => hi x (hsphere hx))
    have hzeroIntegrals : ∀ᶠ i in l, (∮ z in C(center, radius), logDeriv (F i) z) = 0 := by
      filter_upwards [hzeroFree, hanalytic] with i hi hd
      apply DiffContOnCl.circleIntegral_eq_zero hradius.le
      exact ((hd.deriv hopen).div hd hi).diffContOnCl_ball hball
    have hintegralZero := hintegrals.congr' hzeroIntegrals
    rw [tendsto_const_nhds_iff, eq_comm,
      circleIntegral_logDeriv_eq_finsum_analyticOrderNatAt, mul_eq_zero] at hintegralZero
    · replace hintegralZero := hintegralZero.resolve_left (by simp)
      norm_cast at hintegralZero
      refine ne_of_gt ?_ hintegralZero
      apply finsum_cond_pos
      · simp
      · use center
        suffices ∃ᶠ x : ℂ in 𝓝 center, f x ≠ 0 by
          simpa [pos_iff_ne_zero, analyticOrderNatAt, analyticOrderAt_eq_zero, hfcenter,
            analyticOrderAt_eq_top, hfd.analyticAt (hopen.mem_nhds hcenter), hradius]
        rw [eventually_nhdsWithin_iff] at hlocalnonzero
        refine Frequently.mp ?_ hlocalnonzero
        rw [frequently_iff_neBot, Set.ofPred_mem_eq, ← nhdsWithin]
        infer_instance
      · have hdomain := (hfd.analyticOnNhd hopen).mono hball
        have hfinite := IsCompact.finite_sdiff_of_mem_codiscreteWithin
          (isCompact_closedBall center radius)
          hdomain.codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top
        refine hfinite.subset ?_
        simp +contextual [subset_def, analyticOrderNatAt, le_of_lt]
    · exact (hfd.analyticOnNhd hopen).mono hball
    · exact hboundary
    · exact hradius.le

theorem eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn
    {ι : Type*} {U : Set ℂ} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hopen : IsOpen U) (hconnected : IsPreconnected U)
    (hinjective : ∀ᶠ i in l, InjOn (F i) U)
    (hanalytic : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U)
    (hlimit : TendstoLocallyUniformlyOn F f l U) :
    (∃ constant, ∀ x ∈ U, f x = constant) ∨ InjOn f U := by
  rw [or_iff_not_imp_left]
  intro hnotconstant x hx y hy hxy
  by_contra! hne
  obtain ⟨radius, hradius, hball, hyball⟩ :
      ∃ radius > 0, ball x radius ⊆ U ∧ y ∉ ball x radius := by
    simp_rw [← subset_compl_singleton_iff, ← subset_inter_iff, ← Metric.mem_nhds_iff]
    simp [hopen.mem_nhds hx, hne]
  have hsub : TendstoLocallyUniformlyOn (fun i z => F i z - F i y)
      (fun z => f z - f y) l (ball x radius) :=
    (hlimit.mono hball).fun_sub
      (hlimit.tendsto_at hy).tendstoUniformly_const.tendstoUniformlyOn.tendstoLocallyUniformlyOn
  refine (eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn isOpen_ball
    (convex_ball x radius).isPreconnected
    (hinjective.mono fun i hi z hz => ?_) ?_ hsub).resolve_left ?_
      x (by simpa) (by rwa [sub_eq_zero])
  · rw [sub_ne_zero, hi.ne_iff (hball hz) hy]
    exact ne_of_mem_of_not_mem hz hyball
  · exact hanalytic.mono fun i hi => (hi.mono hball).sub_const _
  · intro heq
    refine hnotconstant ⟨f y, ?_⟩
    apply (hlimit.differentiableOn hanalytic hopen).analyticOnNhd hopen
      |>.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hconnected hx
    exact (heq.eventuallyEq_of_mem (ball_mem_nhds x hradius)).mono
      fun z hz => sub_eq_zero.mp hz

end Math.ComplexAnalysis
