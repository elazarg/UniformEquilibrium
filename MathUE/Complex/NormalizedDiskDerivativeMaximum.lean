/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache-2.0; see LICENSES/APACHE_2_0.txt.
Authors: Yury Kudryashov

Adapted from the compact-open maximization argument in
https://github.com/urkud/mathlib4/tree/d43061d911b1aeae0788591da437a3b115098962
under Mathlib/Analysis/Complex/RiemannMapping.lean (PR33505).
-/
module

public import MathUE.Complex.BoundedHolomorphicEquicontinuity
public import MathUE.Complex.NormalizedDiskEmbedding
public import MathUE.Complex.HurwitzLimit
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Complex.AbsMax

/-! # Construct a normalized disk-embedding derivative maximizer

Compactness is obtained from the actual holomorphic family via Arzela--Ascoli.
Hurwitz and positive derivative exclude a constant maximizer. No compact-family
certificate or maximizing map is supplied as an assumption. Surjectivity and
boundary extension are not conclusions of this unit.
-/

public section

namespace Math.ComplexAnalysis

open Set Metric Filter Function
open scoped _root_.Topology UniformConvergence Uniformity

theorem exists_normalized_disk_derivative_maximum {U : Set ℂ}
    (hopen : IsOpen U) (hconnected : IsSimplyConnected U) (hproper : U ≠ univ)
    {base : ℂ} (hbase : base ∈ U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ MapsTo f U (ball 0 1) ∧ InjOn f U ∧
      f base = 0 ∧ 0 < ‖deriv f base‖ ∧
      ∀ g : ℂ → ℂ, DifferentiableOn ℂ g U → MapsTo g U (ball 0 1) →
        InjOn g U → g base = 0 → ‖deriv g base‖ ≤ ‖deriv f base‖ := by
  let compactSets : Set (Set ℂ) := {K | K ⊆ U ∧ IsCompact K}
  have hcompactSets : ∀ K ∈ compactSets, IsCompact K := fun _ => And.right
  let : (𝓤 (ℂ →ᵤ[compactSets] ℂ)).IsCountablyGenerated := by
    let := hopen.locallyCompactSpace
    let : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
    let exhaustion : CompactExhaustion U := default
    apply UniformOnFun.isCountablyGenerated_uniformity
      (t := fun n => Subtype.val '' exhaustion n)
    · intro n
      exact ⟨image_val_subset, (exhaustion.isCompact n).image continuous_subtype_val⟩
    · exact monotone_image.comp exhaustion.subset
    · rintro K ⟨hKU, hK⟩
      lift K to Set U using hKU
      rw [← Subtype.isCompact_iff] at hK
      exact (exhaustion.exists_superset_of_isCompact hK).imp fun n hn => by gcongr
  let evaluate : (ℂ →ᵤ[compactSets] ℂ) → (ℂ → ℂ) := UniformOnFun.toFun _
  have hevaluate : ∀ {f : ℂ →ᵤ[compactSets] ℂ} {s},
      TendstoLocallyUniformlyOn evaluate (evaluate f) (𝓝[s] f) U := by
    intro f s
    have hidentity : Tendsto id (𝓝[s] f) (𝓝 f) := tendsto_id'.mpr nhdsWithin_le_nhds
    simpa [tendstoLocallyUniformlyOn_iff_forall_isCompact hopen,
      UniformOnFun.tendsto_iff_tendstoUniformlyOn, compactSets] using hidentity
  let family : Set (ℂ →ᵤ[compactSets] ℂ) :=
    {f | MapsTo (evaluate f) U (ball 0 1) ∧ InjOn (evaluate f) U ∧
      DifferentiableOn ℂ (evaluate f) U ∧ deriv (evaluate f) base ≠ 0 ∧ evaluate f base = 0}
  have hanalytic : ∀ f ∈ family, DifferentiableOn ℂ (evaluate f) U := fun _ hf => hf.2.2.1
  have hnonempty : family.Nonempty := by
    obtain ⟨f, hfzero, hfinjective, hfderivative⟩ :=
      Math.ComplexUnitDisc.exists_normalized_disk_embedding hopen hconnected hproper hbase
    refine ⟨UniformOnFun.ofFun compactSets (fun z => (f z : ℂ)),
      (fun z _ => (f z).property), ?_, ?_, hfderivative base hbase, ?_⟩
    · simpa [evaluate, InjOn] using hfinjective
    · exact fun z hz => (differentiableAt_of_deriv_ne_zero
        (hfderivative z hz)).differentiableWithinAt
    · simp [evaluate, hfzero]
  have hcompact := ArzelaAscoli.isCompact_closure_of_isClosedEmbedding hcompactSets
    (α := ℂ) (s := family) (F := evaluate) .id ?_ ?_
  · have hclosure : closure family ⊆
        {f | MapsTo (evaluate f) U (ball 0 1) ∧
          ((∃ c, EqOn (evaluate f) (const ℂ c) U) ∨ InjOn (evaluate f) U) ∧
          DifferentiableOn ℂ (evaluate f) U ∧ evaluate f base = 0} := by
      intro f hf
      rw [mem_closure_iff_nhdsWithin_neBot] at hf
      have hlimit : TendstoLocallyUniformlyOn evaluate (evaluate f) (𝓝[family] f) U :=
        hevaluate
      have hd : DifferentiableOn ℂ (evaluate f) U := hlimit.differentiableOn
        (eventually_mem_nhdsWithin.mono hanalytic) hopen
      have hnorm : ∀ z ∈ U, ‖evaluate f z‖ ≤ 1 := by
        intro z hz
        refine le_of_tendsto (hlimit.tendsto_at hz).norm
          (eventually_mem_nhdsWithin.mono fun g hg => ?_)
        exact (mem_ball_zero_iff.mp (hg.1 hz)).le
      have hzero : evaluate f base = 0 := by
        refine tendsto_nhds_unique (hlimit.tendsto_at hbase) ?_
        exact tendsto_const_nhds.congr'
          (eventually_mem_nhdsWithin.mono fun g hg => hg.2.2.2.2.symm)
      refine ⟨?_, ?_, hd, hzero⟩
      · by_contra hnotDisk
        obtain ⟨z, hz, hlarge⟩ : ∃ z ∈ U, 1 ≤ ‖evaluate f z‖ := by
          simpa [MapsTo] using hnotDisk
        have hmax : IsMaxOn (fun z => ‖evaluate f z‖) U z :=
          fun y hy => (hnorm y hy).trans hlarge
        have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
          hconnected.isPathConnected.isConnected.isPreconnected hopen hd hz hmax hbase
        have heq' : evaluate f base = evaluate f z := heq
        have hzZero : evaluate f z = 0 := heq'.symm.trans hzero
        rw [hzZero, norm_zero] at hlarge
        exact (not_le_of_gt zero_lt_one) hlarge
      · exact eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn hopen
          hconnected.isPathConnected.isConnected.isPreconnected
          (eventually_mem_nhdsWithin.mono fun g hg => hg.2.1)
          (eventually_mem_nhdsWithin.mono hanalytic) hlimit
    have hderivativeContinuous : ContinuousOn (fun f => ‖deriv (evaluate f) base‖)
        (closure family) := by
      refine ContinuousOn.mono (ContinuousOn.norm fun f hf => ?_) hclosure
      exact (hevaluate.deriv
        (eventually_mem_nhdsWithin.mono fun g hg => hg.2.2.1) hopen).tendsto_at hbase
    obtain ⟨maximizer, hmaximizer, hmaximum⟩ :=
      hcompact.exists_isMaxOn hnonempty.closure hderivativeContinuous
    have hpositive : 0 < ‖deriv (evaluate maximizer) base‖ := by
      obtain ⟨competitor, hcompetitor⟩ := hnonempty
      exact (norm_pos_iff.mpr hcompetitor.2.2.2.1).trans_le
        (hmaximum (subset_closure hcompetitor))
    obtain ⟨hmaps, hinjective, hd, hzero⟩ := hclosure hmaximizer
    have hactualInjective : InjOn (evaluate maximizer) U := by
      refine hinjective.resolve_left ?_
      rintro ⟨c, hc⟩
      rw [(hc.eventuallyEq_of_mem (hopen.mem_nhds hbase)).deriv_eq] at hpositive
      change 0 < ‖deriv (fun _ : ℂ => c) base‖ at hpositive
      simp only [deriv_const, norm_zero, lt_self_iff_false] at hpositive
    refine ⟨evaluate maximizer, hd, hmaps, hactualInjective, hzero, hpositive, ?_⟩
    intro competitor hd hmaps hinjective hzero
    by_cases hderivative : deriv competitor base = 0
    · simp only [hderivative, norm_zero]
      exact norm_nonneg _
    · exact hmaximum (subset_closure
        (show UniformOnFun.ofFun compactSets competitor ∈ family from
          ⟨hmaps, hinjective, hd, hderivative, hzero⟩))
  · rintro K ⟨hKU, _hK⟩ z hz
    refine (equicontinuousAt_of_forall_norm_le (hopen.mem_nhds (hKU hz))
      (fun i : family => hanalytic i.val i.property)
      ⟨1, fun (i : family) z hz => ?_⟩).equicontinuousWithinAt _
    exact (mem_ball_zero_iff.mp (i.property.1 hz)).le
  · intro K hK z hz
    exact ⟨closedBall 0 1, isCompact_closedBall 0 1,
      fun i hi => ball_subset_closedBall (hi.1 (hK.1 hz))⟩

end Math.ComplexAnalysis
