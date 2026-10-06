/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache-2.0; see LICENSES/APACHE_2_0.txt.
Authors: Yury Kudryashov

Adapted from the final extremal-map argument in
https://github.com/urkud/mathlib4/tree/d43061d911b1aeae0788591da437a3b115098962
under Mathlib/Analysis/Complex/RiemannMapping.lean (PR33505).
-/
module

public import MathUE.Complex.NormalizedDiskDerivativeMaximum
public import MathUE.Complex.DiskEmbeddingDerivativeImprovement

/-! # A normalized holomorphic bijection onto the unit disk

The derivative maximizer is actually constructed. An omitted disk point would
give a strictly better normalized embedding, contradicting that maximum.
No boundary extension or planar complementary-component model is asserted.
-/

public section

namespace Math.ComplexAnalysis

open Set Metric Filter Complex
open scoped _root_.Topology

theorem exists_bijOn_unitBall_map_eq_zero {U : Set ℂ}
    (hopen : IsOpen U) (hconnected : IsSimplyConnected U) (hproper : U ≠ univ)
    {base : ℂ} (hbase : base ∈ U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ BijOn f U (ball 0 1) ∧ f base = 0 := by
  classical
  obtain ⟨f, hfd, hfmap, hfinjective, hfzero, _hfpositive, hfmaximum⟩ :=
    exists_normalized_disk_derivative_maximum hopen hconnected hproper hbase
  refine ⟨f, hfd, ⟨hfmap, hfinjective, ?_⟩, hfzero⟩
  by_contra hnotSurjective
  let bundled : ℂ → UnitDisc := fun z =>
    if hz : z ∈ U then UnitDisc.mk (f z) (mem_ball_zero_iff.mp (hfmap hz)) else 0
  have heq : EqOn (fun z => (bundled z : ℂ)) f U := by
    intro z hz
    simp only [bundled, dite_eq_left hz, UnitDisc.coe_mk]
  have hbundledD : DifferentiableOn ℂ (fun z => (bundled z : ℂ)) U :=
    hfd.congr heq
  have hbundledInjective : InjOn bundled U := by
    intro z hz w hw hzw
    apply hfinjective hz hw
    exact (heq hz).symm.trans
      ((congrArg (fun value : UnitDisc => (value : ℂ)) hzw).trans (heq hw))
  have hbundledZero : bundled base = 0 := by
    apply UnitDisc.coe_injective
    exact (heq hbase).trans hfzero
  have hbundledNotSurjective : ¬SurjOn bundled U univ := by
    intro hsurjective
    apply hnotSurjective
    intro w hw
    obtain ⟨z, hz, hequal⟩ := hsurjective (Set.mem_univ
      (UnitDisc.mk w (mem_ball_zero_iff.mp hw)))
    refine ⟨z, hz, ?_⟩
    exact (heq hz).symm.trans (congrArg (fun value : UnitDisc => (value : ℂ)) hequal)
  obtain ⟨improved, himprovedZero, himprovedInjective, himprovedD, himprovedBetter⟩ :=
    Math.ComplexUnitDisc.exists_disk_embedding_norm_deriv_gt
      hopen hconnected hproper hbase hbundledD hbundledZero hbundledInjective
      hbundledNotSurjective
  have hmaximum := hfmaximum (fun z => (improved z : ℂ)) himprovedD
    (fun z _ => (improved z).property)
    (UnitDisc.coe_injective.comp_injOn himprovedInjective)
    (by simp only [himprovedZero, UnitDisc.coe_zero])
  have hderivative : deriv (fun z => (bundled z : ℂ)) base = deriv f base :=
    (heq.eventuallyEq_of_mem (hopen.mem_nhds hbase)).deriv_eq
  rw [hderivative] at himprovedBetter
  exact hmaximum.not_gt himprovedBetter

end Math.ComplexAnalysis
