/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache-2.0; see LICENSES/APACHE_2_0.txt.
Authors: Yury Kudryashov

Adapted from `exist_map_unitDisc_injOn_norm_deriv_gt` in the RiemannMapping.lean
draft at
https://github.com/urkud/mathlib4/tree/d43061d911b1aeae0788591da437a3b115098962
under Mathlib/Analysis/Complex/RiemannMapping.lean (PR33505).
-/
module

public import MathUE.Complex.NormalizedDiskEmbedding
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Tactic.FieldSimp

/-! # Improve a normalized disk embedding which omits a disk point

The construction shifts an omitted point to zero, takes an actual continuous
square-root branch using the pinned covering theorem, and normalizes again.
The derivative strictly increases. No maximizing embedding, disk surjectivity
theorem, or boundary extension is supplied by this unit.
-/

public section

noncomputable section

namespace Math.ComplexUnitDisc

open Complex Set Function Filter
open scoped _root_.Topology ComplexConjugate Real

theorem exists_disk_embedding_norm_deriv_gt {U : Set ℂ}
    (hopen : IsOpen U) (hconnected : IsSimplyConnected U) (hproper : U ≠ univ)
    {origin : ℂ} (horigin : origin ∈ U) {f : ℂ → UnitDisc}
    (hdifferentiable : DifferentiableOn ℂ (fun z => (f z : ℂ)) U)
    (hnormalized : f origin = 0) (hinjective : InjOn f U)
    (homitted : ¬SurjOn f U univ) :
    ∃ g : ℂ → UnitDisc, g origin = 0 ∧ InjOn g U ∧
      DifferentiableOn ℂ (fun z => (g z : ℂ)) U ∧
      ‖deriv (fun z => (f z : ℂ)) origin‖ < ‖deriv (fun z => (g z : ℂ)) origin‖ := by
  by_cases hzero : deriv (fun z => (f z : ℂ)) origin = 0
  · obtain ⟨g, hgzero, hginjective, hgderivative⟩ :=
      exists_normalized_disk_embedding hopen hconnected hproper horigin
    refine ⟨g, hgzero, hginjective, fun z hz => ?_, ?_⟩
    · exact (differentiableAt_of_deriv_ne_zero (hgderivative z hz)).differentiableWithinAt
    · simpa [hzero] using hgderivative origin horigin
  obtain ⟨c, hc⟩ : ∃ c, ∀ z ∈ U, f z ≠ c := by
    simpa [SurjOn, eq_univ_iff_forall] using homitted
  have hfcontinuous : ContinuousOn f U :=
    UnitDisc.isEmbedding_coe.continuousOn_iff.mpr hdifferentiable.continuousOn
  have hshiftzero : ∀ z ∈ U, shift (-c) (f z) ≠ 0 := by
    intro z hz heq
    apply hc z hz
    exact (shift (-c)).injective (heq.trans (shift_neg_apply_self c).symm)
  obtain ⟨g, hgcontinuous, hgsquare⟩ := UnitDisc.exists_continuousOn_pow_eq
    hconnected hopen ((continuous_shift (-c)).comp_continuousOn hfcontinuous)
    (by rintro ⟨z, hz, heq⟩; exact hshiftzero z hz heq) (2 : ℕ+)
  simp only [Function.comp_def] at hgsquare
  have hgnonzero : ∀ z ∈ U, g z ≠ 0 := by
    intro z hz hgz
    apply hshiftzero z hz
    rw [← hgsquare z, hgz]
    simp
  have hdg : ∀ z ∈ U, HasDerivAt (fun x => (g x : ℂ))
      ((1 - ‖(c : ℂ)‖ ^ 2) /
        (2 * g z * (1 - conj ↑c * f z) ^ 2) * deriv (fun x => (f x : ℂ)) z) z := by
    intro z hz
    have hgcoe : (g z : ℂ) ≠ 0 := by
      intro hzero
      exact hgnonzero z hz (UnitDisc.coe_injective hzero)
    convert (hasDerivAt_pow 2 _).of_comp_left
      (UnitDisc.continuous_coe.continuousAt.comp
        (hgcontinuous.continuousAt (hopen.mem_nhds hz)))
      (hasDerivAt_shift_comp (-c) (hdifferentiable.hasDerivAt (hopen.mem_nhds hz)))
      (by simpa only [Function.comp_def, Nat.cast_ofNat, Nat.reduceSub, pow_one]
            using mul_ne_zero (two_ne_zero : (2 : ℂ) ≠ 0) hgcoe)
      (.of_forall fun x => congrArg (fun w : UnitDisc => (w : ℂ)) (hgsquare x)) using 1
    <;> simp [Function.comp_def, sub_eq_add_neg, field]
  have hgsqnorm (z : ℂ) : ‖(g z : ℂ)‖ ^ 2 = ‖(shift (-c) (f z) : ℂ)‖ := by
    rw [← norm_pow, ← PNat.val_ofNat, ← UnitDisc.coe_pow, hgsquare]
  have hgnorm (z : ℂ) : ‖(g z : ℂ)‖ = √‖(shift (-c) (f z) : ℂ)‖ := by
    rw [← Real.sqrt_sq (norm_nonneg _), hgsqnorm]
  refine ⟨fun z => shift (-g origin) (g z), shift_neg_apply_self _, ?_, ?_, ?_⟩
  · apply (shift (-g origin)).injective.comp_injOn
    intro z hz w hw hzw
    apply hinjective hz hw
    apply (shift (-c)).injective
    rw [← hgsquare z, ← hgsquare w, hzw]
  · intro z hz
    exact (hasDerivAt_shift_comp (-g origin) (hdg z hz)).differentiableAt.differentiableWithinAt
  · have hkey : ‖deriv (fun z => (shift (-g origin) (g z) : ℂ)) origin‖ =
        ‖deriv (fun z => (f z : ℂ)) origin‖ *
          (√‖(c : ℂ)‖ + √‖(c⁻¹ : ℂ)‖) / 2 := by
      have hgo : ‖(g origin : ℂ)‖ = √‖(c : ℂ)‖ := by
        simp [hgnorm, hnormalized, coe_shift]
      rw [(hasDerivAt_shift_comp (-g origin) (hdg origin horigin)).deriv]
      simp only [norm_mul, norm_div, ← mul_assoc, conj_mul', UnitDisc.coe_neg,
        map_neg, neg_mul]
      conv_rhs => rw [mul_comm, mul_div_right_comm]
      congr 1
      norm_cast
      have hpos₁ : 0 < 1 - ‖(c : ℂ)‖ := sub_pos.mpr c.norm_lt_one
      have hpos₂ : 0 < 1 - ‖(c : ℂ)‖ ^ 2 := sub_pos.mpr c.sq_norm_lt_one
      simp [field, hgo, hnormalized, ← sub_eq_add_neg, abs_of_pos, hpos₁, hpos₂]
      ring
    rw [hkey, mul_div_assoc]
    apply lt_mul_of_one_lt_right
    · simpa using hzero
    · have hcpositive : 0 < ‖(c : ℂ)‖ := by
        simpa [hnormalized] using (hc origin horigin).symm
      suffices √‖(c : ℂ)‖ * 2 < ‖(c : ℂ)‖ + 1 by
        simpa [field] using this
      have hroot : √‖(c : ℂ)‖ ≠ 1 := by simp [c.norm_ne_one]
      rw [← sub_ne_zero, ← sq_pos_iff, sub_sq, Real.sq_sqrt] at hroot
      · linear_combination hroot
      · apply norm_nonneg

end Math.ComplexUnitDisc
