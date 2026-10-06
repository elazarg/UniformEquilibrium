/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache-2.0; see LICENSES/APACHE_2_0.txt.
Authors: Yury Kudryashov

Adapted from the UnitDisc/Shift.lean and RiemannMapping.lean source of
https://github.com/urkud/mathlib4/tree/d43061d911b1aeae0788591da437a3b115098962
under Mathlib/Analysis/Complex (PR33505).
This project-owned subset uses the pinned APIs; the external draft is not an
imported or checked dependency. Its original Apache 2.0 attribution is retained.
-/
module

public import Mathlib.Analysis.Complex.UnitDisc.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FunProp

/-! # Actual automorphisms of the complex unit disk

The explicit fractional-linear map and its inverse supply normalization at an
arbitrary disk point. This is only a prerequisite for Riemann mapping, not a
surjectivity theorem for an arbitrary domain or a boundary extension theorem.
-/

public section

noncomputable section

namespace Math.ComplexUnitDisc

open Complex Set Function
open scoped ComplexConjugate

theorem shift_den_ne_zero (z w : UnitDisc) : 1 + conj (z : ℂ) * w ≠ 0 :=
  (star z * w).one_add_coe_ne_zero

theorem norm_shift_formula_le (z w : UnitDisc) :
    ‖(z + w : ℂ) / (1 + conj ↑z * w)‖ ≤
      (‖(z : ℂ)‖ + ‖(w : ℂ)‖) / (1 + ‖(z : ℂ)‖ * ‖(w : ℂ)‖) := by
  have hz := z.sq_norm_lt_one
  have hw := w.sq_norm_lt_one
  have hzw : z.re * w.re + z.im * w.im ≤ ‖(z : ℂ)‖ * ‖(w : ℂ)‖ := by
    rw [norm_def, norm_def, ← Real.sqrt_mul, normSq_apply, normSq_apply]
    · apply Real.le_sqrt_of_sq_le
      linear_combination (norm := {apply le_of_eq; simp; ring})
        sq_nonneg (z.re * w.im - z.im * w.re)
    · apply normSq_nonneg
  rw [norm_div, div_le_div_iff₀, ← sq_le_sq₀]
  · rw [← sub_nonneg] at hzw
    simp [mul_pow, RCLike.norm_sq_eq_def, add_sq] at hz hw ⊢
    linear_combination 2 * mul_nonneg hzw
      (mul_nonneg (sub_nonneg.2 hz.le) (sub_nonneg.2 hw.le))
  any_goals positivity
  simpa using shift_den_ne_zero z w

@[expose] def shiftMap (z w : UnitDisc) : UnitDisc :=
  UnitDisc.mk ((z + w : ℂ) / (1 + conj ↑z * w)) (by
    refine (norm_shift_formula_le z w).trans_lt ?_
    rw [div_lt_one (by positivity)]
    nlinarith only [z.norm_lt_one, w.norm_lt_one])

theorem coe_shiftMap (z w : UnitDisc) :
    (shiftMap z w : ℂ) = (z + w) / (1 + conj ↑z * w) := rfl

theorem shiftMap_eq_iff {z w u : UnitDisc} :
    shiftMap z w = u ↔ (z + w : ℂ) = u + u * conj ↑z * w := by
  rw [← UnitDisc.coe_inj, coe_shiftMap, div_eq_iff (shift_den_ne_zero z w)]
  ring_nf

theorem shiftMap_neg_apply (z w : UnitDisc) : shiftMap (-z) (shiftMap z w) = w := by
  rw [shiftMap_eq_iff, coe_shiftMap, add_div_eq_mul_add_div, ← mul_div_assoc,
    add_div_eq_mul_add_div]
  · simp; ring
  all_goals exact shift_den_ne_zero z w

/-- The actual disk automorphism taking zero to the supplied disk point. -/
@[expose] def shift (z : UnitDisc) : UnitDisc ≃ UnitDisc where
  toFun := shiftMap z
  invFun := shiftMap (-z)
  left_inv := shiftMap_neg_apply z
  right_inv := by
    intro w
    simpa using shiftMap_neg_apply (-z) w

theorem coe_shift (z w : UnitDisc) :
    (shift z w : ℂ) = (z + w) / (1 + conj ↑z * w) := rfl

theorem shift_neg_apply_self (z : UnitDisc) : shift (-z) z = 0 := by
  apply UnitDisc.coe_injective
  simp [coe_shift]

theorem continuous_shift (z : UnitDisc) : Continuous (shift z) := by
  simp only [UnitDisc.isEmbedding_coe.continuous_iff, Function.comp_def, coe_shift]
  exact Continuous.div (by fun_prop) (by fun_prop) fun _ => shift_den_ne_zero _ _

theorem hasDerivWithinAt_shift_comp {f : ℂ → UnitDisc} {z f' : ℂ} {s : Set ℂ}
    (w : UnitDisc) (hf : HasDerivWithinAt (fun x => (f x : ℂ)) f' s z) :
    HasDerivWithinAt (fun x => (shift w (f x) : ℂ))
      ((1 - ‖(w : ℂ)‖ ^ 2) / (1 + conj ↑w * f z) ^ 2 * f') s z := by
  simp only [coe_shift]
  convert HasDerivWithinAt.fun_div (hf.const_add _)
    ((hf.const_mul _).const_add _) (shift_den_ne_zero w (f z)) using 1
  · rw [← mul_conj']
    ring

theorem hasDerivAt_shift_comp {f : ℂ → UnitDisc} {z f' : ℂ}
    (w : UnitDisc) (hf : HasDerivAt (fun x => (f x : ℂ)) f' z) :
    HasDerivAt (fun x => (shift w (f x) : ℂ))
      ((1 - ‖(w : ℂ)‖ ^ 2) / (1 + conj ↑w * f z) ^ 2 * f') z :=
  (hasDerivWithinAt_shift_comp w hf.hasDerivWithinAt).hasDerivAt Filter.univ_mem

theorem deriv_shift_comp_ne_zero {f : ℂ → UnitDisc} {z : ℂ}
    (w : UnitDisc) (hf : deriv (fun x => (f x : ℂ)) z ≠ 0) :
    deriv (fun x => (shift w (f x) : ℂ)) z ≠ 0 := by
  rw [(hasDerivAt_shift_comp w (differentiableAt_of_deriv_ne_zero hf).hasDerivAt).deriv]
  apply mul_ne_zero _ hf
  apply div_ne_zero _ (pow_ne_zero 2 (shift_den_ne_zero w (f z)))
  exact_mod_cast sub_ne_zero.mpr w.sq_norm_lt_one.ne'

end Math.ComplexUnitDisc
