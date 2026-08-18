/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

/-!
# Orbits of the cyclic successor of `Fin m`, and contraction along a self-map

`finRotate m` is the cyclic successor permutation of `Fin m`.  It increments
the underlying numeral modulo `m` (`Math.val_finRotate`), and iterating it
shifts that numeral modulo `m` (`Math.val_iterate_finRotate`), so an
orbit returns to its starting point exactly at the multiples of the period
(`Math.iterate_finRotate_eq_self_iff`), in particular after one period
(`Math.iterate_finRotate_period`), and every index is reached from every other
inside one period (`Math.exists_iterate_finRotate_eq`).

A family reproduced from its own image under a self-map, `D a = c a * D (f a)`,
telescopes along the iterates of that map in any commutative monoid
(`Math.eq_prod_range_mul_iterate`).  Along the cyclic successor, with real
factors in the unit interval, a single factor below one forces the family to
vanish identically (`Math.eq_zero_of_eq_mul_finRotate`): the factors
accumulated over one period then multiply to less than one, while the telescope
reproduces the family from itself.
-/

namespace Math

/-! ## Orbits of the cyclic successor -/

/-- **Numeric form of the cyclic successor.**  It increments the underlying
numeral modulo the period, with no case distinction at the last index, unlike
`coe_finRotate`. -/
theorem val_finRotate {m : ℕ} (phase : Fin m) :
    (finRotate m phase).val = (phase.val + 1) % m := by
  letI : NeZero m := phase.neZero
  have hone : ((1 : Fin m) : ℕ) = 1 % m := Fin.val_natCast 1 m
  rw [finRotate_apply, Fin.val_add, hone, Nat.add_mod_mod]

/-- Iterating the cyclic successor shifts the numeral modulo the period. -/
theorem val_iterate_finRotate {m : ℕ} (phase : Fin m) (n : ℕ) :
    ((finRotate m)^[n] phase).val = (phase.val + n) % m := by
  induction n with
  | zero => simpa using (Nat.mod_eq_of_lt phase.isLt).symm
  | succ n ih =>
    rw [Function.iterate_succ_apply', val_finRotate, ih, Nat.mod_add_mod,
      Nat.add_assoc]

/-- An orbit of the cyclic successor returns to its starting index exactly at
the multiples of the period. -/
theorem iterate_finRotate_eq_self_iff {m : ℕ} (phase : Fin m) (n : ℕ) :
    (finRotate m)^[n] phase = phase ↔ m ∣ n := by
  have hval : phase.val % m = phase.val := Nat.mod_eq_of_lt phase.isLt
  rw [Fin.ext_iff, val_iterate_finRotate]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hmod : phase.val + n ≡ phase.val + 0 [MOD m] := by
      simpa [Nat.ModEq, hval] using h
    exact Nat.modEq_zero_iff_dvd.1 (Nat.ModEq.add_left_cancel' _ hmod)
  · obtain ⟨t, rfl⟩ := h
    rw [Nat.add_mul_mod_self_left, hval]

/-- One full cycle of the cyclic successor is the identity. -/
theorem iterate_finRotate_period {m : ℕ} (phase : Fin m) :
    (finRotate m)^[m] phase = phase :=
  (iterate_finRotate_eq_self_iff phase m).2 dvd_rfl

/-- **The cycle is a single orbit.**  Every index is reached from every other
index within one period. -/
theorem exists_iterate_finRotate_eq {m : ℕ} (phase target : Fin m) :
    ∃ n < m, (finRotate m)^[n] phase = target := by
  have hbound : phase.val < m := phase.isLt
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) hbound
  refine ⟨(target.val + m - phase.val) % m, Nat.mod_lt _ hm, Fin.ext ?_⟩
  rw [val_iterate_finRotate, Nat.add_mod_mod,
    show phase.val + (target.val + m - phase.val) = target.val + m by omega,
    Nat.add_mod_right]
  exact Nat.mod_eq_of_lt target.isLt

/-! ## Telescoping a multiplicative recursion along a self-map -/

/-- **The iteration telescope.**  Unrolling `n` steps of a family reproduced
from its own image under `f` exposes the accumulated factor. -/
theorem eq_prod_range_mul_iterate {α M : Type*} [CommMonoid M] {f : α → α}
    {c D : α → M} (hstep : ∀ a, D a = c a * D (f a)) (n : ℕ) (a : α) :
    D a = (∏ i ∈ Finset.range n, c (f^[i] a)) * D (f^[n] a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Finset.prod_range_succ, Function.iterate_succ_apply',
      hstep (f^[n] a), mul_assoc]

/-- **Contraction around the cycle forces zero.**  A family on `Fin m`
reproduced at every index by a factor in the unit interval vanishes
identically as soon as one factor of the cycle is below one. -/
theorem eq_zero_of_eq_mul_finRotate {m : ℕ} {c : Fin m → ℝ}
    (h0 : ∀ k, 0 ≤ c k) (h1 : ∀ k, c k ≤ 1) (hsome : ∃ k, c k < 1)
    {D : Fin m → ℝ} (hstep : ∀ k, D k = c k * D (finRotate m k)) (phase : Fin m) :
    D phase = 0 := by
  classical
  obtain ⟨target, htarget⟩ := hsome
  obtain ⟨n, hn, hreach⟩ := exists_iterate_finRotate_eq phase target
  have hcycle := eq_prod_range_mul_iterate hstep m phase
  rw [iterate_finRotate_period] at hcycle
  have hsurvival : (∏ i ∈ Finset.range m, c ((finRotate m)^[i] phase)) < 1 := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.mpr hn), hreach]
    have hrest0 : 0 ≤ ∏ i ∈ (Finset.range m).erase n,
        c ((finRotate m)^[i] phase) :=
      Finset.prod_nonneg fun i _ ↦ h0 _
    have hrest1 : (∏ i ∈ (Finset.range m).erase n,
        c ((finRotate m)^[i] phase)) ≤ 1 :=
      Finset.prod_le_one (fun i _ ↦ h0 _) (fun i _ ↦ h1 _)
    nlinarith [hrest0, hrest1, htarget, h0 target]
  have hvanish : D phase * (1 - ∏ i ∈ Finset.range m,
      c ((finRotate m)^[i] phase)) = 0 := by linarith [hcycle]
  rcases mul_eq_zero.mp hvanish with hzero | hone
  · exact hzero
  · linarith

end Math
