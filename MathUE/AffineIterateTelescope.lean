/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Logic.Function.Iterate

/-!
# Unrolling an affine recursion along the iterates of a self-map

A family `value : α → R` reproduced from its own image under a self-map
`f : α → α` by an affine step

`value a = increment a + coefficient a * value (f a)`

unrolls along the iterates of `f`. Two accumulators record what `n` steps
contribute:

* `Math.iterateWeight f coefficient a n` is the product of the coefficients met
  along the first `n` steps of the orbit of `a`;
* `Math.iterateAccumulation f coefficient increment a n` is the corresponding
  weighted sum of the increments.

`Math.eq_iterateAccumulation_add_iterateWeight_mul` is the resulting telescope
`value a = accumulation + weight * value (f^[n] a)`, which needs only a
semiring: neither commutativity, nor an order, nor any finiteness of `α`.

`Math.CyclicContraction` records the purely multiplicative telescope
`Math.eq_prod_range_mul_iterate`, the case `increment = 0` written as a range
product.

When the orbit returns to its start after `n` steps the telescope closes into
the cycle identity `(1 - weight) * value a = accumulation`
(`Math.one_sub_iterateWeight_mul_of_iterate_eq`), which solves for `value a`
over a field as soon as the weight misses one
(`Math.eq_iterateAccumulation_div_of_iterate_eq`). In an ordered ring,
coefficients in the unit interval keep the weight in the unit interval, and
nonnegative increments keep the accumulation nonnegative.
-/

namespace Math

variable {α : Type*} {R : Type*}

section Semiring

variable [Semiring R]

/-- The product of the coefficients met along the first `n` steps of the orbit
of `a` under `f`. -/
def iterateWeight (f : α → α) (coefficient : α → R) : α → ℕ → R
  | _, 0 => 1
  | a, n + 1 => coefficient a * iterateWeight f coefficient (f a) n

/-- The weighted sum of the increments met along the first `n` steps of the
orbit of `a` under `f`, each discounted by the coefficients preceding it. -/
def iterateAccumulation (f : α → α) (coefficient increment : α → R) : α → ℕ → R
  | _, 0 => 0
  | a, n + 1 =>
      increment a + coefficient a * iterateAccumulation f coefficient increment (f a) n

@[simp] theorem iterateWeight_zero (f : α → α) (coefficient : α → R) (a : α) :
    iterateWeight f coefficient a 0 = 1 := rfl

theorem iterateWeight_succ (f : α → α) (coefficient : α → R) (a : α) (n : ℕ) :
    iterateWeight f coefficient a (n + 1) =
      coefficient a * iterateWeight f coefficient (f a) n := rfl

@[simp] theorem iterateAccumulation_zero (f : α → α) (coefficient increment : α → R)
    (a : α) : iterateAccumulation f coefficient increment a 0 = 0 := rfl

theorem iterateAccumulation_succ (f : α → α) (coefficient increment : α → R)
    (a : α) (n : ℕ) :
    iterateAccumulation f coefficient increment a (n + 1) =
      increment a + coefficient a * iterateAccumulation f coefficient increment (f a) n :=
  rfl

/-- **The affine telescope.** Unrolling `n` steps of a family reproduced from
its own image under `f` by an affine step splits it into the accumulated
increments plus the surviving weight times the family `n` steps on. -/
theorem eq_iterateAccumulation_add_iterateWeight_mul {f : α → α}
    {coefficient increment value : α → R}
    (hstep : ∀ a, value a = increment a + coefficient a * value (f a)) :
    ∀ (n : ℕ) (a : α),
      value a =
        iterateAccumulation f coefficient increment a n +
          iterateWeight f coefficient a n * value (f^[n] a) := by
  intro n
  induction n with
  | zero => intro a; simp
  | succ n ih =>
      intro a
      rw [Function.iterate_succ_apply, hstep a, ih (f a), iterateAccumulation_succ,
        iterateWeight_succ, mul_add, mul_assoc, add_assoc]

end Semiring

section OrderedRing

variable [Ring R] [PartialOrder R] [IsOrderedRing R]

/-- Nonnegative coefficients keep the accumulated weight nonnegative. -/
theorem iterateWeight_nonneg {f : α → α} {coefficient : α → R}
    (hcoefficient : ∀ a, 0 ≤ coefficient a) :
    ∀ (n : ℕ) (a : α), 0 ≤ iterateWeight f coefficient a n := by
  intro n
  induction n with
  | zero => intro a; simp
  | succ n ih => exact fun a ↦ mul_nonneg (hcoefficient a) (ih (f a))

/-- Coefficients in the unit interval keep the accumulated weight in the unit
interval. -/
theorem iterateWeight_le_one {f : α → α} {coefficient : α → R}
    (hcoefficient0 : ∀ a, 0 ≤ coefficient a) (hcoefficient1 : ∀ a, coefficient a ≤ 1) :
    ∀ (n : ℕ) (a : α), iterateWeight f coefficient a n ≤ 1 := by
  intro n
  induction n with
  | zero => intro a; simp
  | succ n ih =>
      intro a
      exact mul_le_one₀ (hcoefficient1 a) (iterateWeight_nonneg hcoefficient0 n (f a))
        (ih (f a))

/-- Nonnegative coefficients and nonnegative increments keep the accumulation
nonnegative. -/
theorem iterateAccumulation_nonneg {f : α → α} {coefficient increment : α → R}
    (hcoefficient : ∀ a, 0 ≤ coefficient a) (hincrement : ∀ a, 0 ≤ increment a) :
    ∀ (n : ℕ) (a : α), 0 ≤ iterateAccumulation f coefficient increment a n := by
  intro n
  induction n with
  | zero => intro a; simp
  | succ n ih =>
      exact fun a ↦ add_nonneg (hincrement a) (mul_nonneg (hcoefficient a) (ih (f a)))

end OrderedRing

section Cycle

variable [Ring R]

/-- **The cycle identity.** An orbit returning to its start after `n` steps
closes the telescope: the accumulated increments are exactly the family at the
start damped by the surviving weight. -/
theorem one_sub_iterateWeight_mul_of_iterate_eq {f : α → α}
    {coefficient increment value : α → R}
    (hstep : ∀ a, value a = increment a + coefficient a * value (f a))
    {n : ℕ} {a : α} (hcycle : f^[n] a = a) :
    (1 - iterateWeight f coefficient a n) * value a =
      iterateAccumulation f coefficient increment a n := by
  have htelescope := eq_iterateAccumulation_add_iterateWeight_mul hstep n a
  rw [hcycle] at htelescope
  rw [sub_mul, one_mul]
  exact sub_eq_of_eq_add htelescope

end Cycle

section Field

variable [Field R]

/-- **The cycle identity in divided form.** Whenever the surviving weight of a
returning orbit misses one, the family at the start of the orbit is the
accumulated increments divided by the absorption deficit. -/
theorem eq_iterateAccumulation_div_of_iterate_eq {f : α → α}
    {coefficient increment value : α → R}
    (hstep : ∀ a, value a = increment a + coefficient a * value (f a))
    {n : ℕ} {a : α} (hcycle : f^[n] a = a)
    (hweight : iterateWeight f coefficient a n ≠ 1) :
    value a =
      iterateAccumulation f coefficient increment a n /
        (1 - iterateWeight f coefficient a n) := by
  have hne : (1 : R) - iterateWeight f coefficient a n ≠ 0 :=
    sub_ne_zero_of_ne fun h ↦ hweight h.symm
  rw [eq_div_iff hne, mul_comm]
  exact one_sub_iterateWeight_mul_of_iterate_eq hstep hcycle

end Field

end Math
