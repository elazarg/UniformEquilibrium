import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! # Finite unrolling of a scalar affine recurrence -/

namespace Math

open Finset

/-- An exact scalar affine recurrence unrolls into its initial product term
and the survival-weighted finite sum of its additive charges. -/
theorem affineRecurrence_eq_prod_add_sum_prod
    {R : Type*} [CommSemiring R] (x a b : ℕ → R) (start : ℕ)
    (hstep : ∀ n, start ≤ n → x (n + 1) = a n * x n + b n) :
    ∀ {n}, start ≤ n →
      x n =
        (∏ i ∈ Ico start n, a i) * x start +
          ∑ k ∈ Ico start n, (∏ i ∈ Ico (k + 1) n, a i) * b k := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      rw [hstep n hn, ih]
      have hsum :
          a n * ∑ k ∈ Ico start n,
              (∏ i ∈ Ico (k + 1) n, a i) * b k + b n =
            ∑ k ∈ Ico start (n + 1),
              (∏ i ∈ Ico (k + 1) (n + 1), a i) * b k := by
        rw [sum_Ico_succ_top hn, mul_sum, Ico_self, prod_empty, one_mul]
        refine congr_arg (fun value => value + b n) ?_
        apply sum_congr rfl
        intro k hk
        rw [prod_Ico_succ_top (by have := mem_Ico.mp hk; omega)]
        ring
      rw [← hsum, prod_Ico_succ_top hn]
      ring

end Math
