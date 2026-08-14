import Mathlib

/-!
# E09: signed target transport

This file is deliberately game-free.  It isolates the finite-sum algebra that
a stopped-child composition theorem should consume:

* on a unilateral-deviation law, the expected child target is bounded above by
  the parent target;
* each child payoff is bounded above by its declared target;
* therefore the expected child payoff is bounded above at the parent.

The final two examples formally retain the Q84 fence: signed branch errors can
cancel exactly even when their expected absolute size is linear.
-/

namespace Experiments.SignedTargetTransport

open scoped BigOperators

variable {Child : Type*} [Fintype Child]

theorem weighted_upper_transport
    (weight payoff target : Child → ℝ)
    (parent error targetError : ℝ)
    (weight_nonneg : ∀ child, 0 ≤ weight child)
    (weight_sum : ∑ child, weight child = 1)
    (child_upper : ∀ child, payoff child ≤ target child + error)
    (signed_target_upper :
      ∑ child, weight child * target child ≤ parent + targetError) :
    ∑ child, weight child * payoff child ≤
      parent + targetError + error := by
  calc
    ∑ child, weight child * payoff child ≤
        ∑ child, weight child * (target child + error) := by
      apply Finset.sum_le_sum
      intro child _
      exact mul_le_mul_of_nonneg_left (child_upper child) (weight_nonneg child)
    _ = (∑ child, weight child * target child) + error := by
      simp only [mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, weight_sum, one_mul]
    _ ≤ parent + targetError + error := by
      linarith

theorem weighted_lower_transport
    (weight payoff target : Child → ℝ)
    (parent error targetError : ℝ)
    (weight_nonneg : ∀ child, 0 ≤ weight child)
    (weight_sum : ∑ child, weight child = 1)
    (child_lower : ∀ child, target child - error ≤ payoff child)
    (signed_target_lower :
      parent - targetError ≤ ∑ child, weight child * target child) :
    parent - targetError - error ≤
      ∑ child, weight child * payoff child := by
  calc
    parent - targetError - error ≤
        (∑ child, weight child * target child) - error := by
      exact sub_le_sub_right signed_target_lower error
    _ = ∑ child, weight child * (target child - error) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul, weight_sum, one_mul]
    _ ≤ ∑ child, weight child * payoff child := by
      apply Finset.sum_le_sum
      intro child _
      exact mul_le_mul_of_nonneg_left (child_lower child) (weight_nonneg child)

noncomputable def fairWeight (_ : Fin 2) : ℝ := 1 / 2

def cancelingError : Fin 2 → ℝ
  | 0 => 1
  | 1 => -1

example : ∑ child : Fin 2, fairWeight child * cancelingError child = 0 := by
  norm_num [Fin.sum_univ_two, fairWeight, cancelingError]

example : ∑ child : Fin 2, fairWeight child * |cancelingError child| = 1 := by
  norm_num [Fin.sum_univ_two, fairWeight, cancelingError, abs_of_nonneg, abs_of_nonpos]

end Experiments.SignedTargetTransport
