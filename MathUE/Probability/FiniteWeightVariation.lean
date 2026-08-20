/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Variation bounds for finite nonnegative weights

This file records the finite-weight form of the Jordan decomposition behind
total variation. Unlike the probability-mass-function API, the weights need
not have equal total mass. This makes the results apply directly to finite
subprobability laws without adding an artificial cemetery atom.
-/

noncomputable section

open scoped BigOperators

namespace Math.Probability

variable {α : Type*}

/-- Positive variation of `source - target` on a finite support. -/
def weightPositiveVariationOn
    (support : Finset α) (source target : α → ℝ) : ℝ :=
  ∑ x ∈ support, max (source x - target x) 0

/-- The `L1` distance of two finite weights is their mass difference plus
twice the reverse positive variation. -/
theorem sum_abs_sub_eq_massDifference_add_two_mul_reverseVariation
    (support : Finset α) (source target : α → ℝ) :
    (∑ x ∈ support, |source x - target x|) =
      ((∑ x ∈ support, source x) - ∑ x ∈ support, target x) +
        2 * weightPositiveVariationOn support target source := by
  have hpoint : ∀ x : α,
      |source x - target x| =
        (source x - target x) + 2 * max (target x - source x) 0 := by
    intro x
    by_cases h : 0 ≤ source x - target x
    · rw [abs_of_nonneg h, max_eq_right]
      · ring
      · linarith
    · have hle : source x - target x ≤ 0 := le_of_not_ge h
      rw [abs_of_nonpos hle, max_eq_left]
      · ring
      · linarith
  simp_rw [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_sub_distrib]
  rfl

/-- A bounded observable is Lipschitz, with its sup norm, for the `L1`
distance between arbitrary finite weights. -/
theorem abs_weightedSum_sub_le_mul_sum_abs
    (support : Finset α) (source target payoff : α → ℝ)
    {bound : ℝ} (hpayoff : ∀ x ∈ support, |payoff x| ≤ bound) :
    |(∑ x ∈ support, source x * payoff x) -
        ∑ x ∈ support, target x * payoff x| ≤
      bound * ∑ x ∈ support, |source x - target x| := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ x ∈ support, (source x * payoff x - target x * payoff x)| ≤
        ∑ x ∈ support,
          |source x * payoff x - target x * payoff x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x ∈ support, |source x - target x| * |payoff x| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [show source x * payoff x - target x * payoff x =
        (source x - target x) * payoff x by ring, abs_mul]
    _ ≤ ∑ x ∈ support, |source x - target x| * bound := by
      exact Finset.sum_le_sum fun x hx =>
        mul_le_mul_of_nonneg_left (hpayoff x hx) (abs_nonneg _)
    _ = bound * ∑ x ∈ support, |source x - target x| := by
      rw [← Finset.sum_mul]
      ring

/-- Bounded-observable comparison in terms of total-mass error and reverse
positive variation. -/
theorem abs_weightedSum_sub_le_massError_add_reverseVariation
    (support : Finset α) (source target payoff : α → ℝ)
    {bound totalError : ℝ} (hbound : 0 ≤ bound)
    (hpayoff : ∀ x ∈ support, |payoff x| ≤ bound)
    (hmass :
      |(∑ x ∈ support, source x) -
        ∑ x ∈ support, target x| ≤ totalError) :
    |(∑ x ∈ support, source x * payoff x) -
        ∑ x ∈ support, target x * payoff x| ≤
      bound *
        (totalError +
          2 * weightPositiveVariationOn support target source) := by
  calc
    |(∑ x ∈ support, source x * payoff x) -
          ∑ x ∈ support, target x * payoff x| ≤
        bound * ∑ x ∈ support, |source x - target x| :=
      abs_weightedSum_sub_le_mul_sum_abs support source target payoff
        hpayoff
    _ ≤ bound *
        (totalError +
          2 * weightPositiveVariationOn support target source) := by
      apply mul_le_mul_of_nonneg_left _ hbound
      rw [sum_abs_sub_eq_massDifference_add_two_mul_reverseVariation]
      gcongr
      exact (le_abs_self _).trans hmass

/-- If `target` is dominated by `source` outside controlled and exceptional
sets, reverse variation is paid by the controlled `L1` error and target mass
on the exceptional set. -/
theorem weightPositiveVariationOn_le_controlledError_add_exceptionalMass
    [DecidableEq α]
    (support controlled exceptional : Finset α)
    (source target : α → ℝ)
    (hsource : ∀ x ∈ support, 0 ≤ source x)
    (htarget : ∀ x ∈ support, 0 ≤ target x)
    (hdom : ∀ x ∈ support,
      x ∉ controlled → x ∉ exceptional → target x ≤ source x) :
    weightPositiveVariationOn support target source ≤
      (∑ x ∈ support ∩ controlled, |source x - target x|) +
        ∑ x ∈ support ∩ exceptional, target x := by
  unfold weightPositiveVariationOn
  calc
    (∑ x ∈ support, max (target x - source x) 0) ≤
        ∑ x ∈ support,
          ((if x ∈ controlled then |source x - target x| else 0) +
            if x ∈ exceptional then target x else 0) := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hc : x ∈ controlled
      · have hvariation : max (target x - source x) 0 ≤
            |source x - target x| := by
          apply max_le
          · rw [abs_sub_comm]
            exact le_abs_self _
          · exact abs_nonneg _
        simp only [hc, if_true]
        exact hvariation.trans
          (le_add_of_nonneg_right (by split <;> simp_all))
      · by_cases he : x ∈ exceptional
        · have hvariation : max (target x - source x) 0 ≤ target x := by
            apply max_le
            · linarith [hsource x hx]
            · exact htarget x hx
          simp [hc, he, hvariation]
        · have hvariation : max (target x - source x) 0 = 0 := by
            rw [max_eq_right]
            linarith [hdom x hx hc he]
          simp [hc, he, hvariation]
    _ = (∑ x ∈ support ∩ controlled, |source x - target x|) +
          ∑ x ∈ support ∩ exceptional, target x := by
      rw [Finset.sum_add_distrib]
      congr 1 <;> simp

/-- Direct finite-weight comparison: controlled atoms pay their absolute
error, exceptional atoms pay target mass, and all other atoms are governed by
one-sided domination. -/
theorem abs_weightedSum_sub_le_of_domination_off
    [DecidableEq α]
    (support controlled exceptional : Finset α)
    (source target payoff : α → ℝ)
    {bound totalError controlledError exceptionalMass : ℝ}
    (hbound : 0 ≤ bound)
    (hpayoff : ∀ x ∈ support, |payoff x| ≤ bound)
    (hsource : ∀ x ∈ support, 0 ≤ source x)
    (htarget : ∀ x ∈ support, 0 ≤ target x)
    (hdom : ∀ x ∈ support,
      x ∉ controlled → x ∉ exceptional → target x ≤ source x)
    (hmass :
      |(∑ x ∈ support, source x) -
        ∑ x ∈ support, target x| ≤ totalError)
    (hcontrolled :
      (∑ x ∈ support ∩ controlled, |source x - target x|) ≤
        controlledError)
    (hexceptional :
      (∑ x ∈ support ∩ exceptional, target x) ≤ exceptionalMass) :
    |(∑ x ∈ support, source x * payoff x) -
        ∑ x ∈ support, target x * payoff x| ≤
      bound *
        (totalError + 2 * (controlledError + exceptionalMass)) := by
  have hvariation :=
    weightPositiveVariationOn_le_controlledError_add_exceptionalMass
      support controlled exceptional source target hsource htarget hdom
  have hvariationBound :
      weightPositiveVariationOn support target source ≤
        controlledError + exceptionalMass :=
    hvariation.trans (add_le_add hcontrolled hexceptional)
  calc
    |(∑ x ∈ support, source x * payoff x) -
          ∑ x ∈ support, target x * payoff x| ≤
        bound *
          (totalError +
            2 * weightPositiveVariationOn support target source) :=
      abs_weightedSum_sub_le_massError_add_reverseVariation
        support source target payoff hbound hpayoff hmass
    _ ≤ bound *
        (totalError + 2 * (controlledError + exceptionalMass)) := by
      gcongr

end Math.Probability
