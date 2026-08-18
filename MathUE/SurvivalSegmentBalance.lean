/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.CyclicMaxAffineBound

/-!
# Balance across a segment whose two ends carry the same value

Fix per-step acting probabilities `p` and survival factors `β` with
`p t + β t = 1`, and a value sequence obeying the one-step recursion
`V t = p t * a t + β t * V (t + 1)`.  `MathUE/CyclicMaxAffineBound.lean`
unrolls that recursion: `V 0` is the survival-weighted accumulation of the
`a`'s over the segment plus the surviving remainder times `V L`.

Complementarity adds one identity the unrolling itself does not use: the
accumulated weights and the surviving mass total one.  Consequently, when the
two ends of the segment carry the *same* value `R`, the unrolling collapses to

`∑ t < L, (∏ u < t, β u) * p t * (a t - R) = 0`,

a weighted balance of the deviations of the `a`'s from `R`.  With strictly
positive weights this is a sign screen: the deviations across the segment are
either all zero, or include both a positive and a negative one.

## Main results

* `Math.weightedRate_add_survivalProduct_eq_one` — the weights total one
* `Math.sum_survivalProduct_mul_deviation_eq_zero` — the balance
* `Math.eq_of_nonneg_of_segmentBalance`, `Math.eq_of_nonpos_of_segmentBalance`
  — a one-signed segment has only zero deviations
* `Math.exists_lt_and_exists_gt_of_segmentBalance` — the screen: a nonzero
  deviation forces both signs
-/

noncomputable section

namespace Math

open Finset CyclicMaxAffine

/-! ## The weights of a segment -/

/-- **Total mass of a segment.**  Under complementarity each step either acts,
carrying the survival weight of the steps before it, or the whole segment
survives.  It is the unrolling of the constant sequence `1`. -/
theorem weightedRate_add_survivalProduct_eq_one {p β : ℕ → ℝ}
    (hcompl : ∀ t, p t + β t = 1) (L : ℕ) :
    weightedRate p β L + survivalProduct β L = 1 := by
  have hunroll := prefix_eq p β (fun _ ↦ (1 : ℝ)) L (fun t _ ↦ by
    show (1 : ℝ) = β t * 1 + p t
    linarith [hcompl t])
  simpa using hunroll.symm

/-! ## The balance -/

/-- **Segment balance.**  A segment whose entry and exit values agree weights
the deviations of its intermediate rewards from that common value to zero. -/
theorem sum_survivalProduct_mul_deviation_eq_zero {p β a V : ℕ → ℝ} {R : ℝ} {L : ℕ}
    (hcompl : ∀ t, p t + β t = 1)
    (hrec : ∀ t, t < L → V t = p t * a t + β t * V (t + 1))
    (hentry : V 0 = R) (hexit : V L = R) :
    ∑ t ∈ range L, survivalProduct β t * p t * (a t - R) = 0 := by
  have hunroll := prefix_eq (fun t ↦ p t * a t) β V L (fun t ht ↦ by
    rw [hrec t ht]; ring)
  have hmass := weightedRate_add_survivalProduct_eq_one hcompl L
  have hsplit : ∑ t ∈ range L, survivalProduct β t * p t * (a t - R) =
      weightedRate (fun t ↦ p t * a t) β L - weightedRate p β L * R := by
    rw [weightedRate, weightedRate, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ ↦ by ring
  rw [hentry, hexit] at hunroll
  rw [hsplit]
  linear_combination -hunroll - R * hmass

/-! ## The sign screen -/

/-- A segment all of whose deviations are nonnegative has only zero
deviations. -/
theorem eq_of_nonneg_of_segmentBalance {p β a : ℕ → ℝ} {R : ℝ} {L : ℕ}
    (hβ : ∀ t, t < L → 0 < β t) (hp : ∀ t, t < L → 0 < p t)
    (hbal : ∑ t ∈ range L, survivalProduct β t * p t * (a t - R) = 0)
    (hsign : ∀ t, t < L → R ≤ a t) {t : ℕ} (ht : t < L) : a t = R := by
  have hsurv : ∀ u, u ≤ L → 0 < survivalProduct β u := by
    intro u hu
    exact Finset.prod_pos fun i hi ↦ hβ i (lt_of_lt_of_le (Finset.mem_range.mp hi) hu)
  have hterm : ∀ u ∈ range L, 0 ≤ survivalProduct β u * p u * (a u - R) := by
    intro u hu
    have hu' := Finset.mem_range.mp hu
    exact mul_nonneg (mul_nonneg (hsurv u hu'.le).le (hp u hu').le)
      (by linarith [hsign u hu'])
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hbal t (Finset.mem_range.mpr ht)
  have hweight : 0 < survivalProduct β t * p t := mul_pos (hsurv t ht.le) (hp t ht)
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h (ne_of_gt hweight)
  · linarith

/-- A segment all of whose deviations are nonpositive has only zero
deviations. -/
theorem eq_of_nonpos_of_segmentBalance {p β a : ℕ → ℝ} {R : ℝ} {L : ℕ}
    (hβ : ∀ t, t < L → 0 < β t) (hp : ∀ t, t < L → 0 < p t)
    (hbal : ∑ t ∈ range L, survivalProduct β t * p t * (a t - R) = 0)
    (hsign : ∀ t, t < L → a t ≤ R) {t : ℕ} (ht : t < L) : a t = R := by
  have hneg : ∑ u ∈ range L, survivalProduct β u * p u * ((fun v ↦ -a v) u - -R) = 0 := by
    have hrewrite : ∑ u ∈ range L, survivalProduct β u * p u * ((fun v ↦ -a v) u - -R) =
        -∑ u ∈ range L, survivalProduct β u * p u * (a u - R) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun u _ ↦ by ring
    rw [hrewrite, hbal, neg_zero]
  have hkey := eq_of_nonneg_of_segmentBalance (a := fun v ↦ -a v) (R := -R) hβ hp hneg
    (fun u hu ↦ by linarith [hsign u hu]) ht
  linarith [hkey]

/-- **The screen.**  A deviation different from zero anywhere in the segment
forces both a strictly positive and a strictly negative deviation in the same
stretch. -/
theorem exists_lt_and_exists_gt_of_segmentBalance {p β a : ℕ → ℝ} {R : ℝ} {L : ℕ}
    (hβ : ∀ t, t < L → 0 < β t) (hp : ∀ t, t < L → 0 < p t)
    (hbal : ∑ t ∈ range L, survivalProduct β t * p t * (a t - R) = 0)
    {t₀ : ℕ} (ht₀ : t₀ < L) (hne : a t₀ ≠ R) :
    (∃ t, t < L ∧ R < a t) ∧ (∃ t, t < L ∧ a t < R) := by
  constructor
  · by_contra hcontra
    push Not at hcontra
    exact hne (eq_of_nonpos_of_segmentBalance hβ hp hbal (fun u hu ↦ hcontra u hu) ht₀)
  · by_contra hcontra
    push Not at hcontra
    exact hne (eq_of_nonneg_of_segmentBalance hβ hp hbal (fun u hu ↦ hcontra u hu) ht₀)

end Math
