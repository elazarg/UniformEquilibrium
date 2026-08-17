/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.CirculantColliderCompletion

/-!
# One collider-completion pocket table and its algebraic cyclic equilibrium

This file fixes the five-player collider completion of
`Research/Quitting/CirculantColliderCompletion.lean` at solo self value `1`,
joint value `-2`, and margin vector

`(m 1, m 2, m 3, m 4) = (-1/2, 2, 1, -2)`.

The table sits in the pocket — `m 1 < 0`, `m 4 < 0`, `0 ≤ m 2`, `0 ≤ m 3`, and
margin sum `1/2 > 0` — and its adjacent pairs are not sure exit sets, so it is
not screened out by the sure-exit test.  It nevertheless has a uniform
equilibrium payoff.

The witness is the period-five single-quitter profile of constant step four,
in which player `4 * k` quits at phase `k` with probability `1 - q` at every
phase, where `q` is the unique root in `(0, 1)` of the cubic
`q³ - 4q² - 2q + 4`.  The realized payoff is

`(1, 1, 2q - q²/2, 3 - 5q/2 + q²/2, (1 + q)/2)`.

Both the profile and the payoff depend on `q`, which is irrational; the two
statements below that mention `q` therefore quantify over an arbitrary root of
the cubic in `(0, 1)`, and `candidateCubic_root_unique` shows there is only
one.

This is a checked statement about one table, not a general theorem about
collider completions.  The general statement is
`GameTheory.CirculantColliderCompletion.isEmpty_counterexampleRegime_colliderPocket`.
-/

noncomputable section

namespace GameTheory
namespace ColliderPocketCandidateEquilibrium

open CirculantConstantStepCycle CirculantColliderCompletion
open QuittingSureSetOwnerRepair

/-! ## The table -/

/-- The margin vector `(0, -1/2, 2, 1, -2)`. -/
def candidateMargin : ZMod 5 → ℝ :=
  fun d =>
    if d = 1 then -(1 / 2)
    else if d = 2 then 2
    else if d = 3 then 1
    else if d = 4 then -2
    else 0

@[simp] theorem candidateMargin_zero : candidateMargin 0 = 0 := by
  rw [candidateMargin]
  norm_num [show (0 : ZMod 5) ≠ 1 from by decide, show (0 : ZMod 5) ≠ 2 from by decide,
    show (0 : ZMod 5) ≠ 3 from by decide, show (0 : ZMod 5) ≠ 4 from by decide]

@[simp] theorem candidateMargin_one : candidateMargin 1 = -(1 / 2) := by
  rw [candidateMargin, if_pos rfl]

@[simp] theorem candidateMargin_two : candidateMargin 2 = 2 := by
  rw [candidateMargin, if_neg (by decide), if_pos rfl]

@[simp] theorem candidateMargin_three : candidateMargin 3 = 1 := by
  rw [candidateMargin, if_neg (by decide), if_neg (by decide), if_pos rfl]

@[simp] theorem candidateMargin_four : candidateMargin 4 = -2 := by
  rw [candidateMargin, if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_pos rfl]

/-- The collider completion at solo self value `1`, joint value `-2`, and the
margin vector `candidateMargin`. -/
def candidateReward : {S : Finset (ZMod 5) // S.Nonempty} → Payoff (ZMod 5) :=
  colliderReward 1 (-2) candidateMargin

/-! ## The anchor cubic -/

/-- The cubic whose root in `(0, 1)` is the per-phase survival probability of
the witness profile. -/
def candidateCubic (q : ℝ) : ℝ := q ^ 3 - 4 * q ^ 2 - 2 * q + 4

/-- The step-four anchor of the table is the cubic scaled by `-1/2`. -/
theorem stepAnchor_candidateMargin (q : ℝ) :
    stepAnchor candidateMargin 4 q = -(candidateCubic q) / 2 := by
  rw [stepAnchor_eq, candidateCubic,
    show (2 : ZMod 5) * 4 = 3 from by decide,
    show (3 : ZMod 5) * 4 = 2 from by decide,
    show (4 : ZMod 5) * 4 = 1 from by decide,
    candidateMargin_one, candidateMargin_two, candidateMargin_three,
    candidateMargin_four]
  ring

/-- **The cubic has a root strictly inside the unit interval.** -/
theorem exists_candidateCubic_root :
    ∃ q ∈ Set.Ioo (0 : ℝ) 1, candidateCubic q = 0 := by
  obtain ⟨q, hq, hroot⟩ :=
    exists_stepAnchor_root candidateMargin (c := 4) candidateMargin_zero (by decide)
      (by norm_num) (by
        have hfive : (∑ e : ZMod 5, candidateMargin e) =
            candidateMargin 0 + candidateMargin 1 + candidateMargin 2 +
              candidateMargin 3 + candidateMargin 4 :=
          Fin.sum_univ_five (fun e : ZMod 5 => candidateMargin e)
        rw [hfive]
        norm_num)
  refine ⟨q, hq, ?_⟩
  rw [stepAnchor_candidateMargin] at hroot
  linarith

/-- **The root is unique in the unit interval.**  The cubic is strictly
decreasing there. -/
theorem candidateCubic_root_unique {q₁ q₂ : ℝ}
    (h₁ : q₁ ∈ Set.Ioo (0 : ℝ) 1) (h₂ : q₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hr₁ : candidateCubic q₁ = 0) (hr₂ : candidateCubic q₂ = 0) : q₁ = q₂ := by
  obtain ⟨ha₁, hb₁⟩ := h₁
  obtain ⟨ha₂, hb₂⟩ := h₂
  rw [candidateCubic] at hr₁ hr₂
  have hfac : (q₁ - q₂) *
      (q₁ ^ 2 + q₁ * q₂ + q₂ ^ 2 - 4 * (q₁ + q₂) - 2) = 0 := by
    linear_combination hr₁ - hr₂
  have e₁ : q₁ ^ 2 < q₁ := by nlinarith
  have e₂ : q₂ ^ 2 < q₂ := by nlinarith
  have e₃ : q₁ * q₂ < q₂ := by nlinarith
  have hbracket : q₁ ^ 2 + q₁ * q₂ + q₂ ^ 2 - 4 * (q₁ + q₂) - 2 < 0 := by linarith
  rcases mul_eq_zero.mp hfac with hzero | hzero
  · linarith
  · exact absurd hzero (ne_of_lt hbracket)

/-! ## The realized payoff -/

/-- The payoff realized by the witness profile:
`(1, 1, 2q - q²/2, 3 - 5q/2 + q²/2, (1 + q)/2)`. -/
def candidatePayoff (q : ℝ) : Payoff (ZMod 5) :=
  fun who =>
    if who = 2 then 2 * q - q ^ 2 / 2
    else if who = 3 then 3 - 5 * q / 2 + q ^ 2 / 2
    else if who = 4 then (1 + q) / 2
    else 1

/-- At a root of the cubic the displayed origin row of the step-four profile is
the payoff above. -/
theorem stepValue_zero_eq_candidatePayoff {q : ℝ} (hroot : candidateCubic q = 0) :
    stepValue candidateMargin 4 q 1 1 0 = candidatePayoff q := by
  rw [candidateCubic] at hroot
  funext who
  rw [stepValue_zero_apply, candidatePayoff, one_mul]
  rcases zmod_five_cases who with h | h | h | h | h <;> subst h
  · rw [stepSlack_zero, if_neg (by decide), if_neg (by decide), if_neg (by decide)]
    ring
  · rw [stepSlack_one, if_neg (by decide), if_neg (by decide), if_neg (by decide)]
    ring
  · rw [stepSlack_two, if_pos rfl, show (2 : ZMod 5) * 4 = 3 from by decide,
      show (3 : ZMod 5) * 4 = 2 from by decide,
      show (4 : ZMod 5) * 4 = 1 from by decide,
      candidateMargin_one, candidateMargin_two, candidateMargin_three]
    linear_combination ((1 : ℝ) / 2) * hroot
  · rw [stepSlack_three, if_neg (by decide), if_pos rfl,
      show (3 : ZMod 5) * 4 = 2 from by decide,
      show (4 : ZMod 5) * 4 = 1 from by decide,
      candidateMargin_one, candidateMargin_two]
    ring
  · rw [stepSlack_four, if_neg (by decide), if_neg (by decide), if_pos rfl,
      show (4 : ZMod 5) * 4 = 1 from by decide, candidateMargin_one]
    ring

/-! ## The headline -/

/-- **The table has the uniform-equilibrium payoff
`(1, 1, 2q - q²/2, 3 - 5q/2 + q²/2, (1 + q)/2)`** at any root `q` of
`q³ - 4q² - 2q + 4` in `(0, 1)`.  The witness is the period-five single-quitter
profile of constant step four at the uniform quit probability `1 - q`; the
deviation class is all behavior strategies, not stopping times. -/
theorem candidate_isUniformEquilibriumPayoff {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hroot : candidateCubic q = 0) :
    (quittingGame candidateReward).IsUniformEquilibriumPayoff none
      (candidatePayoff q) := by
  have hanchor : stepAnchor candidateMargin 4 q = 0 := by
    rw [stepAnchor_candidateMargin, hroot]
    norm_num
  have hcubic := hroot
  rw [candidateCubic] at hcubic
  rw [← stepValue_zero_eq_candidatePayoff hroot]
  refine isUniformEquilibriumPayoff_constantStep (c' := 1)
    (isCirculantPairTable_colliderReward 1 (-2) candidateMargin candidateMargin_zero)
    (by decide) (by norm_num) hq.1 hq.2 hanchor ?_ ?_ ?_ ?_
  · rw [colliderJoin_four]
  · rw [show (2 : ZMod 5) * 4 = 3 from by decide,
      show (3 : ZMod 5) * 4 = 2 from by decide,
      show (4 : ZMod 5) * 4 = 1 from by decide,
      colliderJoin_of_ne 1 (-2) (by decide),
      candidateMargin_one, candidateMargin_two, candidateMargin_three]
    nlinarith [hq.1, hq.2, sq_nonneg q]
  · rw [show (3 : ZMod 5) * 4 = 2 from by decide,
      show (4 : ZMod 5) * 4 = 1 from by decide,
      colliderJoin_of_ne 1 (-2) (by decide),
      candidateMargin_one, candidateMargin_two]
    nlinarith [hq.1, hq.2]
  · rw [show (4 : ZMod 5) * 4 = 1 from by decide,
      colliderJoin_of_ne 1 (-2) (by decide), candidateMargin_one]
    norm_num

/-- **The table is in no counterexample regime.**  A terminal exploitability
gap is incompatible with an existing uniform-equilibrium payoff. -/
theorem candidate_isEmpty_counterexampleRegime :
    IsEmpty (QuittingCounterexampleRegime candidateReward) := by
  refine isEmpty_counterexampleRegime_colliderPocket candidateMargin_zero
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_
  rw [candidateMargin_one]
  norm_num

/-! ## The sure-exit screen does not see the table -/

/-- **No adjacent pair of the table is a sure exit set.**  The owner of an
adjacent pair strictly gains by stepping out: it is paid `1/2` alone against
`-2` inside the pair. -/
theorem candidate_not_isQuittingSureExitSet (y : ZMod 5) :
    ¬ IsQuittingSureExitSet candidateReward {y, y + 1} := by
  refine not_isQuittingSureExitSet_of_strict_toggle candidateReward
    (Or.inl ⟨y, by simp, ?_⟩)
  rw [candidateReward, erase_adjacent_left, quittingSetReward_singleton,
    quittingSetReward_adjacent_owner, show y + 1 - y = 1 from by ring,
    candidateMargin_one]
  norm_num

end ColliderPocketCandidateEquilibrium
end GameTheory
