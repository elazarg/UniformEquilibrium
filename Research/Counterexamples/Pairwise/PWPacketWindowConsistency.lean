/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib

/-!
# Exact arithmetic for the P x W consistency witness

This file checks the two quantitative estimates used by
`PW_PACKET_WINDOW_REPORT.md`.

The four singleton rows are `1 + b_i`, where

* `b_0 = x_1 - x_2`,
* `b_1 = x_2 - x_3`,
* `b_2 = x_3 - x_0`, and
* `b_3 = x_0 - x_1 / 2`.

Packet feasibility says that all four `b_i` are nonnegative.  The first
theorem proves the table-wide refusal margin `1 / 256`.  The second theorem
checks the phasewise singleton-probability estimate behind the periodic
refusal obstruction.
-/

namespace GameTheory.CounterexamplePairwiseConsistency.PW

/-- Every feasible packet mass has all four coordinates at least `1 / 8`. -/
theorem packet_coordinate_lower_bounds
    {x0 x1 x2 x3 : ℝ}
    (hsum : x0 + x1 + x2 + x3 = 1)
    (hb0 : 0 ≤ x1 - x2) (hb1 : 0 ≤ x2 - x3)
    (hb2 : 0 ≤ x3 - x0) (hb3 : 0 ≤ x0 - x1 / 2) :
    1 / 8 ≤ x0 ∧ 1 / 8 ≤ x1 ∧ 1 / 8 ≤ x2 ∧ 1 / 8 ≤ x3 := by
  have hx2_le_x1 : x2 ≤ x1 := by linarith
  have hx3_le_x2 : x3 ≤ x2 := by linarith
  have hx0_le_x3 : x0 ≤ x3 := by linarith
  have hx1_le_two_x0 : x1 ≤ 2 * x0 := by linarith
  have hx1_quarter : 1 / 4 ≤ x1 := by linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The exact table-wide packet refusal margin.  The four displayed terms
are `refusal_i - mixture_i`; at least one is at least `1 / 256`. -/
theorem packet_uniform_refusal_gap
    {x0 x1 x2 x3 : ℝ}
    (hsum : x0 + x1 + x2 + x3 = 1)
    (hb0 : 0 ≤ x1 - x2) (hb1 : 0 ≤ x2 - x3)
    (hb2 : 0 ≤ x3 - x0) (hb3 : 0 ≤ x0 - x1 / 2) :
    1 / 256 ≤ x0 * (x1 - x2) / (1 - x0) ∨
      1 / 256 ≤ x1 * (x2 - x3) / (1 - x1) ∨
      1 / 256 ≤ x2 * (x3 - x0) / (1 - x2) ∨
      1 / 256 ≤ x3 * (x0 - x1 / 2) / (1 - x3) := by
  obtain ⟨hx0e, hx1e, hx2e, hx3e⟩ :=
    packet_coordinate_lower_bounds hsum hb0 hb1 hb2 hb3
  have hx0lt : x0 < 1 := by linarith
  have hx1lt : x1 < 1 := by linarith
  have hx2lt : x2 < 1 := by linarith
  have hx3lt : x3 < 1 := by linarith
  have hx1_quarter : 1 / 4 ≤ x1 := by linarith
  by_cases h0 : 1 / 32 ≤ x1 - x2
  · left
    rw [le_div_iff₀ (by linarith : 0 < 1 - x0)]
    nlinarith
  by_cases h1 : 1 / 32 ≤ x2 - x3
  · right; left
    rw [le_div_iff₀ (by linarith : 0 < 1 - x1)]
    nlinarith
  by_cases h2 : 1 / 32 ≤ x3 - x0
  · right; right; left
    rw [le_div_iff₀ (by linarith : 0 < 1 - x2)]
    nlinarith
  · right; right; right
    have h3 : 1 / 32 ≤ x0 - x1 / 2 := by linarith
    rw [le_div_iff₀ (by linarith : 0 < 1 - x3)]
    nlinarith

/-- With three symmetric opponents and phase hazard at most `1 / 200`, the
conditional probability that an absorbing phase has exactly one quitter is
at least `99 / 100`. -/
theorem three_opponent_singleton_ratio
    {p : ℝ} (hp : p ≤ 1 / 200) :
    99 / 100 ≤ 3 * (1 - p) ^ 2 / (3 - 3 * p + p ^ 2) := by
  have hden : 0 < 3 - 3 * p + p ^ 2 := by nlinarith
  rw [le_div_iff₀ hden]
  nlinarith [sq_nonneg p]

/-- A phasewise singleton-ratio bound passes to the terminal phase mixture.
This is the finite convexity step used for every periodically repeated word. -/
theorem weighted_singleton_ratio_lower_bound
    {κ : Type} [Fintype κ]
    (weight ratio : κ → ℝ)
    (hweight : ∀ phase, 0 ≤ weight phase)
    (hsum : ∑ phase, weight phase = 1)
    (hratio : ∀ phase, 99 / 100 ≤ ratio phase) :
    99 / 100 ≤ ∑ phase, weight phase * ratio phase := by
  calc
    (99 / 100 : ℝ) = ∑ phase, weight phase * (99 / 100) := by
      rw [← Finset.sum_mul, hsum]
      norm_num
    _ ≤ ∑ phase, weight phase * ratio phase := by
      exact Finset.sum_le_sum fun phase _ ↦
        mul_le_mul_of_nonneg_left (hratio phase) (hweight phase)

/-- The exact payoff gap used for every canonical periodic window. -/
theorem periodic_refusal_gap_arithmetic :
    (7 / 6 : ℝ) * (99 / 100) - 9 / 8 = 3 / 100 ∧
      (1 / 32 : ℝ) / 2 < 3 / 100 := by
  norm_num

/-- The selected uniform packet has fourth-player mixture `9 / 8`, refusal
value `7 / 6`, and refusal gain `1 / 24`. -/
theorem selected_packet_arithmetic :
    ((2 : ℝ) + 1 / 2 + 1 + 1) / 4 = 9 / 8 ∧
      ((2 : ℝ) + 1 / 2 + 1) / 3 = 7 / 6 ∧
      (7 / 6 : ℝ) - 9 / 8 = 1 / 24 := by
  norm_num


end GameTheory.CounterexamplePairwiseConsistency.PW
