import Mathlib

/-!
# Exact scalar checks for the cyclic four-player T x P x W witness

The table-wide packet theorem and the exact tail-step identities already live
in `TailPacketCyclicFourWitness.lean`.  This companion probe certifies the new
triple-specific facts:

* after dropping the original date zero and reindexing the tail, player 2's
  deterministic phase-stop values are positive and strictly increase from
  one phase to the next;
* the first phase already gives the common `eta / 2` margin; and
* the discarded hazard `1 / 3` supports the exact stationary Bellman
  self-loop which shows that neither global terminal instability nor global
  charge capacity is being claimed.

The strategic passage from deterministic stopping times to arbitrary
behavioral deviations is the repository's `BehaviorPureTimeExtremality`
theorem; this file isolates only the rational algebra needed by the argument.
-/

namespace GameTheory.CounterexamplePairwiseConsistency.TPW

/-- Write `x = 2^(k+1)` at an original tail date `k >= 1`.  The owner hazard
is `1/(2x-1)`, and at the next date it is `1/(4x-1)`.  Player 2's conditional
stop payoff is `1-5p`.  It is positive after the one-date shift, and including
one more owner-survival factor strictly increases the stop value. -/
theorem shifted_phase_factor_increases (x : ℝ) (hx : 4 ≤ x) :
    0 < 1 - 5 / (2 * x - 1) ∧
      1 - 5 / (2 * x - 1) <
        (1 - 1 / (2 * x - 1)) * (1 - 5 / (4 * x - 1)) := by
  have hden₁ : 0 < 2 * x - 1 := by linarith
  have hden₂ : 0 < 4 * x - 1 := by linarith
  have hfive : 5 / (2 * x - 1) < 1 := by
    rw [div_lt_one hden₁]
    linarith
  constructor
  · linarith
  · have hcompare : 5 / (4 * x - 1) < 4 / (2 * x - 1) := by
      rw [div_lt_div_iff₀ hden₂ hden₁]
      nlinarith
    have hcross :
        0 < 5 / (2 * x - 1) * (1 / (4 * x - 1)) := by
      positivity
    have hgap :
        0 < 4 / (2 * x - 1) - 5 / (4 * x - 1) +
          5 / (2 * x - 1) * (1 / (4 * x - 1)) := by
      linarith
    have hid :
        (1 - 1 / (2 * x - 1)) * (1 - 5 / (4 * x - 1)) =
          (1 - 5 / (2 * x - 1)) +
            (4 / (2 * x - 1) - 5 / (4 * x - 1) +
              5 / (2 * x - 1) * (1 / (4 * x - 1))) := by
      ring
    rw [hid]
    linarith

/-- Multiplying by a positive prefix-survival probability preserves the
strict phase improvement. -/
theorem shifted_phase_value_increases
    (pref x : ℝ) (hpref : 0 < pref) (hx : 4 ≤ x) :
    pref * (1 - 5 / (2 * x - 1)) <
      pref * (1 - 1 / (2 * x - 1)) *
        (1 - 5 / (4 * x - 1)) := by
  have hfactor := (shifted_phase_factor_increases x hx).2
  nlinarith [mul_pos hpref
    (sub_pos.mpr hfactor)]

/-- Every first phase in the shifted canonical family has value at least
`2/7`, while the common triple margin asks only for `eta/2 = 1/104`. -/
theorem shifted_first_phase_common_margin (x : ℝ) (hx : 4 ≤ x) :
    (2 / 7 : ℝ) ≤ 1 - 5 / (2 * x - 1) ∧
      (1 / 52 : ℝ) / 2 < 2 / 7 := by
  have hden : 0 < 2 * x - 1 := by linarith
  constructor
  · have hfrac : 5 / (2 * x - 1) ≤ (5 / 7 : ℝ) := by
      rw [div_le_iff₀ hden]
      nlinarith
    linarith
  · norm_num

/-- Exact arithmetic at the original date-zero hazard `p=1/3`.  The first
line gives every nonowner's pure-Quit endpoint against owner 0; the remaining
lines are the Continue endpoints at `w=(1,4,0,0)` and the positive charge. -/
theorem discarded_root_stationary_self_loop_arithmetic :
    ((1 - (1 / 3 : ℝ)) * 1 + (1 / 3 : ℝ) * (-4) = -2 / 3) ∧
      ((1 / 3 : ℝ) * 4 + (1 - 1 / 3) * 4 = 4) ∧
      ((1 / 3 : ℝ) * 0 + (1 - 1 / 3) * 0 = 0) ∧
      (0 < (1 / 3 : ℝ)) := by
  norm_num

/-- The symmetric funded packet has mixture `5/4`, refusal `4/3`, and hence
more than the common table-wide margin `1/52`. -/
theorem symmetric_packet_common_margin :
    ((1 : ℝ) + 4) / 4 = 5 / 4 ∧
      (4 / 3 : ℝ) - 5 / 4 = 1 / 12 ∧
      (1 / 52 : ℝ) ≤ 1 / 12 := by
  norm_num


end GameTheory.CounterexamplePairwiseConsistency.TPW
