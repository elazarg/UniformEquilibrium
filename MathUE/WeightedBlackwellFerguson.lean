/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Weighted Blackwell--Ferguson scalar identities

This module records the asymmetric scalar mechanism behind a two-step
Blackwell--Ferguson stopping rule.  Let `a + b = 1`, with `a ≥ b > 0`, and
put `c = a - b`.  A centered increment is `-b` with probability `a` and `a`
with probability `b`.  At denominator `D`, the stopping probability

`a * b / (D * (D + c))`

supports exact Bellman identities for the reciprocal potential
`-a * b / D`.  The same quadratic denominator has a one-step energy drift
of exactly `a * b` before stopping.

Everything here is game-independent real algebra.  In particular, this
module does not construct a stochastic-game behavior strategy.
-/

noncomputable section

namespace MathUE
namespace WeightedBlackwellFerguson

/-- The asymmetric stopping probability. -/
def stopProbability (a b D : ℝ) : ℝ :=
  a * b / (D * (D + (a - b)))

/-- The reciprocal Bellman potential. -/
def potential (a b D : ℝ) : ℝ :=
  -(a * b) / D

/-- The quadratic energy matched to the stopping probability. -/
def energy (a b D : ℝ) : ℝ :=
  D * (D + (a - b))

theorem energy_eq_denominator (a b D : ℝ) :
    energy a b D = D * (D + (a - b)) :=
  rfl

theorem energy_pos {a b D : ℝ}
    (hab : b ≤ a) (hb : 0 < b) (hD : b ≤ D) :
    0 < energy a b D := by
  unfold energy
  have hDpos : 0 < D := hb.trans_le hD
  have hsecond : 0 < D + (a - b) := by linarith
  positivity

theorem stopProbability_pos {a b D : ℝ}
    (hab : b ≤ a) (hb : 0 < b) (hD : b ≤ D) :
    0 < stopProbability a b D := by
  unfold stopProbability
  have ha : 0 < a := hb.trans_le hab
  exact div_pos (mul_pos ha hb) (energy_pos hab hb hD)

theorem stopProbability_nonneg {a b D : ℝ}
    (hab : b ≤ a) (hb : 0 < b) (hD : b ≤ D) :
    0 ≤ stopProbability a b D :=
  (stopProbability_pos hab hb hD).le

/-- On the admissible half-line `D ≥ b`, the stopping probability is at
most one.  Equality holds at `D = b`. -/
theorem stopProbability_le_one {a b D : ℝ}
    (hab : b ≤ a) (hb : 0 < b) (hD : b ≤ D) :
    stopProbability a b D ≤ 1 := by
  unfold stopProbability
  have henergy := energy_pos hab hb hD
  change a * b / energy a b D ≤ 1
  rw [div_le_one henergy]
  have hfirst : b * a ≤ D * a :=
    mul_le_mul_of_nonneg_right hD (hb.trans_le hab).le
  have hsecond : D * a ≤ D * (D + (a - b)) := by
    apply mul_le_mul_of_nonneg_left _ (hb.trans_le hD).le
    linarith
  calc
    a * b = b * a := mul_comm _ _
    _ ≤ D * a := hfirst
    _ ≤ D * (D + (a - b)) := hsecond
    _ = energy a b D := rfl

@[simp] theorem stopProbability_at_floor {a b : ℝ} (ha : a ≠ 0)
    (hb : b ≠ 0) :
    stopProbability a b b = 1 := by
  unfold stopProbability
  rw [show b * (b + (a - b)) = a * b by ring,
    div_self (mul_ne_zero ha hb)]

theorem potential_nonpos {a b D : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hD : 0 ≤ D) :
    potential a b D ≤ 0 := by
  unfold potential
  rw [neg_div]
  exact neg_nonpos.mpr (div_nonneg (mul_nonneg ha hb) hD)

theorem potential_strictMono_on_pos {a b D E : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hD : 0 < D) (hDE : D ≤ E) :
    potential a b D ≤ potential a b E := by
  unfold potential
  have hE : 0 < E := hD.trans_le hDE
  rw [neg_div, neg_div]
  exact neg_le_neg (div_le_div_of_nonneg_left (mul_nonneg ha.le hb.le) hD hDE)

/-- Exact Bellman identity for the `-b` increment. -/
theorem potential_sub_id {a b D : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hD : D ≠ 0)
    (hDb : D - b ≠ 0) (hDc : D + (a - b) ≠ 0) :
    stopProbability a b D * b +
        (1 - stopProbability a b D) * potential a b (D - b) =
      potential a b D := by
  unfold stopProbability potential
  field_simp
  ring

/-- Exact Bellman identity for the `+a` increment. -/
theorem potential_add_id {a b D : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hD : D ≠ 0)
    (hDa : D + a ≠ 0) (hDc : D + (a - b) ≠ 0) :
    -stopProbability a b D * a +
        (1 - stopProbability a b D) * potential a b (D + a) =
      potential a b D := by
  unfold stopProbability potential
  field_simp
  ring

/-- The two weighted increments cancel algebraically. -/
theorem centered_increment_mean_zero (a b : ℝ) :
    a * (-b) + b * a = 0 := by
  ring

/-- Its second moment is `a * b`. -/
theorem centered_increment_second_moment {a b : ℝ}
    (hsum : a + b = 1) :
    a * (-b) ^ 2 + b * a ^ 2 = a * b := by
  calc
    a * (-b) ^ 2 + b * a ^ 2 = a * b * (a + b) := by ring
    _ = a * b := by rw [hsum]; ring

/-- Exact expected energy drift under the centered two-point increment. -/
theorem energy_expect_step {a b D : ℝ} (hsum : a + b = 1) :
    a * energy a b (D - b) + b * energy a b (D + a) =
      energy a b D + a * b := by
  calc
    a * energy a b (D - b) + b * energy a b (D + a) =
        (a + b) * (energy a b D + a * b) := by
      unfold energy
      ring
    _ = energy a b D + a * b := by rw [hsum]; ring

/-- Stopping at the reciprocal-energy rate turns the positive raw energy
drift into a weak energy descent. -/
theorem one_sub_stop_mul_energy_drift_le {a b D : ℝ}
    (hab : b ≤ a) (hb : 0 < b) (hD : b ≤ D) :
    (1 - stopProbability a b D) * (energy a b D + a * b) ≤
      energy a b D := by
  have hE : 0 < energy a b D := energy_pos hab hb hD
  have habpos : 0 < a * b := mul_pos (hb.trans_le hab) hb
  unfold stopProbability
  rw [show D * (D + (a - b)) = energy a b D by rfl]
  field_simp
  nlinarith [sq_nonneg (a * b)]

/-- The exact version of the stopped energy calculation. -/
theorem one_sub_stop_mul_energy_drift_eq {a b D : ℝ}
    (hab : b ≤ a) (hb : 0 < b) (hD : b ≤ D) :
    (1 - stopProbability a b D) * (energy a b D + a * b) =
      energy a b D - (a * b) ^ 2 / energy a b D := by
  have hE : energy a b D ≠ 0 := (energy_pos hab hb hD).ne'
  unfold stopProbability
  rw [show D * (D + (a - b)) = energy a b D by rfl]
  field_simp
  ring

/-- Algebraic form of the player-two one-stage deviation ledger.  The
quantity `q` is the probability of the `+a` branch, `mu = q - b`, and `p` is
the current stopping probability. -/
theorem stageReward_le_ledger {a b D p q μ : ℝ}
    (hsum : a + b = 1) (hmu : μ = q - b)
    (hd : 0 ≤ 2 * b - a) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq1 : q ≤ 1)
    (hpotential : potential a b D ≤ 0) :
    2 * p * q + (1 - p) * (1 - q) ≤
      2 * b - 2 * potential a b D - μ + 3 * a * p := by
  have haq : 0 ≤ a - μ := by
    rw [hmu]
    linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hp1) hd,
    mul_nonneg hp0 haq]

/-- A positive balance `M + increment` bounds the accumulated increment from
below, with one additional positive-step allowance. -/
theorem stopped_increment_sum_lower_bound {M b raw increment : ℝ}
    (hb : 0 < b) (hraw : 0 < raw)
    (hsum : raw = M + increment) :
    -(M + b) < increment := by
  nlinarith

end WeightedBlackwellFerguson
end MathUE
