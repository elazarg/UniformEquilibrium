/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact rational subdivision of a scalar absorption arc

The varying hazards `q / (n - l*q)` preserve an arc's survival probability
exactly. Their prefix survival is affine in the local date, and the residual
absorption coefficient is `(n-l)*q/(n-l*q)`. A ceiling choice gives a positive
mesh length with hazards bounded by any supplied positive tolerance.

These are scalar algebraic statements. They do not construct a stochastic-game
profile or assert a deviation bound.
-/

noncomputable section

open scoped BigOperators

namespace Math

/-- Hazard at local date `l` in the exact rational subdivision. -/
def rationalArcHazard (q : ℝ) (n l : ℕ) : ℝ := q / (n - l * q)

/-- Conditional probability of absorption during the remaining part of an arc. -/
def rationalArcResidual (q : ℝ) (n l : ℕ) : ℝ :=
  (n - (l : ℝ)) * q / (n - l * q)

/-- Probability of surviving the first `l` dates of the subdivided arc. -/
def rationalArcPrefix (q : ℝ) (n l : ℕ) : ℝ :=
  ∏ k ∈ Finset.range l, (1 - rationalArcHazard q n k)

/-- The odds of absorption in the coarse arc. -/
def rationalArcOdds (q : ℝ) : ℝ := q / (1 - q)

/-- A positive subdivision length at a specified hazard tolerance. -/
def rationalArcLength (q δ : ℝ) : ℕ := max 1 (Nat.ceil (rationalArcOdds q / δ))

theorem rationalArc_denominator_pos {q : ℝ} {n l : ℕ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hn : 0 < n) (hl : l ≤ n) :
    0 < (n : ℝ) - l * q := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlR : (l : ℝ) ≤ n := by exact_mod_cast hl
  have hslack := mul_nonneg (sub_nonneg.mpr hlR) hq0
  have hsurvival := mul_pos hnR (sub_pos.mpr hq1)
  nlinarith

theorem rationalArcHazard_nonneg {q : ℝ} {n : ℕ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (l : Fin n) :
    0 ≤ rationalArcHazard q n l := by
  have hn : 0 < n := Nat.zero_lt_of_lt l.isLt
  exact div_nonneg hq0
    (rationalArc_denominator_pos hq0 hq1 hn l.isLt.le).le

theorem rationalArcHazard_lt_one {q : ℝ} {n : ℕ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (l : Fin n) :
    rationalArcHazard q n l < 1 := by
  have hn : 0 < n := Nat.zero_lt_of_lt l.isLt
  have hden := rationalArc_denominator_pos hq0 hq1 hn l.isLt.le
  have hlR : ((l : ℕ) : ℝ) + 1 ≤ n := by
    exact_mod_cast Nat.succ_le_of_lt l.isLt
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hslack := mul_nonneg (sub_nonneg.mpr hlR) hq0
  have hsurvival := mul_pos hnR (sub_pos.mpr hq1)
  rw [rationalArcHazard, div_lt_one hden]
  nlinarith

theorem rationalArcPrefix_eq {q : ℝ} {n l : ℕ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hn : 0 < n) (hl : l ≤ n) :
    rationalArcPrefix q n l = ((n : ℝ) - l * q) / n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  revert hl
  induction l with
  | zero =>
      intro hl
      simp [rationalArcPrefix, hn0]
  | succ l ih =>
      intro hl
      have hl' : l ≤ n := Nat.le_trans (Nat.le_succ l) hl
      have hden := rationalArc_denominator_pos hq0 hq1 hn hl'
      change (∏ k ∈ Finset.range (l + 1), (1 - rationalArcHazard q n k)) = _
      rw [Finset.prod_range_succ]
      change rationalArcPrefix q n l * (1 - rationalArcHazard q n l) = _
      rw [ih hl', rationalArcHazard, Nat.cast_succ]
      field_simp [hn0, ne_of_gt hden]
      ring

theorem rationalArcPrefix_at_length {q : ℝ} {n : ℕ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hn : 0 < n) :
    rationalArcPrefix q n n = 1 - q := by
  rw [rationalArcPrefix_eq hq0 hq1 hn le_rfl]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp [hn0]

theorem rationalArcResidual_nonneg {q : ℝ} {n l : ℕ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hn : 0 < n) (hl : l ≤ n) :
    0 ≤ rationalArcResidual q n l := by
  have hlR : (l : ℝ) ≤ n := by exact_mod_cast hl
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr hlR) hq0)
    (rationalArc_denominator_pos hq0 hq1 hn hl).le

theorem rationalArcResidual_le {q : ℝ} {n l : ℕ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hn : 0 < n) (hl : l ≤ n) :
    rationalArcResidual q n l ≤ q := by
  have hden := rationalArc_denominator_pos hq0 hq1 hn hl
  have hproduct := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg l) hq0) (sub_nonneg.mpr hq1.le)
  rw [rationalArcResidual, div_le_iff₀ hden]
  nlinarith

@[simp] theorem rationalArcResidual_start (q : ℝ) {n : ℕ} (hn : 0 < n) :
    rationalArcResidual q n 0 = q := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp [rationalArcResidual, hn0]

@[simp] theorem rationalArcResidual_end (q : ℝ) (n : ℕ) :
    rationalArcResidual q n n = 0 := by
  simp [rationalArcResidual]

theorem rationalArcResidual_recursion {q : ℝ} {n : ℕ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (l : Fin n) :
    rationalArcResidual q n l = rationalArcHazard q n l +
      (1 - rationalArcHazard q n l) * rationalArcResidual q n (l.val + 1) := by
  have hn : 0 < n := Nat.zero_lt_of_lt l.isLt
  have hden := rationalArc_denominator_pos hq0 hq1 hn l.isLt.le
  have hnext := rationalArc_denominator_pos hq0 hq1 hn
    (Nat.succ_le_of_lt l.isLt)
  have hnext0 : (n : ℝ) - ((l.val : ℝ) + 1) * q ≠ 0 := by
    simpa only [Nat.cast_succ] using ne_of_gt hnext
  have hnextNormalized : (n : ℝ) - l.val * q - q ≠ 0 := by
    convert hnext0 using 1
    ring
  unfold rationalArcResidual rationalArcHazard
  rw [Nat.cast_add, Nat.cast_one]
  rw [show (n : ℝ) - ((l.val : ℝ) + 1) * q = (n : ℝ) - l.val * q - q by ring]
  field_simp [ne_of_gt hden, hnextNormalized]
  ring

theorem rationalArcPrefix_mul_hazard {q : ℝ} {n : ℕ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (l : Fin n) :
    rationalArcPrefix q n l * rationalArcHazard q n l = q / n := by
  have hn : 0 < n := Nat.zero_lt_of_lt l.isLt
  have hden := rationalArc_denominator_pos hq0 hq1 hn l.isLt.le
  rw [rationalArcPrefix_eq hq0 hq1 hn l.isLt.le, rationalArcHazard]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp [hn0, ne_of_gt hden]

theorem rationalArcHazard_le_odds_div {q : ℝ} {n : ℕ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (l : Fin n) :
    rationalArcHazard q n l ≤ rationalArcOdds q / n := by
  have hn : 0 < n := Nat.zero_lt_of_lt l.isLt
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlR : ((l : ℕ) : ℝ) ≤ n := by exact_mod_cast l.isLt.le
  have hsurvival : 0 < 1 - q := sub_pos.mpr hq1
  have hslack := mul_nonneg (sub_nonneg.mpr hlR) hq0
  have hdenle : (1 - q) * n ≤ (n : ℝ) - l.val * q := by nlinarith
  unfold rationalArcHazard rationalArcOdds
  rw [div_div]
  exact div_le_div_of_nonneg_left hq0 (mul_pos hsurvival hnR) hdenle

theorem rationalArcLength_pos (q δ : ℝ) : 0 < rationalArcLength q δ := by
  exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

theorem rationalArcLength_le {q δ : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hδ : 0 < δ) :
    (rationalArcLength q δ : ℝ) ≤ 1 + rationalArcOdds q / δ := by
  have hodds : 0 ≤ rationalArcOdds q / δ :=
    div_nonneg (div_nonneg hq0 (sub_pos.mpr hq1).le) hδ.le
  have hceil := (Nat.ceil_lt_add_one hodds).le
  unfold rationalArcLength
  rw [Nat.cast_max, Nat.cast_one]
  exact max_le (by linarith) (by linarith)

theorem rationalArcHazard_le_tolerance {q δ : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hδ : 0 < δ)
    (l : Fin (rationalArcLength q δ)) :
    rationalArcHazard q (rationalArcLength q δ) l ≤ δ := by
  have hnR : 0 < (rationalArcLength q δ : ℝ) := by
    exact_mod_cast rationalArcLength_pos q δ
  have hceil : rationalArcOdds q / δ ≤ (rationalArcLength q δ : ℝ) := by
    have hlength : Nat.ceil (rationalArcOdds q / δ) ≤ rationalArcLength q δ :=
      le_max_right _ _
    exact (Nat.le_ceil _).trans (by exact_mod_cast hlength)
  have hscaled := (div_le_iff₀ hδ).mp hceil
  exact (rationalArcHazard_le_odds_div hq0 hq1 l).trans
    ((div_le_iff₀ hnR).mpr (by nlinarith))

@[simp] theorem rationalArcHazard_zero (n l : ℕ) : rationalArcHazard 0 n l = 0 := by
  simp [rationalArcHazard]

@[simp] theorem rationalArcResidual_zero (n l : ℕ) :
    rationalArcResidual 0 n l = 0 := by
  simp [rationalArcResidual]

@[simp] theorem rationalArcPrefix_zero (n l : ℕ) : rationalArcPrefix 0 n l = 1 := by
  simp [rationalArcPrefix]

@[simp] theorem rationalArcLength_zero (δ : ℝ) : rationalArcLength 0 δ = 1 := by
  simp [rationalArcLength, rationalArcOdds]

/-- Rational input produces exact rational hazards, including at zero input. -/
theorem rationalArcHazard_ratCast (q : ℚ) (n l : ℕ) :
    ((q / ((n : ℚ) - l * q) : ℚ) : ℝ) = rationalArcHazard q n l := by
  simp [rationalArcHazard]

/-- The remaining absorption coefficient also has an exact rational witness. -/
theorem rationalArcResidual_ratCast (q : ℚ) (n l : ℕ) :
    ((((n : ℚ) - l) * q / (n - l * q) : ℚ) : ℝ) = rationalArcResidual q n l := by
  simp [rationalArcResidual]

/-- Every finite survival product has an exact rational witness. -/
theorem rationalArcPrefix_ratCast (q : ℚ) (n l : ℕ) :
    ((∏ k ∈ Finset.range l, (1 - q / ((n : ℚ) - k * q)) : ℚ) : ℝ) =
      rationalArcPrefix q n l := by
  simp [rationalArcPrefix, rationalArcHazard, Rat.cast_prod]

/-- Every finite stopping mass has an exact rational witness. -/
theorem rationalArcPrefix_mul_hazard_ratCast (q : ℚ) (n l : ℕ) :
    (((∏ k ∈ Finset.range l, (1 - q / ((n : ℚ) - k * q))) *
      (q / ((n : ℚ) - l * q)) : ℚ) : ℝ) =
      rationalArcPrefix q n l * rationalArcHazard q n l := by
  rw [Rat.cast_mul, rationalArcPrefix_ratCast, rationalArcHazard_ratCast]

end Math
