import Mathlib

/-!
# Exact scalar checks for the cyclic four-player T x P witness

This probe deliberately isolates the two pieces of real algebra that carry
universal quantifiers in the argument:

* every normalized packet admitted by the cyclic singleton table has a
  refusal gain at least `1 / 52` for some owner; and
* the rational nonstationary tail has exact telescoping survival and enough
  one-stage slack to deter a nonowner's pure Quit deviation.

It does not claim counterexample-regime provenance or the global properties
(A) and (B) of the companion tail-packet analysis.
-/

namespace CounterexamplePairwiseConsistency

/-- Universal packet calculation for the singleton matrix

`r_i({j}) = 1` when `i = j`, `4` when `i = j + 1 (mod 4)`, and `0` otherwise.

The four displayed hypotheses are exactly `1 <= m_i(lambda)`.  The result
gives a full-support lower bound and the uniform refusal gap.  For an active
owner `i`, the corresponding disjunct is

`lambda_i / (1-lambda_i) * (m_i(lambda)-1) >= 1/52`,

which is exactly `refusal_i(lambda) - m_i(lambda)`.
-/
theorem cyclic_packet_uniform_refusal
    (l0 l1 l2 l3 : ℝ)
    (hl0 : 0 ≤ l0) (hl1 : 0 ≤ l1) (hl2 : 0 ≤ l2) (hl3 : 0 ≤ l3)
    (hsum : l0 + l1 + l2 + l3 = 1)
    (hm0 : 1 ≤ l0 + 4 * l3)
    (hm1 : 1 ≤ l1 + 4 * l0)
    (hm2 : 1 ≤ l2 + 4 * l1)
    (hm3 : 1 ≤ l3 + 4 * l2) :
    (1 / 13 : ℝ) ≤ l0 ∧
    (1 / 13 : ℝ) ≤ l1 ∧
    (1 / 13 : ℝ) ≤ l2 ∧
    (1 / 13 : ℝ) ≤ l3 ∧
      ((1 / 52 : ℝ) ≤ l0 / (1 - l0) * (l0 + 4 * l3 - 1) ∨
       (1 / 52 : ℝ) ≤ l1 / (1 - l1) * (l1 + 4 * l0 - 1) ∨
       (1 / 52 : ℝ) ≤ l2 / (1 - l2) * (l2 + 4 * l1 - 1) ∨
       (1 / 52 : ℝ) ≤ l3 / (1 - l3) * (l3 + 4 * l2 - 1)) := by
  have lower0 : (1 / 13 : ℝ) ≤ l0 := by
    by_cases hquarter : (1 / 4 : ℝ) ≤ l0
    · linarith
    · have hquarter' : l0 < (1 / 4 : ℝ) := lt_of_not_ge hquarter
      nlinarith
  have lower1 : (1 / 13 : ℝ) ≤ l1 := by
    by_cases hquarter : (1 / 4 : ℝ) ≤ l1
    · linarith
    · have hquarter' : l1 < (1 / 4 : ℝ) := lt_of_not_ge hquarter
      nlinarith
  have lower2 : (1 / 13 : ℝ) ≤ l2 := by
    by_cases hquarter : (1 / 4 : ℝ) ≤ l2
    · linarith
    · have hquarter' : l2 < (1 / 4 : ℝ) := lt_of_not_ge hquarter
      nlinarith
  have lower3 : (1 / 13 : ℝ) ≤ l3 := by
    by_cases hquarter : (1 / 4 : ℝ) ≤ l3
    · linarith
    · have hquarter' : l3 < (1 / 4 : ℝ) := lt_of_not_ge hquarter
      nlinarith
  have upper0 : l0 ≤ (10 / 13 : ℝ) := by linarith
  have upper1 : l1 ≤ (10 / 13 : ℝ) := by linarith
  have upper2 : l2 ≤ (10 / 13 : ℝ) := by linarith
  have upper3 : l3 ≤ (10 / 13 : ℝ) := by linarith
  have surplus :
      (1 / 4 : ℝ) ≤ l0 + 4 * l3 - 1 ∨
      (1 / 4 : ℝ) ≤ l1 + 4 * l0 - 1 ∨
      (1 / 4 : ℝ) ≤ l2 + 4 * l1 - 1 ∨
      (1 / 4 : ℝ) ≤ l3 + 4 * l2 - 1 := by
    by_contra h
    push Not at h
    nlinarith
  refine ⟨lower0, lower1, lower2, lower3, ?_⟩
  rcases surplus with h0 | h1 | h2 | h3
  · left
    have hden : 0 < 1 - l0 := by linarith
    have hratio : (1 / 13 : ℝ) ≤ l0 / (1 - l0) := by
      rw [le_div_iff₀ hden]
      nlinarith
    have hnonnegRatio : 0 ≤ l0 / (1 - l0) := div_nonneg hl0 hden.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hratio)
      (sub_nonneg.mpr h0)]
  · right; left
    have hden : 0 < 1 - l1 := by linarith
    have hratio : (1 / 13 : ℝ) ≤ l1 / (1 - l1) := by
      rw [le_div_iff₀ hden]
      nlinarith
    have hnonnegRatio : 0 ≤ l1 / (1 - l1) := div_nonneg hl1 hden.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hratio)
      (sub_nonneg.mpr h1)]
  · right; right; left
    have hden : 0 < 1 - l2 := by linarith
    have hratio : (1 / 13 : ℝ) ≤ l2 / (1 - l2) := by
      rw [le_div_iff₀ hden]
      nlinarith
    have hnonnegRatio : 0 ≤ l2 / (1 - l2) := div_nonneg hl2 hden.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hratio)
      (sub_nonneg.mpr h2)]
  · right; right; right
    have hden : 0 < 1 - l3 := by linarith
    have hratio : (1 / 13 : ℝ) ≤ l3 / (1 - l3) := by
      rw [le_div_iff₀ hden]
      nlinarith
    have hnonnegRatio : 0 ≤ l3 / (1 - l3) := div_nonneg hl3 hden.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hratio)
      (sub_nonneg.mpr h3)]

/-- One scalar step of the rational tail.  At scale `s >= 2`, put

`p = 1/(2s-1)`, `P = 1-1/s`, and `P' = 1-1/(2s)`.

The first equality is exact telescoping survival.  The second inequality is
the nonowner Nash comparison when every nonsingleton reward is `-4`, so the
pure-Quit endpoint is `1-5p`.  The last inequality is the geometric majorant
used to prove summability after instantiating `s = 2^(t+1)`.
-/
theorem rational_tail_step (s : ℝ) (hs : 2 ≤ s) :
    let p := 1 / (2 * s - 1)
    let P := 1 - 1 / s
    let Pnext := 1 - 1 / (2 * s)
    0 < p ∧ p < 1 ∧
      P = (1 - p) * Pnext ∧
      1 - 5 * p ≤ P ∧
      p ≤ 1 / s := by
  dsimp
  have hspos : 0 < s := by linarith
  have hden : 0 < 2 * s - 1 := by linarith
  have htwos : 0 < 2 * s := by positivity
  constructor
  · exact one_div_pos.mpr hden
  constructor
  · rw [div_lt_one hden]
    linarith
  constructor
  · rw [one_sub_div hspos.ne', one_sub_div hden.ne',
      one_sub_div htwos.ne', div_mul_div_comm]
    rw [mul_comm ((2 * s - 1) - 1) (2 * s - 1)]
    rw [mul_div_mul_left ((2 * s - 1) - 1) (2 * s) hden.ne']
    rw [show (2 * s - 1) - 1 = 2 * (s - 1) by ring]
    exact (mul_div_mul_left (s - 1) s (by norm_num : (2 : ℝ) ≠ 0)).symm
  constructor
  · rw [sub_le_sub_iff_left]
    have hh : 1 / s ≤ 5 / (2 * s - 1) := by
      rw [div_le_div_iff₀ hspos hden]
      nlinarith
    simpa [div_eq_mul_inv] using hh
  · rw [div_le_div_iff₀ hden hspos]
    linarith

/-- The prescribed nonowner values obey their exact Bellman equations once
the survival identity holds.  The owner equation is the constant `1 = 1`.
-/
theorem rational_tail_bellman_values
    (p P Pnext : ℝ) (hsurvival : P = (1 - p) * Pnext) :
    (1 + 3 * (1 - P) = 4 * p + (1 - p) * (1 + 3 * (1 - Pnext))) ∧
    (P = 0 * p + (1 - p) * Pnext) := by
  constructor
  · rw [hsurvival]
    ring
  · simpa using hsurvival

end CounterexamplePairwiseConsistency
