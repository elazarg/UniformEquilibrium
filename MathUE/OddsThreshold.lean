/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith

/-!
# The odds form of a two-branch comparison

A Bernoulli trial with success probability `rate` pays `cost` on success and
forgoes `gain` on failure. The comparison

`rate * cost ≤ (1 - rate) * gain`

is the statement that the expected cost of the success branch does not exceed
the expected gain of the failure branch. Below sure success and against a
positive cost it is equivalent to a ceiling on the *odds* `rate / (1 - rate)`,
namely `rate / (1 - rate) ≤ gain / cost`, which separates the trial's own
parameter from the two branch values.

Two degenerations bracket that threshold. A nonpositive cost against a
nonnegative gain satisfies the comparison outright, for every `rate` in the
unit interval and with no division. At `rate = 1` the failure branch is
unreachable and the comparison collapses to the sign of the cost alone.

The odds transform `rate ↦ rate / (1 - rate)` is compared with the reciprocal
coordinate in `MathUE/InverseCoordinateRecurrence.lean`.
-/

namespace Math

/-- **The odds threshold.** Below sure success and against a positive cost,
the two-branch comparison is exactly a ceiling on the odds of the trial. -/
theorem mul_le_one_sub_mul_iff_odds_le {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {rate cost gain : K} (hrate : rate < 1) (hcost : 0 < cost) :
    rate * cost ≤ (1 - rate) * gain ↔ rate / (1 - rate) ≤ gain / cost := by
  have hsurvival : 0 < 1 - rate := by linarith
  rw [div_le_div_iff₀ hsurvival hcost]
  constructor <;> intro hbound <;> nlinarith [hbound]

/-- A nonpositive cost against a nonnegative gain imposes no constraint at
all: the success branch never costs and the failure branch never pays. This
needs no division, no linearity, and no inverses. -/
theorem mul_le_one_sub_mul_of_nonpos {K : Type*} [Ring K] [PartialOrder K]
    [IsOrderedRing K] {rate cost gain : K} (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1)
    (hcost : cost ≤ 0) (hgain : 0 ≤ gain) :
    rate * cost ≤ (1 - rate) * gain :=
  le_trans (mul_nonpos_of_nonneg_of_nonpos hrate0 hcost)
    (mul_nonneg (by simpa using sub_nonneg.2 hrate1) hgain)

/-- At sure success the failure branch is unreachable and the comparison
degenerates to the sign of the cost. -/
theorem one_mul_le_one_sub_one_mul_iff {K : Type*} [Ring K] [PartialOrder K]
    {cost gain : K} : (1 : K) * cost ≤ (1 - 1) * gain ↔ cost ≤ 0 := by
  simp

end Math
