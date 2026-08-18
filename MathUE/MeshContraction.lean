/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Mesh buckets and geometric slack absorption

Two scalar lemmas behind discretized backward-induction constructions.

* Two reals in the same scaled-floor bucket lie within one mesh of each
  other.
* A bounded sequence in which every term is at most a sub-unit slope times
  the next term plus a slack absorbs the slack geometrically: every term is
  at most `slope * slack / (1 - slope)`.
-/

namespace Math

/-- Two reals whose scaled floors agree lie within one mesh of each other. -/
theorem abs_sub_le_of_floor_div_eq {left right mesh : ℝ} (hmesh : 0 < mesh)
    (hfloor : ⌊left / mesh⌋ = ⌊right / mesh⌋) : |left - right| ≤ mesh := by
  have hleft₁ : (⌊left / mesh⌋ : ℝ) ≤ left / mesh := Int.floor_le (left / mesh)
  have hleft₂ : left / mesh < ⌊left / mesh⌋ + 1 :=
    Int.lt_floor_add_one (left / mesh)
  have hright₁ : (⌊right / mesh⌋ : ℝ) ≤ right / mesh :=
    Int.floor_le (right / mesh)
  have hright₂ : right / mesh < ⌊right / mesh⌋ + 1 :=
    Int.lt_floor_add_one (right / mesh)
  rw [hfloor] at hleft₁ hleft₂
  have hdiv : |left / mesh - right / mesh| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hsplit : left - right = (left / mesh - right / mesh) * mesh := by
    field_simp
  rw [hsplit, abs_mul, abs_of_pos hmesh]
  calc |left / mesh - right / mesh| * mesh ≤ 1 * mesh :=
        mul_le_mul_of_nonneg_right hdiv hmesh.le
    _ = mesh := one_mul mesh

/-- **Geometric slack absorption.**  A bounded sequence in which every term
is at most a sub-unit slope times the next term plus a slack is bounded by
the geometric sum of the slack alone: the initial bound decays away. -/
theorem le_div_of_forall_le_mul_succ_add {u : ℕ → ℝ} {slope slack bound : ℝ}
    (hslope0 : 0 ≤ slope) (hslope1 : slope < 1) (hslack : 0 ≤ slack)
    (hbound : ∀ n, u n ≤ bound)
    (hstep : ∀ n, u n ≤ slope * (u (n + 1) + slack)) :
    ∀ n, u n ≤ slope * slack / (1 - slope) := by
  have hone : 0 < 1 - slope := by linarith
  have hgeom : slope * (slope * slack / (1 - slope) + slack) =
      slope * slack / (1 - slope) := by
    field_simp
    ring
  have hcap : 0 ≤ max bound 0 := le_max_right bound 0
  have hiterate : ∀ fuel n,
      u n ≤ slope ^ fuel * max bound 0 + slope * slack / (1 - slope) := by
    intro fuel
    induction fuel with
    | zero =>
        intro n
        have hterm : u n ≤ max bound 0 := (hbound n).trans (le_max_left _ _)
        have hquotient : 0 ≤ slope * slack / (1 - slope) := by positivity
        rw [pow_zero, one_mul]
        linarith
    | succ fuel ih =>
        intro n
        have hnext := ih (n + 1)
        calc u n ≤ slope * (u (n + 1) + slack) := hstep n
          _ ≤ slope * (slope ^ fuel * max bound 0 +
              slope * slack / (1 - slope) + slack) := by
                apply mul_le_mul_of_nonneg_left _ hslope0
                linarith
          _ = slope ^ (fuel + 1) * max bound 0 +
              slope * (slope * slack / (1 - slope) + slack) := by
                rw [pow_succ]
                ring
          _ = slope ^ (fuel + 1) * max bound 0 +
              slope * slack / (1 - slope) := by rw [hgeom]
  intro n
  refine le_of_forall_pos_le_add fun tolerance htolerance => ?_
  have hshrunk : 0 < tolerance / (max bound 0 + 1) :=
    div_pos htolerance (by linarith)
  obtain ⟨fuel, hfuel⟩ := exists_pow_lt_of_lt_one hshrunk hslope1
  have hpow0 : 0 ≤ slope ^ fuel := pow_nonneg hslope0 fuel
  have hcancel : tolerance / (max bound 0 + 1) * (max bound 0 + 1) =
      tolerance :=
    div_mul_cancel₀ tolerance (by linarith : max bound 0 + 1 ≠ 0)
  have hpowBound : slope ^ fuel * max bound 0 ≤ tolerance := by
    have hmul := mul_le_mul_of_nonneg_right hfuel.le hcap
    have hshrunk0 : 0 ≤ tolerance / (max bound 0 + 1) := hshrunk.le
    calc slope ^ fuel * max bound 0 ≤
        tolerance / (max bound 0 + 1) * max bound 0 := hmul
      _ ≤ tolerance := by linarith
  have := hiterate fuel n
  linarith

end Math
