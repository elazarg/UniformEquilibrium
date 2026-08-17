/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

/-!
# Roots of an anchor cubic and their backward partial sums

An *anchor cubic* is the polynomial `a + bβ + cβ² + dβ³` read as a discounted
sum of four successive coefficients at a common per-step survival factor `β`.
Two facts about such a cubic are recorded here.

* If the leading coefficient `a` is negative and the total `a + b + c + d` is
  positive, the intermediate value theorem places a root strictly inside
  `(0, 1)`.
* At a root with `β > 0` the *backward partial sum* `b + cβ + dβ²` — the anchor
  cubic with its first coefficient dropped and the rest advanced one step —
  equals `-a / β`.  When `a < 0` this is positive: the anchor equation itself
  funds the deepest partial sum, with no further sign hypothesis on
  `b`, `c`, `d`.

## Main definitions

* `cubicAnchor` — the value `a + bβ + cβ² + dβ³`
* `cubicAnchorTail` — the backward partial sum `b + cβ + dβ²`

## Main results

* `exists_cubicAnchor_root_mem_Ioo` — the root in `(0, 1)`
* `cubicAnchorTail_eq_of_root` — the backward partial sum at a nonzero root
* `cubicAnchorTail_pos_of_root` — its positivity at a positive root of an
  anchor cubic with negative leading coefficient
-/

noncomputable section

namespace Math

/-- The anchor cubic `a + bβ + cβ² + dβ³` at survival factor `β`. -/
def cubicAnchor (a b c d β : ℝ) : ℝ := a + b * β + c * β ^ 2 + d * β ^ 3

/-- The backward partial sum `b + cβ + dβ²`: the anchor cubic with its first
coefficient dropped and the remaining ones advanced by one step. -/
def cubicAnchorTail (b c d β : ℝ) : ℝ := b + c * β + d * β ^ 2

@[simp] theorem cubicAnchor_zero (a b c d : ℝ) : cubicAnchor a b c d 0 = a := by
  simp [cubicAnchor]

@[simp] theorem cubicAnchor_one (a b c d : ℝ) :
    cubicAnchor a b c d 1 = a + b + c + d := by
  simp [cubicAnchor]

theorem continuous_cubicAnchor (a b c d : ℝ) : Continuous (cubicAnchor a b c d) := by
  unfold cubicAnchor
  fun_prop

/-- **A root strictly inside the unit interval.**  An anchor cubic that starts
negative at `β = 0` and is positive at `β = 1` vanishes somewhere in between. -/
theorem exists_cubicAnchor_root_mem_Ioo {a b c d : ℝ} (ha : a < 0)
    (htotal : 0 < a + b + c + d) :
    ∃ β ∈ Set.Ioo (0 : ℝ) 1, cubicAnchor a b c d β = 0 := by
  have hcont : ContinuousOn (cubicAnchor a b c d) (Set.Icc (0 : ℝ) 1) :=
    (continuous_cubicAnchor a b c d).continuousOn
  have hmem : (0 : ℝ) ∈ Set.Ioo (cubicAnchor a b c d 0) (cubicAnchor a b c d 1) := by
    rw [cubicAnchor_zero, cubicAnchor_one]
    exact ⟨ha, htotal⟩
  obtain ⟨β, hβ, hroot⟩ := intermediate_value_Ioo zero_le_one hcont hmem
  exact ⟨β, hβ, hroot⟩

/-- **The anchor equation funds the backward partial sum.**  At a nonzero root
of the anchor cubic the backward partial sum is exactly `-a / β`. -/
theorem cubicAnchorTail_eq_of_root {a b c d β : ℝ} (hβ : β ≠ 0)
    (hroot : cubicAnchor a b c d β = 0) : cubicAnchorTail b c d β = -a / β := by
  rw [cubicAnchorTail, eq_div_iff hβ]
  simp only [cubicAnchor] at hroot
  have hexpand : (b + c * β + d * β ^ 2) * β = b * β + c * β ^ 2 + d * β ^ 3 := by
    ring
  rw [hexpand]
  linarith

/-- **Automatic patience.**  At a positive root of an anchor cubic with
negative leading coefficient the backward partial sum is positive, whatever
the signs of the remaining coefficients. -/
theorem cubicAnchorTail_pos_of_root {a b c d β : ℝ} (hβ : 0 < β) (ha : a < 0)
    (hroot : cubicAnchor a b c d β = 0) : 0 < cubicAnchorTail b c d β := by
  rw [cubicAnchorTail_eq_of_root hβ.ne' hroot]
  exact div_pos (neg_pos.mpr ha) hβ

end Math
