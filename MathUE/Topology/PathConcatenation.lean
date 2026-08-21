/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.UniformSpace.Path

/-!
# Path concatenation at a prescribed time

Mathlib's `Path.trans` assigns half of the unit interval to each constituent.
For clocked constructions the split must instead reflect the two elapsed
durations.  `Path.transAt` concatenates at any prescribed interior point.
-/

noncomputable section

open Set unitInterval
open scoped unitInterval

namespace Path

variable {X : Type*} [TopologicalSpace X] {x y z : X}

/-- Concatenate two paths so that the first occupies `[0, split]` and the
second occupies `[split, 1]`. -/
def transAt (first : Path x y) (second : Path y z) (split : ℝ)
    (hsplitPos : 0 < split) (hsplitOne : split < 1) : Path x z where
  toFun time := if (time : ℝ) ≤ split then
      first.extend ((time : ℝ) / split)
    else
      second.extend (((time : ℝ) - split) / (1 - split))
  continuous_toFun := by
    let left : unitInterval → X := fun time =>
      first.extend ((time : ℝ) / split)
    let right : unitInterval → X := fun time =>
      second.extend (((time : ℝ) - split) / (1 - split))
    have hleft : Continuous left := by
      dsimp [left]
      fun_prop
    have hright : Continuous right := by
      dsimp [right]
      fun_prop
    apply Continuous.if_le hleft hright continuous_subtype_val continuous_const
    intro time htime
    change first.extend ((time : ℝ) / split) =
      second.extend (((time : ℝ) - split) / (1 - split))
    rw [htime]
    rw [div_self hsplitPos.ne', sub_self, zero_div]
    simp
  source' := by
    have hzero : (((0 : unitInterval) : ℝ) ≤ split) := by
      simpa using hsplitPos.le
    rw [if_pos hzero]
    simp
  target' := by
    have hone : ¬(((1 : unitInterval) : ℝ) ≤ split) := by
      simpa using not_le_of_gt hsplitOne
    rw [if_neg hone]
    change second.extend ((1 - split) / (1 - split)) = z
    have hdenom : 1 - split ≠ 0 := sub_ne_zero.mpr (ne_of_gt hsplitOne)
    rw [div_self hdenom]
    simp

@[simp] theorem transAt_apply_of_le
    (first : Path x y) (second : Path y z) {split : ℝ}
    (hsplitPos : 0 < split) (hsplitOne : split < 1)
    (time : unitInterval) (htime : (time : ℝ) ≤ split) :
    first.transAt second split hsplitPos hsplitOne time =
      first.extend ((time : ℝ) / split) := by
  simp [transAt, htime]

@[simp] theorem transAt_apply_of_lt
    (first : Path x y) (second : Path y z) {split : ℝ}
    (hsplitPos : 0 < split) (hsplitOne : split < 1)
    (time : unitInterval) (htime : split < (time : ℝ)) :
    first.transAt second split hsplitPos hsplitOne time =
      second.extend (((time : ℝ) - split) / (1 - split)) := by
  change (if (time : ℝ) ≤ split then
      first.extend ((time : ℝ) / split)
    else second.extend (((time : ℝ) - split) / (1 - split))) = _
  rw [if_neg (not_le_of_gt htime)]

end Path
