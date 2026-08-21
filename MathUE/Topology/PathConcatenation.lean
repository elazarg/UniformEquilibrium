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

/-- Reparameterize the initial segment up to `cut` over the whole unit
interval. -/
def initialSegment (path : Path x y) (cut : unitInterval) :
    Path x (path cut) where
  toFun time := path ⟨(time : ℝ) * (cut : ℝ), by
    constructor
    · exact mul_nonneg time.property.1 cut.property.1
    · nlinarith [time.property.1, time.property.2,
        cut.property.1, cut.property.2]⟩
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

@[simp] theorem initialSegment_apply (path : Path x y)
    (cut time : unitInterval) :
    path.initialSegment cut time =
      path ⟨(time : ℝ) * (cut : ℝ), by
        constructor
        · exact mul_nonneg time.property.1 cut.property.1
        · nlinarith [time.property.1, time.property.2,
            cut.property.1, cut.property.2]⟩ :=
  rfl

/-- Initial-segment reparameterization preserves monotonicity. -/
theorem monotone_initialSegment [Preorder X]
    (path : Path x y) (cut : unitInterval) (hpath : Monotone path) :
    Monotone (path.initialSegment cut) := by
  intro first second hle
  apply hpath
  exact mul_le_mul_of_nonneg_right
    (show (first : ℝ) ≤ (second : ℝ) from hle) cut.property.1

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

/-- The normalized parameter in the first path before the prescribed split. -/
def transAtLeftParameter {split : ℝ} (hsplitPos : 0 < split)
    (time : unitInterval) (htime : (time : ℝ) ≤ split) : unitInterval :=
  ⟨(time : ℝ) / split,
    div_nonneg time.property.1 hsplitPos.le,
    (div_le_one hsplitPos).2 htime⟩

/-- The normalized parameter in the second path after the prescribed split. -/
def transAtRightParameter {split : ℝ} (hsplitOne : split < 1)
    (time : unitInterval) (htime : split ≤ (time : ℝ)) : unitInterval :=
  ⟨((time : ℝ) - split) / (1 - split),
    div_nonneg (sub_nonneg.mpr htime) (sub_nonneg.mpr hsplitOne.le),
    (div_le_one (sub_pos.mpr hsplitOne)).2 (by linarith [time.property.2])⟩

@[simp] theorem transAt_apply_leftParameter
    (first : Path x y) (second : Path y z) {split : ℝ}
    (hsplitPos : 0 < split) (hsplitOne : split < 1)
    (time : unitInterval) (htime : (time : ℝ) ≤ split) :
    first.transAt second split hsplitPos hsplitOne time =
      first (transAtLeftParameter hsplitPos time htime) := by
  rw [transAt_apply_of_le first second hsplitPos hsplitOne time htime]
  exact Path.extend_apply first _

@[simp] theorem transAt_apply_rightParameter
    (first : Path x y) (second : Path y z) {split : ℝ}
    (hsplitPos : 0 < split) (hsplitOne : split < 1)
    (time : unitInterval) (htime : split < (time : ℝ)) :
    first.transAt second split hsplitPos hsplitOne time =
      second (transAtRightParameter hsplitOne time htime.le) := by
  rw [transAt_apply_of_lt first second hsplitPos hsplitOne time htime]
  exact Path.extend_apply second _

/-- Concatenating monotone paths at any interior split preserves
monotonicity. -/
theorem monotone_transAt [Preorder X]
    (first : Path x y) (second : Path y z) {split : ℝ}
    (hsplitPos : 0 < split) (hsplitOne : split < 1)
    (hfirst : Monotone first) (hsecond : Monotone second) :
    Monotone (first.transAt second split hsplitPos hsplitOne) := by
  intro earlier later hel
  by_cases hlater : (later : ℝ) ≤ split
  · rw [transAt_apply_leftParameter first second hsplitPos hsplitOne later hlater,
      transAt_apply_leftParameter first second hsplitPos hsplitOne earlier
        (le_trans (show (earlier : ℝ) ≤ later from hel) hlater)]
    apply hfirst
    exact div_le_div_of_nonneg_right
      (show (earlier : ℝ) ≤ later from hel) hsplitPos.le
  · have hlater' : split < (later : ℝ) := lt_of_not_ge hlater
    by_cases hearlier : (earlier : ℝ) ≤ split
    · rw [transAt_apply_leftParameter first second hsplitPos hsplitOne earlier hearlier,
        transAt_apply_rightParameter first second hsplitPos hsplitOne later hlater']
      calc
        first (transAtLeftParameter hsplitPos earlier hearlier) ≤ first 1 :=
          hfirst (unitInterval.le_one _)
        _ = y := first.target
        _ = second 0 := second.source.symm
        _ ≤ second (transAtRightParameter hsplitOne later hlater'.le) :=
          hsecond (unitInterval.nonneg _)
    · have hearlier' : split < (earlier : ℝ) := lt_of_not_ge hearlier
      rw [transAt_apply_rightParameter first second hsplitPos hsplitOne earlier hearlier',
        transAt_apply_rightParameter first second hsplitPos hsplitOne later hlater']
      apply hsecond
      exact div_le_div_of_nonneg_right
        (sub_le_sub_right (show (earlier : ℝ) ≤ later from hel) split)
        (sub_nonneg.mpr hsplitOne.le)

end Path
