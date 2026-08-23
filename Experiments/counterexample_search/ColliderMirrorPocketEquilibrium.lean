/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Circulant.TerminalExploitabilityColliderClosure
import UniformEquilibrium.Quitting.Classification.Circulant.ColliderClosure

/-!
# One distant-pocket collider completion, in the branch only step four reaches

This file fixes the five-player collider completion of
`Research/Quitting/CirculantColliderCompletion.lean` at solo self value `1`,
joint value `-2`, and margin vector

`(m 1, m 2, m 3, m 4) = (10, -1, -4, 3/10)`.

The table lies in the distant pocket — `m 2 < 0`, `m 3 < 0`, `0 ≤ m 1`,
`0 ≤ m 4`, margin sum `53/10 > 0` — and it sits in the one branch of that
pocket that none of the pocket's other three producers reaches.  The join
margin away from distance four is `low - s = -3`, and

* `m 3 = -4 < -3`, so the step-two floor at the deepest elapsed phase fails;
* `-3 < -1 = m 2`, so no skip pair is a sure exit set, recorded below as
  `mirror_not_isQuittingSureExitSet_skip`;
* `m 2 + m 4 = -7/10 < 0` and `m 1 * m 4 = 3 < 4 = m 2 * m 3`, so neither
  condition that places the step-three root early enough holds.

What fires is the step-four cycle at an anchor root beyond
`m 4 / (s - low) = 1/10`, supplied by
`GameTheory.CirculantColliderCompletion.exists_stepFour_root_of_lt_mul`.

This is a checked statement about one table, not a general theorem about
collider completions.  The general statements are
`GameTheory.CirculantColliderCompletion.isEmpty_terminalExploitabilityWitness_colliderDistantPocket`
and `GameTheory.CirculantColliderCompletion.exists_uniformEquilibriumPayoff_colliderReward`.
-/

noncomputable section

namespace GameTheory
namespace ColliderMirrorPocketEquilibrium

open CirculantConstantStepCycle CirculantColliderCompletion
open QuittingSureSetOwnerRepair

/-! ## The table -/

/-- The margin vector `(0, 10, -1, -4, 3/10)`. -/
def mirrorMargin : ZMod 5 → ℝ :=
  fun d =>
    if d = 1 then 10
    else if d = 2 then -1
    else if d = 3 then -4
    else if d = 4 then 3 / 10
    else 0

@[simp] theorem mirrorMargin_zero : mirrorMargin 0 = 0 := by
  rw [mirrorMargin, if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide)]

@[simp] theorem mirrorMargin_one : mirrorMargin 1 = 10 := by
  rw [mirrorMargin, if_pos rfl]

@[simp] theorem mirrorMargin_two : mirrorMargin 2 = -1 := by
  rw [mirrorMargin, if_neg (by decide), if_pos rfl]

@[simp] theorem mirrorMargin_three : mirrorMargin 3 = -4 := by
  rw [mirrorMargin, if_neg (by decide), if_neg (by decide), if_pos rfl]

@[simp] theorem mirrorMargin_four : mirrorMargin 4 = 3 / 10 := by
  rw [mirrorMargin, if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_pos rfl]

/-- The collider completion at solo self value `1`, joint value `-2`, and the
margin vector `mirrorMargin`. -/
def mirrorReward : {S : Finset (ZMod 5) // S.Nonempty} → Payoff (ZMod 5) :=
  colliderReward 1 (-2) mirrorMargin

/-! ## The branch the table sits in -/

/-- **No skip pair of the table is a sure exit set.**  The near member of a
skip pair strictly gains by stepping out: it is paid `0` alone against `-2`
inside the pair. -/
theorem mirror_not_isQuittingSureExitSet_skip (y : ZMod 5) :
    ¬ IsQuittingSureExitSet mirrorReward {y, y + 2} := by
  refine not_isQuittingSureExitSet_of_strict_toggle mirrorReward
    (Or.inl ⟨y, by simp, ?_⟩)
  rw [mirrorReward, erase_skip_left, quittingSetReward_singleton,
    quittingSetReward_skip_left, show y + 2 - y = 2 from by ring, mirrorMargin_two]
  norm_num

/-- **The step-two floor fails**: the join margin away from distance four is
below `m 3`. -/
theorem mirror_lt_margin_three : mirrorMargin 3 < (-2 : ℝ) - 1 := by
  rw [mirrorMargin_three]
  norm_num

/-- **Neither placement condition for the step-three root holds**: the two
distant margins do not sum with `m 4` to a nonnegative number, and the product
of the negative margins exceeds the product of the nonnegative ones. -/
theorem mirror_stepThree_unavailable :
    mirrorMargin 2 + mirrorMargin 4 < 0 ∧
      mirrorMargin 1 * mirrorMargin 4 < mirrorMargin 2 * mirrorMargin 3 := by
  rw [mirrorMargin_one, mirrorMargin_two, mirrorMargin_three, mirrorMargin_four]
  norm_num

/-! ## The headline -/

/-- **The table has a uniform-equilibrium payoff.**  The witness is the
period-five single-quitter profile of constant step four at a uniform quit
probability; the deviation class is all behavior strategies, not stopping
times. -/
theorem mirror_exists_uniformEquilibriumPayoff :
    ∃ payoff : Payoff (ZMod 5),
      (quittingGame mirrorReward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_colliderDistantPocket
    (s := 1) (low := -2) mirrorMargin_zero (by norm_num) (by norm_num)
    (by rw [mirrorMargin_one]; norm_num) (by rw [mirrorMargin_two]; norm_num)
    (by rw [mirrorMargin_three]; norm_num) (by rw [mirrorMargin_four]; norm_num)
    (by rw [mirrorMargin_one, mirrorMargin_two, mirrorMargin_three,
      mirrorMargin_four]; norm_num)

/-- **The table is in no terminal exploitability witness.** -/
theorem mirror_isEmpty_terminalExploitabilityWitness :
    IsEmpty (QuittingTerminalExploitabilityWitness mirrorReward) :=
  isEmpty_terminalExploitabilityWitness_colliderDistantPocket
    (s := 1) (low := -2) mirrorMargin_zero (by norm_num) (by norm_num)
    (by rw [mirrorMargin_one]; norm_num) (by rw [mirrorMargin_two]; norm_num)
    (by rw [mirrorMargin_three]; norm_num) (by rw [mirrorMargin_four]; norm_num)
    (by rw [mirrorMargin_one, mirrorMargin_two, mirrorMargin_three,
      mirrorMargin_four]; norm_num)

end ColliderMirrorPocketEquilibrium
end GameTheory
