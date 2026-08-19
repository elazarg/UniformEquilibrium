/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Circulant.ColliderCompletion
import UniformEquilibrium.Quitting.Classification.Circulant.ColliderCompletion

/-!
# One all-nonnegative collider completion and its solo exit

This file fixes the five-player collider completion of
`Research/Quitting/CirculantColliderCompletion.lean` at solo self value `1`,
joint value `-2`, and margin vector

`(m 1, m 2, m 3, m 4) = (1, 1, 1, 1)`.

Every nonzero distance carries a positive margin, so the margin sum is `4` and
the table lies outside the nonpositive-sum branch, carries no step of negative
margin, and is not a complementary pocket.  No constant-step cyclic profile is
available to it.

The witness is instead the stationary pure profile at which player zero alone
quits at every live history.  Its exit set is a sure exit set: the quitter is
paid its solo self value `1`, which beats the value `0` of never being
absorbed, and every other player is paid `2` for watching against `-2` for
joining — except the collider at distance four, paid `1` for joining, still
short of `2`.  The realized payoff is `(1, 2, 2, 2, 2)`.

This is a checked statement about one table, not a general theorem about
collider completions.  The general statements are
`GameTheory.CirculantTrichotomyClosure.exists_uniformEquilibriumPayoff_of_nonneg_margins`
and `GameTheory.CirculantColliderCompletion.isEmpty_counterexampleRegime_or_distantPocket`.
-/

noncomputable section

namespace GameTheory
namespace ColliderNonnegativeMarginEquilibrium

open CirculantConstantStepCycle CirculantColliderCompletion
open CirculantTrichotomyClosure QuittingSureSetOwnerRepair

/-! ## The table -/

/-- The margin vector `(0, 1, 1, 1, 1)`. -/
def flatMargin : ZMod 5 → ℝ := fun d => if d = 0 then 0 else 1

@[simp] theorem flatMargin_zero : flatMargin 0 = 0 := by
  rw [flatMargin, if_pos rfl]

theorem flatMargin_of_ne {d : ZMod 5} (hd : d ≠ 0) : flatMargin d = 1 := by
  rw [flatMargin, if_neg hd]

/-- The collider completion at solo self value `1`, joint value `-2`, and the
margin vector `flatMargin`. -/
def flatReward : {S : Finset (ZMod 5) // S.Nonempty} → Payoff (ZMod 5) :=
  colliderReward 1 (-2) flatMargin

/-- The payoff `(1, 2, 2, 2, 2)` realized by the solo exit of player zero. -/
def flatPayoff : Payoff (ZMod 5) := fun who => if who = 0 then 1 else 2

/-! ## The solo exit -/

/-- Every join margin of the completion is at most every singleton margin of
the table: the former are nonpositive and the latter are `1`. -/
theorem colliderJoin_le_flatMargin {d : ZMod 5} (hd : d ≠ 0) :
    colliderJoin 1 (-2) d ≤ flatMargin d := by
  have hjoin : colliderJoin (1 : ℝ) (-2 : ℝ) d ≤ 0 :=
    colliderJoin_nonpos (by norm_num) d
  rw [flatMargin_of_ne hd]
  linarith

/-- **The solo exit of player zero is a sure exit set.**  Every join margin of
the completion is nonpositive and every singleton margin of the table is
nonnegative. -/
theorem flat_isQuittingSureExitSet : IsQuittingSureExitSet flatReward {0} :=
  isQuittingSureExitSet_singleton_of_isCirculantPairTable
    (isCirculantPairTable_colliderReward 1 (-2) flatMargin flatMargin_zero)
    (by norm_num) (fun _ hd => colliderJoin_le_flatMargin hd) 0

/-- The exit set's own row is the payoff `(1, 2, 2, 2, 2)`. -/
theorem quittingSetReward_flatReward_singleton_zero :
    quittingSetReward flatReward {(0 : ZMod 5)} = flatPayoff := by
  funext who
  rw [flatReward, quittingSetReward_singleton, flatPayoff]
  by_cases hwho : who = 0
  · rw [if_pos hwho, hwho, sub_self, flatMargin_zero]
    norm_num
  · rw [if_neg hwho, flatMargin_of_ne (sub_ne_zero_of_ne (Ne.symm hwho))]
    norm_num

/-! ## The headline -/

/-- **The table has the uniform-equilibrium payoff `(1, 2, 2, 2, 2)`.**  The
witness is the stationary pure profile at which player zero alone quits at
every live history; the deviation class is all behavior strategies, not
stopping times. -/
theorem flat_isUniformEquilibriumPayoff :
    (quittingGame flatReward).IsUniformEquilibriumPayoff none flatPayoff := by
  rw [← quittingSetReward_flatReward_singleton_zero]
  exact isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet _
    flat_isQuittingSureExitSet

/-- **The table is in no counterexample regime.**  A terminal exploitability
gap is incompatible with an existing uniform-equilibrium payoff. -/
theorem flat_isEmpty_counterexampleRegime :
    IsEmpty (QuittingCounterexampleRegime flatReward) :=
  ⟨fun regime => regime.not_exists_uniformEquilibriumPayoff
    ⟨flatPayoff, flat_isUniformEquilibriumPayoff⟩⟩

/-- **No step of the table has negative margin**, so no constant-step cyclic
profile of `Research/Quitting/CirculantConstantStepCycle.lean` is available to
it and the firing-step branch does not reach it. -/
theorem flat_not_exists_isFiringStep : ¬ ∃ c : ZMod 5, IsFiringStep flatMargin c := by
  rintro ⟨c, hc, hneg, -, -⟩
  rw [flatMargin_of_ne hc] at hneg
  linarith

end ColliderNonnegativeMarginEquilibrium
end GameTheory
