/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Analytic.SwitchingResidueRegression
import UniformEquilibrium.Quitting.Paths.SureExitSet
import MathUE.Finset.FinThree

/-!
# The switching-residue regression table has no sure exit set

`QuittingSwitchingResidueRegression` proves, by pure arithmetic on a
concrete three-player reward table, that every one of the seven nonempty
coalitions of `Fin 3` fails the sure-exit inequality system `SureExitFails`.
That module deliberately uses no stochastic-game dynamics, roots, or
profiles.

This tiny bridge file connects that arithmetic fact to the game layer's
`IsQuittingSureExitSet` (`QuittingSureExitSet.lean`): it packages the same
table as a genuine quitting-game reward `gameReward` on
`{S : Finset Player // S.Nonempty}`, checks that its extended set reward
`quittingSetReward gameReward` agrees with the arithmetic `reward` table at
every coalition including the empty one, and concludes that `gameReward` has
no sure exit set at all — for every nonempty `S`,
`¬ IsQuittingSureExitSet gameReward S`.

Every result here is original to this development; none of it is quoted or
adapted from a specific published source.
-/

noncomputable section

namespace GameTheory

namespace QuittingSwitchingResidueRegressionBridge

open QuittingSureSetOwnerRepair QuittingSwitchingResidueRegression

/-- **The game-layer reward table.** The arithmetic table
`QuittingSwitchingResidueRegression.reward`, restricted to nonempty
coalitions, read as a genuine quitting-game reward. -/
def gameReward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun S ↦ QuittingSwitchingResidueRegression.reward S.1

/-- The extended set reward of `gameReward` agrees with the arithmetic
`reward` table at every coalition, including the empty one. -/
theorem quittingSetReward_gameReward (S : Finset Player) :
    quittingSetReward gameReward S = QuittingSwitchingResidueRegression.reward S := by
  funext who
  by_cases hS : S.Nonempty
  · simp [quittingSetReward_of_nonempty gameReward hS, gameReward]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS, quittingSetReward_empty,
      QuittingSwitchingResidueRegression.reward]

/-- A failure of the arithmetic sure-exit system at `S` defeats the
game-layer sure-exit-set predicate at the same `S`. -/
theorem not_isQuittingSureExitSet_of_sureExitFails
    {S : Finset Player} (h : SureExitFails S) :
    ¬ IsQuittingSureExitSet gameReward S := by
  apply not_isQuittingSureExitSet_of_strict_toggle
  simpa only [SureExitFails, quittingSetReward_gameReward] using h

/-- **No sure exit set.** Every nonempty coalition fails the game-layer
sure-exit-set test against `gameReward`: this is exactly the arithmetic
failure `SureExitFails`, established over the seven nonempty coalitions of
`QuittingSwitchingResidueRegression`, transported through
`quittingSetReward_gameReward`. -/
theorem not_isQuittingSureExitSet_gameReward
    (S : Finset Player) (hS : S.Nonempty) :
    ¬ IsQuittingSureExitSet gameReward S := by
  rcases Math.Finset.nonempty_fin_three_cases S hS with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_isQuittingSureExitSet_of_sureExitFails sureExitFails_1
  · exact not_isQuittingSureExitSet_of_sureExitFails sureExitFails_2
  · exact not_isQuittingSureExitSet_of_sureExitFails sureExitFails_3
  · exact not_isQuittingSureExitSet_of_sureExitFails sureExitFails_12
  · exact not_isQuittingSureExitSet_of_sureExitFails sureExitFails_13
  · exact not_isQuittingSureExitSet_of_sureExitFails sureExitFails_23
  · exact not_isQuittingSureExitSet_of_sureExitFails sureExitFails_123

end QuittingSwitchingResidueRegressionBridge

end GameTheory
