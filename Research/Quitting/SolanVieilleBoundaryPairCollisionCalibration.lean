/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.PairActiveSoloPhase
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryTable

/-!
# Pair-collision calibration for the Solan–Vieille boundary table

The production singleton calibration
`SolanVieilleBoundarySoloMatrixCalibration` proves the boundary table's
normalized solo-matrix margin and zero-freeness.  This module records the
separate collision-row condition needed by the tentative pointwise solo phase.

The table is pair-collision nondegenerate
(`quittingPairCollisionNondegenerate_boundaryReward`): every collision row pays `1`,
while a same-pair solo exit pays `4` and a cross-pair one pays `0`, so joining
another player's exit always changes what a player receives.  That is the
table hypothesis of the pointwise solo phase of
`Research/Quitting/PairActiveSoloPhase.lean`, which is a condition on
collision rows and independent of zero-freeness of the singleton rows.

Nothing here asserts that the table carries a diffuse tail, a solo window, or
a counterexample.
-/

noncomputable section

namespace GameTheory

namespace SolanVieilleBoundary

/-- Every collision row of the table pays `1` to each colliding player. -/
theorem quittingSingletonCollisionReward_boundaryReward_eq_one
    (owner who : Player) :
    quittingSingletonCollisionReward boundaryReward owner who = 1 := by
  exact boundaryReward_pair_eq_one owner who

/-- Closed form of the pair collision increments: joining a same-pair
partner's exit costs `3`, joining a cross-pair player's exit gains `1`. -/
theorem quittingPairCollisionIncrement_boundaryReward_eval
    (who owner : Player) :
    quittingPairCollisionIncrement boundaryReward who owner =
      if owner = who then 0
      else if owner.val / 2 = who.val / 2 then -3 else 1 := by
  rw [quittingPairCollisionIncrement,
    quittingSingletonCollisionReward_boundaryReward_eq_one, soloReward_eval]
  split_ifs <;> norm_num

/-- **The Solan–Vieille boundary table is pair-collision nondegenerate.**
Joining another player's solo exit always changes what a player receives, so
the pointwise solo phase of
`Research/Quitting/PairActiveSoloPhase.lean` applies to this table. -/
theorem quittingPairCollisionNondegenerate_boundaryReward :
    QuittingPairCollisionNondegenerate boundaryReward := by
  intro who owner hne
  rw [quittingPairCollisionIncrement_boundaryReward_eval,
    if_neg (fun h => hne h.symm)]
  split_ifs <;> norm_num

end SolanVieilleBoundary

end GameTheory
