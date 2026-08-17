/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.DiffuseTailSoloStructure
import Research.Quitting.PairActiveSoloPhase
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryTable

/-!
# Zero-free calibration: the Solan–Vieille boundary table

`QuittingZeroFreeSoloMatrix`
(`Research/Quitting/DiffuseTailSoloStructure.lean`) names the Solan–Vieille
boundary table as an intended instance; this module supplies the instance.

The normalized solo matrix of the table of
`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean` is
computed in closed form: an off-diagonal entry is `3` inside a pair and `-1`
across the pairs, so every off-diagonal entry has absolute value at least `1`.
That is exactly the hypothesis consumed by T3
(`quittingTailPersistentlySolo_of_zeroFree`) and by the contrapositive
window statement (`isEmpty_fencedSoloWindows_of_zeroFree`).

The margin form `soloMatrixMargin_boundaryReward` is recorded because the
quantitative T2 inequality
(`survivalGap_mul_abs_normalizedSoloMatrix_le_of_soloWindow`) divides by the
entry, so a uniform positive lower bound, not mere nonvanishing, is what a
budget argument needs.

The other table named in the same docstring, the regular five-player
tournament seed, has its reward function under `Experiments/`; since Research
must never import Experiments, its zero-free instance lives beside it in
`Experiments/counterexample_search/RegularTournamentFiveSeedZeroFree.lean`.

The same table is also pair-collision nondegenerate
(`pairCollisionNondegenerate_boundaryReward`): every collision row pays `1`,
while a same-pair solo exit pays `4` and a cross-pair one pays `0`, so joining
another player's exit always changes what a player receives.  That is the
table hypothesis of the pointwise solo phase of
`Research/Quitting/PairActiveSoloPhase.lean`, which is a condition on
collision rows and independent of zero-freeness of the singleton rows.

Nothing here asserts that either table carries a diffuse tail, a solo window,
or a counterexample; this module supplies one hypothesis of conditional
theorems and nothing else.
-/

noncomputable section

namespace GameTheory

namespace SolanVieilleBoundary

open QuittingLCPClassification

/-- Closed form of the normalized solo matrix.  The diagonal vanishes, an
own-pair entry is `3`, and a cross-pair entry is `-1`. -/
theorem normalizedSoloMatrix_eval (who owner : Player) :
    normalizedSoloMatrix boundaryReward who owner =
      if owner = who then 0
      else if owner.val / 2 = who.val / 2 then 3 else -1 := by
  rw [normalizedSoloMatrix_eq_soloReward_sub]
  fin_cases who <;> fin_cases owner <;> norm_num

/-- Every off-diagonal entry has absolute value at least `1`: the table is
zero-free with a uniform margin. -/
theorem one_le_abs_normalizedSoloMatrix {who owner : Player} (hne : who ≠ owner) :
    1 ≤ |normalizedSoloMatrix boundaryReward who owner| := by
  rw [normalizedSoloMatrix_eval, if_neg (fun h ↦ hne h.symm)]
  split_ifs <;> norm_num

/-- **The Solan–Vieille boundary table has solo-matrix margin one.**  This is
the quantitative hypothesis the effective charge budget consumes. -/
theorem soloMatrixMargin_boundaryReward :
    QuittingSoloMatrixMargin boundaryReward 1 :=
  fun _ _ hne => one_le_abs_normalizedSoloMatrix hne

/-- **The Solan–Vieille boundary table is zero-free.**  No off-diagonal entry
of its normalized solo matrix vanishes. -/
theorem zeroFree_boundaryReward :
    QuittingZeroFreeSoloMatrix boundaryReward :=
  quittingZeroFreeSoloMatrix_of_soloMatrixMargin boundaryReward one_pos
    soloMatrixMargin_boundaryReward

/-- Every collision row of the table pays `1` to each colliding player. -/
theorem collisionReward_eval (owner who : Player) :
    quittingSingletonCollisionReward boundaryReward owner who = 1 := by
  fin_cases owner <;> fin_cases who <;> rfl

/-- Closed form of the pair collision increments: joining a same-pair
partner's exit costs `3`, joining a cross-pair player's exit gains `1`. -/
theorem quittingPairCollisionIncrement_eval (who owner : Player) :
    quittingPairCollisionIncrement boundaryReward who owner =
      if owner = who then 0
      else if owner.val / 2 = who.val / 2 then -3 else 1 := by
  rw [quittingPairCollisionIncrement, collisionReward_eval, soloReward_eval]
  split_ifs <;> norm_num

/-- **The Solan–Vieille boundary table is pair-collision nondegenerate.**
Joining another player's solo exit always changes what a player receives, so
the pointwise solo phase of
`Research/Quitting/PairActiveSoloPhase.lean` applies to this table. -/
theorem pairCollisionNondegenerate_boundaryReward :
    QuittingPairCollisionNondegenerate boundaryReward := by
  intro who owner hne
  rw [quittingPairCollisionIncrement_eval, if_neg (fun h => hne h.symm)]
  split_ifs <;> norm_num

end SolanVieilleBoundary

end GameTheory
