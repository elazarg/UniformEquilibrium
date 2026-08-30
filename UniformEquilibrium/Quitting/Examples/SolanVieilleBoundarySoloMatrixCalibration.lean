/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.DiffuseTailSoloStructure
import UniformEquilibrium.Quitting.Examples.BlockPair.FourPlayerPairedSingleton
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryTable

/-!
# Solo-matrix calibration of the Solan–Vieille boundary table

The normalized solo matrix of `boundaryReward` has closed form: an
off-diagonal entry is `3` inside a pair and `-1` across the pairs.  Thus every
off-diagonal entry has absolute value at least `1`, giving both the literal
solo-matrix margin-one property and zero-freeness.

These are table facts.  They do not assert the existence of a diffuse tail,
a solo window, or a counterexample.
-/

noncomputable section

namespace GameTheory

namespace SolanVieilleBoundary

open QuittingLCPClassification

/-- The boundary table's normalized solo matrix is the canonical paired
singleton matrix. -/
theorem normalizedSoloMatrix_boundaryReward_eq_pairedSingletonMatrix :
    normalizedSoloMatrix boundaryReward =
      FourPlayerPairedSingleton.pairedSingletonMatrix := by
  funext who owner
  rw [normalizedSoloMatrix_eq_soloReward_sub]
  fin_cases who <;> fin_cases owner <;>
    norm_num [FourPlayerPairedSingleton.pairedSingletonMatrix]

/-- Closed form of the normalized solo matrix of the boundary table.  The
diagonal vanishes, an own-pair entry is `3`, and a cross-pair entry is `-1`. -/
theorem normalizedSoloMatrix_boundaryReward_eval (who owner : Player) :
    normalizedSoloMatrix boundaryReward who owner =
      if owner = who then 0
      else if owner.val / 2 = who.val / 2 then 3 else -1 := by
  rw [normalizedSoloMatrix_boundaryReward_eq_pairedSingletonMatrix]
  fin_cases who <;> fin_cases owner <;>
    norm_num [FourPlayerPairedSingleton.pairedSingletonMatrix]

/-- Every off-diagonal entry of the boundary table's normalized solo matrix
has absolute value at least `1`. -/
theorem one_le_abs_normalizedSoloMatrix_boundaryReward
    {who owner : Player} (hne : who ≠ owner) :
    1 ≤ |normalizedSoloMatrix boundaryReward who owner| := by
  rw [normalizedSoloMatrix_boundaryReward_eval, if_neg (fun h ↦ hne h.symm)]
  split_ifs <;> norm_num

/-- The boundary table has normalized solo-matrix margin one. -/
theorem quittingSoloMatrixMargin_one_boundaryReward :
    QuittingSoloMatrixMargin boundaryReward 1 :=
  fun _ _ hne ↦ one_le_abs_normalizedSoloMatrix_boundaryReward hne

/-- No off-diagonal entry of the boundary table's normalized solo matrix
vanishes. -/
theorem quittingZeroFreeSoloMatrix_boundaryReward :
    QuittingZeroFreeSoloMatrix boundaryReward :=
  quittingZeroFreeSoloMatrix_of_soloMatrixMargin boundaryReward one_pos
    quittingSoloMatrixMargin_one_boundaryReward

end SolanVieilleBoundary

end GameTheory
