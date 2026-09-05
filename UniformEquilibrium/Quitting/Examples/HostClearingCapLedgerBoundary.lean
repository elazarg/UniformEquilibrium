/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Examples.HostClearingBoundary
import UniformEquilibrium.Quitting.Root.FiniteWordWeightedCapDefectLedger

/-! # The marked outsider's reached cap ledger is one

This computes the ledger of the separate marked profile from the host-clock
regression. It does not identify that profile with the original clock word.
-/

noncomputable section

namespace GameTheory.HostClearingBoundary

open QuittingSureSetOwnerRepair

theorem marked_outsider_capDefect :
    quittingRootCoordinateNashDefect reward (quittingTerminalSemanticPair reward tail).2
      markedRoot 1 = 1 := by
  rw [tail_diagonal]
  change quittingRootCoordinateNashDefect reward 0 markedRoot 1 = 1
  unfold quittingRootCoordinateNashDefect
  rw [markedRoot, quittingRootQuitPayoff_pureSetRoot_eq_insert,
    quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty _ _ _ (by simp)]
  unfold quittingRootSuccessorPayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootAbsorbingContribution_pureSetRoot]
  norm_num [quittingSetReward, reward,
    show ({2} : Finset (Fin 4)) ≠ {1, 2} by decide]
  split_ifs <;> norm_num

theorem marked_outsider_capLedger :
    quittingFiniteWordPlayerCapDefectLedger reward [markedRoot] tail 1 = 1 := by
  simpa [quittingFiniteWordPlayerCapDefectLedger] using marked_outsider_capDefect

end GameTheory.HostClearingBoundary
