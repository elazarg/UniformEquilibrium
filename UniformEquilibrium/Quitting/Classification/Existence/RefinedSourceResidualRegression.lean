/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.PositiveRhoLandingClassificationBoundary
import UniformEquilibrium.Quitting.Classification.OnePlayer.StationaryBranch

/-!
# A regression for excluding refined pointwise source residuals

The refined corrected-pointwise residual is not disjoint from the three AKRS
branches.  In the one-player unit-reward game, the exact stationary branch
holds, but the constant all-Continue support--Bellman spine still supplies the
positive-singleton suffix-defect residual at every nonnegative tolerance.

Thus a proof of the three-branch classification cannot establish the first
dependency by showing that every refined source residual is impossible.  It
must instead consume a residual using other source data, or choose an already
available classified branch before retaining that residual.
-/

noncomputable section

namespace GameTheory

open StochasticGame

namespace RefinedSourceResidualRegression

open CompactSpineSurvivalBoundaryRegression
open StationaryPrefixEndpointDecouplingRegression

/-- The unit one-player game has a positive-singleton suffix-defect residual
at every nonnegative tolerance. -/
theorem nonempty_positiveSingletonDefectResidual (delta : ℝ)
    (hdelta : 0 ≤ delta) :
    Nonempty (QuittingSupportBellmanPositiveSingletonDefectResidual
      reward delta) := by
  obtain ⟨value, roots, hvalue, hbellman, hsupport, hsurvival, _hmismatch⟩ :=
    exists_positiveSurvival_supportBellmanSpine_with_terminal_mismatch
  obtain ⟨boundary⟩ := exists_quittingSupportBellmanPositiveSurvivalBoundary
    reward value roots delta 0 (hsurvival 0) hvalue hbellman
      (fun time ↦ (hsupport time).mono hdelta)
  have hsolo : 0 < reward (quittingSingletonTerminal PUnit.unit) PUnit.unit := by
    simp [reward]
  exact ⟨{
    boundary := boundary
    defect := boundary.positiveSingletonSuffixDefectOf PUnit.unit hsolo }⟩

/-- Consequently the full refined residual occurs at every nonnegative
tolerance, through its positive-survival arm. -/
theorem refinedSourceResidualAt (delta : ℝ) (hdelta : 0 ≤ delta) :
    QuittingCorrectedPointwiseRefinedSourceResidualAt reward delta := by
  exact Or.inr (Or.inr (nonempty_positiveSingletonDefectResidual delta hdelta))

/-- The same game belongs to the exact stationary classification branch.
Hence occurrence of a refined source residual does not obstruct the AKRS
conclusion and cannot be ruled out unconditionally. -/
theorem stationaryExistence_and_refinedSourceResidualAt (delta : ℝ)
    (hdelta : 0 ≤ delta) :
    QuittingStationaryεEquilibriumExistence reward ∧
      QuittingCorrectedPointwiseRefinedSourceResidualAt reward delta := by
  exact ⟨quittingStationaryεEquilibriumExistence_onePlayer reward,
    refinedSourceResidualAt delta hdelta⟩

/-- In particular, the universal no-residual premise used by the sufficient
source-closure capstone is false, already for the unit one-player game. -/
theorem not_forall_positive_no_refinedSourceResidual :
    ¬(∀ delta : ℝ, 0 < delta →
      ¬QuittingCorrectedPointwiseRefinedSourceResidualAt reward delta) := by
  intro hnoResidual
  exact hnoResidual 1 (by norm_num) (refinedSourceResidualAt 1 (by norm_num))

end RefinedSourceResidualRegression
end GameTheory
