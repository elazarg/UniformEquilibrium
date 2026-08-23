/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Experiments.counterexample_search.RegularTournamentFiveSeed
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.DiffuseTailSoloStructure
import UniformEquilibrium.Quitting.Cycles.DiffuseTailSoloStructure

/-!
# Zero-free calibration: the regular five-player tournament seed

`QuittingZeroFreeSoloMatrix`
(`Research/Quitting/DiffuseTailSoloStructure.lean`) names the regular
five-player tournament seed as an intended instance; this module supplies the
instance for the literal seed table of
`Experiments/counterexample_search/RegularTournamentFiveSeed.lean`.

The seed's normalized solo matrix is the tournament matrix `2 A - Aᵀ`
(`normalizedSoloMatrix_eq_singletonMatrix`), whose off-diagonal entries are
`2` on a tournament edge and `-1` against it.  Hence every off-diagonal entry
has absolute value at least `1`, which is the margin form the quantitative T2
inequality `survivalGap_mul_abs_normalizedSoloMatrix_le_of_soloWindow`
consumes.

The companion instance for the Solan–Vieille boundary table is in
`Research/Quitting/DiffuseTailSoloCalibrations.lean`.  It is in the Research
lane because its table is production data; this one is in the Experiments
lane because the seed table is, and Research must never import Experiments.

## Scope

This is a hypothesis check on one literal table, not evidence that the seed
carries a diffuse tail or a solo window.  The seed's realized game has a
uniform-equilibrium payoff
(`Experiments/counterexample_search/RegularTournamentFiveSeedSureExit.lean`),
so it is a calibration instance, not a counterexample candidate.

## Reproduction

This module can be checked independently with Lean.
-/

noncomputable section

namespace GameTheory
namespace RegularTournamentFiveSeed

open QuittingLCPClassification Math.LinearProgramming

/-- Off the diagonal the tournament matrix takes the value `2` or `-1`. -/
theorem singletonMatrix_eq_two_or_neg_one {first second : Player}
    (hne : first ≠ second) :
    singletonMatrix first second = 2 ∨ singletonMatrix first second = -1 := by
  fin_cases first <;> fin_cases second <;>
    simp_all [singletonMatrix, tournamentSkewMatrix, adjacency]

/-- Every off-diagonal entry has absolute value at least `1`: the seed table
is zero-free with a uniform margin. -/
theorem one_le_abs_normalizedSoloMatrix {who owner : Player} (hne : who ≠ owner) :
    1 ≤ |normalizedSoloMatrix reward who owner| := by
  rw [normalizedSoloMatrix_eq_singletonMatrix]
  rcases singletonMatrix_eq_two_or_neg_one hne with hentry | hentry <;>
    rw [hentry] <;> norm_num

/-- **The regular five-player tournament seed has solo-matrix margin one.**
This is the quantitative hypothesis the effective charge budget consumes. -/
theorem soloMatrixMargin_reward : QuittingSoloMatrixMargin reward 1 :=
  fun _ _ hne => one_le_abs_normalizedSoloMatrix hne

/-- **The regular five-player tournament seed is zero-free.**  No off-diagonal
entry of its normalized solo matrix vanishes. -/
theorem zeroFree_reward : QuittingZeroFreeSoloMatrix reward := by
  intro who owner hne hzero
  have hone := one_le_abs_normalizedSoloMatrix hne
  rw [hzero] at hone
  norm_num at hone

end RegularTournamentFiveSeed
end GameTheory
