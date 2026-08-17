/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.DiffuseTailSoloStructure
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

The margin form `one_le_abs_normalizedSoloMatrix` is recorded because the
quantitative T2 inequality
(`survivalGap_mul_abs_normalizedSoloMatrix_le_of_soloWindow`) divides by the
entry, so a uniform positive lower bound, not mere nonvanishing, is what a
budget argument needs.

The other table named in the same docstring, the regular five-player
tournament seed, has its reward function under `Experiments/`; since Research
must never import Experiments, its zero-free instance lives beside it in
`Experiments/counterexample_search/RegularTournamentFiveSeedZeroFree.lean`.

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

/-- **The Solan–Vieille boundary table is zero-free.**  No off-diagonal entry
of its normalized solo matrix vanishes. -/
theorem zeroFree_boundaryReward :
    QuittingZeroFreeSoloMatrix boundaryReward := by
  intro who owner hne hzero
  have hone := one_le_abs_normalizedSoloMatrix hne
  rw [hzero] at hone
  norm_num at hone

end SolanVieilleBoundary

end GameTheory
