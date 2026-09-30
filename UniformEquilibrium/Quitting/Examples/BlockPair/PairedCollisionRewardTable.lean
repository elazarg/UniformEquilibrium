/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryTable
import UniformEquilibrium.Quitting.Classification.LCP.Normalization

/-!
# The literal paired-collision reward family

Only the twelve member coordinates in two-player collision rows vary with `c`.
The live and Never rewards use the repository's zero convention.
-/

noncomputable section

namespace GameTheory.PairedCollisionReward

abbrev Player := Fin 4

/-- The fifteen literal terminal rows from the paired collision packet. -/
def reward (c : ℝ) (quitters : {S : Finset Player // S.Nonempty}) : Payoff Player :=
  match decide (0 ∈ quitters.1), decide (1 ∈ quitters.1),
      decide (2 ∈ quitters.1), decide (3 ∈ quitters.1) with
  | true, false, false, false => ![1, 4, 0, 0]
  | false, true, false, false => ![4, 1, 0, 0]
  | false, false, true, false => ![0, 0, 1, 4]
  | false, false, false, true => ![0, 0, 4, 1]
  | true, true, false, false => ![c, c, 1, 1]
  | true, false, true, false => ![c, 1, c, 0]
  | true, false, false, true => ![c, 0, 1, c]
  | false, true, true, false => ![0, c, c, 1]
  | false, true, false, true => ![1, c, 0, c]
  | false, false, true, true => ![1, 1, c, c]
  | true, true, true, false => ![1, 0, 0, 0]
  | true, true, false, true => ![0, 1, 0, 0]
  | true, false, true, true => ![0, 0, 0, 1]
  | false, true, true, true => ![0, 0, 1, 0]
  | true, true, true, true => ![-1, -1, -1, -1]
  | false, false, false, false => ![0, 0, 0, 0]

/-- At parameter one this is literally the existing boundary table. -/
@[simp] theorem reward_one : reward 1 = SolanVieilleBoundary.boundaryReward := rfl

/-- The raw singleton rows are independent of the collision parameter. -/
@[simp] theorem soloReward_eval (c : ℝ) (owner who : Player) :
    quittingSoloReward (reward c) owner who =
      if owner = who then 1
      else if owner.val / 2 = who.val / 2 then 4
      else 0 := by
  fin_cases owner <;> fin_cases who <;> rfl

theorem unitSoloExit (c : ℝ) : QuittingUnitSoloExit (reward c) := by
  intro who
  simp

/-- The singleton-difference matrix is constant over the entire real family. -/
theorem singletonMatrix (c : ℝ) (who owner : Player) :
    QuittingLCPClassification.quittingSingletonMatrix (reward c) who owner =
      ![![0, 3, -1, -1], ![3, 0, -1, -1],
        ![-1, -1, 0, 3], ![-1, -1, 3, 0]] who owner := by
  fin_cases who <;> fin_cases owner <;>
    norm_num [QuittingLCPClassification.quittingSingletonMatrix, reward]

/-- Member rewards are bounded by one for every real `c ≤ 1`. -/
theorem cappedJointExit {c : ℝ} (hc : c ≤ 1) :
    QuittingCappedJointExit (reward c) := by
  intro quitters who
  fin_cases quitters <;> fin_cases who <;> simp [reward] <;> linarith

end GameTheory.PairedCollisionReward
