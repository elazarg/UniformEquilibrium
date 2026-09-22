/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.BalancedSingletonCertificate
import UniformEquilibrium.Quitting.Classification.PreemptionGateDictionary

/-!
# Exact four-player passive-row cycle fixture

This file checks the packet's displayed rational singleton matrix and its
three-phase ambient balanced cycle. Own singleton levels and nonsingleton
coalition rewards remain arbitrary. No R0-degree or open-neighborhood claim
is made here.
-/

noncomputable section

namespace GameTheory.PassiveRowFourFixture

abbrev Player := Fin 4
abbrev Reward := {S : Finset Player // S.Nonempty} → Payoff Player

/-- The packet's literal singleton-difference matrix. -/
def matrix : Matrix Player Player ℝ :=
  !![0, -1, 2, -2; 2, 0, -1, 1; -1, 2, 0, 1; -1, 2, 2, 0]

/-- The selected principal on players zero, one, and two. -/
def childMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  fun who quitter => matrix who.castSucc quitter.castSucc

theorem childMatrix_inverse : childMatrix⁻¹ =
    (1 / 7 : ℝ) • !![2, 4, 1; 1, 2, 4; 4, 1, 2] := by
  apply Matrix.inv_eq_left_inv
  ext who quitter
  fin_cases who <;> fin_cases quitter <;>
    norm_num [childMatrix, matrix, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.one_apply]

/-- The three active owners, leaving player three passive. -/
def owner : Fin 3 → Player := ![0, 1, 2]

/-- The exact phase surpluses over each player's own singleton. -/
def surplus : Fin 3 → Payoff Player :=
  ![![0, 1, 0, 2 / 7], ![0, 0, 1, 11 / 7], ![1, 0, 0, 8 / 7]]

def coarse (reward : Reward) (phase : Fin 3) : Payoff Player :=
  fun who => quittingSoloReward reward who who + surplus phase who

/-- Exact row factorization for the fourth player on the selected triple. -/
theorem outside_row_factorization (selected : Fin 3) :
    matrix 3 selected.castSucc =
      ∑ inside : Fin 3,
        (![8 / 7, 2 / 7, 11 / 7] inside) *
          matrix (inside.castSucc) (selected.castSucc) := by
  fin_cases selected <;> norm_num [matrix, Fin.sum_univ_succ]

/-- The displayed phase values are a balanced singleton certificate for
every table with this singleton-difference matrix. -/
def certificate (reward : Reward)
    (hmatrix : ∀ who quitter,
      quittingSoloReward reward quitter who -
        quittingSoloReward reward who who = matrix who quitter) :
    BalancedSingletonCycleCertificate (L := 3) reward := by
  refine {
    owner := owner
    hazard := fun _ => 1 / 2
    coarse := coarse reward
    initial := 0
    hazard_nonneg := by intro; norm_num
    hazard_lt_one := by intro; norm_num
    arc := ?_
    active := ?_
    soloFloor := ?_
    opponentDivergence := ?_ }
  · intro phase
    funext who
    have h := hmatrix who (owner phase)
    fin_cases phase <;> fin_cases who <;>
      norm_num [coarse, surplus, owner, quittingSingletonArcPayoff, matrix] at h ⊢ <;>
      linarith
  · intro phase
    fin_cases phase <;> norm_num [coarse, surplus, owner]
  · intro phase who
    fin_cases phase <;> fin_cases who <;> norm_num [coarse, surplus]
  · intro who
    fin_cases who
    · exact ⟨1, by norm_num [owner], by norm_num⟩
    · exact ⟨2, by norm_num [owner], by norm_num⟩
    · exact ⟨0, by norm_num [owner], by norm_num⟩
    · exact ⟨0, by norm_num [owner], by norm_num⟩

/-- The explicit fixed uniform payoff is the own-singleton baseline plus
the phase-zero surplus `(0,1,0,2/7)`. -/
theorem target_isUniformEquilibriumPayoff (reward : Reward)
    (hmatrix : ∀ who quitter,
      quittingSoloReward reward quitter who -
        quittingSoloReward reward who who = matrix who quitter) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (coarse reward 0) :=
  (certificate reward hmatrix).isUniformEquilibriumPayoff

end GameTheory.PassiveRowFourFixture
