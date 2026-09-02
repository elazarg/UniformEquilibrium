/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.FullSupportLCPSignBarrier
import UniformEquilibrium.Quitting.Classification.PreemptionGateDictionary
import UniformEquilibrium.Quitting.Cycles.BalancedSingletonCertificate

/-!
# A balanced singleton cycle on the full-core four-player fibre

The normalized singleton matrix `fullCoreMatrix` admits an explicit
four-phase balanced singleton cycle.  The cycle is valid for every actual
reward table in that normalized fibre, independently of all nonsingleton
rewards.  The existing balanced-cycle compiler therefore supplies a literal
uniform-equilibrium payoff for the whole affine fibre.
-/

noncomputable section

namespace GameTheory
namespace FourPointCrossedRowsNoCyclicSign

open QuittingLCPClassification

private theorem sqrt13_sq : Real.sqrt 13 ^ 2 = 13 := by
  exact Real.sq_sqrt (by norm_num)

private theorem sqrt13_nonneg : 0 ≤ Real.sqrt 13 :=
  Real.sqrt_nonneg 13

private theorem sqrt13_pos : 0 < Real.sqrt 13 := by
  positivity

private theorem sqrt13_lt_four : Real.sqrt 13 < 4 := by
  nlinarith [sqrt13_sq, sqrt13_nonneg]

@[simp] private theorem finRotate_four_apply (phase : Player) :
    finRotate 4 phase = ![(1 : Player), 2, 3, 0] phase := by
  fin_cases phase <;> decide

/-- The four interior coarse hazards of the balanced full-core cycle. -/
def fullCoreBalancedHazard : Player → ℝ :=
  ![(1 + 5 * Real.sqrt 13) / 54,
    (19 + 7 * Real.sqrt 13) / 138,
    (1 + Real.sqrt 13) / 14,
    (13 + Real.sqrt 13) / 78]

/-- The four nonnegative excess payoff vectors, relative to the vector of
own-singleton baselines. -/
def fullCoreBalancedExcess : Player → Payoff Player :=
  ![![0, (1 + 5 * Real.sqrt 13) / 54,
        (11 + Real.sqrt 13) / 54, 0],
    ![0, 0, (19 + 7 * Real.sqrt 13) / 46,
        (7 + 5 * Real.sqrt 13) / 46],
    ![(3 + Real.sqrt 13) / 14, 0, 0,
        (1 + Real.sqrt 13) / 14],
    ![(13 + Real.sqrt 13) / 78,
        (13 + 7 * Real.sqrt 13) / 78, 0, 0]]

/-- The same selected payoff written from an arbitrary singleton baseline
vector. -/
def fullCoreBalancedAffinePayoff (baseline : Payoff Player) : Payoff Player :=
  ![baseline 0,
    baseline 1 + (1 + 5 * Real.sqrt 13) / 54,
    baseline 2 + (11 + Real.sqrt 13) / 54,
    baseline 3]

theorem fullCoreBalancedHazard_pos (phase : Player) :
    0 < fullCoreBalancedHazard phase := by
  fin_cases phase <;>
    simp [fullCoreBalancedHazard] <;>
    nlinarith [sqrt13_pos]

theorem fullCoreBalancedHazard_nonneg (phase : Player) :
    0 ≤ fullCoreBalancedHazard phase :=
  (fullCoreBalancedHazard_pos phase).le

theorem fullCoreBalancedHazard_lt_one (phase : Player) :
    fullCoreBalancedHazard phase < 1 := by
  fin_cases phase <;>
    simp [fullCoreBalancedHazard] <;>
    nlinarith [sqrt13_lt_four]

theorem fullCoreBalancedExcess_nonneg (phase who : Player) :
    0 ≤ fullCoreBalancedExcess phase who := by
  fin_cases phase <;> fin_cases who <;>
    simp [fullCoreBalancedExcess] <;>
    nlinarith [sqrt13_nonneg]

theorem fullCoreBalancedExcess_owner_eq_zero (phase : Player) :
    fullCoreBalancedExcess phase phase = 0 := by
  fin_cases phase <;> simp [fullCoreBalancedExcess]

/-- All sixteen coordinates of the exact balanced singleton arc system. -/
theorem fullCoreBalancedExcess_arc (phase : Player) :
    fullCoreBalancedExcess phase =
      quittingSingletonArcPayoff (fullCoreBalancedHazard phase)
        (fun who ↦ fullCoreMatrix who phase)
        (fullCoreBalancedExcess (finRotate 4 phase)) := by
  funext who
  fin_cases phase <;> fin_cases who <;>
    simp [fullCoreBalancedExcess, fullCoreBalancedHazard,
      quittingSingletonArcPayoff, fullCoreMatrix, matrix] <;>
    nlinarith [sqrt13_sq]

/-- The normalized matrix hypothesis is exactly the singleton-row affine
identity used by the balanced arc. -/
theorem quittingSoloReward_eq_solo_add_fullCoreMatrix
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hmatrix : normalizedSoloMatrix reward = fullCoreMatrix)
    (who owner : Player) :
    quittingSoloReward reward owner who =
      quittingSoloReward reward who who + fullCoreMatrix who owner := by
  have hentry := congrFun (congrFun hmatrix who) owner
  rw [normalizedSoloMatrix_eq_soloReward_sub] at hentry
  linarith

/-- Exact actual-data characterization of the normalized full-core fibre. -/
theorem normalizedSoloMatrix_eq_fullCoreMatrix_iff
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player) :
    normalizedSoloMatrix reward = fullCoreMatrix ↔
      ∀ who owner,
        quittingSoloReward reward owner who =
          quittingSoloReward reward who who + fullCoreMatrix who owner := by
  constructor
  · intro hmatrix who owner
    exact quittingSoloReward_eq_solo_add_fullCoreMatrix
      reward hmatrix who owner
  · intro hrows
    funext who owner
    rw [normalizedSoloMatrix_eq_soloReward_sub, hrows who owner]
    ring

/-- Every actual reward table in the normalized full-core fibre supplies the
explicit four-phase balanced singleton certificate. -/
def fullCoreBalancedSingletonCycleCertificate
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hmatrix : normalizedSoloMatrix reward = fullCoreMatrix) :
    BalancedSingletonCycleCertificate (L := 4) reward where
  owner := fun phase ↦ phase
  hazard := fullCoreBalancedHazard
  coarse := fun phase who ↦
    quittingSoloReward reward who who + fullCoreBalancedExcess phase who
  initial := 0
  hazard_nonneg := fullCoreBalancedHazard_nonneg
  hazard_lt_one := fullCoreBalancedHazard_lt_one
  arc := by
    intro phase
    funext who
    change quittingSoloReward reward who who + fullCoreBalancedExcess phase who =
      fullCoreBalancedHazard phase * quittingSoloReward reward phase who +
        (1 - fullCoreBalancedHazard phase) *
          (quittingSoloReward reward who who +
            fullCoreBalancedExcess (finRotate 4 phase) who)
    rw [quittingSoloReward_eq_solo_add_fullCoreMatrix reward hmatrix who phase]
    have harc := congrFun (fullCoreBalancedExcess_arc phase) who
    change fullCoreBalancedExcess phase who =
      fullCoreBalancedHazard phase * fullCoreMatrix who phase +
        (1 - fullCoreBalancedHazard phase) *
          fullCoreBalancedExcess (finRotate 4 phase) who at harc
    change quittingSoloReward reward who who + fullCoreBalancedExcess phase who =
      fullCoreBalancedHazard phase *
          (quittingSoloReward reward who who + fullCoreMatrix who phase) +
        (1 - fullCoreBalancedHazard phase) *
          (quittingSoloReward reward who who +
            fullCoreBalancedExcess (finRotate 4 phase) who)
    rw [harc]
    ring
  active := by
    intro phase
    simp [fullCoreBalancedExcess_owner_eq_zero]
  soloFloor := by
    intro phase who
    exact le_add_of_nonneg_right (fullCoreBalancedExcess_nonneg phase who)
  opponentDivergence := by
    intro who
    fin_cases who
    · exact ⟨1, by decide, fullCoreBalancedHazard_pos 1⟩
    · exact ⟨0, by decide, fullCoreBalancedHazard_pos 0⟩
    · exact ⟨0, by decide, fullCoreBalancedHazard_pos 0⟩
    · exact ⟨0, by decide, fullCoreBalancedHazard_pos 0⟩

/-- Every table whose normalized singleton matrix is `fullCoreMatrix` has the
displayed fixed uniform-equilibrium payoff. -/
theorem fullCoreMatrix_isUniformEquilibriumPayoff
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hmatrix : normalizedSoloMatrix reward = fullCoreMatrix) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (fullCoreBalancedAffinePayoff
        (fun who ↦ quittingSoloReward reward who who)) := by
  have hcertificate :=
    (fullCoreBalancedSingletonCycleCertificate reward hmatrix).isUniformEquilibriumPayoff
  convert hcertificate using 1
  funext who
  fin_cases who <;>
    simp [fullCoreBalancedAffinePayoff, fullCoreBalancedExcess,
      fullCoreBalancedSingletonCycleCertificate]

/-- Literal affine-singleton-row form of the full-core fibre theorem.  No
condition is imposed on a nonsingleton reward row. -/
theorem fullCoreSingletonRows_isUniformEquilibriumPayoff
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (baseline : Payoff Player)
    (hrows : ∀ who owner,
      reward (quittingSingletonTerminal owner) who =
        baseline who + fullCoreMatrix who owner) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (fullCoreBalancedAffinePayoff baseline) := by
  have hmatrix : normalizedSoloMatrix reward = fullCoreMatrix := by
    funext who owner
    rw [normalizedSoloMatrix_eq_soloReward_sub]
    change reward (quittingSingletonTerminal owner) who -
        reward (quittingSingletonTerminal who) who = fullCoreMatrix who owner
    rw [hrows who owner, hrows who who, fullCoreMatrix_diagonal]
    ring
  have hbase : ∀ who,
      quittingSoloReward reward who who = baseline who := by
    intro who
    have h := hrows who who
    rw [fullCoreMatrix_diagonal, add_zero] at h
    exact h
  have huniform := fullCoreMatrix_isUniformEquilibriumPayoff reward hmatrix
  convert huniform using 1
  funext who
  fin_cases who <;>
    simp [fullCoreBalancedAffinePayoff, hbase]

end FourPointCrossedRowsNoCyclicSign
end GameTheory
