/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.ConditionedProductPurification

/-!
# A five-player phase--seam regression with positive singleton atoms

This file kernel-checks the literal rational table behind the scalar
phase--seam regression.  At each of five phases exactly one opponent Quits
with probability `1 / 2`.  Every phase therefore has a positive nonempty
opponent-only atom, while player zero's exact Bellman maps all contract by
`1 / 2`.  Exact propagation around the word gives the closing map `x / 32`,
but the supported Continue row at phase four requires `x >= 1`.

The result is an interface separation.  It is not a counterexample to
uniform-equilibrium existence, and it supplies neither deleted-game source
provenance nor positive omitted-player gaps.
-/

noncomputable section

namespace GameTheory
namespace FinFivePhaseSeamAtomFloor

open Math.Probability Set

abbrev Player := Fin 5

/-- The unique possible quitter at each phase. -/
def phaseQuitter : Player → Player := ![2, 3, 4, 2, 1]

/-- The common fair Quit/Continue marginal. -/
def halfCoin : PMF Bool :=
  quittingHazardCoin (1 / 2 : ℝ) (by norm_num) (by norm_num)

/-- At phase `phase`, only `phaseQuitter phase` may Quit. -/
def phaseRoot (phase : Player) : Player → PMF Bool :=
  quittingSoloStationaryRoot (phaseQuitter phase) halfCoin

/-- The literal reward table, extended harmlessly to the empty coalition. -/
def weight (coalition : Finset Player) (who : Player) : ℝ :=
  if who = 0 then
    if coalition = {0, 1} then 1
    else if coalition = {0, 2} ∨ coalition = {0, 3} ∨ coalition = {0, 4}
      then -1
    else 0
  else 0

/-- The reward table on nonempty quitting coalitions. -/
def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  rewardOfWeight weight

@[simp] theorem weightOfReward_eq (coalition : Finset Player)
    (hcoalition : coalition.Nonempty) (who : Player) :
    weightOfReward reward coalition who = weight coalition who := by
  exact weightOfReward_rewardOfWeight weight coalition hcoalition who

theorem phaseQuitter_ne_phase (phase : Player) :
    phaseQuitter phase ≠ phase := by
  fin_cases phase <;> decide

theorem phaseQuitter_ne_zero (phase : Player) :
    phaseQuitter phase ≠ 0 := by
  fin_cases phase <;> decide

/-- The face owner literally Continues at its own phase root. -/
theorem phaseRoot_owner_quiet (phase : Player) :
    phaseRoot phase phase = PMF.pure false := by
  exact quittingSoloStationaryRoot_apply_other
    (Ne.symm (phaseQuitter_ne_phase phase)) halfCoin

/-- Player zero also Continues surely at every phase. -/
theorem phaseRoot_zero_continue (phase : Player) :
    phaseRoot phase 0 = PMF.pure false := by
  exact quittingSoloStationaryRoot_apply_other
    (Ne.symm (phaseQuitter_ne_zero phase)) halfCoin

/-- Every phase has the nonempty singleton atom selected in the note. -/
theorem phaseRoot_singletonAtomMass (phase : Player) :
    quittingRootCoalitionMass (phaseRoot phase) {phaseQuitter phase} =
      (1 / 2 : ℝ) := by
  rw [phaseRoot, quittingRootCoalitionMass_solo_of_nonempty
    (phaseQuitter phase) halfCoin {phaseQuitter phase}
      (Finset.singleton_nonempty _)]
  simp [halfCoin]

/-- The selected atom is opponent-only for the face owner. -/
theorem phaseRoot_singletonAtom_excludes_owner (phase : Player) :
    phase ∉ ({phaseQuitter phase} : Finset Player) := by
  simp [Ne.symm (phaseQuitter_ne_phase phase)]

@[simp] theorem singletonWeight_phaseQuitter_zero (phase : Player) :
    weight {phaseQuitter phase} 0 = 0 := by
  have hpair : ∀ other : Player,
      ({phaseQuitter phase} : Finset Player) ≠ {0, other} := by
    intro other heq
    have hmem : (0 : Player) ∈ ({phaseQuitter phase} : Finset Player) := by
      rw [heq]
      simp
    apply (Ne.symm (phaseQuitter_ne_zero phase))
    simpa using hmem
  simp [weight, hpair]

/-- Every player-zero scalar Bellman map is exactly `z |-> z / 2`. -/
theorem playerZero_successorPayoff (phase : Player) (tail : Payoff Player) :
    quittingRootSuccessorPayoff reward tail (phaseRoot phase) 0 =
      tail 0 / 2 := by
  rw [phaseRoot, congrFun
    (quittingRootSuccessorPayoff_solo reward (phaseQuitter phase) halfCoin tail) 0]
  simp only [halfCoin, quittingHazardCoin_true_toReal,
    quittingHazardCoin_false_toReal]
  change (1 / 2 : ℝ) * weight {phaseQuitter phase} 0 +
      (1 - 1 / 2 : ℝ) * tail 0 = tail 0 / 2
  rw [singletonWeight_phaseQuitter_zero]
  ring

/-- The propagated scalar annotations `v_0,...,v_4`. -/
def phaseValue (x : ℝ) : Player → ℝ :=
  ![x, x / 16, x / 8, x / 4, x / 2]

/-- The successor scalar read by each phase root. -/
def phaseTail (x : ℝ) : Player → ℝ :=
  ![x / 16, x / 8, x / 4, x / 2, x]

/-- Phases one through four obey exact nonseam Bellman propagation. -/
theorem playerZero_exact_nonseam_propagation (x : ℝ) (phase : Player)
    (hphase : phase ≠ 0) :
    phaseValue x phase =
      quittingRootSuccessorPayoff reward (fun _ => phaseTail x phase)
        (phaseRoot phase) 0 := by
  rw [playerZero_successorPayoff]
  fin_cases phase <;> simp_all [phaseValue, phaseTail] <;> ring

/-- Closing phase zero sends the propagated `v_1` to `x / 32`. -/
theorem playerZero_closingMap (x : ℝ) :
    quittingRootSuccessorPayoff reward (fun _ => phaseTail x 0)
        (phaseRoot 0) 0 = x / 32 := by
  rw [playerZero_successorPayoff]
  simp [phaseTail]
  ring

@[simp] theorem pairWeight_zero_one :
    weight ({0, 1} : Finset Player) 0 = 1 := by
  norm_num [weight]

/-- At phase four, player zero's Quit-minus-Continue endpoint difference is
`(1 - x) / 2`; its supported Continue row therefore requires `x >= 1`. -/
theorem phaseFour_playerZero_endpointDifference (x : ℝ) :
    quittingRootEndpointDifference reward (fun _ => x) (phaseRoot 4) 0 =
      (1 - x) / 2 := by
  have hne : (0 : Player) ≠ phaseQuitter 4 := by decide
  rw [quittingRootEndpointDifference,
    phaseRoot,
    quittingRootQuitPayoff_soloStationaryRoot_other reward hne,
    quittingRootContinuePayoff_soloStationaryRoot_other reward hne]
  have hsoloZero : quittingSoloReward reward 0 0 = 0 := by
    change weight ({0} : Finset Player) 0 = 0
    rw [weight, if_pos rfl]
    simp only [if_neg (by decide : ({0} : Finset Player) ≠ {0, 1})]
    have hpairs : ¬(({0} : Finset Player) = ({0, 2} : Finset Player) ∨
      ({0} : Finset Player) = ({0, 3} : Finset Player) ∨
      ({0} : Finset Player) = ({0, 4} : Finset Player)) := by decide
    rw [if_neg hpairs]
  have hsoloOne : quittingSoloReward reward 1 0 = 0 := by
    change weight ({1} : Finset Player) 0 = 0
    rw [weight, if_pos rfl]
    simp only [if_neg (by decide : ({1} : Finset Player) ≠ {0, 1})]
    have hpairs : ¬(({1} : Finset Player) = ({0, 2} : Finset Player) ∨
      ({1} : Finset Player) = ({0, 3} : Finset Player) ∨
      ({1} : Finset Player) = ({0, 4} : Finset Player)) := by decide
    rw [if_neg hpairs]
  have hpair : quittingSingletonCollisionReward reward 1 0 = 1 := by
    change weight ({1, 0} : Finset Player) 0 = 1
    have hset : ({1, 0} : Finset Player) = {0, 1} := by
      ext who
      simp [or_comm]
    rw [hset, pairWeight_zero_one]
  have hq : phaseQuitter 4 = 1 := rfl
  rw [hq]
  rw [hsoloZero, hsoloOne, hpair]
  norm_num [halfCoin]
  ring

/-- The phase-four support row alone is feasible at the canonical endpoint. -/
theorem phaseFour_row_feasible :
    quittingRootEndpointDifference reward (fun _ => (1 : ℝ))
      (phaseRoot 4) 0 ≤ 0 := by
  rw [phaseFour_playerZero_endpointDifference]
  norm_num

/-- The upper closing-seam row alone is feasible at `x = 0`. -/
theorem closingSeam_row_feasible :
    (31 / 32 : ℝ) * 0 ≤ 0 := by
  norm_num

/-- At exact closure, the phase-four support row and the closing-seam row
are jointly infeasible on the canonical reward interval. -/
theorem not_exists_exact_phaseFour_closingSeam :
    ¬ ∃ x : ℝ, x ∈ Set.Icc (-1) 1 ∧
      quittingRootEndpointDifference reward (fun _ => x)
          (phaseRoot 4) 0 ≤ 0 ∧
        (31 / 32 : ℝ) * x ≤ 0 := by
  rintro ⟨x, _hx, hphase, hseam⟩
  rw [phaseFour_playerZero_endpointDifference] at hphase
  norm_num at hphase hseam
  linarith

end FinFivePhaseSeamAtomFloor
end GameTheory
