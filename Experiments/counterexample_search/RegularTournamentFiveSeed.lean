/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.LinearProgramming.Tournament
import UniformEquilibrium.Quitting.Classification.LCP.Gate
import UniformEquilibrium.Quitting.Classification.ImmediateSingletonCollision
import UniformEquilibrium.Quitting.Classification.PreemptionCycle
import UniformEquilibrium.Quitting.Classification.PreemptionGateDictionary
import UniformEquilibrium.Quitting.Classification.TerminalExploitabilitySoloExitPreference

/-!
# The regular five-player tournament seed

This is a checked finite calibration of the regular five-cycle singleton
geometry.  Its singleton matrix is `2 A - Aᵀ` for the regular
five-cycle tournament.  The normal core is all five players, the
homogeneous simplex branch is absent, and the table contains both a strict
directed preemption cycle and a marked immediate collision.

The module proves no standard-Q conclusion.  Such a conclusion requires a
separate implication from the two LCP uniqueness statements to solvability for
every right-hand side.

The seed also satisfies both assumptions of the quitting existence theorem of
Solan and Vieille, *Quitting games*, Math. Oper. Res. 26 (2001), Theorem 1.2,
so granting that theorem it carries no terminal exploitability witness.  That exclusion
is conditional on the theorem and is not proved here.
-/

noncomputable section

namespace GameTheory
namespace RegularTournamentFiveSeed

open Finset
open QuittingLCPClassification
open Math.LinearProgramming

abbrev Player := Fin 5

/-- The regular tournament on five cyclic vertices. -/
def adjacency : Player → Player → ℝ := fun i j =>
  match i with
  | 0 => ![0, 1, 1, 0, 0] j
  | 1 => ![0, 0, 1, 1, 0] j
  | 2 => ![0, 0, 0, 1, 1] j
  | 3 => ![1, 0, 0, 0, 1] j
  | 4 => ![1, 1, 0, 0, 0] j

def singletonMatrix : Player → Player → ℝ := tournamentSkewMatrix 2 adjacency

theorem adjacency_tournament : IsFractionalTournament adjacency := by
  constructor
  · intro i
    fin_cases i <;> norm_num [adjacency]
  · constructor
    · intro i j
      fin_cases i <;> fin_cases j <;> norm_num [adjacency]
    · intro i j hne
      fin_cases i <;> fin_cases j <;> simp_all [adjacency]

theorem adjacency_hasUnitOutneighbor :
    FractionalTournamentHasUnitOutneighbor adjacency := by
  intro i
  fin_cases i
  · exact ⟨1, by decide, by norm_num [adjacency]⟩
  · exact ⟨2, by decide, by simp [adjacency]⟩
  · exact ⟨3, by decide, by simp [adjacency]⟩
  · exact ⟨4, by decide, by simp [adjacency]⟩
  · exact ⟨0, by decide, by simp [adjacency]⟩

theorem singletonMatrix_entries :
    singletonMatrix = fun i j =>
      match i with
      | 0 => ![0, 2, 2, -1, -1] j
      | 1 => ![-1, 0, 2, 2, -1] j
      | 2 => ![-1, -1, 0, 2, 2] j
      | 3 => ![2, -1, -1, 0, 2] j
      | 4 => ![2, 2, -1, -1, 0] j := by
  funext i j
  fin_cases i <;> fin_cases j <;> norm_num [singletonMatrix, tournamentSkewMatrix,
    adjacency]

theorem singletonMatrix_diagonal (i : Player) : singletonMatrix i i = 0 := by
  fin_cases i <;> norm_num [singletonMatrix, tournamentSkewMatrix, adjacency]

theorem singletonMatrix_has_negative (i : Player) :
    ∃ j, i ≠ j ∧ singletonMatrix i j < 0 := by
  fin_cases i
  · exact ⟨3, by decide, by change (2 * 0 - 1 : ℝ) < 0; norm_num⟩
  · exact ⟨4, by decide, by change (2 * 0 - 1 : ℝ) < 0; norm_num⟩
  · exact ⟨0, by decide, by change (2 * 0 - 1 : ℝ) < 0; norm_num⟩
  · exact ⟨1, by decide, by change (2 * 0 - 1 : ℝ) < 0; norm_num⟩
  · exact ⟨2, by decide, by change (2 * 0 - 1 : ℝ) < 0; norm_num⟩

theorem normalLayer_eq_univ (n : ℕ) :
    normalLayer singletonMatrix n = Finset.univ := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [normalLayer, ih]
      apply Finset.filter_eq_self.mpr
      intro i hi
      obtain ⟨j, hne, hneg⟩ := singletonMatrix_has_negative i
      exact ⟨j, Finset.mem_univ j, hne.symm, le_of_lt hneg⟩

theorem normalCore_eq_univ : normalCore singletonMatrix = Finset.univ := by
  ext i
  simp [mem_normalCore, normalLayer_eq_univ]

theorem no_homogeneous : ¬HasHomogeneousSimplexSolution singletonMatrix := by
  rw [show singletonMatrix = tournamentSkewMatrix 2 adjacency by rfl]
  exact not_singletonLCPFeasible_tournamentSkewMatrix 2 adjacency
    adjacency_tournament adjacency_hasUnitOutneighbor (by norm_num)

/-- Singleton rows realize the matrix and the marked `{0,1}` collision. -/
def reward : {S : Finset Player // S.Nonempty} → Payoff Player := fun S who =>
  if S.1.card = 1 then
    1 + ∑ owner ∈ S.1, singletonMatrix who owner
  else if S.1 = ({0, 1} : Finset Player) then
    if who = 1 then 1 else 0
  else 0

theorem reward_singleton (owner who : Player) :
    reward (quittingProjectiveSingletonTerminal owner) who =
      1 + singletonMatrix who owner := by
  simp [reward, quittingProjectiveSingletonTerminal]

theorem normalizedSoloMatrix_eq_singletonMatrix :
    normalizedSoloMatrix reward = singletonMatrix := by
  funext who owner
  rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
  unfold quittingProjectiveLCPMatrix
  rw [reward_singleton, reward_singleton]
  simp [singletonMatrix_diagonal]

theorem normalCore_reward_eq_univ :
    normalCore (normalizedSoloMatrix reward) = Finset.univ := by
  rw [normalizedSoloMatrix_eq_singletonMatrix]
  exact normalCore_eq_univ

theorem no_preemption_two_cycle :
    ¬(∃ owner other : Player,
      QuittingSoloPreempts reward 1 owner other ∧
        QuittingSoloPreempts reward 1 other owner) := by
  rintro ⟨owner, other, hedge, hback⟩
  rw [quittingSoloPreempts_iff_normalizedSoloMatrix_le_neg] at hedge hback
  rw [normalizedSoloMatrix_eq_singletonMatrix] at hedge hback
  rcases hedge with ⟨hne, hedge⟩
  rcases hback with ⟨_, hback⟩
  fin_cases owner <;> fin_cases other <;>
    simp_all [singletonMatrix, tournamentSkewMatrix, adjacency] <;> linarith

def cycleVertex : ℕ → Player := fun time =>
  if time % 3 = 0 then 0 else if time % 3 = 1 then 1 else 3

theorem cycleVertex_periodic (time : ℕ) :
    cycleVertex (time + 3) = cycleVertex time := by
  simp [cycleVertex]

theorem cycleVertex_edge (time : ℕ) :
    QuittingSoloPreempts reward 1 (cycleVertex time)
      (cycleVertex (time + 1)) := by
  have hlt : time % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases h : time % 3 <;>
    simp [cycleVertex, Nat.add_mod, h,
      quittingSoloPreempts_iff_normalizedSoloMatrix_le_neg,
      normalizedSoloMatrix_eq_singletonMatrix, singletonMatrix,
      tournamentSkewMatrix, adjacency]

def directedPreemptionCycle : QuittingSoloPreemptionCycle reward 1 where
  period := 3
  period_pos := by norm_num
  vertex := cycleVertex
  vertex_periodic := cycleVertex_periodic
  edge := cycleVertex_edge

theorem directed_preemption_cycle :
    Nonempty (QuittingSoloPreemptionCycle reward 1) :=
  ⟨directedPreemptionCycle⟩

def collision : QuittingImmediateSingletonCollision reward 1 where
  owner := 0
  collider := 1
  collider_ne_owner := by decide
  owner_solo_floor := by
    change 1 ≤ reward (quittingProjectiveSingletonTerminal 0) 0
    rw [reward_singleton]
    norm_num [singletonMatrix, tournamentSkewMatrix, adjacency]
  collider_gain_floor := by
    change reward (quittingProjectiveSingletonTerminal 0) 1 + 1 ≤
      reward ⟨{0, 1}, by simp⟩ 1
    rw [reward_singleton]
    norm_num [reward, singletonMatrix, tournamentSkewMatrix, adjacency]

theorem collision_is_marked :
    collision.owner = 0 ∧ collision.collider = 1 := by
  simp [collision]

/-! ## The solo-exit preference screen -/

/-- Every player's own solo exit pays it exactly `1`: the tournament skew
matrix has zero diagonal. -/
theorem reward_unitSoloExit : QuittingUnitSoloExit reward := by
  intro who
  show reward ⟨{who}, Finset.singleton_nonempty who⟩ who = 1
  simp [reward, singletonMatrix_diagonal]

/-- No member of a quitting coalition is paid more than `1`.  The entries
above `1` all sit in singleton rows at nonmember coordinates. -/
theorem reward_cappedJointExit : QuittingCappedJointExit reward := by
  refine quittingCappedJointExit_of_solo_of_larger (fun who ↦ ?_)
    (fun quitters who _ hcard ↦ ?_)
  · exact le_of_eq (reward_unitSoloExit who)
  · show (if quitters.1.card = 1 then _ else _) ≤ (1 : ℝ)
    rw [if_neg hcard]
    split
    · split <;> norm_num
    · norm_num

/-- The seed carries no terminal exploitability witness.  The seed's preemption cycle
and marked collision therefore cannot by themselves force one. -/
theorem reward_isEmpty_terminalExploitabilityWitness :
    IsEmpty (QuittingTerminalExploitabilityWitness reward) :=
  isEmpty_quittingTerminalExploitabilityWitness_of_cappedJointExit
    reward_unitSoloExit reward_cappedJointExit

end RegularTournamentFiveSeed
end GameTheory
