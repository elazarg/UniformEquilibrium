/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import UniformEquilibrium.Quitting.Classification.BlockDeletionInequality
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPairedFamily

/-!
# Exact row slacks of the paired capped-clock fixture

This module evaluates the capped-clock reward-row margins and the unweighted
singleton-deletion extrema of the explicit paired-family table.
-/

noncomputable section

namespace GameTheory
namespace CappedClockPairedFixtureSlacks

open scoped BigOperators
open CappedClockPairedFamily

def childZero : Child := ⟨0, by decide⟩

def childOne : Child := ⟨1, by decide⟩

/-- The seven nonempty child coalitions in the packet's displayed order
`0, 1, 01, 2, 02, 12, 012`. -/
def childCoalition : Fin 7 → {A : Finset Child // A.Nonempty}
  | 0 => ⟨{childZero}, by simp⟩
  | 1 => ⟨{childOne}, by simp⟩
  | 2 => ⟨{childZero, childOne}, by simp⟩
  | 3 => ⟨{childTwo}, by simp⟩
  | 4 => ⟨{childZero, childTwo}, by simp⟩
  | 5 => ⟨{childOne, childTwo}, by simp⟩
  | 6 => ⟨{childZero, childOne, childTwo}, by simp⟩

/-- Right side minus left side of the joint-Never certificate row. -/
def neverSlack : ℝ :=
  (∑ child, weight child *
    parentReward exampleReward
      (quittingSingletonTerminal (some child)) (some child)) -
  parentReward exampleReward (quittingSingletonTerminal none) none

/-- Right side minus left side of a future-absorption row. -/
def futureSlack (A : {A : Finset Child // A.Nonempty}) : ℝ :=
  2 * (1 - parentReward exampleReward
      ⟨cappedClockChildCoalition A.1,
        cappedClockChildCoalition_nonempty A.2⟩ (some childTwo)) -
    (1 - parentReward exampleReward
      ⟨cappedClockChildCoalition A.1,
        cappedClockChildCoalition_nonempty A.2⟩ none)

/-- Right side minus left side of a joining row. -/
def joinSlack (A : {A : Finset Child // A.Nonempty}) : ℝ :=
  2 * (parentReward exampleReward
      ⟨cappedClockChildCoalition (insert childTwo A.1),
        cappedClockChildCoalition_nonempty
          (Finset.insert_nonempty childTwo A.1)⟩ (some childTwo) -
      parentReward exampleReward
        ⟨cappedClockChildCoalition A.1,
          cappedClockChildCoalition_nonempty A.2⟩ (some childTwo)) -
    (parentReward exampleReward
        ⟨cappedClockJoinedCoalition A.1,
          cappedClockJoinedCoalition_nonempty A.1⟩ none -
      parentReward exampleReward
        ⟨cappedClockChildCoalition A.1,
          cappedClockChildCoalition_nonempty A.2⟩ none)

theorem neverSlack_eq_one : neverSlack = 1 := by
  have hsingleton (owner : Option Child) :
      parentReward exampleReward (quittingSingletonTerminal owner) owner = 1 :=
    (exampleReward_conditions.singleton_rows owner owner).trans
      (boundarySingletonSource_self owner)
  have hsum : ∑ child, weight child = 2 := by
    apply Finset.sum_eq_single childTwo
    · intro child _ hne
      simp [weight, hne]
    · intro hnot
      exact (hnot (Finset.mem_univ childTwo)).elim
  unfold neverSlack
  simp_rw [hsingleton]
  simp only [mul_one]
  rw [hsum]
  norm_num

/-- `futureSlack` is exactly the canonical weighted certificate margin, not
merely its already-simplified `2e₂` formula. -/
theorem futureSlack_eq_certificateMargin
    (A : {A : Finset Child // A.Nonempty}) :
    futureSlack A =
      (∑ child, weight child *
        (parentReward exampleReward
            (quittingSingletonTerminal (some child)) (some child) -
          parentReward exampleReward
            ⟨cappedClockChildCoalition A.1,
              cappedClockChildCoalition_nonempty A.2⟩ (some child))) -
        (parentReward exampleReward
            (quittingSingletonTerminal none) none -
          parentReward exampleReward
            ⟨cappedClockChildCoalition A.1,
              cappedClockChildCoalition_nonempty A.2⟩ none) := by
  have hsingleton (owner : Option Child) :
      parentReward exampleReward (quittingSingletonTerminal owner) owner = 1 :=
    (exampleReward_conditions.singleton_rows owner owner).trans
      (boundarySingletonSource_self owner)
  simp_rw [hsingleton]
  simp [futureSlack, weight]

/-- `joinSlack` is exactly the canonical weighted joining-row margin. -/
theorem joinSlack_eq_certificateMargin
    (A : {A : Finset Child // A.Nonempty}) :
    joinSlack A =
      (∑ child, weight child *
        (parentReward exampleReward
            ⟨cappedClockChildCoalition (insert child A.1),
              cappedClockChildCoalition_nonempty
                (Finset.insert_nonempty child A.1)⟩ (some child) -
          parentReward exampleReward
            ⟨cappedClockChildCoalition A.1,
              cappedClockChildCoalition_nonempty A.2⟩ (some child))) -
        (parentReward exampleReward
            ⟨cappedClockJoinedCoalition A.1,
              cappedClockJoinedCoalition_nonempty A.1⟩ none -
          parentReward exampleReward
            ⟨cappedClockChildCoalition A.1,
              cappedClockChildCoalition_nonempty A.2⟩ none) := by
  simp [joinSlack, weight]

theorem futureSlack_childCoalition (index : Fin 7) :
    futureSlack (childCoalition index) =
      ![(1 : ℝ), 1, 1, 3, 1, 1, 1] index := by
  fin_cases index <;>
    norm_num [futureSlack, childCoalition, childZero, childOne, childTwo,
      exampleReward]

theorem joinSlack_childCoalition (index : Fin 7) :
    joinSlack (childCoalition index) =
      ![(2 : ℝ), 2, 1, 2, 3, 4, 1] index := by
  fin_cases index <;>
    norm_num [joinSlack, childCoalition, childZero, childOne, childTwo,
      exampleReward]

/-- Every singleton-deletion gate sees own singleton value one. -/
theorem singleton_self (owner : Player) :
    exampleReward (quittingSingletonTerminal owner) owner = 1 :=
  singleton_self_eq_one exampleReward_conditions owner

/-- Every singleton deletion has unweighted survivor continue floor zero. -/
theorem singleton_continueFloor (owner : Player) :
    quittingBlockContinueFloor exampleReward {owner} owner = 0 := by
  apply le_antisymm
  · exact quittingBlockContinueFloor_nonpos exampleReward {owner} owner
  · apply le_quittingBlockContinueFloor
    · norm_num
    · intro S hS hdisjoint
      fin_cases owner <;> fin_cases S <;>
        simp_all [exampleReward, Finset.disjoint_left]

/-- Every singleton deletion has unweighted survivor join cap two. -/
theorem singleton_joinCap (owner : Player) :
    quittingBlockJoinCap exampleReward {owner} owner = 2 := by
  apply le_antisymm
  · apply quittingBlockJoinCap_le
    · norm_num
    · intro S hS hdisjoint
      fin_cases owner <;> fin_cases S <;>
        simp_all [exampleReward, Finset.disjoint_left] <;> norm_num
  · fin_cases owner
    · exact (sub_le_quittingBlockJoinCap exampleReward {0} 0
        {2} (by simp) (by decide)).trans' (by norm_num [exampleReward])
    · exact (sub_le_quittingBlockJoinCap exampleReward {1} 1
        {2} (by simp) (by decide)).trans' (by norm_num [exampleReward])
    · exact (sub_le_quittingBlockJoinCap exampleReward {2} 2
        {0} (by simp) (by decide)).trans' (by norm_num [exampleReward])
    · exact (sub_le_quittingBlockJoinCap exampleReward {3} 3
        {0} (by simp) (by decide)).trans' (by norm_num [exampleReward])

end CappedClockPairedFixtureSlacks
end GameTheory
