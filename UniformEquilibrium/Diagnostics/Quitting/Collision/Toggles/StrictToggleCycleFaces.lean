/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.ReachableSimpleCycle

/-!
# Persistent, free, and outside faces of a strict-toggle cycle

This file extracts the relabeling-invariant face partition from the actual
coalition vertices carried by a reachable simple strict-toggle cycle.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingTerminalExploitabilityWitness.ReachableStrictToggleSimpleCycle

variable {witness : QuittingTerminalExploitabilityWitness reward}
variable {seed : Finset ι}

/-- The actual terminal coalitions occurring as sources around the cycle. -/
def coalitions (cycle : witness.ReachableStrictToggleSimpleCycle seed) :
    List (Finset ι) :=
  cycle.cycle.edges.map fun edge => edge.1

/-- Players contained in every cycle coalition. -/
def persistentBase (cycle : witness.ReachableStrictToggleSimpleCycle seed) :
    Finset ι :=
  Finset.univ.filter fun who => ∀ coalition ∈ cycle.coalitions, who ∈ coalition

/-- Players contained in at least one cycle coalition. -/
def usedPlayers (cycle : witness.ReachableStrictToggleSimpleCycle seed) :
    Finset ι :=
  Finset.univ.filter fun who => ∃ coalition ∈ cycle.coalitions, who ∈ coalition

/-- Players whose membership changes along the cycle. -/
def freePlayers (cycle : witness.ReachableStrictToggleSimpleCycle seed) :
    Finset ι :=
  cycle.usedPlayers \ cycle.persistentBase

/-- Players absent from every cycle coalition. -/
def outsidePlayers (cycle : witness.ReachableStrictToggleSimpleCycle seed) :
    Finset ι :=
  Finset.univ \ (cycle.persistentBase ∪ cycle.freePlayers)

@[simp] theorem coalitions_length
    (cycle : witness.ReachableStrictToggleSimpleCycle seed) :
    cycle.coalitions.length = cycle.cycle.length := by
  simp [coalitions]

theorem coalitions_nonempty
    (cycle : witness.ReachableStrictToggleSimpleCycle seed) :
    cycle.coalitions ≠ [] := by
  intro hempty
  have hzero : cycle.coalitions.length = 0 := by simp [hempty]
  rw [cycle.coalitions_length] at hzero
  have hfour := cycle.four_le_length
  exact (by omega : False)

theorem persistentBase_subset_usedPlayers
    (cycle : witness.ReachableStrictToggleSimpleCycle seed) :
    cycle.persistentBase ⊆ cycle.usedPlayers := by
  intro who hbase
  obtain ⟨coalition, hcoalition⟩ :=
    List.exists_mem_of_ne_nil cycle.coalitions cycle.coalitions_nonempty
  have hall : ∀ candidate ∈ cycle.coalitions, who ∈ candidate := by
    simpa [persistentBase] using hbase
  simp only [usedPlayers, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨coalition, hcoalition, hall coalition hcoalition⟩

/-- The persistent and free faces are disjoint. -/
theorem disjoint_persistentBase_freePlayers
    (cycle : witness.ReachableStrictToggleSimpleCycle seed) :
    Disjoint cycle.persistentBase cycle.freePlayers := by
  exact Finset.disjoint_sdiff

/-- Persistent plus free players are exactly the players used by the cycle. -/
theorem persistentBase_union_freePlayers
    (cycle : witness.ReachableStrictToggleSimpleCycle seed) :
    cycle.persistentBase ∪ cycle.freePlayers = cycle.usedPlayers := by
  exact Finset.union_sdiff_of_subset cycle.persistentBase_subset_usedPlayers

/-- The outside face is the complement of the used-player face. -/
theorem outsidePlayers_eq_usedPlayers_compl
    (cycle : witness.ReachableStrictToggleSimpleCycle seed) :
    cycle.outsidePlayers = cycle.usedPlayersᶜ := by
  rw [outsidePlayers, cycle.persistentBase_union_freePlayers]
  rfl

/-- The three faces partition the ambient finite player set. -/
theorem persistent_free_outside_partition
    (cycle : witness.ReachableStrictToggleSimpleCycle seed) :
    cycle.persistentBase ∪ cycle.freePlayers ∪ cycle.outsidePlayers = Finset.univ := by
  rw [cycle.persistentBase_union_freePlayers,
    cycle.outsidePlayers_eq_usedPlayers_compl]
  exact Finset.union_compl cycle.usedPlayers

private theorem strictTogglePlayer_mem_freePlayers_of_consecutive
    (cycle : witness.ReachableStrictToggleSimpleCycle seed)
    (source target : Finset ι)
    (hsource : source ∈ cycle.coalitions)
    (htarget : target ∈ cycle.coalitions)
    (hnext : witness.strictToggleSuccessor source = target) :
    witness.strictTogglePlayer source ∈ cycle.freePlayers := by
  let mover := witness.strictTogglePlayer source
  have hused : mover ∈ cycle.usedPlayers := by
    simp only [usedPlayers, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hmover : mover ∈ source
    · exact ⟨source, hsource, hmover⟩
    · refine ⟨target, htarget, ?_⟩
      rw [← hnext, strictToggleSuccessor,
        quittingToggleCoalition_of_notMem hmover]
      exact Finset.mem_insert_self mover source
  have hnotPersistent : mover ∉ cycle.persistentBase := by
    intro hpersistent
    have hall : ∀ coalition ∈ cycle.coalitions, mover ∈ coalition := by
      simpa [persistentBase] using hpersistent
    by_cases hmover : mover ∈ source
    · have htargetMover := hall target htarget
      rw [← hnext, strictToggleSuccessor,
        quittingToggleCoalition_of_mem hmover] at htargetMover
      simp at htargetMover
    · exact hmover (hall source hsource)
  exact Finset.mem_sdiff.mpr ⟨hused, hnotPersistent⟩

omit [Fintype ι] in
private theorem quittingToggleCoalition_twice
    (coalition : Finset ι) (who : ι) :
    quittingToggleCoalition (quittingToggleCoalition coalition who) who = coalition := by
  by_cases hwho : who ∈ coalition
  · rw [quittingToggleCoalition_of_mem hwho]
    have herase : who ∉ coalition.erase who := by simp
    rw [quittingToggleCoalition_of_notMem herase]
    exact Finset.insert_erase hwho
  · rw [quittingToggleCoalition_of_notMem hwho]
    rw [quittingToggleCoalition_of_mem (Finset.mem_insert_self who coalition)]
    exact Finset.erase_insert hwho

/-- A simple strict-toggle cycle has at least two genuinely changing player
labels.  Otherwise its first two edges toggle the same sole free label and
the selected successor returns in two steps, contradicting strictness. -/
theorem two_le_card_freePlayers
    (cycle : witness.ReachableStrictToggleSimpleCycle seed) :
    2 ≤ cycle.freePlayers.card := by
  have hlength : 3 ≤ cycle.cycle.edges.length := by
    rw [cycle.cycle.edges_length]
    exact cycle.four_le_length.trans' (by omega)
  obtain ⟨first, second, third, rest, hedges⟩ :
      ∃ first second third rest,
        cycle.cycle.edges = first :: second :: third :: rest := by
    cases hedge : cycle.cycle.edges with
    | nil => simp [hedge] at hlength
    | cons first tail =>
        cases htail : tail with
        | nil => simp [hedge, htail] at hlength
        | cons second tail' =>
            cases htail' : tail' with
            | nil => simp [hedge, htail, htail'] at hlength
            | cons third rest => exact ⟨first, second, third, rest, rfl⟩
  have hchain := cycle.cycle.edges_isChain
  have hfirstNext : witness.strictToggleReachableNext seed first = second := by
    change (witness.strictToggleReachableGraph seed).target first =
      (witness.strictToggleReachableGraph seed).source second
    have hpair :
        (witness.strictToggleReachableGraph seed).target first =
            (witness.strictToggleReachableGraph seed).source second ∧
          (witness.strictToggleReachableGraph seed).target second =
            (witness.strictToggleReachableGraph seed).source third ∧
          List.IsChain
            (fun left right =>
              (witness.strictToggleReachableGraph seed).target left =
                (witness.strictToggleReachableGraph seed).source right)
            (third :: rest) := by
      simpa [hedges] using hchain
    exact hpair.1
  have hsecondNext : witness.strictToggleReachableNext seed second = third := by
    change (witness.strictToggleReachableGraph seed).target second =
      (witness.strictToggleReachableGraph seed).source third
    have hpair :
        (witness.strictToggleReachableGraph seed).target first =
            (witness.strictToggleReachableGraph seed).source second ∧
          (witness.strictToggleReachableGraph seed).target second =
            (witness.strictToggleReachableGraph seed).source third ∧
          List.IsChain
            (fun left right =>
              (witness.strictToggleReachableGraph seed).target left =
                (witness.strictToggleReachableGraph seed).source right)
            (third :: rest) := by
      simpa [hedges] using hchain
    exact hpair.2.1
  have hfirstMem : first.1 ∈ cycle.coalitions := by simp [coalitions, hedges]
  have hsecondMem : second.1 ∈ cycle.coalitions := by simp [coalitions, hedges]
  have hthirdMem : third.1 ∈ cycle.coalitions := by simp [coalitions, hedges]
  have hmoverFirst := strictTogglePlayer_mem_freePlayers_of_consecutive
    cycle first.1 second.1 hfirstMem hsecondMem (congrArg Subtype.val hfirstNext)
  have hmoverSecond := strictTogglePlayer_mem_freePlayers_of_consecutive
    cycle second.1 third.1 hsecondMem hthirdMem (congrArg Subtype.val hsecondNext)
  by_contra hcard
  have hsame : witness.strictTogglePlayer first.1 =
      witness.strictTogglePlayer second.1 := by
    exact Finset.card_le_one.mp (by omega) _ hmoverFirst _ hmoverSecond
  have hplayerOnNext :
      witness.strictTogglePlayer (witness.strictToggleSuccessor first.1) =
        witness.strictTogglePlayer first.1 := by
    have hfirstVal : witness.strictToggleSuccessor first.1 = second.1 :=
      congrArg (fun state => state.1) hfirstNext
    rw [hfirstVal]
    exact hsame.symm
  have hreturn : witness.strictToggleSuccessor
      (witness.strictToggleSuccessor first.1) = first.1 := by
    change quittingToggleCoalition (witness.strictToggleSuccessor first.1)
      (witness.strictTogglePlayer (witness.strictToggleSuccessor first.1)) = first.1
    rw [hplayerOnNext]
    unfold strictToggleSuccessor
    exact quittingToggleCoalition_twice first.1
      (witness.strictTogglePlayer first.1)
  exact witness.strictToggleSuccessor_twice_ne first.1 hreturn

/-- The persistent face has exactly the three semantic compiler shapes:
empty, a named singleton, or at least two sure base quitters. -/
theorem persistentBase_shape
    (cycle : witness.ReachableStrictToggleSimpleCycle seed) :
    cycle.persistentBase = ∅ ∨
      (∃ owner, cycle.persistentBase = {owner}) ∨
      2 ≤ cycle.persistentBase.card := by
  rcases Nat.eq_zero_or_pos cycle.persistentBase.card with hzero | hpos
  · exact Or.inl (Finset.card_eq_zero.mp hzero)
  · by_cases hone : cycle.persistentBase.card = 1
    · obtain ⟨owner, howner⟩ := Finset.card_eq_one.mp hone
      exact Or.inr (Or.inl ⟨owner, howner⟩)
    · exact Or.inr (Or.inr (by omega))

end QuittingTerminalExploitabilityWitness.ReachableStrictToggleSimpleCycle

end GameTheory
