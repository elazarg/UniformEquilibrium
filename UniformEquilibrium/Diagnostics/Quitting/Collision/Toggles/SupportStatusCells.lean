/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.PersistentBaseInducedGame
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.StrictToggleCycleFaces
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.SupportStatusEnumeration

/-!
# Exact support-status cells for a binary mixed face

The earlier enumeration counts three labels per free player.  This module
attaches those labels to their actual simplex equalities and inequalities and
checks that the mixed polytope, hence every induced Nash set, is covered by
the resulting finite family.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [DecidableEq ι]

/-- One coordinate lies in the labelled pure-Continue, pure-Quit, or strictly
mixed support cell. -/
def IsQuittingBinarySupportStatus
    (status : QuittingBinarySupportStatus) (weights : Bool → ℝ) : Prop :=
  if status = 0 then weights true = 0
  else if status = 1 then weights false = 0
  else 0 < weights true ∧ 0 < weights false

/-- The exact product cell attached to one status assignment. -/
def quittingBinarySupportCell (free : Finset ι)
    (status : free → QuittingBinarySupportStatus) :
    Set (mixedPolytope (quittingBinaryForm free).sig) :=
  {point | ∀ who, IsQuittingBinarySupportStatus (status who) (point.1 who)}

/-- A canonical support label for a Boolean simplex coordinate. -/
def quittingBinarySupportStatusOf (weights : Bool → ℝ) :
    QuittingBinarySupportStatus :=
  if weights true = 0 then 0 else if weights false = 0 then 1 else 2

/-- Every Boolean simplex point satisfies its canonical status conditions. -/
theorem isQuittingBinarySupportStatus_statusOf
    (weights : Bool → ℝ) (hweights : weights ∈ stdSimplex ℝ Bool) :
    IsQuittingBinarySupportStatus (quittingBinarySupportStatusOf weights) weights := by
  have hnonneg : ∀ action, 0 ≤ weights action := hweights.1
  by_cases hquit : weights true = 0
  · simp [quittingBinarySupportStatusOf, IsQuittingBinarySupportStatus, hquit]
  · by_cases hcontinue : weights false = 0
    · simp [quittingBinarySupportStatusOf, IsQuittingBinarySupportStatus,
        hquit, hcontinue]
    · have hquitPos : 0 < weights true := lt_of_le_of_ne
        (hnonneg true) (Ne.symm hquit)
      have hcontinuePos : 0 < weights false := lt_of_le_of_ne
        (hnonneg false) (Ne.symm hcontinue)
      simp [quittingBinarySupportStatusOf, IsQuittingBinarySupportStatus,
        hquit, hcontinue, hquitPos, hcontinuePos]

/-- Every mixed point belongs to one of the explicitly enumerated exact
support-status cells. -/
theorem exists_mem_quittingBinarySupportCell
    (free : Finset ι)
    (point : mixedPolytope (quittingBinaryForm free).sig) :
    ∃ status ∈ quittingBinarySupportStatusCells free,
      point ∈ quittingBinarySupportCell free status := by
  let status : free → QuittingBinarySupportStatus := fun who =>
    quittingBinarySupportStatusOf (point.1 who)
  refine ⟨status, mem_quittingBinarySupportStatusCells free status, ?_⟩
  intro who
  exact isQuittingBinarySupportStatus_statusOf (point.1 who)
    (point.2 who (Set.mem_univ who))

/-- In particular, the complete induced Nash carrier is covered by the same
finite family of exact equality/inequality cells. -/
theorem exists_mem_quittingPersistentBaseNash_supportCell
    [Fintype ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι)
    (point : mixedPolytope (quittingBinaryForm free).sig)
    (hpoint : point ∈ quittingPersistentBaseNashSet reward base free) :
    ∃ status ∈ quittingBinarySupportStatusCells free,
      point ∈ quittingPersistentBaseNashSet reward base free ∩
        quittingBinarySupportCell free status := by
  obtain ⟨status, hstatus, hcell⟩ :=
    exists_mem_quittingBinarySupportCell free point
  exact ⟨status, hstatus, hpoint, hcell⟩

namespace QuittingTerminalExploitabilityWitness.ReachableStrictToggleSimpleCycle

variable [Fintype ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {witness : QuittingTerminalExploitabilityWitness reward}
variable {seed : Finset ι}

/-- On a four-player cycle with nonempty persistent base, at most three
players are free. -/
theorem card_freePlayers_le_three
    (cycle : witness.ReachableStrictToggleSimpleCycle seed)
    (hfour : Fintype.card ι = 4) (hbase : cycle.persistentBase.Nonempty) :
    cycle.freePlayers.card ≤ 3 := by
  have hunion : (cycle.persistentBase ∪ cycle.freePlayers).card ≤ 4 := by
    have hle := Finset.card_le_card
      (show cycle.persistentBase ∪ cycle.freePlayers ⊆ Finset.univ from
        Finset.subset_univ _)
    simpa [Finset.card_univ, hfour] using hle
  rw [Finset.card_union_of_disjoint cycle.disjoint_persistentBase_freePlayers] at hunion
  have hbaseCard : 1 ≤ cycle.persistentBase.card :=
    Finset.one_le_card.mpr hbase
  omega

/-- Hence the exact support-status cover of the induced Nash carrier has at
most twenty-seven cells on every nonempty-base four-player cycle. -/
theorem card_supportStatusCells_le_twentySeven
    (cycle : witness.ReachableStrictToggleSimpleCycle seed)
    (hfour : Fintype.card ι = 4) (hbase : cycle.persistentBase.Nonempty) :
    (quittingBinarySupportStatusCells cycle.freePlayers).card ≤ 27 :=
  card_quittingBinarySupportStatusCells_le_twentySeven cycle.freePlayers
    (cycle.card_freePlayers_le_three hfour hbase)

end QuittingTerminalExploitabilityWitness.ReachableStrictToggleSimpleCycle

end GameTheory
