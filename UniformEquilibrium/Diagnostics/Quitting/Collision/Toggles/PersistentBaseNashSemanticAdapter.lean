/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.PersistentBaseInducedGame
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.PersistentBaseSemanticDispatch
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.StrictToggleCycleFaces

/-!
# Induced-Nash adapter for persistent strict-toggle faces

An exact Nash point of the induced free-player game already supplies the
free-coordinate endpoint inequalities required by the persistent-base
semantic compiler.  Thus only the persistent leave and outsider join signs
remain to be checked on the extended quitting root.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- An induced mixed Nash point, together with the two remaining face sign
screens, constructs the existing all-behavior persistent-base certificate. -/
theorem nonempty_quittingPersistentBaseCertificate_of_inducedNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) (hdisjoint : Disjoint base free)
    (hbase : 2 ≤ base.card)
    (point : mixedPolytope (quittingBinaryForm free).sig)
    (hpoint : point ∈ quittingPersistentBaseNashSet reward base free)
    (hleave : ∀ who ∈ base,
      0 ≤ quittingRootEndpointDifference reward 0
        (quittingPersistentBaseRoot base free point) who)
    (hjoin : ∀ who ∉ base ∪ free,
      quittingRootEndpointDifference reward 0
        (quittingPersistentBaseRoot base free point) who ≤ 0) :
    Nonempty (QuittingPersistentBaseCertificate reward base free
      (quittingPersistentBaseRoot base free point)) := by
  let root := quittingPersistentBaseRoot base free point
  have hbaseNonempty : base.Nonempty := by
    exact (Finset.one_lt_card_iff_nontrivial.mp
      (lt_of_lt_of_le Nat.one_lt_two hbase)).nonempty
  refine ⟨{
    disjoint := hdisjoint
    two_le_base_card := hbase
    base_quits := fun who hwho ↦ by
      exact quittingPersistentBaseRoot_apply_of_mem_base
        base free point hwho
    outsiders_continue := fun who hwho ↦ by
      exact quittingPersistentBaseRoot_apply_of_outside
        base free point hwho
    free_nash := ?_
    base_leave := hleave
    outsider_join := hjoin }⟩
  intro who hwho
  obtain ⟨hquit, hcontinue⟩ :=
    quittingPersistentBaseRoot_free_purePayoff_le reward base free
      hbaseNonempty hdisjoint point hpoint who hwho
  have hquitDifference := quittingRootQuitPayoff_sub_successorPayoff
    reward 0 root who
  have hcontinueDifference := quittingRootContinuePayoff_sub_successorPayoff
    reward 0 root who
  change (root who false).toReal *
        quittingRootEndpointDifference reward 0 root who ≤ 0 ∧
      0 ≤ (root who true).toReal *
        quittingRootEndpointDifference reward 0 root who
  constructor
  · linarith
  · linarith

/-- The accepted induced-Nash face directly yields a named uniform payoff;
no stationary-only deviation restriction remains. -/
theorem exists_uniformPayoff_of_persistentBase_inducedNash_signs
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base free : Finset ι) (hdisjoint : Disjoint base free)
    (hbase : 2 ≤ base.card)
    (haccepted : ∃ point ∈ quittingPersistentBaseNashSet reward base free,
      (∀ who ∈ base,
        0 ≤ quittingRootEndpointDifference reward 0
          (quittingPersistentBaseRoot base free point) who) ∧
      ∀ who ∉ base ∪ free,
        quittingRootEndpointDifference reward 0
          (quittingPersistentBaseRoot base free point) who ≤ 0) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨point, hpoint, hleave, hjoin⟩ := haccepted
  obtain ⟨certificate⟩ :=
    nonempty_quittingPersistentBaseCertificate_of_inducedNash
      reward base free hdisjoint hbase point hpoint hleave hjoin
  exact ⟨fun player ↦ quittingTerminalPayoff reward
      (quittingStationaryProfile reward
        (quittingPersistentBaseRoot base free point)) player,
    certificate.isUniformEquilibriumPayoff⟩

namespace QuittingTerminalExploitabilityWitness.ReachableStrictToggleSimpleCycle

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {witness : QuittingTerminalExploitabilityWitness reward}
variable {seed : Finset ι}

/-- On the persistent face of an actual reachable strict-toggle cycle, an
accepted induced Nash point closes through the all-behavior compiler.  The
remaining hypotheses are exactly the leave signs of persistent players and
the join signs of players outside the cycle. -/
theorem exists_uniformPayoff_of_inducedNash_signs
    (cycle : witness.ReachableStrictToggleSimpleCycle seed)
    (hbase : 2 ≤ cycle.persistentBase.card)
    (haccepted : ∃ point ∈ quittingPersistentBaseNashSet reward
        cycle.persistentBase cycle.freePlayers,
      (∀ who ∈ cycle.persistentBase,
        0 ≤ quittingRootEndpointDifference reward 0
          (quittingPersistentBaseRoot cycle.persistentBase
            cycle.freePlayers point) who) ∧
      ∀ who ∈ cycle.outsidePlayers,
        quittingRootEndpointDifference reward 0
          (quittingPersistentBaseRoot cycle.persistentBase
            cycle.freePlayers point) who ≤ 0) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply exists_uniformPayoff_of_persistentBase_inducedNash_signs
    reward cycle.persistentBase cycle.freePlayers
    cycle.disjoint_persistentBase_freePlayers hbase
  obtain ⟨point, hpoint, hleave, hjoin⟩ := haccepted
  refine ⟨point, hpoint, hleave, ?_⟩
  intro who houtside
  apply hjoin who
  simpa [outsidePlayers] using houtside

end QuittingTerminalExploitabilityWitness.ReachableStrictToggleSimpleCycle

end GameTheory
