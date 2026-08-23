/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.StaticStrategicOrientation
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.OffDiagonal.StaticOrientationDispatch
import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Punishment.InstantPunishment

/-!
# Static compression of singleton strategic orientations

The static singleton dispatcher reduces to an atomic coalition-toggle handoff
or exact player deletion.  The positive-punishment arm closes because the
instant-punishment construction would otherwise supply a uniform-equilibrium
payoff.

The stopping-law corollary consumes only the static field of its orientation
packet.  Neither result assumes or constructs a chronological realization of
the atomic handoff.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingTerminalExploitabilityWitness

/-- A strict joiner of a singleton supplies a literal atomic-toggle handoff,
with the pure pair row as its unstable atom. -/
theorem hasStaticAtomicToggleHandoff_of_strictSingletonJoiner
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (owner joiner : ι) (hne : joiner ≠ owner)
    (hstrict : quittingSoloReward reward owner joiner <
      quittingSingletonCollisionReward reward owner joiner) :
    HasQuittingStaticAtomicToggleHandoff reward := by
  classical
  let quitters : Finset ι := {owner}
  have hquitters : quitters.Nonempty := by
    simp [quitters]
  have hjoiner : joiner ∉ quitters := by
    simp [quitters, hne]
  have htoggle : reward ⟨quitters, hquitters⟩ joiner <
      reward
        ⟨insert joiner quitters,
          Finset.insert_nonempty joiner quitters⟩ joiner := by
    simpa [quitters, quittingSoloReward,
      quittingSingletonCollisionReward, Finset.pair_comm] using hstrict
  exact ⟨joiner, quitters, hquitters, hjoiner, htoggle,
    exists_outsider_atomicDeviation_of_strict_ownerToggle reward
      witness.terminalGap_pos witness.terminalExploitability joiner quitters
      hquitters hjoiner htoggle⟩

/-- The three-way static singleton dispatcher reduces exactly to atomic
instability or player deletion.

Full behavioral best-response semantics enter through
`isUniformEquilibriumPayoff_soloReward_of_instantPunishment`. -/
theorem singletonStaticStrategicDispatch_compress
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward) (owner : ι)
    (hdispatch : HasQuittingSingletonStaticStrategicDispatch reward owner
      witness.terminalGap) :
    HasQuittingStaticAtomicToggleHandoff reward ∨
      HasQuittingExactPlayerDeletionAtGap reward owner witness.terminalGap := by
  classical
  rcases hdispatch with hatomic | hpunishment | hdeletion
  · exact Or.inl hatomic
  · have hupper := quittingPunishmentValue_le_max_solo reward owner
    rw [quittingSetReward_singleton_eq_soloReward] at hupper
    have hsoloPos : 0 < quittingSoloReward reward owner owner := by
      by_contra hnot
      have hsoloNonpos : quittingSoloReward reward owner owner ≤ 0 :=
        le_of_not_gt hnot
      rw [max_eq_right hsoloNonpos] at hupper
      linarith
    have hIR : IsQuittingInstantPunishmentIR reward owner := by
      unfold IsQuittingInstantPunishmentIR
      rwa [max_eq_left hsoloPos.le] at hupper
    have hnotNoJoin : ¬ IsQuittingInstantNoJoin reward owner := by
      intro hnoJoin
      have hUE := isUniformEquilibriumPayoff_soloReward_of_instantPunishment
        reward owner hIR hnoJoin
      exact witness.not_exists_uniformEquilibriumPayoff
        ⟨quittingSoloReward reward owner, hUE⟩
    unfold IsQuittingInstantNoJoin at hnotNoJoin
    push Not at hnotNoJoin
    obtain ⟨joiner, hjoinerNe, hstrict⟩ := hnotNoJoin
    exact Or.inl
      (witness.hasStaticAtomicToggleHandoff_of_strictSingletonJoiner
        owner joiner hjoinerNe hstrict)
  · exact Or.inr hdeletion

/-- The exact top-level stopping-law singleton orientation reduces to atomic
instability or exact deletion.  Terminal membership and singleton cardinality
are packet provenance; the static compression does not use them. -/
theorem stoppingLawSingletonStrategicOrientation_compress
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (horientation :
      HasQuittingStoppingLawSingletonStrategicOrientation
        (witness := witness) packet) :
    HasQuittingStaticAtomicToggleHandoff reward ∨
      HasQuittingExactPlayerDeletionAtGap reward packet.observer
        witness.terminalGap := by
  obtain ⟨_observerMem, _singleton, hstatic⟩ := horientation
  exact witness.singletonStaticStrategicDispatch_compress
    packet.observer hstatic

end QuittingTerminalExploitabilityWitness

end GameTheory
