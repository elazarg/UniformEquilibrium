/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.LargeBaseStationarySemanticHandoff

/-!
# Stationary paid handoff for a prescribed singleton owner

The compact singleton-base gap and the pointwise stationary handoff compose
for an owner selected before either the gap or the induced Nash point.  The
observer and the induced point remain outputs.  This wrapper makes no
connection to a separately selected fixed-law reset profile.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A terminal exploitability witness supplies a uniform positive gap and a
stationary paid handoff at every induced Nash point for any prescribed owner.

The last conjunct records an actual source selected from the nonempty induced
Nash carrier.  It does not identify that source with any independently
constructed semantic-law target. -/
theorem QuittingTerminalExploitabilityWitness.exists_prescribedOwner_stationaryHandoff
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward) (owner : ι) :
    ∃ delta : ℝ, 0 < delta ∧
      (∀ point ∈ quittingPersistentBaseNashSet reward {owner}
          (Finset.univ.erase owner),
        delta ≤ quittingSingletonBaseOwnerFloorExcess reward owner
            (quittingPersistentBaseRoot {owner} (Finset.univ.erase owner)
              point) ∧
          Nonempty (QuittingSingletonBaseStationaryHandoff reward owner
            (Finset.univ.erase owner) point delta witness.terminalGap)) ∧
      ∃ point ∈ quittingPersistentBaseNashSet reward {owner}
          (Finset.univ.erase owner),
        Nonempty (QuittingSingletonBaseStationaryHandoff reward owner
          (Finset.univ.erase owner) point delta witness.terminalGap) := by
  obtain ⟨delta, hdeltaPos, hdelta⟩ :=
    witness.exists_pos_ownerFloorExcess_gap owner
      (Finset.univ.erase owner) rfl
  have hpointwise : ∀ point ∈ quittingPersistentBaseNashSet reward {owner}
      (Finset.univ.erase owner),
      delta ≤ quittingSingletonBaseOwnerFloorExcess reward owner
          (quittingPersistentBaseRoot {owner} (Finset.univ.erase owner)
            point) ∧
        Nonempty (QuittingSingletonBaseStationaryHandoff reward owner
          (Finset.univ.erase owner) point delta witness.terminalGap) := by
    intro point hpoint
    have hlower := hdelta point hpoint
    exact ⟨hlower, exists_singletonBaseStationaryHandoff reward owner
      (Finset.univ.erase owner) rfl point hpoint witness hdeltaPos hlower⟩
  obtain ⟨point, hpoint⟩ := quittingPersistentBaseNashSet_nonempty reward
    {owner} (Finset.univ.erase owner)
  exact ⟨delta, hdeltaPos, hpointwise, point, hpoint,
    (hpointwise point hpoint).2⟩

end GameTheory
