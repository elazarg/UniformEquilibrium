/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.OffDiagonal.StaticOrientationDispatch
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.UniversalStaticAtomicToggleHandoff

/-!
# Static compression of singleton strategic orientations

The terminal witness already supplies a table-level atomic coalition-toggle
handoff.  Consequently the existing singleton compression surfaces delegate
to that stronger universal result without using their packet inputs.

The stopping-law corollary consumes only the static field of its orientation
packet.  Neither result assumes or constructs a chronological realization of
the atomic handoff.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingTerminalExploitabilityWitness

/-- The three-way static singleton dispatcher reduces exactly to atomic
instability or player deletion.  The stronger universal handoff always
selects the first alternative; the supplied dispatcher is retained only for
the established theorem surface. -/
theorem singletonStaticStrategicDispatch_compress
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward) (owner : ι)
    (hdispatch : HasQuittingSingletonStaticStrategicDispatch reward owner
      witness.terminalGap) :
    HasQuittingStaticAtomicToggleHandoff reward ∨
      HasQuittingExactPlayerDeletionAtGap reward owner witness.terminalGap := by
  rcases hdispatch with _ | _ | _ <;>
    exact Or.inl witness.hasStaticAtomicToggleHandoff

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
  obtain ⟨_, _, _⟩ := horientation
  exact Or.inl witness.hasStaticAtomicToggleHandoff

end QuittingTerminalExploitabilityWitness

end GameTheory
