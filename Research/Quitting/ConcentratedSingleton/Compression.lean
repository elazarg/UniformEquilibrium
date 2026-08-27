/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.ConcentratedSingleton.StrategicDispatch
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.StaticStrategicCompression

/-!
# Tentative compression of the concentrated singleton handoff

The terminal witness already supplies a table-level static atomic handoff.
The established concentrated compression theorem therefore delegates to
that universal result while preserving its packet-indexed input surface.

This theorem remains in Research with the rich packet-level dispatch that it
consumes.  The independently useful static compression interface lives in
`StoppingLaw.StaticStrategicCompression`.
-/

noncomputable section

namespace GameTheory

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- **Full concentrated-singleton compression.**  The stronger universal
atomic handoff always selects the first alternative.  The supplied dispatch
is retained only for the established theorem surface. -/
theorem QuittingTerminalExploitabilityWitness.concentratedSingletonStrategicDispatch_compress
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (witness : QuittingTerminalExploitabilityWitness reward)
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {terminal : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ}
    (packet : QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale)
    (other : iota)
    (hdispatch : HasQuittingConcentratedSingletonStrategicDispatch
      witness packet other) :
    HasQuittingStaticAtomicToggleHandoff reward ∨
      HasQuittingExactPlayerDeletionAtGap reward other
        witness.terminalGap := by
  obtain ⟨_, _, _, _⟩ := hdispatch
  exact Or.inl witness.hasStaticAtomicToggleHandoff

end GameTheory
