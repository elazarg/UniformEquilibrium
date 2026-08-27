/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.StaticStrategicOrientation
import UniformEquilibrium.Quitting.Classification.TerminalExploitabilityToggles

/-!
# Universal static atomic-toggle handoff

A terminal exploitability witness already forces one strict singleton
insertion and an unstable pure joined row.  Thus the table-level atomic
handoff is available before any stopping-law or concentrated packet is
selected.  The result carries no profile, date, tail, minimum, or packet
provenance.
-/

noncomputable section

namespace GameTheory

variable {iota : Type} [Fintype iota] [DecidableEq iota]

namespace QuittingTerminalExploitabilityWitness

/-- A strict joiner of a singleton supplies a literal atomic-toggle handoff,
with the pure pair row as its unstable atom. -/
theorem hasStaticAtomicToggleHandoff_of_strictSingletonJoiner
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (owner joiner : iota) (hne : joiner ≠ owner)
    (hstrict : quittingSoloReward reward owner joiner <
      quittingSingletonCollisionReward reward owner joiner) :
    HasQuittingStaticAtomicToggleHandoff reward := by
  classical
  let quitters : Finset iota := {owner}
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

/-- Every terminal exploitability witness already forces a table-level
atomic-toggle handoff.  No selected profile or packet is used or retained. -/
theorem hasStaticAtomicToggleHandoff
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (witness : QuittingTerminalExploitabilityWitness reward) :
    HasQuittingStaticAtomicToggleHandoff reward := by
  obtain ⟨owner, howner⟩ := witness.exists_terminalGap_le_soloReward
  have hownerStrict : -witness.terminalGap <
      quittingSoloReward reward owner owner := by
    linarith [witness.terminalGap_pos]
  obtain ⟨joiner, hjoinerNe, hjoin⟩ :=
    witness.exists_collision_gain hownerStrict
  have hstrict : quittingSoloReward reward owner joiner <
      quittingSingletonCollisionReward reward owner joiner := by
    linarith [witness.terminalGap_pos]
  exact witness.hasStaticAtomicToggleHandoff_of_strictSingletonJoiner
    owner joiner hjoinerNe hstrict

end QuittingTerminalExploitabilityWitness

end GameTheory
