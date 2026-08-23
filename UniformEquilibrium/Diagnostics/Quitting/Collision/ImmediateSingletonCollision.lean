/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.TerminalExploitabilityToggles
import UniformEquilibrium.Quitting.Classification.ImmediateSingletonCollision

/-!
# Immediate singleton collision in a quitting counterexample

Every quitting terminal exploitability witness selects an owner with solo reward at
least the terminal gap.  The membership-toggle instability at that owner's
singleton exit then selects a distinct collider whose immediate Quit gains at
least the same gap.  The resulting executable row has zero owner debt and the
collider's full positive debt is an actual source-matched legal gain.

This is a necessary geometry for a terminal exploitability witness.  No converse or
uniform-equilibrium conclusion is asserted.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {player : Type} [Fintype player] [DecidableEq player]
variable {reward : {S : Finset player // S.Nonempty} → Payoff player}

namespace QuittingTerminalExploitabilityWitness

/-- Every terminal exploitability witness has a canonical immediate singleton
collision carrying its full terminal gap. -/
theorem exists_immediateSingletonCollision
    (witness : QuittingTerminalExploitabilityWitness reward) :
    Nonempty (QuittingImmediateSingletonCollision reward
      witness.terminalGap) := by
  obtain ⟨owner, howner⟩ := witness.exists_terminalGap_le_soloReward
  have hownerStrict : -witness.terminalGap <
      quittingSoloReward reward owner owner := by
    linarith [witness.terminalGap_pos]
  obtain ⟨collider, hne, hgain⟩ :=
    witness.exists_collision_gain hownerStrict
  exact ⟨{
    owner := owner
    collider := collider
    collider_ne_owner := hne
    owner_solo_floor := howner
    collider_gain_floor := hgain
  }⟩

/-- Every player with positive punishment value owns a full-gap singleton
collision.  The punishment ceiling forces the positive solo payoff required
by the collision-gain theorem. -/
theorem exists_collision_gain_of_punishmentValue_pos
    (witness : QuittingTerminalExploitabilityWitness reward) {owner : player}
    (howner : 0 < quittingPunishmentValue reward owner) :
    ∃ other, other ≠ owner ∧
      quittingSoloReward reward owner other + witness.terminalGap ≤
        quittingSingletonCollisionReward reward owner other := by
  have hceil := quittingPunishmentValue_le_max_solo reward owner
  have hsolo : 0 < quittingSoloReward reward owner owner := by
    rcases le_total (quittingSetReward reward ({owner} : Finset player) owner) 0
        with hnonpos | hnonneg
    · rw [max_eq_right hnonpos] at hceil
      linarith
    · rw [max_eq_left hnonneg] at hceil
      rw [← quittingSetReward_singleton_eq_soloReward]
      linarith
  exact witness.exists_collision_gain (by linarith [witness.terminalGap_pos])

end QuittingTerminalExploitabilityWitness

end GameTheory
