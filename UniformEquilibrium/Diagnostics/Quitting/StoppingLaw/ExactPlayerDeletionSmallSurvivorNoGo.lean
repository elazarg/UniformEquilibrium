/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.StaticStrategicOrientation
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSmallSurvivorDeletion

/-!
# Exact player deletion cannot retain a positive gap with at most three survivors

A literal deleted quitting game on at most three players has a
uniform-equilibrium payoff, so it cannot retain any strictly positive terminal
exploitability gap.  The Fin4 specialization removes exact player deletion as
a possible positive-gap certificate.

These are statements entirely about the deleted reward table.  They do not
lift a deleted-game equilibrium, assert that deletion is strategically
harmless, or consume any alternative atlas output.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Exact deletion at a strictly positive gap is impossible whenever the
literal deleted player type has cardinality at most three. -/
theorem not_hasQuittingExactPlayerDeletionAtGap_of_deleted_card_le_three
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hcard : Fintype.card (QuittingDeletedPlayer owner) ≤ 3)
    {gap : ℝ} (hgap : 0 < gap) :
    ¬ HasQuittingExactPlayerDeletionAtGap reward owner gap := by
  rintro ⟨_, hdeletedGap⟩
  exact not_hasTerminalExploitabilityGap_of_card_le_three hcard
    (quittingDeletePlayerReward reward owner) hgap hdeletedGap

/-- Deleting one player from an ambient type of cardinality at most four
leaves at most three players, so no strictly positive exact gap survives. -/
theorem not_hasQuittingExactPlayerDeletionAtGap_of_card_le_four
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hcard : Fintype.card ι ≤ 4)
    {gap : ℝ} (hgap : 0 < gap) :
    ¬ HasQuittingExactPlayerDeletionAtGap reward owner gap := by
  apply not_hasQuittingExactPlayerDeletionAtGap_of_deleted_card_le_three
    reward owner (gap := gap) (hgap := hgap)
  have hdeletedCard := card_quittingDeletedPlayer_lt owner
  omega

/-- On `Fin 4`, exact player deletion cannot retain any strictly positive
terminal exploitability gap. -/
theorem not_hasQuittingExactPlayerDeletionAtGap_finFour
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner : Fin 4) {gap : ℝ} (hgap : 0 < gap) :
    ¬ HasQuittingExactPlayerDeletionAtGap reward owner gap := by
  exact not_hasQuittingExactPlayerDeletionAtGap_of_card_le_four
    reward owner (by decide) hgap

end GameTheory
