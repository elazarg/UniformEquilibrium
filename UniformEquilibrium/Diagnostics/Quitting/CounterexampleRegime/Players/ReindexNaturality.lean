/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityWitness
import UniformEquilibrium.Quitting.Classification.PlayerReindexNaturality

/-!
# Naturality of the quitting terminal exploitability witness

The terminal exploitability witness consequences of player reindexing live above the
generic reward-table and equilibrium naturality interface. The equivalence is
deliberately existential: it does not claim preservation of a selected gap or
prefix-capacity witness field by field.
-/

noncomputable section

namespace GameTheory

variable {ι κ : Type}
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Inhabitation of the combined terminal exploitability witness is invariant under
player relabeling. This is the certificate-forgetting form appropriate for
canonical finite searches. -/
theorem nonempty_terminalExploitabilityWitness_reindex_iff (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Nonempty (QuittingTerminalExploitabilityWitness (quittingRewardReindex e reward)) ↔
      Nonempty (QuittingTerminalExploitabilityWitness reward) := by
  rw [← not_exists_uniformEquilibriumPayoff_iff_nonempty_terminalExploitabilityWitness,
    ← not_exists_uniformEquilibriumPayoff_iff_nonempty_terminalExploitabilityWitness]
  exact not_exists_uniformEquilibriumPayoff_reindex_iff e reward

/-- Every finite counterexample search can be carried out on the canonical
player type `Fin (Fintype.card ι)`. -/
theorem nonempty_terminalExploitabilityWitness_reindex_fin_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Nonempty (QuittingTerminalExploitabilityWitness
        (quittingRewardReindex (Fintype.equivFin ι) reward)) ↔
      Nonempty (QuittingTerminalExploitabilityWitness reward) :=
  nonempty_terminalExploitabilityWitness_reindex_iff (Fintype.equivFin ι) reward

end GameTheory
