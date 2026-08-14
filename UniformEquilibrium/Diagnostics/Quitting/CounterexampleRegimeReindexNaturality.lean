/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime
import UniformEquilibrium.Quitting.Classification.PlayerReindexNaturality

/-!
# Naturality of the quitting counterexample regime

The counterexample-regime consequences of player reindexing live above the
generic reward-table and equilibrium naturality interface. The equivalence is
deliberately existential: it does not claim preservation of a selected gap or
prefix-capacity witness field by field.
-/

noncomputable section

namespace GameTheory

variable {ι κ : Type}
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [Nonempty ι] [Nonempty κ]

/-- Inhabitation of the combined counterexample regime is invariant under
player relabeling. This is the certificate-forgetting form appropriate for
canonical finite searches. -/
theorem nonempty_counterexampleRegime_reindex_iff (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Nonempty (QuittingCounterexampleRegime (quittingRewardReindex e reward)) ↔
      Nonempty (QuittingCounterexampleRegime reward) := by
  rw [← not_exists_uniformEquilibriumPayoff_iff_nonempty_counterexampleRegime,
    ← not_exists_uniformEquilibriumPayoff_iff_nonempty_counterexampleRegime]
  exact not_exists_uniformEquilibriumPayoff_reindex_iff e reward

/-- Every finite counterexample search can be carried out on the canonical
player type `Fin (Fintype.card ι)`. -/
theorem nonempty_counterexampleRegime_reindex_fin_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Nonempty (QuittingCounterexampleRegime
        (quittingRewardReindex (Fintype.equivFin ι) reward)) ↔
      Nonempty (QuittingCounterexampleRegime reward) :=
  nonempty_counterexampleRegime_reindex_iff (Fintype.equivFin ι) reward

end GameTheory
