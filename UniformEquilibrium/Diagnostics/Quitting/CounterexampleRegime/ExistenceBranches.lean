/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Toggles
import UniformEquilibrium.Quitting.Classification.ExistenceBranches

/-!
# A counterexample regime refutes the two profile-level existence branches

`UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean` states the
three branches of the source characterization of `ε`-equilibrium existence in
quitting games.  Two of them ask for a terminal approximate equilibrium of a
prescribed shape at every positive tolerance, so a counterexample regime kills
both outright: its terminal gap bounds every profile away from being an
approximate equilibrium below the gap, whatever its shape.

The remaining branch is stated through stagewise perfectness against a plan's
own continuation vector rather than through a global approximate-Nash
inequality, so it is not refuted by this argument and no statement about it is
made here.
-/

noncomputable section

namespace GameTheory

namespace QuittingCounterexampleRegime

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- **A counterexample regime refutes the stationary branch.**  Under a
positive terminal exploitability gap no profile at all is a terminal
approximate equilibrium below the gap, so in particular no stationary one
is. -/
theorem not_quittingStationaryεEquilibriumExistence
    (regime : QuittingCounterexampleRegime reward) :
    ¬ QuittingStationaryεEquilibriumExistence reward := by
  intro hbranch
  obtain ⟨root, hroot⟩ :=
    hbranch (regime.terminalGap / 2) (by linarith [regime.terminalGap_pos])
  exact regime.not_isεAsymptoticNash_of_lt_terminalGap _
    (by linarith [regime.terminalGap_pos]) hroot

/-- **A counterexample regime refutes the instant-punishment branch** for the
same reason. -/
theorem not_quittingInstantPunishmentεEquilibriumExistence
    (regime : QuittingCounterexampleRegime reward) :
    ¬ QuittingInstantPunishmentεEquilibriumExistence reward := by
  intro hbranch
  obtain ⟨quitter, root, punishRow, hquit, hcap, hnash⟩ :=
    hbranch (regime.terminalGap / 2) (by linarith [regime.terminalGap_pos])
  exact regime.not_isεAsymptoticNash_of_lt_terminalGap _
    (by linarith [regime.terminalGap_pos]) hnash

end QuittingCounterexampleRegime

end GameTheory
