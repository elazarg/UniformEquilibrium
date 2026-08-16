/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime
import UniformEquilibrium.Quitting.Boundary.Repair.AtomicBlockerCompletion

/-!
# Atomic-blocker obstruction in a quitting counterexample regime

The reusable atomic completion and terminal-exploitability theorem live in
`Quitting.Boundary.Repair.AtomicBlockerCompletion`.  This module specializes
that theorem to the gap carried by a counterexample regime.
-/

namespace GameTheory
namespace QuittingCounterexampleRegime

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The terminal gap forces every forced-owner Nash row's blocker balance
below the negative gap. -/
theorem quittingAtomicBlockerBalance_le_neg_terminalGap
    (regime : QuittingCounterexampleRegime reward)
    {owner : ι} {root : ι → PMF Bool}
    (hrow : IsQuittingForcedOwnerNashRow reward owner root) :
    quittingAtomicBlockerBalance reward root owner ≤ -regime.terminalGap :=
  quittingAtomicBlockerBalance_le_neg_of_terminalExploitabilityGap hrow
    regime.terminalGap_pos regime.terminalExploitability

end QuittingCounterexampleRegime
end GameTheory
