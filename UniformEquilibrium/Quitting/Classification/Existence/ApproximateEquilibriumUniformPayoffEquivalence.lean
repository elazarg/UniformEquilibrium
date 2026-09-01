/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.ArbitraryNeverExtraction
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-!
# Approximate-equilibrium existence and uniform-payoff existence

For a finite quitting game, existence of terminal approximate equilibria at
every positive error is exactly existence of some uniform-equilibrium payoff.
The root-sequence formulation is behaviorally exact, and compact terminal
target selection fixes one payoff vector.  Conversely, a uniform-equilibrium
payoff supplies terminal approximate equilibria at every positive error.

This equivalence is a notion-alignment result.  In particular, it cannot be
used as evidence for the stronger AKRS fixed-branch classification.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Root-sequence approximate-equilibrium existence is equivalent to the
existence of some uniform-equilibrium payoff. -/
theorem quittingApproximateEquilibriumExistence_iff_exists_uniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    QuittingApproximateEquilibriumExistence reward ↔
      ∃ payoff : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  rw [quittingApproximateEquilibriumExistence_iff_behavior]
  exact
    (quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors
      reward).symm

namespace QuittingLCPClassification

/-- The arbitrary-never hypothesis used by AKRS is likewise equivalent to
uniform-payoff existence for its normalized zero-never quitting game.  This
does not identify any stationary, instant-punishment, or sequentially-perfect
branch. -/
theorem
    QuittingPayoffTable.approximateEquilibriumExistence_iff_exists_zeroNeverUniformPayoff
    (table : QuittingPayoffTable ι) :
    table.ApproximateEquilibriumExistence ↔
      ∃ payoff : Payoff ι,
        (quittingGame table.zeroNeverReward).IsUniformEquilibriumPayoff
          none payoff := by
  rw [table.approximateEquilibriumExistence_iff_zeroNever,
    quittingApproximateEquilibriumExistence_iff_exists_uniformEquilibriumPayoff]

end QuittingLCPClassification
end GameTheory
