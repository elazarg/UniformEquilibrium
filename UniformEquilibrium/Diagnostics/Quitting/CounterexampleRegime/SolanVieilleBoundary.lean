/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryEquilibrium
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.UniformPayoffBridge

/-!
# The Solan–Vieille boundary table is in no counterexample regime

`GameTheory.SolanVieilleBoundary.boundaryReward_isUniformEquilibriumPayoff`
exhibits a uniform-equilibrium payoff for the table of Solan and Vieille,
*Quitting games*, Math. Oper. Res. 26 (2001), Section 3.  A positive terminal
exploitability gap is incompatible with the existence of any
uniform-equilibrium payoff, so that table carries no
`QuittingCounterexampleRegime`.

The exclusion lives in the diagnostics lane rather than beside the
equilibrium it consumes, because `QuittingCounterexampleRegime` is a
diagnostic interface and the quitting mathematics lane does not depend on
diagnostics.
-/

noncomputable section

namespace GameTheory

namespace SolanVieilleBoundary

/-- **The Solan–Vieille boundary table lies in no counterexample regime.** -/
theorem boundaryReward_isEmpty_counterexampleRegime :
    IsEmpty (QuittingCounterexampleRegime boundaryReward) :=
  isEmpty_quittingCounterexampleRegime_of_exists_uniformEquilibriumPayoff
    boundaryReward boundaryReward_exists_uniformEquilibriumPayoff

end SolanVieilleBoundary

end GameTheory
