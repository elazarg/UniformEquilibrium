/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime
import UniformEquilibrium.Quitting.Cycles.CollisionAwareFiniteReturn

/-!
# Collision-aware finite-return exclusion in a counterexample regime

The production verifier compiles every collision-aware finite return to a
uniform payoff at its prescribed boundary.  A counterexample regime therefore
excludes such a return at every positive cycle length and every boundary.
-/

namespace GameTheory
namespace QuittingCounterexampleRegime

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A counterexample regime forbids every finite collision-aware normalized
return, at any prescribed boundary. -/
theorem not_nonempty_collisionAwareFiniteReturn
    (regime : QuittingCounterexampleRegime reward)
    (boundary : Payoff ι)
    (K : ℕ) [NeZero K] :
    ¬ Nonempty (QuittingCollisionAwareFiniteReturn reward boundary K) := by
  rintro ⟨returnData⟩
  exact regime.not_exists_uniformEquilibriumPayoff
    ⟨boundary, returnData.boundary_isUniformEquilibriumPayoff⟩

end QuittingCounterexampleRegime
end GameTheory
