/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime

/-!
# Uniform-payoff bridge for counterexample diagnostics

This adapter packages the routine incompatibility between a supplied
uniform-equilibrium payoff and a `QuittingCounterexampleRegime`.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Any uniform-equilibrium payoff excludes a counterexample regime. -/
theorem isEmpty_quittingCounterexampleRegime_of_exists_uniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hexists : ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    IsEmpty (QuittingCounterexampleRegime reward) :=
  ⟨fun regime => regime.not_exists_uniformEquilibriumPayoff hexists⟩

end GameTheory
