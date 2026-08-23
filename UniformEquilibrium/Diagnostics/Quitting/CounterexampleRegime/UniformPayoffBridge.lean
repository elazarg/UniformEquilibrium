/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityWitness

/-!
# Uniform-payoff bridge for counterexample diagnostics

This adapter packages the routine incompatibility between a supplied
uniform-equilibrium payoff and a `QuittingTerminalExploitabilityWitness`.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Any uniform-equilibrium payoff excludes a terminal exploitability witness. -/
theorem isEmpty_quittingTerminalExploitabilityWitness_of_exists_uniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hexists : ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    IsEmpty (QuittingTerminalExploitabilityWitness reward) :=
  ⟨fun witness => witness.not_exists_uniformEquilibriumPayoff hexists⟩

end GameTheory
