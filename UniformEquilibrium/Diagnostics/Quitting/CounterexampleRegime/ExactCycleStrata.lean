/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityWitness
import UniformEquilibrium.Quitting.Cycles.OwnShiftCycleExactification

/-!
# Exact-cycle exclusion in the quitting terminal exploitability witness

The combined terminal exploitability witness already contains a positive terminal
exploitability gap and therefore excludes uniform-equilibrium payoffs.  Reward
closure upgrades this pointwise failure to an open reward-table neighborhood.
Since every absorbing punishment-admissible exact cycle compiles to a uniform
payoff, the same neighborhood is disjoint from every solved finite-cycle
stratum, with no bound on period or support pattern.

This is a robust finite-dimensional restriction on a counterexample, not a
density theorem.  The own-set exactification API gives an exact playerwise test
inside each fixed-root slice, but failure of that restricted test does not
certify exclusion from the full solved-cycle locus.
-/

noncomputable section

namespace GameTheory
namespace QuittingTerminalExploitabilityWitness

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A counterexample table itself carries no solved exact quitting cycle. -/
theorem not_hasSolvedExactQuittingCycle
    (witness : QuittingTerminalExploitabilityWitness reward) :
    ¬ HasSolvedExactQuittingCycle reward := by
  intro hsolved
  exact witness.not_exists_uniformEquilibriumPayoff
    hsolved.exists_uniformEquilibriumPayoff

/-- **Robust solved-cycle exclusion.**  One positive-radius coordinatewise
reward neighborhood of every terminal exploitability witness is disjoint from all
absorbing punishment-admissible exact cycles of all finite periods. -/
theorem exists_solvedExactCycleExclusionRadius
    (witness : QuittingTerminalExploitabilityWitness reward) :
    ∃ η : ℝ, 0 < η ∧
      ∀ nearby : {S : Finset ι // S.Nonempty} → Payoff ι,
        (∀ S who, |nearby S who - reward S who| ≤ η) →
          ¬ HasSolvedExactQuittingCycle nearby :=
  exists_rewardNeighborhood_without_solvedExactQuittingCycle reward
    witness.not_exists_uniformEquilibriumPayoff

end QuittingTerminalExploitabilityWitness
end GameTheory
