/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityWitness
import UniformEquilibrium.Quitting.Circulation.KActiveMarkedAtomBudgetPathConsumer

/-!
# Counterexample exclusions from cumulative marked clocks

The production compact-path compiler turns compatible finite prefixes with a divergent
absorption budget into a uniform-equilibrium payoff. Consequently, a selected
terminal exploitability witness must exclude both the general fixed-activity prefix family and
the fixed one-active singleton-mark specialization.
-/

noncomputable section

namespace GameTheory

open Finset Set StochasticGame Filter Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction Math.Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Counterexample-facing exclusions -/

/-- A terminal exploitability witness cannot admit cumulative-clock `K`-active prefix
families of the form consumed above, for any fixed `K`. -/
theorem QuittingTerminalExploitabilityWitness.not_KActiveAbsorptionBudgetPrefixes
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (K : ℕ) (bound : ℝ)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    ¬(∀ epsilon, 0 < epsilon →
      ∃ budget : ℕ → ℝ,
        Tendsto budget atTop atTop ∧
        ∀ horizon,
          (compactBudgetedPrefixSolutionSet
            (quittingCirculationPathBox bound
              (fun who => quittingPunishmentValue reward who - epsilon))
            (IsQuittingKActiveCirculationPathEdge reward K epsilon 0)
            (fun point => quittingSimplexAbsorptionMass point.2)
            budget horizon).Nonempty) := by
  intro hprefix
  exact witness.not_exists_uniformEquilibriumPayoff
    (quittingGame_exists_uniformEquilibriumPayoff_of_KActiveAbsorptionBudgetPrefixes
      reward K bound hreward hprefix)

/-- In particular, a counterexample cannot retain one fixed one-active
singleton edge with a divergent cumulative clock on compatible prefixes at
every accuracy. -/
theorem QuittingTerminalExploitabilityWitness.not_oneActiveMarkedBudgetPrefixes
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (bound : ℝ)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    ¬(∀ epsilon, 0 < epsilon →
      ∃ (markedPlayer clockOwner : ι) (budget : ℕ → ℝ),
        Tendsto budget atTop atTop ∧
        ∀ horizon,
          (compactBudgetedPrefixSolutionSet
            (quittingCirculationPathBox bound
              (fun who => quittingPunishmentValue reward who - epsilon))
            (IsQuittingKActiveCirculationPathEdge reward 1 epsilon 0)
            (fun point => quittingSimplexOpponentCoalitionMass
              point.2 markedPlayer {clockOwner})
            budget horizon).Nonempty) := by
  intro hprefix
  exact witness.not_exists_uniformEquilibriumPayoff
    (quittingGame_exists_uniformEquilibriumPayoff_of_oneActiveMarkedBudgetPrefixes
      reward bound hreward hprefix)
end GameTheory
