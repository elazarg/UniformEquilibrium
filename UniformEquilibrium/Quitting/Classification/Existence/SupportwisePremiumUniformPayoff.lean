/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.ProductLowPremiumUniformPayoff
import UniformEquilibrium.Quitting.Classification.SupportwiseQuittingPremiumProductLow

/-! # Uniform payoff from supportwise weighted quitting premiums -/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Supportwise balance is a direct special case of the shared product-low
periodic producer. -/
theorem exists_periodic_allSuffix_terminalNash_of_supportwiseBalance
    [Nonempty ι] (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    (hbalanced : IsSupportwiseBalancedQuittingPremiumTable reward)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (roots : ℕ → ι → PMF Bool) (period : ℕ), 0 < period ∧
      (∀ n, roots (n + period) = roots n) ∧
      ∀ start,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε
          (quittingRootSequenceProfile reward roots start) :=
  exists_periodic_allSuffix_terminalNash_of_productLowPremium reward hsingleton
    (hasProductLowQuittingPremium_of_supportwiseBalance reward hbalanced) hε

/-- The supportwise fixed-payoff result is the corresponding direct
product-low corollary. -/
theorem exists_uniformEquilibriumPayoff_of_supportwiseBalance
    [Nonempty ι] (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    (hbalanced : IsSupportwiseBalancedQuittingPremiumTable reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_productLowPremium reward hsingleton
    (hasProductLowQuittingPremium_of_supportwiseBalance reward hbalanced)

end GameTheory
