import UniformEquilibrium.Quitting.Classification.ProductLowQuittingPremiumDecision
import UniformEquilibrium.Quitting.Classification.Existence.ProductLowPremiumUniformPayoff

/-! # Uniform payoff from the executable rational product-low decision

This module connects the checked Boolean decision for a
rational reward table to the existing product-low periodic producer and
fixed-payoff consumer.  The original producer remains independent of real
quantifier elimination.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {players : ℕ}

private theorem rationalQuittingRewardToReal_singleton_nonnegative
    (reward : RationalQuittingReward players)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player) :
    ∀ player,
      0 ≤ rationalQuittingRewardToReal reward
        (quittingSingletonTerminal player) player := by
  intro player
  change (0 : ℝ) ≤ (reward (quittingSingletonTerminal player) player : ℝ)
  exact_mod_cast hsingleton player

/-- A true executable product-low decision produces one periodic root sequence
whose every suffix is terminal approximate Nash at the requested positive
error. -/
theorem exists_periodic_allSuffix_terminalNash_of_productLowPremiumDecision
    [Nonempty (Fin players)]
    (reward : RationalQuittingReward players)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    (hdecision : decideHasProductLowQuittingPremium reward = true)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (roots : ℕ → Fin players → PMF Bool) (period : ℕ), 0 < period ∧
      (∀ n, roots (n + period) = roots n) ∧
      ∀ start,
        (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
          (quittingTerminalPayoff (rationalQuittingRewardToReal reward)) ε
          (quittingRootSequenceProfile
            (rationalQuittingRewardToReal reward) roots start) := by
  apply exists_periodic_allSuffix_terminalNash_of_productLowPremium
    (rationalQuittingRewardToReal reward)
    (rationalQuittingRewardToReal_singleton_nonnegative reward hsingleton)
  · exact (decideHasProductLowQuittingPremium_eq_true_iff reward).mp hdecision
  · exact hε

/-- A true executable product-low decision produces a fixed uniform-equilibrium
payoff for every nonempty rational quitting table with nonnegative own
singleton rewards. -/
theorem exists_uniformEquilibriumPayoff_of_productLowPremiumDecision
    [Nonempty (Fin players)]
    (reward : RationalQuittingReward players)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    (hdecision : decideHasProductLowQuittingPremium reward = true) :
    ∃ payoff : Payoff (Fin players),
      (quittingGame (rationalQuittingRewardToReal reward)).IsUniformEquilibriumPayoff
        none payoff := by
  apply exists_uniformEquilibriumPayoff_of_productLowPremium
    (rationalQuittingRewardToReal reward)
    (rationalQuittingRewardToReal_singleton_nonnegative reward hsingleton)
  exact (decideHasProductLowQuittingPremium_eq_true_iff reward).mp hdecision

end GameTheory
