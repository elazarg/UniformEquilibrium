import UniformEquilibrium.Quitting.Classification.Existence.SupportwisePremiumUniformPayoff
import UniformEquilibrium.Quitting.Classification.QuittingPremiumSupportPeelingOrder

/-! # Uniform payoff from weak quitting-premium support peeling -/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Weak premium support peeling produces a literal periodic root sequence
whose every actual suffix is a terminal approximate Nash profile. -/
theorem exists_periodic_allSuffix_terminalNash_of_weakPremiumSupportPeeling
    [Nonempty ι] (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    (hpeel : HasWeakQuittingPremiumSupportPeeling reward)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (roots : ℕ → ι → PMF Bool) (period : ℕ), 0 < period ∧
      (∀ n, roots (n + period) = roots n) ∧
      ∀ start,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε
          (quittingRootSequenceProfile reward roots start) :=
  exists_periodic_allSuffix_terminalNash_of_supportwiseBalance
    reward hsingleton
      (supportwiseBalance_of_weakQuittingPremiumSupportPeeling reward hpeel) hε

/-- A full positive-premium player ranking gives the same literal periodic
every-suffix terminal approximate Nash conclusion. -/
theorem exists_periodic_allSuffix_terminalNash_of_positivePremiumPlayerRanking
    [Nonempty ι] (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    (hranking : HasPositiveQuittingPremiumPlayerRanking reward)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (roots : ℕ → ι → PMF Bool) (period : ℕ), 0 < period ∧
      (∀ n, roots (n + period) = roots n) ∧
      ∀ start,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε
          (quittingRootSequenceProfile reward roots start) :=
  exists_periodic_allSuffix_terminalNash_of_weakPremiumSupportPeeling
    reward hsingleton
      ((weakQuittingPremiumSupportPeeling_iff_playerRanking reward).mpr hranking) hε

/-- Weak premium support peeling yields one fixed uniform-equilibrium payoff
of the original reward table. -/
theorem exists_uniformEquilibriumPayoff_of_weakPremiumSupportPeeling
    [Nonempty ι] (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    (hpeel : HasWeakQuittingPremiumSupportPeeling reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_supportwiseBalance reward hsingleton
    (supportwiseBalance_of_weakQuittingPremiumSupportPeeling reward hpeel)

/-- The equivalent full player-ranking condition yields one fixed
uniform-equilibrium payoff of the original reward table. -/
theorem exists_uniformEquilibriumPayoff_of_positivePremiumPlayerRanking
    [Nonempty ι] (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    (hranking : HasPositiveQuittingPremiumPlayerRanking reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_weakPremiumSupportPeeling
    reward hsingleton
      ((weakQuittingPremiumSupportPeeling_iff_playerRanking reward).mpr hranking)

end GameTheory
