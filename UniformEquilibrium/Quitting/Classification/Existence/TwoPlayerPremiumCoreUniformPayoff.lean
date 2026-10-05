import UniformEquilibrium.Quitting.Classification.TwoPlayerPremiumCoreSmoothDrift
import UniformEquilibrium.Quitting.Classification.Existence.BoundaryDifferentiablePotentialUniformPayoff

/-! # Uniform payoffs for four-player strict-leave premium cores

Nonnegative singleton rewards give normality. If a singleton is positive,
the canonical obstruction theorem would produce a rational polynomial on
the same full robust relation. Its exact-root restriction contradicts smooth
potential exclusion. Otherwise the established zero-solo branch applies.
-/

noncomputable section

namespace GameTheory

open Math.Interval Math.Interval.RationalPolynomial

/-- Four-player strict-leave premium cores with nonnegative singleton rewards
have a uniform-equilibrium payoff. The target is fixed before the accuracy;
unilateral deviations range over complete behavioral strategies. -/
theorem exists_uniformEquilibriumPayoff_of_twoPlayerPremiumCore_strictLeave
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    (hsingleton : ∀ player, 0 ≤ reward (quittingSingletonTerminal player) player)
    (first second : Fin 4) (hne : first ≠ second)
    (houtside : ∀ player, player ≠ first → player ≠ second →
      ∀ terminal, player ∈ terminal.val →
        reward terminal player = reward (quittingSingletonTerminal player) player)
    (hleave : reward ⟨{first, second}, by simp⟩ first <
      reward (quittingSingletonTerminal second) first) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply exists_uniformEquilibriumPayoff_of_continuous_boundaryDifferentiable_potential_exclusion
    reward hsingleton
  intro potential _hcontinuous hdiff
  exact not_isQuittingFullExactRootPotential_of_twoPlayerPremiumCore_strictLeave
    hnonnegative first second hne houtside hleave
    (M := quittingRewardBound reward) (bound := quittingRewardBound reward + 2)
    (abs_reward_le_quittingRewardBound reward) (by linarith) potential hdiff

end GameTheory
