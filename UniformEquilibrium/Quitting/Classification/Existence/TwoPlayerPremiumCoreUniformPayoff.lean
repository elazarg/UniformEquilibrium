import MathUE.Interval.RationalPolynomialRegularity
import UniformEquilibrium.Quitting.Classification.AbnormalPlayers
import UniformEquilibrium.Quitting.Classification.TwoPlayerPremiumCoreSmoothDrift
import UniformEquilibrium.Quitting.Projective.PolynomialForwardCertificateCharacterization
import UniformEquilibrium.Quitting.Punishment.ZeroSoloDisjunct
import UniformEquilibrium.Quitting.RewardBound

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
  classical
  by_cases hpositive : ∃ player, 0 < reward (quittingSingletonTerminal player) player
  · by_contra hnoUniform
    let rewardBound := quittingRewardBound reward
    have hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound :=
      abs_reward_le_quittingRewardBound reward
    have hnormal : ∀ player, IsQuittingNormalPlayer reward player :=
      fun player => isQuittingNormalPlayer_of_singleton_nonneg
        reward player (hsingleton player)
    obtain ⟨_, tolerance, htolerance, _, expression, hrobust⟩ :=
      (quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential
        reward rewardBound hreward hnormal hpositive).mp hnoUniform
    have hexact : IsQuittingFullExactRootPotential reward (rewardBound + 2)
        (fun point => evalReal point expression) :=
      isQuittingFullExactRootPotential_of_robustPotential reward
        (by exact_mod_cast htolerance.le)
        (fun terminal player => (hreward terminal player).trans (by linarith))
        (fun point => evalReal point expression) hrobust
    exact not_isQuittingFullExactRootPotential_of_twoPlayerPremiumCore_strictLeave
      hnonnegative first second hne houtside hleave
      (M := rewardBound) (bound := rewardBound + 2) hreward (by linarith)
      (fun point => evalReal point expression)
      (fun point _ => (contDiff_evalReal expression 1).differentiable_one point) hexact
  · apply exists_uniformEquilibriumPayoff_of_zeroSolo reward
    intro player
    exact le_of_not_gt fun hplayer => hpositive ⟨player, hplayer⟩

end GameTheory
