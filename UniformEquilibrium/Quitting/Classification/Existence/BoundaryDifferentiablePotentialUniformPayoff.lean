import MathUE.Interval.RationalPolynomialRegularity
import MathUE.Analysis.LowerBoxBoundarySmoothDrift
import UniformEquilibrium.Quitting.Classification.AbnormalPlayers
import UniformEquilibrium.Quitting.Projective.ExactRootPotentialRestriction
import UniformEquilibrium.Quitting.Projective.PolynomialForwardCertificateCharacterization
import UniformEquilibrium.Quitting.Punishment.ZeroSoloDisjunct
import UniformEquilibrium.Quitting.RewardBound

/-! # Four-player uniform payoff from boundary-differentiable potential exclusion -/

noncomputable section

namespace GameTheory

open Math.Interval Math.Interval.RationalPolynomial

/-- The actual polynomial obstruction is discharged by an exact-root analytic
exclusion. No participant-premium sign hypothesis is imposed. -/
theorem exists_uniformEquilibriumPayoff_of_continuous_boundaryDifferentiable_potential_exclusion
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsingleton : ∀ player, 0 ≤ reward (quittingSingletonTerminal player) player)
    (hexclusion : ∀ potential : Payoff (Fin 4) → ℝ,
      Continuous potential →
      (∀ point ∈ Math.lowerBoxBoundary
        (fun player => quittingSoloReward reward player player)
        (fun _ => quittingRewardBound reward + 2), DifferentiableAt ℝ potential point) →
      ¬IsQuittingFullExactRootPotential reward (quittingRewardBound reward + 2) potential) :
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
    exact hexclusion (fun point => evalReal point expression)
      (contDiff_evalReal expression 1).continuous
      (fun point _ => (contDiff_evalReal expression 1).differentiable_one point) hexact
  · apply exists_uniformEquilibriumPayoff_of_zeroSolo reward
    intro player
    exact le_of_not_gt fun hplayer => hpositive ⟨player, hplayer⟩

end GameTheory
