import MathUE.LinearProgramming.NonnegativeInverseDegree
import MathUE.LinearProgramming.PositiveInverseR0
import UniformEquilibrium.Quitting.Classification.LCP.NonnegativeInverseRewardApproximation
import UniformEquilibrium.Quitting.Classification.LCP.PositiveInverse
import UniformEquilibrium.Quitting.Classification.LCP.SingletonDegreeCriterion
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityRewardRobustness

/-!
# Uniform equilibrium from a nonnegative singleton-matrix inverse

A negative determinant and entrywise nonnegative inverse of the literal
singleton comparison matrix suffice in every dimension at least three.  The
strict-inverse case follows from the existing R0-degree criterion.  The
boundary case uses literal reward-table approximation and fixed-skeleton
reward closure, retaining one fixed payoff target and unrestricted behavioral
deviations.
-/

noncomputable section

namespace GameTheory

open _root_.Math.LinearProgramming QuittingLCPClassification

/-- A strictly positive singleton-matrix inverse and negative determinant
force a uniform-equilibrium payoff through the canonical R0 degree. -/
theorem exists_uniformEquilibriumPayoff_of_strictlyPositive_singletonInverse
    {n : ℕ}
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (hdet : (quittingSingletonMatrix reward).det < 0)
    (hpositive : HasStrictlyPositiveInverse (quittingSingletonMatrix reward)) :
    ∃ payoff : Payoff (Fin n),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  let matrix := quittingSingletonMatrix reward
  have hR0 : IsR0Matrix matrix :=
    isR0Matrix_of_strictlyPositiveInverse matrix hpositive
  have hdegree : r0Degree matrix hR0 = -1 := by
    rw [r0Degree_eq_sign_det_of_nonnegative_inverse matrix hR0 hpositive.1
      (fun row column => (hpositive.2 row column).le), sign_neg hdet]
    rfl
  apply exists_uniformEquilibriumPayoff_of_r0Degree_ne_one reward hR0
  change r0Degree matrix hR0 ≠ 1
  rw [hdegree]
  norm_num

/-- In every dimension at least three, a negative singleton determinant and
entrywise nonnegative actual inverse suffice for an original-game uniform
equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse
    {n : ℕ} (hcard : 3 ≤ n)
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (hdet : (quittingSingletonMatrix reward).det < 0)
    (hinverse : ∀ row column,
      0 ≤ (quittingSingletonMatrix reward)⁻¹ row column) :
    ∃ payoff : Payoff (Fin n),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨threshold, hthreshold, hsmall⟩ :=
    exists_pos_strictlyPositiveInverse_singletonMatrix_rewardApproximation
      reward (by simpa using hcard) hdet.ne hinverse
  apply exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables reward
  intro delta hdelta
  let epsilon := min delta threshold / 2
  have hminimum : 0 < min delta threshold := lt_min hdelta hthreshold
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    linarith
  have hepsilonDelta : epsilon < delta := by
    dsimp only [epsilon]
    have := min_le_left delta threshold
    linarith
  have hepsilonThreshold : epsilon < threshold := by
    dsimp only [epsilon]
    have := min_le_right delta threshold
    linarith
  obtain ⟨hpositive, hsign, hclose⟩ :=
    hsmall epsilon hepsilon hepsilonThreshold
  let nearby := subtractOffOwnSingletonReward epsilon reward
  have hnearbyDet : (quittingSingletonMatrix nearby).det < 0 := by
    apply sign_eq_neg_one_iff.mp
    exact hsign.trans (sign_eq_neg_one_iff.mpr hdet)
  refine ⟨nearby, ?_, ?_⟩
  · intro terminal player
    exact (hclose terminal player).trans (by
      rw [abs_of_pos hepsilon]
      exact hepsilonDelta.le)
  · exact exists_uniformEquilibriumPayoff_of_strictlyPositive_singletonInverse
      nearby hnearbyDet hpositive

end GameTheory
