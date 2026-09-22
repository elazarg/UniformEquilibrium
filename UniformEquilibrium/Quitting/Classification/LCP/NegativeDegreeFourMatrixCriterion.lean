import MathUE.LinearProgramming.Examples.NegativeDegreeFourMatrixStability
import UniformEquilibrium.Quitting.Classification.LCP.SingletonDegreeCriterion

/-!
# Raw quitting games with the explicit negative-degree singleton matrix

Every four-player reward table with the displayed singleton comparison
matrix has an original-game uniform-equilibrium payoff. The singleton
payoff levels and every nonsingleton reward remain unrestricted. The proof
uses the exact full R0 and degree `-1` calculations and the generic degree
criterion, with no reward normalization or additional strategic hypothesis.
-/

noncomputable section

open Filter
open scoped Topology

namespace GameTheory

open _root_.Math.LinearProgramming QuittingLCPClassification

/-- Any raw four-player table with the explicit negative-degree singleton
matrix admits an original-game uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_negativeDegreeFourMatrix
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hmatrix : quittingSingletonMatrix reward = NegativeDegreeFourMatrix.matrix) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have hR0 : IsR0Matrix (quittingSingletonMatrix reward) :=
    hmatrix.symm ▸ NegativeDegreeFourMatrix.isR0Matrix
  apply exists_uniformEquilibriumPayoff_of_r0Degree_ne_one reward hR0
  have hdegree : r0Degree (quittingSingletonMatrix reward) hR0 = -1 := by
    simpa only [hmatrix] using NegativeDegreeFourMatrix.r0Degree_eq_neg_one
  rw [hdegree]
  norm_num

/-- The raw criterion persists on a literal matrix neighborhood: every raw
reward table with a nearby singleton matrix has an original uniform payoff. -/
theorem eventually_exists_uniformEquilibriumPayoff_near_negativeDegreeFourMatrix :
    ∀ᶠ matrix : Matrix (Fin 4) (Fin 4) ℝ in 𝓝 NegativeDegreeFourMatrix.matrix,
      ∀ reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4),
        quittingSingletonMatrix reward = matrix →
        ∃ payoff : Payoff (Fin 4),
          (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  filter_upwards [NegativeDegreeFourMatrix.eventually_r0Degree_neg_one_and_three_supports]
    with matrix hmatrix
  intro reward hequal
  have hdiagonal (who : Fin 4) : matrix who who = 0 := by
    rw [← hequal]
    simp only [quittingSingletonMatrix, sub_self]
  obtain ⟨hR0, hdegree, _hsupports, _hroots⟩ := hmatrix hdiagonal
  have hR0Reward : IsR0Matrix (quittingSingletonMatrix reward) := hequal.symm ▸ hR0
  apply exists_uniformEquilibriumPayoff_of_r0Degree_ne_one reward hR0Reward
  have hdegreeReward : r0Degree (quittingSingletonMatrix reward) hR0Reward = -1 := by
    simpa only [hequal] using hdegree
  rw [hdegreeReward]
  norm_num

end GameTheory
