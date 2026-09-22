import MathUE.LinearProgramming.Examples.NegativeDegreeFourMatrix
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

end GameTheory
