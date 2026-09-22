import UniformEquilibrium.Diagnostics.Quitting.FinFourSingletonDegreeCriterion
import UniformEquilibrium.Quitting.Classification.LCP.NonnegativeInverseCriterion

/-!
# Four-player uniform equilibrium from a nonnegative singleton inverse

A negative determinant and entrywise nonnegative inverse of the literal
singleton matrix suffice for an original uniform-equilibrium payoff through
the generic finite-player reward-approximation criterion.

The non-R0 case is separately discharged by the same original-game source.
-/

noncomputable section

namespace GameTheory

open _root_.Math.LinearProgramming QuittingLCPClassification

/-- A failure of full singleton R0 is already sufficient in four-player games. -/
theorem finFour_exists_uniformEquilibriumPayoff_of_not_isR0Matrix
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnot : ¬IsR0Matrix (quittingSingletonMatrix reward)) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hno
  exact hnot (finFour_isR0Matrix_quittingSingletonMatrix_of_no_uniformPayoff reward hno)

/-- The four-player statement is the direct specialization of the generic
dimension-at-least-three nonnegative-inverse criterion. -/
theorem finFour_exists_uniformEquilibriumPayoff_of_nonnegative_inverse
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hdet : Matrix.det (quittingSingletonMatrix reward) < 0)
    (hinverse : ∀ row column, 0 ≤ (quittingSingletonMatrix reward)⁻¹ row column) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  exact exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse
    (by decide : 3 ≤ 4) reward hdet hinverse

end GameTheory
