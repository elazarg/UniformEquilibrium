import MathUE.LinearProgramming.NonnegativeInverseDegree
import UniformEquilibrium.Diagnostics.Quitting.FinFourSingletonDegreeCriterion

/-!
# Four-player uniform equilibrium from a nonnegative singleton inverse

A negative determinant and entrywise nonnegative inverse of the literal
singleton matrix suffice for an original uniform-equilibrium payoff. Under
the contrary hypothesis, the existing four-player source supplies full R0
and degree one; the inverse computation gives degree minus one.

The non-R0 case is separately discharged by the same original-game source.
No strict inverse positivity, reward approximation, or auxiliary-game
no-equilibrium premise is used.
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

/-- Zero entries in the nonnegative inverse are permitted; full R0 is derived
from original noUE in the contradiction argument, not imposed on the table. -/
theorem finFour_exists_uniformEquilibriumPayoff_of_nonnegative_inverse
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hdet : Matrix.det (quittingSingletonMatrix reward) < 0)
    (hinverse : ∀ row column, 0 ≤ (quittingSingletonMatrix reward)⁻¹ row column) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hno
  obtain ⟨hR0, hdegree⟩ :=
    finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff reward hno
  have hnegativeDegree : r0Degree (quittingSingletonMatrix reward) hR0 = -1 := by
    rw [r0Degree_eq_sign_det_of_nonnegative_inverse
      (quittingSingletonMatrix reward) hR0 hdet.ne hinverse, sign_neg hdet]
    rfl
  omega

end GameTheory
