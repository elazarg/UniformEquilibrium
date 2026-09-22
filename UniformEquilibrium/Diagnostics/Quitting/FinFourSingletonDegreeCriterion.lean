import UniformEquilibrium.Quitting.Classification.LCP.SingletonDegreeCriterion
import UniformEquilibrium.Diagnostics.Quitting.FinFourAuxiliaryDiscountedLocalization

/-!
# Original four-player noUE forces full singleton R0 and degree one

The actual four-player residual supplies full R0. The generic finite-player
degree criterion then applies to that matrix under the same original-game
no-equilibrium hypothesis.
-/

noncomputable section

namespace GameTheory

open _root_.Math.LinearProgramming QuittingLCPClassification

/-- Original four-player noUE supplies full R0 and degree one for the original
singleton matrix, with no auxiliary no-equilibrium hypothesis. -/
theorem finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hno : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ hR0 : IsR0Matrix (quittingSingletonMatrix reward),
      r0Degree (quittingSingletonMatrix reward) hR0 = 1 := by
  have hR0 := finFour_isR0Matrix_quittingSingletonMatrix_of_no_uniformPayoff reward hno
  exact ⟨hR0, singleton_r0Degree_eq_one_of_no_uniformPayoff reward hR0 hno⟩

end GameTheory
