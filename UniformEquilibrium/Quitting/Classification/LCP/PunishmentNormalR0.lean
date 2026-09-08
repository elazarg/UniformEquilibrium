import UniformEquilibrium.Quitting.Classification.LCP.HomogeneousProductionNormalDispatch
import MathUE.LinearProgramming.CopositiveQ

/-!
# Original-game normality excludes full homogeneous singleton solutions

The matrix is the full singleton comparison matrix of the supplied table.
Normality concerns the original game, not a separately shifted game. The
existing supported-normal homogeneous witness consumer yields the contradiction.
-/

noncomputable section

namespace GameTheory.QuittingLCPClassification

open Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- All-player punishment normality and absence of original UE force full R₀. -/
theorem isR0Matrix_quittingSingletonMatrix_of_normal_of_no_uniformPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward ⟨{who}, Finset.singleton_nonempty who⟩ who)
    (hnot : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    IsR0Matrix (quittingSingletonMatrix reward) := by
  rw [isR0Matrix_iff_not_singletonLCPFeasible]
  rintro ⟨weight, hresidual, hcomplementary⟩
  have hmatrix : normalizedSoloMatrix reward = quittingSingletonMatrix reward := by
    funext who owner
    exact normalized_singletonMatrix_eq_quittingSingletonMatrix reward who owner
  apply hnot
  apply exists_uniformEquilibriumPayoff_of_homogeneous_supported_normal reward weight
  · simpa only [hmatrix] using hresidual
  · simpa only [hmatrix] using hcomplementary
  · intro owner _
    exact hnormal owner

end GameTheory.QuittingLCPClassification
