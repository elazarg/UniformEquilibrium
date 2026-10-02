import MathUE.LinearProgramming.StandardQSimplexImage
import UniformEquilibrium.Quitting.Classification.LCP.CopositiveQBridge
import UniformEquilibrium.Quitting.Classification.LCP.FullNormalCoreHomogeneousTransfer
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.AmbientCarrierElimination

/-! # Bare Fin4 no-UE produces ambient textbook Q and its analytic simplex point

This composes the existing semantic source, actual full-core elimination,
literal subtype reindexing, and Q-convention bridge. There is no strategy,
punishment-normality, reward bound, or positive-singleton input.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification
open ThreeCoreAmbientCarrierElimination
open Math.LinearProgramming
open scoped BigOperators

/-- Bare Fin4 no-UE makes the actual receiver-row singleton matrix ambient
textbook Q. The normal core and its Q certificate are internally produced. -/
theorem isStandardQ_quittingProjectiveLCPMatrix_of_finFour_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    IsStandardQ (quittingProjectiveLCPMatrix reward) := by
  have hside := standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff reward hnot
  have hcore :=
    normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff
      reward (by simp) hnot
  have hQ := isStandardQMatrix_reindexMatrix
    (fullNormalCoreEquiv (normalizedSoloMatrix reward) hcore)
    (normalPlayerMatrix (normalizedSoloMatrix reward)) hside.normal_standardQ
  rw [reindex_normalPlayerMatrix_fullNormalCoreEquiv,
    normalizedSoloMatrix_eq_projectiveLCPMatrix] at hQ
  exact (isStandardQ_iff_isStandardQMatrix _).mpr hQ

/-- Bare Fin4 no-UE produces an actual simplex vector with strictly positive
image under its actual singleton matrix. This is not a homogeneous LCP solution. -/
theorem exists_finFour_simplex_positive_projectiveResidual_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ weight : Convexity.StdSimplex ℝ (Fin 4),
      ∀ receiver, 0 < ∑ owner, weight.weights owner *
        quittingProjectiveLCPMatrix reward receiver owner := by
  simpa only [singletonLCPResidual_eq] using
    exists_simplex_positive_residual_of_standardQ (quittingProjectiveLCPMatrix reward)
      (isStandardQ_quittingProjectiveLCPMatrix_of_finFour_no_uniformPayoff reward hnot)

/-- The exact nonnegative-image simplex input for the face-only packet is
an output of the source no-UE hypothesis, not an additional semantic premise. -/
theorem exists_finFour_simplex_nonnegative_projectiveResidual_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ weight : Convexity.StdSimplex ℝ (Fin 4),
      ∀ receiver, 0 ≤ ∑ owner, weight.weights owner *
        quittingProjectiveLCPMatrix reward receiver owner := by
  obtain ⟨weight, hpositive⟩ :=
    exists_finFour_simplex_positive_projectiveResidual_of_no_uniformPayoff reward hnot
  exact ⟨weight, fun receiver => (hpositive receiver).le⟩

end GameTheory
