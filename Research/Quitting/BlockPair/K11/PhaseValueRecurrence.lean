import Research.Quitting.BlockPair.K11.CyclicNumeratorEvaluation
import Research.Quitting.BlockPair.K11.ImmediateSemantic
import Research.Quitting.BlockPair.K11.ContinueMassPhase
import UniformEquilibrium.Quitting.Root.SuccessorCertificate

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

open Math.Interval

/-- The quotient values determined by the cyclic numerators satisfy the
quitting-game one-phase Bellman recurrence. -/
theorem phaseValue_eq_quittingRootSuccessorPayoff
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (hrho : rho x < 1) (phase : Phase) :
    phaseValue x phase = quittingRootSuccessorPayoff reward
      (phaseValue x (nextPhase phase)) (phaseRoot x hx phase) := by
  funext who
  unfold quittingRootSuccessorPayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    phaseRoot_absorbingContribution_eq_evalReal_immediateReward,
    phaseRoot_continueMass_eq_evalReal_phaseSurvival]
  unfold phaseValue rho
  have hdenominator :
      1 - RationalPolynomial.evalReal x jointCycleSurvival ≠ 0 := by
    unfold rho at hrho
    linarith
  have hrecurrence := evalReal_cyclicValueNumerator_recurrence x phase who
  field_simp
  linear_combination hrecurrence

end GameTheory.BlockPairK11.ConditionalData
