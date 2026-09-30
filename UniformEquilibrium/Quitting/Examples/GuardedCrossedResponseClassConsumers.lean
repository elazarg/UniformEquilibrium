import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseHalfRawCoverage
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseHalfCeilingProducer

/-! # Original-game uniform payoffs for both literal raw-table classes -/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

open QuittingLCPClassification

/-- The literal half-ceiling table has a contracting exact stationary Nash
root with selected hazards strictly below half and at least one active outsider. -/
theorem halfCeiling_exists_stationaryTerminalNash_uniformPayoff :
    ∃ root : Fin 4 → PMF Bool, ∃ value : Payoff (Fin 4),
      0 < hazardOfRoot root 0 ∧ hazardOfRoot root 0 < 1 / 2 ∧
      0 < hazardOfRoot root 1 ∧ hazardOfRoot root 1 < 1 / 2 ∧
      (∃ outsider, outsider ≠ 0 ∧ outsider ≠ 1 ∧ 0 < hazardOfRoot root outsider) ∧
      value = quittingTerminalPayoff halfCeilingReward
        (quittingStationaryProfile halfCeilingReward root) ∧
      (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
      (quittingGame halfCeilingReward).IsεAsymptoticNash
        (quittingTerminalPayoff halfCeilingReward) 0
        (quittingStationaryProfile halfCeilingReward root) ∧
      (quittingGame halfCeilingReward).IsUniformEquilibriumPayoff none value := by
  apply exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_halfStrictRaw
  · rw [halfCeiling_singletonMatrix, sourceSingletonMatrix_det]
    norm_num
  · intro row column
    rw [halfCeiling_singletonMatrix]
    exact sourceSingletonMatrix_inverse_pos row column
  · exact halfCeiling_strictRawGuards

/-- The literal unit table supplies all sixteen comparisons of the
matrix-free producer; this implication does not use its singleton matrix. -/
theorem unitCeiling_exists_uniformPayoff_of_oneSidedRaw :
    ∃ value : Payoff (Fin 4),
      (quittingGame unitCeilingReward).IsUniformEquilibriumPayoff none value :=
  exists_uniformPayoff_of_oneSidedWeakUnitRawGuards unitCeilingReward 0 1
    (by decide) unitCeiling_oneSidedWeakRawGuards

end GameTheory.GuardedCrossedResponseExamples
