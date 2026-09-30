import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseRootArithmetic
import UniformEquilibrium.Quitting.Stationary.EndpointCompiler

/-! # Actual stationary profiles and complete caps at the two exact roots -/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

open _root_.Math.Probability _root_.Math.PMFProduct

def halfCeilingRoot : Fin 4 → PMF Bool :=
  rootOfHazard halfCeilingHazard
    (fun who => (halfCeiling_hazard_bounds who).1)
    (fun who => (halfCeiling_hazard_bounds who).2)

def unitCeilingRoot : Fin 4 → PMF Bool :=
  rootOfHazard unitCeilingHazard
    (fun who => (unitCeiling_hazard_bounds who).1)
    (fun who => (unitCeiling_hazard_bounds who).2)

theorem halfCeilingRoot_hazard : hazardOfRoot halfCeilingRoot = halfCeilingHazard :=
  hazardOfRoot_rootOfHazard _ _ _

theorem unitCeilingRoot_hazard : hazardOfRoot unitCeilingRoot = unitCeilingHazard :=
  hazardOfRoot_rootOfHazard _ _ _

private theorem deletedContinueMass_eq (root : Fin 4 → PMF Bool) (who : Fin 4) :
    quittingStationaryFixedOpponentsContinueMass root who =
      continueMassExcl (hazardOfRoot root) who := by
  change quittingStationaryContinueMass (Function.update root who (PMF.pure false)) = _
  rw [quittingStationaryContinueMass_eq_hazard_split _ who]
  have hself : hazardOfRoot (Function.update root who (PMF.pure false)) who = 0 := by
    simp [hazardOfRoot]
  rw [hself, sub_zero, one_mul]
  unfold continueMassExcl
  apply Finset.prod_congr rfl
  intro other hother
  simp [hazardOfRoot, Finset.ne_of_mem_erase hother]

theorem halfCeilingRoot_deletedSurvival (who : Fin 4) :
    quittingStationaryFixedOpponentsContinueMass halfCeilingRoot who =
      ![1 / 2, 14 / 27, 7 / 12, 7 / 18] who := by
  rw [deletedContinueMass_eq, halfCeilingRoot_hazard, halfCeiling_continueMassExcl]

theorem unitCeilingRoot_deletedSurvival (who : Fin 4) :
    quittingStationaryFixedOpponentsContinueMass unitCeilingRoot who = 0 := by
  rw [deletedContinueMass_eq, unitCeilingRoot_hazard, unitCeiling_continueMassExcl]

theorem halfCeilingRoot_contracts (who : Fin 4) :
    quittingStationaryFixedOpponentsContinueMass halfCeilingRoot who < 1 := by
  rw [halfCeilingRoot_deletedSurvival]
  fin_cases who <;> norm_num

theorem unitCeilingRoot_contracts (who : Fin 4) :
    quittingStationaryFixedOpponentsContinueMass unitCeilingRoot who < 1 := by
  rw [unitCeilingRoot_deletedSurvival]
  norm_num

theorem halfCeilingRoot_jointSurvival :
    quittingStationaryContinueMass halfCeilingRoot = 7 / 18 := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp_rw [pmfBool_false_toReal]
  change (∏ who, (1 - hazardOfRoot halfCeilingRoot who)) = 7 / 18
  rw [halfCeilingRoot_hazard]
  exact halfCeiling_jointSurvival

theorem unitCeilingRoot_jointSurvival : quittingStationaryContinueMass unitCeilingRoot = 0 := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp_rw [pmfBool_false_toReal]
  change (∏ who, (1 - hazardOfRoot unitCeilingRoot who)) = 0
  rw [unitCeilingRoot_hazard]
  exact unitCeiling_jointSurvival

theorem halfCeilingRoot_bellman :
    halfCeilingValue = quittingRootSuccessorPayoff halfCeilingReward halfCeilingValue
      halfCeilingRoot := by
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix, quittingRootQuitPayoff_eq_sigmaValue,
    quittingRootContinuePayoff_eq_gammaValue, pmfBool_false_toReal]
  change halfCeilingValue who = hazardOfRoot halfCeilingRoot who * _ +
    (1 - hazardOfRoot halfCeilingRoot who) * _
  rw [halfCeilingRoot_hazard]
  rw [gammaValue, halfCeiling_sigmaValue, halfCeiling_excludedValue,
    halfCeiling_continueMassExcl]
  fin_cases who <;> norm_num [halfCeilingValue, halfCeilingHazard]

theorem unitCeilingRoot_bellman :
    unitCeilingValue = quittingRootSuccessorPayoff unitCeilingReward unitCeilingValue
      unitCeilingRoot := by
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix, quittingRootQuitPayoff_eq_sigmaValue,
    quittingRootContinuePayoff_eq_gammaValue, pmfBool_false_toReal]
  change unitCeilingValue who = hazardOfRoot unitCeilingRoot who * _ +
    (1 - hazardOfRoot unitCeilingRoot who) * _
  rw [unitCeilingRoot_hazard]
  rw [gammaValue, unitCeiling_sigmaValue, unitCeiling_excludedValue,
    unitCeiling_continueMassExcl]
  fin_cases who <;> norm_num [unitCeilingValue, unitCeilingHazard]

theorem halfCeilingRoot_endpointNash :
    IsεQuittingRootEndpointNash halfCeilingReward halfCeilingValue 0 halfCeilingRoot := by
  intro who
  rw [quittingRootEndpointDifference, quittingRootQuitPayoff_eq_sigmaValue,
    quittingRootContinuePayoff_eq_gammaValue, pmfBool_false_toReal]
  simp only [neg_zero]
  change (1 - hazardOfRoot halfCeilingRoot who) * (_ - _) ≤ 0 ∧
    0 ≤ hazardOfRoot halfCeilingRoot who * (_ - _)
  rw [halfCeilingRoot_hazard]
  rw [gammaValue, halfCeiling_sigmaValue, halfCeiling_excludedValue,
    halfCeiling_continueMassExcl]
  fin_cases who <;> norm_num [halfCeilingValue, halfCeilingHazard]

theorem unitCeilingRoot_endpointNash :
    IsεQuittingRootEndpointNash unitCeilingReward unitCeilingValue 0 unitCeilingRoot := by
  intro who
  rw [quittingRootEndpointDifference, quittingRootQuitPayoff_eq_sigmaValue,
    quittingRootContinuePayoff_eq_gammaValue, pmfBool_false_toReal]
  simp only [neg_zero]
  change (1 - hazardOfRoot unitCeilingRoot who) * (_ - _) ≤ 0 ∧
    0 ≤ hazardOfRoot unitCeilingRoot who * (_ - _)
  rw [unitCeilingRoot_hazard]
  rw [gammaValue, unitCeiling_sigmaValue, unitCeiling_excludedValue,
    unitCeiling_continueMassExcl]
  fin_cases who <;> norm_num [unitCeilingValue, unitCeilingHazard]

private theorem halfCeilingRoot_absorbs : quittingStationaryContinueMass halfCeilingRoot < 1 := by
  rw [halfCeilingRoot_jointSurvival]
  norm_num

private theorem unitCeilingRoot_absorbs : quittingStationaryContinueMass unitCeilingRoot < 1 := by
  rw [unitCeilingRoot_jointSurvival]
  norm_num

theorem halfCeilingRoot_terminalPayoff :
    quittingTerminalPayoff halfCeilingReward
      (quittingStationaryProfile halfCeilingReward halfCeilingRoot) = halfCeilingValue :=
  quittingTerminalPayoff_stationary_eq_of_fixedPoint _ _ _
    halfCeilingRoot_absorbs halfCeilingRoot_bellman

theorem unitCeilingRoot_terminalPayoff :
    quittingTerminalPayoff unitCeilingReward
      (quittingStationaryProfile unitCeilingReward unitCeilingRoot) = unitCeilingValue :=
  quittingTerminalPayoff_stationary_eq_of_fixedPoint _ _ _
    unitCeilingRoot_absorbs unitCeilingRoot_bellman

theorem halfCeilingRoot_fullCap (who : Fin 4) :
    quittingStationaryFullRateUnilateralCap halfCeilingReward halfCeilingRoot who =
      halfCeilingValue who :=
  quittingStationaryFullRateUnilateralCap_eq_of_fixedPoint_endpointNash _ _ _
    halfCeilingRoot_absorbs halfCeilingRoot_bellman halfCeilingRoot_endpointNash
    (isQuittingStationaryBoundaryAdmissible_of_contracts _ _ _ halfCeilingRoot_contracts) who

theorem unitCeilingRoot_fullCap (who : Fin 4) :
    quittingStationaryFullRateUnilateralCap unitCeilingReward unitCeilingRoot who =
      unitCeilingValue who :=
  quittingStationaryFullRateUnilateralCap_eq_of_fixedPoint_endpointNash _ _ _
    unitCeilingRoot_absorbs unitCeilingRoot_bellman unitCeilingRoot_endpointNash
    (isQuittingStationaryBoundaryAdmissible_of_contracts _ _ _ unitCeilingRoot_contracts) who

theorem halfCeilingRoot_terminalNash :
    (quittingGame halfCeilingReward).IsεAsymptoticNash (quittingTerminalPayoff halfCeilingReward)
      0 (quittingStationaryProfile halfCeilingReward halfCeilingRoot) :=
  isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts _ _ _
    halfCeilingRoot_absorbs halfCeilingRoot_bellman halfCeilingRoot_endpointNash
    halfCeilingRoot_contracts

theorem unitCeilingRoot_terminalNash :
    (quittingGame unitCeilingReward).IsεAsymptoticNash (quittingTerminalPayoff unitCeilingReward)
      0 (quittingStationaryProfile unitCeilingReward unitCeilingRoot) :=
  isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts _ _ _
    unitCeilingRoot_absorbs unitCeilingRoot_bellman unitCeilingRoot_endpointNash
    unitCeilingRoot_contracts

theorem halfCeilingValue_uniformPayoff :
    (quittingGame halfCeilingReward).IsUniformEquilibriumPayoff none halfCeilingValue :=
  isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts _ _ _
    halfCeilingRoot_absorbs halfCeilingRoot_bellman halfCeilingRoot_endpointNash
    halfCeilingRoot_contracts

theorem unitCeilingValue_uniformPayoff :
    (quittingGame unitCeilingReward).IsUniformEquilibriumPayoff none unitCeilingValue :=
  isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts _ _ _
    unitCeilingRoot_absorbs unitCeilingRoot_bellman unitCeilingRoot_endpointNash
    unitCeilingRoot_contracts

end GameTheory.GuardedCrossedResponseExamples
