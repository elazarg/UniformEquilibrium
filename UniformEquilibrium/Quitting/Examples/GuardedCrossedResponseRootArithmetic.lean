import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseTables
import UniformEquilibrium.Quitting.Root.FinFourEndpointRowSum
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseRawResidual

/-! # Exact residual and deleted-clock arithmetic at the two literal roots -/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

open QuittingFinFourEndpointRows Math.Finset

def halfCeilingHazard : Fin 4 → ℝ := ![2 / 9, 1 / 4, 1 / 3, 0]
def unitCeilingHazard : Fin 4 → ℝ := ![5 / 7, 2 / 3, 1, 1]

def halfCeilingValue : Payoff (Fin 4) := ![3 / 2, 5 / 13, 53 / 21, 15 / 22]
def unitCeilingValue : Payoff (Fin 4) := ![0, -19 / 7, -29 / 21, 2 / 7]

theorem halfCeiling_hazard_bounds (who : Fin 4) :
    0 ≤ halfCeilingHazard who ∧ halfCeilingHazard who ≤ 1 := by
  fin_cases who <;> norm_num [halfCeilingHazard]

theorem unitCeiling_hazard_bounds (who : Fin 4) :
    0 ≤ unitCeilingHazard who ∧ unitCeilingHazard who ≤ 1 := by
  fin_cases who <;> norm_num [unitCeilingHazard]

theorem halfCeiling_sigmaValue (who : Fin 4) :
    sigmaValue (weightOfReward halfCeilingReward) halfCeilingHazard who =
      ![3 / 2, 5 / 13, 53 / 21, 49 / 108] who := by
  rw [sigmaValue_eq_pureQuitEndpointRowSum]
  fin_cases who
  all_goals
    simp only [pureQuitEndpointRowSum, Fin.sum_univ_succ]
    simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ,
      halfCeilingHazard]
    norm_num +decide [weightOfReward, halfCeilingReward, coalitionCode]

theorem halfCeiling_excludedValue (who : Fin 4) :
    excludedValue (weightOfReward halfCeilingReward) halfCeilingHazard who =
      ![3 / 4, 5 / 27, 265 / 252, 5 / 12] who := by
  rw [excludedValue_eq_excludedEndpointRowSum]
  fin_cases who
  all_goals
    simp only [excludedEndpointRowSum, Fin.sum_univ_succ]
    simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ,
      halfCeilingHazard]
    norm_num +decide [weightOfReward, halfCeilingReward, coalitionCode]

theorem unitCeiling_sigmaValue (who : Fin 4) :
    sigmaValue (weightOfReward unitCeilingReward) unitCeilingHazard who =
      ![0, -19 / 7, -29 / 21, 2 / 7] who := by
  rw [sigmaValue_eq_pureQuitEndpointRowSum]
  fin_cases who
  all_goals
    simp only [pureQuitEndpointRowSum, Fin.sum_univ_succ]
    simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ,
      unitCeilingHazard]
    norm_num +decide [weightOfReward, unitCeilingReward, coalitionCode]

theorem unitCeiling_excludedValue (who : Fin 4) :
    excludedValue (weightOfReward unitCeilingReward) unitCeilingHazard who =
      ![0, -19 / 7, -10 / 7, -5 / 21] who := by
  rw [excludedValue_eq_excludedEndpointRowSum]
  fin_cases who
  all_goals
    simp only [excludedEndpointRowSum, Fin.sum_univ_succ]
    simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ,
      unitCeilingHazard]
    norm_num +decide [weightOfReward, unitCeilingReward, coalitionCode]

theorem halfCeiling_continueMassExcl (who : Fin 4) :
    continueMassExcl halfCeilingHazard who = ![1 / 2, 14 / 27, 7 / 12, 7 / 18] who := by
  fin_cases who
  · change continueMassExcl halfCeilingHazard (0 : Fin 4) = 1 / 2
    rw [continueMassExcl,
      show Finset.univ.erase (0 : Fin 4) = {1, 2, 3} by decide]
    norm_num [halfCeilingHazard, Finset.prod_insert]
  · change continueMassExcl halfCeilingHazard (1 : Fin 4) = 14 / 27
    rw [continueMassExcl,
      show Finset.univ.erase (1 : Fin 4) = {0, 2, 3} by decide]
    norm_num [halfCeilingHazard, Finset.prod_insert]
  · change continueMassExcl halfCeilingHazard (2 : Fin 4) = 7 / 12
    rw [continueMassExcl,
      show Finset.univ.erase (2 : Fin 4) = {0, 1, 3} by decide]
    norm_num [halfCeilingHazard, Finset.prod_insert]
  · change continueMassExcl halfCeilingHazard (3 : Fin 4) = 7 / 18
    rw [continueMassExcl,
      show Finset.univ.erase (3 : Fin 4) = {0, 1, 2} by decide]
    norm_num [halfCeilingHazard, Finset.prod_insert]

theorem unitCeiling_continueMassExcl (who : Fin 4) :
    continueMassExcl unitCeilingHazard who = 0 := by
  fin_cases who
  · change continueMassExcl unitCeilingHazard (0 : Fin 4) = 0
    rw [continueMassExcl,
      show Finset.univ.erase (0 : Fin 4) = {1, 2, 3} by decide]
    norm_num [unitCeilingHazard, Finset.prod_insert]
  · change continueMassExcl unitCeilingHazard (1 : Fin 4) = 0
    rw [continueMassExcl,
      show Finset.univ.erase (1 : Fin 4) = {0, 2, 3} by decide]
    norm_num [unitCeilingHazard, Finset.prod_insert]
  · change continueMassExcl unitCeilingHazard (2 : Fin 4) = 0
    rw [continueMassExcl,
      show Finset.univ.erase (2 : Fin 4) = {0, 1, 3} by decide]
    norm_num [unitCeilingHazard, Finset.prod_insert]
  · change continueMassExcl unitCeilingHazard (3 : Fin 4) = 0
    rw [continueMassExcl,
      show Finset.univ.erase (3 : Fin 4) = {0, 1, 2} by decide]
    norm_num [unitCeilingHazard, Finset.prod_insert]

theorem halfCeiling_displacement (who : Fin 4) :
    quittingDiscountedDisplacement halfCeilingReward 0 halfCeilingHazard who =
      ![0, 0, 0, -271 / 1944] who := by
  rw [quittingDiscountedDisplacement, halfCeiling_sigmaValue, halfCeiling_excludedValue,
    halfCeiling_continueMassExcl]
  fin_cases who <;> norm_num

theorem unitCeiling_displacement (who : Fin 4) :
    quittingDiscountedDisplacement unitCeilingReward 0 unitCeilingHazard who =
      ![0, 0, 1 / 21, 11 / 21] who := by
  rw [quittingDiscountedDisplacement, unitCeiling_sigmaValue, unitCeiling_excludedValue,
    unitCeiling_continueMassExcl]
  fin_cases who <;> norm_num [unitCeilingValue]

theorem halfCeiling_jointSurvival :
    (∏ who : Fin 4, (1 - halfCeilingHazard who)) = 7 / 18 := by
  norm_num [Fin.prod_univ_succ, halfCeilingHazard]

theorem unitCeiling_jointSurvival :
    (∏ who : Fin 4, (1 - unitCeilingHazard who)) = 0 := by
  norm_num [Fin.prod_univ_succ, unitCeilingHazard]

end GameTheory.GuardedCrossedResponseExamples
