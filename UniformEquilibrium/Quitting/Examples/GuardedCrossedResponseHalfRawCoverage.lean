import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseRawCoverage
import UniformEquilibrium.Quitting.Root.FinFourEndpointRowSum
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseHalfCeilingAdapter

/-! # Exact half-ceiling Bernstein arrays for the literal reward table -/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

open QuittingFinFourEndpointRows Math.Finset

private theorem first_sigma (x y : ℝ) :
    sigmaValue (weightOfReward halfCeilingReward) (halfFirstRow x y) 0 =
      3 * (1 - x) * (1 - y) - (4 / 3) * x * (1 - y) -
        (3 / 2) * (1 - x) * y - (3 / 2) * x * y := by
  rw [sigmaValue_eq_pureQuitEndpointRowSum]
  simp only [pureQuitEndpointRowSum, Fin.sum_univ_succ]
  simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ,
    halfFirstRow]
  norm_num +decide [weightOfReward, halfCeilingReward, coalitionCode]
  ring

private theorem first_excluded (x y : ℝ) :
    excludedValue (weightOfReward halfCeilingReward) (halfFirstRow x y) 0 =
      2 * (1 - x) * (1 - y) + x * (1 - y) / 2 + (1 - x) * y / 2 + x * y / 2 := by
  rw [excludedValue_eq_excludedEndpointRowSum]
  simp only [excludedEndpointRowSum, Fin.sum_univ_succ]
  simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ,
    halfFirstRow]
  norm_num +decide [weightOfReward, halfCeilingReward, coalitionCode]
  ring

private theorem second_sigma (x y : ℝ) :
    sigmaValue (weightOfReward halfCeilingReward) (halfSecondRow x y) 1 =
      2 * (1 - x) * (1 - y) - (463 / 182) * x * (1 - y) -
        (5 / 2) * (1 - x) * y - (5 / 2) * x * y := by
  rw [sigmaValue_eq_pureQuitEndpointRowSum]
  simp only [pureQuitEndpointRowSum, Fin.sum_univ_succ]
  simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ,
    halfSecondRow]
  norm_num +decide [weightOfReward, halfCeilingReward, coalitionCode]
  ring

private theorem second_excluded (x y : ℝ) :
    excludedValue (weightOfReward halfCeilingReward) (halfSecondRow x y) 1 =
      (3 / 2) * (1 - x) * (1 - y) -
        x * (1 - y) / 2 - (1 - x) * y / 2 - x * y / 2 := by
  rw [excludedValue_eq_excludedEndpointRowSum]
  simp only [excludedEndpointRowSum, Fin.sum_univ_succ]
  simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ,
    halfSecondRow]
  norm_num +decide [weightOfReward, halfCeilingReward, coalitionCode]
  ring

theorem halfCeiling_firstResidual (x y : ℝ) :
    quittingHalfFirstResidual halfCeilingReward x y =
      (1 - (1 / 2) * (1 - x) * (1 - y)) *
        (3 * (1 - x) * (1 - y) - (4 / 3) * x * (1 - y) -
          (3 / 2) * (1 - x) * y - (3 / 2) * x * y) -
        (2 * (1 - x) * (1 - y) + x * (1 - y) / 2 + (1 - x) * y / 2 + x * y / 2) := by
  have hopponents : Finset.univ.erase (0 : Fin 4) = {1, 2, 3} := by decide
  have hmass : continueMassExcl (halfFirstRow x y) 0 = (1 / 2) * (1 - x) * (1 - y) := by
    simp [continueMassExcl, hopponents, halfFirstRow, Finset.prod_insert]
    ring
  rw [quittingHalfFirstResidual, quittingDiscountedDisplacement, first_sigma,
    first_excluded, hmass]
  norm_num

theorem halfCeiling_secondResidual (x y : ℝ) :
    quittingHalfSecondResidual halfCeilingReward x y =
      (1 - (1 / 2) * (1 - x) * (1 - y)) *
        (2 * (1 - x) * (1 - y) - (463 / 182) * x * (1 - y) -
          (5 / 2) * (1 - x) * y - (5 / 2) * x * y) -
        ((3 / 2) * (1 - x) * (1 - y) -
          x * (1 - y) / 2 - (1 - x) * y / 2 - x * y / 2) := by
  have hopponents : Finset.univ.erase (1 : Fin 4) = {0, 2, 3} := by decide
  have hmass : continueMassExcl (halfSecondRow x y) 1 = (1 / 2) * (1 - x) * (1 - y) := by
    simp [continueMassExcl, hopponents, halfSecondRow, Finset.prod_insert]
    ring
  rw [quittingHalfSecondResidual, quittingDiscountedDisplacement, second_sigma,
    second_excluded, hmass]
  norm_num

def halfCeiling_firstBernsteinArray : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1 / 2, -1 / 8, -2; -1 / 12, -49 / 48, -2; -11 / 6, -23 / 12, -2]

def halfCeiling_secondBernsteinArray : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1 / 2, -1 / 8, -2; -99 / 728, -1563 / 1456, -2; -186 / 91, -184 / 91, -2]

theorem halfCeiling_firstCoefficient (first second : Fin 3) :
    Math.quadraticTensorBernsteinCoefficient (quittingHalfFirstResidual halfCeilingReward)
      first second = halfCeiling_firstBernsteinArray first second := by
  fin_cases first <;> fin_cases second <;>
    norm_num [Math.quadraticTensorBernsteinCoefficient, Math.quadraticBernsteinCoefficient,
      halfCeiling_firstResidual, halfCeiling_firstBernsteinArray]

theorem halfCeiling_secondCoefficient (first second : Fin 3) :
    Math.quadraticTensorBernsteinCoefficient (quittingHalfSecondResidual halfCeilingReward)
      first second = halfCeiling_secondBernsteinArray first second := by
  fin_cases first <;> fin_cases second <;>
    norm_num [Math.quadraticTensorBernsteinCoefficient, Math.quadraticBernsteinCoefficient,
      halfCeiling_secondResidual, halfCeiling_secondBernsteinArray]

theorem halfCeiling_strictBernsteinUpper : QuittingHalfStrictBernsteinUpper halfCeilingReward := by
  constructor
  · intro first second
    rw [halfCeiling_firstCoefficient]
    fin_cases first <;> fin_cases second <;> norm_num [halfCeiling_firstBernsteinArray]
  · intro first second
    rw [halfCeiling_secondCoefficient]
    fin_cases first <;> fin_cases second <;> norm_num [halfCeiling_secondBernsteinArray]

theorem halfCeiling_strictRawGuards : QuittingHalfStrictRawGuards halfCeilingReward :=
  ⟨halfCeiling_lowerFirst, halfCeiling_lowerSecond, halfCeiling_strictBernsteinUpper⟩

end GameTheory.GuardedCrossedResponseExamples
