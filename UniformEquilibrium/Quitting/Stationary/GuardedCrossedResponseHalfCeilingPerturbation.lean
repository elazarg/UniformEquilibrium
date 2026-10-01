import UniformEquilibrium.Quitting.Stationary.RewardCoordinatePerturbation
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseHalfCeilingBilinear
import MathUE.Polynomial.TensorBernsteinQuadraticPerturbation

/-! # Raw source errors imply the exact half-face Bernstein error array -/

noncomputable section

namespace GameTheory

private theorem halfFirstRow_corner_box (first second : Fin 2) :
    ∀ coordinate ∈ Finset.univ.erase (0 : Fin 4),
      0 ≤ halfFirstRow first.val second.val coordinate ∧
        halfFirstRow first.val second.val coordinate ≤ 1 := by
  intro coordinate _
  fin_cases first <;> fin_cases second <;> fin_cases coordinate <;>
    norm_num [halfFirstRow]

private theorem halfSecondRow_corner_box (first second : Fin 2) :
    ∀ coordinate ∈ Finset.univ.erase (1 : Fin 4),
      0 ≤ halfSecondRow first.val second.val coordinate ∧
        halfSecondRow first.val second.val coordinate ≤ 1 := by
  intro coordinate _
  fin_cases first <;> fin_cases second <;> fin_cases coordinate <;>
    norm_num [halfSecondRow]

private theorem halfFirstRow_corner_mass (first second : Fin 2) :
    1 - continueMassExcl (halfFirstRow first.val second.val) 0 =
      if first = 0 ∧ second = 0 then 1 / 2 else 1 := by
  rw [continueMassExcl,
    show Finset.univ.erase (0 : Fin 4) = {1, 2, 3} by decide]
  fin_cases first <;> fin_cases second <;> norm_num [halfFirstRow]

private theorem halfSecondRow_corner_mass (first second : Fin 2) :
    1 - continueMassExcl (halfSecondRow first.val second.val) 1 =
      if first = 0 ∧ second = 0 then 1 / 2 else 1 := by
  rw [continueMassExcl,
    show Finset.univ.erase (1 : Fin 4) = {0, 2, 3} by decide]
  fin_cases first <;> fin_cases second <;> norm_num [halfSecondRow]

private theorem abs_halfResidualCoefficient_sub_le
    (reward other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (error : ℝ)
    (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (row : ℝ → ℝ → Fin 4 → ℝ) (who : Fin 4)
    (residual : ({S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) → ℝ → ℝ → ℝ)
    (hbox : ∀ first second : Fin 2, ∀ coordinate ∈ Finset.univ.erase who,
      0 ≤ row first.val second.val coordinate ∧ row first.val second.val coordinate ≤ 1)
    (hmass : ∀ first second : Fin 2,
      1 - continueMassExcl (row first.val second.val) who =
        if first = 0 ∧ second = 0 then 1 / 2 else 1)
    (hshape : ∀ source x y, residual source x y =
      Math.bilinearSurvivalDifference (1 / 2)
        (fun x y => sigmaValue (weightOfReward source) (row x y) who)
        (fun x y => excludedValue (weightOfReward source) (row x y) who) x y)
    (first second : Fin 3) :
    |Math.quadraticTensorBernsteinCoefficient (residual other) first second -
      Math.quadraticTensorBernsteinCoefficient (residual reward) first second| ≤
      Math.halfSurvivalBernsteinErrorFactor first second * error := by
  have hfunction source : residual source =
      Math.bilinearSurvivalDifference (1 / 2)
        (fun x y => sigmaValue (weightOfReward source) (row x y) who)
        (fun x y => excludedValue (weightOfReward source) (row x y) who) := by
    funext x y
    exact hshape source x y
  rw [hfunction other, hfunction reward]
  apply Math.abs_halfSurvivalBernsteinCoefficient_sub_le
  · intro x y
    exact abs_sigmaValue_sub_le_of_coordinate_error reward other error hclose
      (row x.val y.val) who (hbox x y)
  · intro x y
    have h := abs_excludedValue_sub_le_of_coordinate_error reward other error hclose
      (row x.val y.val) who (hbox x y)
    simpa only [hmass x y, mul_comm] using h

/-- The first actual selected source polynomial has the packet's exact error array. -/
theorem abs_quittingHalfFirstResidual_coefficient_sub_le
    (reward other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (error : ℝ)
    (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (first second : Fin 3) :
    |Math.quadraticTensorBernsteinCoefficient (quittingHalfFirstResidual other) first second -
      Math.quadraticTensorBernsteinCoefficient (quittingHalfFirstResidual reward) first second| ≤
      Math.halfSurvivalBernsteinErrorFactor first second * error := by
  apply abs_halfResidualCoefficient_sub_le reward other error hclose halfFirstRow 0
    quittingHalfFirstResidual halfFirstRow_corner_box halfFirstRow_corner_mass
  intro source x y
  exact quittingHalfFirst_displacement_eq_canonical source x y

/-- The second actual selected source polynomial obeys the same exact error array. -/
theorem abs_quittingHalfSecondResidual_coefficient_sub_le
    (reward other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (error : ℝ)
    (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (first second : Fin 3) :
    |Math.quadraticTensorBernsteinCoefficient (quittingHalfSecondResidual other) first second -
      Math.quadraticTensorBernsteinCoefficient (quittingHalfSecondResidual reward) first second| ≤
      Math.halfSurvivalBernsteinErrorFactor first second * error := by
  apply abs_halfResidualCoefficient_sub_le reward other error hclose halfSecondRow 1
    quittingHalfSecondResidual halfSecondRow_corner_box halfSecondRow_corner_mass
  intro source x y
  exact quittingHalfSecond_displacement_eq_canonical source x y

end GameTheory
