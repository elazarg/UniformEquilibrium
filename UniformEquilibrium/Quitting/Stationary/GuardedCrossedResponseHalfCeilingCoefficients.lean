import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseHalfCeilingBilinear
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseHalfCeilingSign

/-! # Nine finite coefficient tests for the actual four-player residual rows -/

noncomputable section

namespace GameTheory

/-- The first actual reward row has its exact degree-(2,2) Bernstein expansion. -/
theorem quittingHalfFirstResidual_eq_tensorBernstein
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (x y : ℝ) :
    quittingHalfFirstResidual reward x y =
      ∑ first : Fin 3, ∑ second : Fin 3,
        quittingHalfTensorCoefficient (quittingHalfFirstResidual reward) first second *
          quittingHalfBernsteinBasis first x * quittingHalfBernsteinBasis second y := by
  have hfunction : quittingHalfFirstResidual reward =
      quittingHalfCanonicalResidual
        (fun x y => sigmaValue (weightOfReward reward) (halfFirstRow x y) 0)
        (fun x y => excludedValue (weightOfReward reward) (halfFirstRow x y) 0) := by
    funext x y
    exact quittingHalfFirst_displacement_eq_canonical reward x y
  rw [hfunction]
  exact quittingHalfCanonicalResidual_eq_tensorBernstein _ _ x y

/-- The second actual reward row has its exact degree-(2,2) Bernstein expansion. -/
theorem quittingHalfSecondResidual_eq_tensorBernstein
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (x y : ℝ) :
    quittingHalfSecondResidual reward x y =
      ∑ first : Fin 3, ∑ second : Fin 3,
        quittingHalfTensorCoefficient (quittingHalfSecondResidual reward) first second *
          quittingHalfBernsteinBasis first x * quittingHalfBernsteinBasis second y := by
  have hfunction : quittingHalfSecondResidual reward =
      quittingHalfCanonicalResidual
        (fun x y => sigmaValue (weightOfReward reward) (halfSecondRow x y) 1)
        (fun x y => excludedValue (weightOfReward reward) (halfSecondRow x y) 1) := by
    funext x y
    exact quittingHalfSecond_displacement_eq_canonical reward x y
  rw [hfunction]
  exact quittingHalfCanonicalResidual_eq_tensorBernstein _ _ x y

/-- All eighteen strict coefficient tests from the packet, with no sampled
root or polynomial expansion supplied as a hypothesis. -/
structure QuittingHalfStrictBernsteinUpper
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) : Prop where
  first : ∀ indexX indexY : Fin 3,
    quittingHalfTensorCoefficient (quittingHalfFirstResidual reward) indexX indexY < 0
  second : ∀ indexX indexY : Fin 3,
    quittingHalfTensorCoefficient (quittingHalfSecondResidual reward) indexX indexY < 0

/-- Strict first-row coefficient negativity gives the full closed-square guard. -/
theorem quittingHalfFirstResidual_neg_of_coefficients
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hcoeff : QuittingHalfStrictBernsteinUpper reward)
    (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    quittingHalfFirstResidual reward x y < 0 := by
  rw [quittingHalfFirstResidual_eq_tensorBernstein]
  exact quittingHalfTensor_sum_neg_of_coefficients_neg
    _ x y hx hy hcoeff.first

/-- Strict second-row coefficient negativity gives the full closed-square guard. -/
theorem quittingHalfSecondResidual_neg_of_coefficients
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hcoeff : QuittingHalfStrictBernsteinUpper reward)
    (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    quittingHalfSecondResidual reward x y < 0 := by
  rw [quittingHalfSecondResidual_eq_tensorBernstein]
  exact quittingHalfTensor_sum_neg_of_coefficients_neg
    _ x y hx hy hcoeff.second

end GameTheory
