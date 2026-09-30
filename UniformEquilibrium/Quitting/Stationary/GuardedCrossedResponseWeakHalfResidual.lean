import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseWeakHalfLower

/-! # Exact half-face reward perturbations and coefficient strictification -/

noncomputable section

namespace GameTheory

private theorem first_opponent_complements :
    ({1, 2, 3} : Finset (Fin 4)) \ {1} = {2, 3} ∧
    ({1, 2, 3} : Finset (Fin 4)) \ {2} = {1, 3} ∧
    ({1, 2, 3} : Finset (Fin 4)) \ {3} = {1, 2} ∧
    ({1, 2, 3} : Finset (Fin 4)) \ {1, 2} = {3} ∧
    ({1, 2, 3} : Finset (Fin 4)) \ {1, 3} = {2} ∧
    ({1, 2, 3} : Finset (Fin 4)) \ {2, 3} = {1} ∧
    ({1, 2, 3} : Finset (Fin 4)) \ {1, 2, 3} = ∅ := by decide

private theorem second_opponent_complements :
    ({0, 2, 3} : Finset (Fin 4)) \ {0} = {2, 3} ∧
    ({0, 2, 3} : Finset (Fin 4)) \ {2} = {0, 3} ∧
    ({0, 2, 3} : Finset (Fin 4)) \ {3} = {0, 2} ∧
    ({0, 2, 3} : Finset (Fin 4)) \ {0, 2} = {3} ∧
    ({0, 2, 3} : Finset (Fin 4)) \ {0, 3} = {2} ∧
    ({0, 2, 3} : Finset (Fin 4)) \ {2, 3} = {0} ∧
    ({0, 2, 3} : Finset (Fin 4)) \ {0, 2, 3} = ∅ := by decide

private theorem first_half_sigma_perturb
    (epsilon : ℝ)
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (x y : ℝ) :
    sigmaValue (weightOfReward (quittingCrossedWeakHalfPerturb epsilon reward))
        (halfFirstRow x y) 0 =
      sigmaValue (weightOfReward reward) (halfFirstRow x y) 0 - 3 * epsilon / 2 := by
  have hopponents : Finset.univ.erase (0 : Fin 4) = {1, 2, 3} := by decide
  have hpowerset : ({1, 2, 3} : Finset (Fin 4)).powerset =
      {∅, {1}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}, {1, 2, 3}} := by decide
  rcases first_opponent_complements with ⟨h1, h2, h3, h12, h13, h23, -⟩
  simp +decide [sigmaValue, hopponents, hpowerset, halfFirstRow,
    weightOfReward, quittingCrossedWeakHalfPerturb, Finset.sum_insert, Finset.prod_insert,
    h1, h2, h3, h12, h13, h23]
  ring

private theorem second_half_sigma_perturb
    (epsilon : ℝ)
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (x y : ℝ) :
    sigmaValue (weightOfReward (quittingCrossedWeakHalfPerturb epsilon reward))
        (halfSecondRow x y) 1 =
      sigmaValue (weightOfReward reward) (halfSecondRow x y) 1 - 3 * epsilon / 2 := by
  have hopponents : Finset.univ.erase (1 : Fin 4) = {0, 2, 3} := by decide
  have hpowerset : ({0, 2, 3} : Finset (Fin 4)).powerset =
      {∅, {0}, {2}, {3}, {0, 2}, {0, 3}, {2, 3}, {0, 2, 3}} := by decide
  rcases second_opponent_complements with ⟨h0, h2, h3, h02, h03, h23, -⟩
  simp +decide [sigmaValue, hopponents, hpowerset, halfSecondRow,
    weightOfReward, quittingCrossedWeakHalfPerturb, Finset.sum_insert, Finset.prod_insert,
    h0, h2, h3, h02, h03, h23]
  ring

private theorem first_half_excluded_perturb
    (epsilon : ℝ)
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (x y : ℝ) :
    excludedValue (weightOfReward (quittingCrossedWeakHalfPerturb epsilon reward))
        (halfFirstRow x y) 0 =
      excludedValue (weightOfReward reward) (halfFirstRow x y) 0 - epsilon / 2 := by
  have hopponents : Finset.univ.erase (0 : Fin 4) = {1, 2, 3} := by decide
  have hpowerset : ({1, 2, 3} : Finset (Fin 4)).powerset.erase ∅ =
      {{1}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}, {1, 2, 3}} := by decide
  rcases first_opponent_complements with ⟨h1, h2, h3, h12, h13, h23, -⟩
  simp +decide [excludedValue, hopponents, hpowerset, halfFirstRow,
    weightOfReward, quittingCrossedWeakHalfPerturb, Finset.sum_insert, Finset.prod_insert,
    h1, h2, h3, h12, h13, h23]
  ring

private theorem second_half_excluded_perturb
    (epsilon : ℝ)
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (x y : ℝ) :
    excludedValue (weightOfReward (quittingCrossedWeakHalfPerturb epsilon reward))
        (halfSecondRow x y) 1 =
      excludedValue (weightOfReward reward) (halfSecondRow x y) 1 - epsilon / 2 := by
  have hopponents : Finset.univ.erase (1 : Fin 4) = {0, 2, 3} := by decide
  have hpowerset : ({0, 2, 3} : Finset (Fin 4)).powerset.erase ∅ =
      {{0}, {2}, {3}, {0, 2}, {0, 3}, {2, 3}, {0, 2, 3}} := by decide
  rcases second_opponent_complements with ⟨h0, h2, h3, h02, h03, h23, -⟩
  simp +decide [excludedValue, hopponents, hpowerset, halfSecondRow,
    weightOfReward, quittingCrossedWeakHalfPerturb, Finset.sum_insert, Finset.prod_insert,
    h0, h2, h3, h02, h03, h23]
  ring

/-- Equation (6.2) on the first selected half face, for all ambient outsider rates. -/
theorem quittingHalfFirstResidual_weakHalfPerturb
    (epsilon : ℝ)
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (x y : ℝ) :
    quittingHalfFirstResidual (quittingCrossedWeakHalfPerturb epsilon reward) x y =
      quittingHalfFirstResidual reward x y - epsilon +
        (3 * epsilon / 4) * (1 - x) * (1 - y) := by
  have hmass : continueMassExcl (halfFirstRow x y) 0 =
      (1 / 2) * (1 - x) * (1 - y) := by
    rw [continueMassExcl, show Finset.univ.erase (0 : Fin 4) = {1, 2, 3} by decide]
    simp [halfFirstRow]
    ring
  simp only [quittingHalfFirstResidual, quittingDiscountedDisplacement,
    first_half_sigma_perturb, first_half_excluded_perturb, hmass]
  ring

/-- Equation (6.2) on the second selected half face. -/
theorem quittingHalfSecondResidual_weakHalfPerturb
    (epsilon : ℝ)
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (x y : ℝ) :
    quittingHalfSecondResidual (quittingCrossedWeakHalfPerturb epsilon reward) x y =
      quittingHalfSecondResidual reward x y - epsilon +
        (3 * epsilon / 4) * (1 - x) * (1 - y) := by
  have hmass : continueMassExcl (halfSecondRow x y) 1 =
      (1 / 2) * (1 - x) * (1 - y) := by
    rw [continueMassExcl, show Finset.univ.erase (1 : Fin 4) = {0, 2, 3} by decide]
    simp [halfSecondRow]
    ring
  simp only [quittingHalfSecondResidual, quittingDiscountedDisplacement,
    second_half_sigma_perturb, second_half_excluded_perturb, hmass]
  ring

/-- The weak eighteen coefficient tests on the literal reward residuals. -/
structure QuittingHalfWeakBernsteinUpper
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) : Prop where
  first : ∀ indexX indexY : Fin 3,
    Math.quadraticTensorBernsteinCoefficient (quittingHalfFirstResidual reward) indexX indexY ≤ 0
  second : ∀ indexX indexY : Fin 3,
    Math.quadraticTensorBernsteinCoefficient (quittingHalfSecondResidual reward) indexX indexY ≤ 0

private theorem tensorCoefficient_halfPerturb
    (function : ℝ → ℝ → ℝ) (epsilon : ℝ) (u v : Fin 3) :
    Math.quadraticTensorBernsteinCoefficient
        (fun x y => function x y - epsilon +
          (3 * epsilon / 4) * (1 - x) * (1 - y)) u v =
      Math.quadraticTensorBernsteinCoefficient function u v - epsilon +
        (3 * epsilon / 4) * (1 - (u.val : ℝ) / 2) *
          (1 - (v.val : ℝ) / 2) := by
  fin_cases u <;> fin_cases v <;>
    simp [Math.quadraticTensorBernsteinCoefficient, Math.quadraticBernsteinCoefficient] <;> ring

private theorem tensorCoefficient_halfPerturb_lt_zero
    (function : ℝ → ℝ → ℝ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (u v : Fin 3) (hweak : Math.quadraticTensorBernsteinCoefficient function u v ≤ 0) :
    Math.quadraticTensorBernsteinCoefficient
      (fun x y => function x y - epsilon +
        (3 * epsilon / 4) * (1 - x) * (1 - y)) u v < 0 := by
  rw [tensorCoefficient_halfPerturb]
  fin_cases u <;> fin_cases v <;> norm_num at * <;> linarith

/-- Each weak coefficient becomes strict under the actual reward perturbation. -/
theorem quittingHalf_strictBernsteinUpper_of_weakHalfPerturb
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hweak : QuittingHalfWeakBernsteinUpper reward) :
    QuittingHalfStrictBernsteinUpper (quittingCrossedWeakHalfPerturb epsilon reward) := by
  have hfirst : quittingHalfFirstResidual (quittingCrossedWeakHalfPerturb epsilon reward) =
      fun x y => quittingHalfFirstResidual reward x y - epsilon +
        (3 * epsilon / 4) * (1 - x) * (1 - y) := by
    funext x y
    exact quittingHalfFirstResidual_weakHalfPerturb epsilon reward x y
  have hsecond : quittingHalfSecondResidual (quittingCrossedWeakHalfPerturb epsilon reward) =
      fun x y => quittingHalfSecondResidual reward x y - epsilon +
        (3 * epsilon / 4) * (1 - x) * (1 - y) := by
    funext x y
    exact quittingHalfSecondResidual_weakHalfPerturb epsilon reward x y
  constructor
  · intro u v
    rw [hfirst]
    exact tensorCoefficient_halfPerturb_lt_zero _ epsilon hepsilon u v (hweak.first u v)
  · intro u v
    rw [hsecond]
    exact tensorCoefficient_halfPerturb_lt_zero _ epsilon hepsilon u v (hweak.second u v)

end GameTheory
