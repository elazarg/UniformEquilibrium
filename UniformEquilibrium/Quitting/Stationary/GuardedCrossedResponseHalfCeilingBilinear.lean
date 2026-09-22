import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseHalfCeilingBernstein
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseHalfCeilingMultiaffine

/-! # Four-player half-ceiling residual is biquadratic in its two outsider rates -/

noncomputable section

namespace GameTheory

def halfFirstRow (x y : ℝ) : Fin 4 → ℝ := ![0, 1 / 2, x, y]
def halfSecondRow (x y : ℝ) : Fin 4 → ℝ := ![1 / 2, 0, x, y]

/-- The packet's first selected half-ceiling polynomial in outsider rates. -/
def quittingHalfFirstResidual
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (x y : ℝ) : ℝ :=
  quittingDiscountedDisplacement reward 0 (halfFirstRow x y) 0

/-- The packet's second selected half-ceiling polynomial in outsider rates. -/
def quittingHalfSecondResidual
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (x y : ℝ) : ℝ :=
  quittingDiscountedDisplacement reward 0 (halfSecondRow x y) 1

/-- Corner interpolation for a two-variable affine-in-each-coordinate function. -/
def quittingHalfBilinearInterpolation (function : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  (1 - x) * (1 - y) * function 0 0 +
    x * (1 - y) * function 1 0 +
      (1 - x) * y * function 0 1 + x * y * function 1 1

private theorem halfFirstRow_update_two (x y : ℝ) :
    Function.update (halfFirstRow 0 y) 2 x = halfFirstRow x y := by
  funext coordinate
  fin_cases coordinate <;> simp [halfFirstRow]

private theorem halfFirstRow_update_three (x y : ℝ) :
    Function.update (halfFirstRow x 0) 3 y = halfFirstRow x y := by
  funext coordinate
  fin_cases coordinate <;> simp [halfFirstRow]

private theorem halfSecondRow_update_two (x y : ℝ) :
    Function.update (halfSecondRow 0 y) 2 x = halfSecondRow x y := by
  funext coordinate
  fin_cases coordinate <;> simp [halfSecondRow]

private theorem halfSecondRow_update_three (x y : ℝ) :
    Function.update (halfSecondRow x 0) 3 y = halfSecondRow x y := by
  funext coordinate
  fin_cases coordinate <;> simp [halfSecondRow]

private theorem halfRowValue_bilinear
    (row : ℝ → ℝ → Fin 4 → ℝ) (value : (Fin 4 → ℝ) → ℝ)
    (hrowTwo : ∀ x y, Function.update (row 0 y) 2 x = row x y)
    (hrowThree : ∀ x y, Function.update (row x 0) 3 y = row x y)
    (hvalueTwo : ∀ hazard rate,
      value (Function.update hazard 2 rate) =
        (1 - rate) * value (Function.update hazard 2 0) +
          rate * value (Function.update hazard 2 1))
    (hvalueThree : ∀ hazard rate,
      value (Function.update hazard 3 rate) =
        (1 - rate) * value (Function.update hazard 3 0) +
          rate * value (Function.update hazard 3 1))
    (x y : ℝ) :
    value (row x y) = quittingHalfBilinearInterpolation
      (fun x y => value (row x y)) x y := by
  have hx := hvalueTwo (row 0 y) x
  rw [hrowTwo x y, hrowTwo 0 y, hrowTwo 1 y] at hx
  have hy0 := hvalueThree (row 0 0) y
  rw [hrowThree 0 y, hrowThree 0 0, hrowThree 0 1] at hy0
  have hy1 := hvalueThree (row 1 0) y
  rw [hrowThree 1 y, hrowThree 1 0, hrowThree 1 1] at hy1
  rw [hx, hy0, hy1]
  unfold quittingHalfBilinearInterpolation
  ring

/-- The actual pure-Quit sum at the first selected half face is bilinear. -/
theorem quittingHalfFirst_sigmaValue_bilinear
    (weight : Finset (Fin 4) → Fin 4 → ℝ) (x y : ℝ) :
    sigmaValue weight (halfFirstRow x y) 0 =
      quittingHalfBilinearInterpolation
        (fun x y => sigmaValue weight (halfFirstRow x y) 0) x y := by
  refine halfRowValue_bilinear halfFirstRow
    (fun hazard => sigmaValue weight hazard 0)
    halfFirstRow_update_two halfFirstRow_update_three ?_ ?_ x y
  · intro hazard rate
    exact quittingSigmaValue_update_affine weight hazard 0 2 (by decide) rate
  · intro hazard rate
    exact quittingSigmaValue_update_affine weight hazard 0 3 (by decide) rate

/-- The actual Continue sum at the first selected half face is bilinear. -/
theorem quittingHalfFirst_excludedValue_bilinear
    (weight : Finset (Fin 4) → Fin 4 → ℝ) (x y : ℝ) :
    excludedValue weight (halfFirstRow x y) 0 =
      quittingHalfBilinearInterpolation
        (fun x y => excludedValue weight (halfFirstRow x y) 0) x y := by
  refine halfRowValue_bilinear halfFirstRow
    (fun hazard => excludedValue weight hazard 0)
    halfFirstRow_update_two halfFirstRow_update_three ?_ ?_ x y
  · intro hazard rate
    exact quittingExcludedValue_update_affine weight hazard 0 2 (by decide) rate
  · intro hazard rate
    exact quittingExcludedValue_update_affine weight hazard 0 3 (by decide) rate

/-- The actual pure-Quit sum at the second selected half face is bilinear. -/
theorem quittingHalfSecond_sigmaValue_bilinear
    (weight : Finset (Fin 4) → Fin 4 → ℝ) (x y : ℝ) :
    sigmaValue weight (halfSecondRow x y) 1 =
      quittingHalfBilinearInterpolation
        (fun x y => sigmaValue weight (halfSecondRow x y) 1) x y := by
  refine halfRowValue_bilinear halfSecondRow
    (fun hazard => sigmaValue weight hazard 1)
    halfSecondRow_update_two halfSecondRow_update_three ?_ ?_ x y
  · intro hazard rate
    exact quittingSigmaValue_update_affine weight hazard 1 2 (by decide) rate
  · intro hazard rate
    exact quittingSigmaValue_update_affine weight hazard 1 3 (by decide) rate

/-- The actual Continue sum at the second selected half face is bilinear. -/
theorem quittingHalfSecond_excludedValue_bilinear
    (weight : Finset (Fin 4) → Fin 4 → ℝ) (x y : ℝ) :
    excludedValue weight (halfSecondRow x y) 1 =
      quittingHalfBilinearInterpolation
        (fun x y => excludedValue weight (halfSecondRow x y) 1) x y := by
  refine halfRowValue_bilinear halfSecondRow
    (fun hazard => excludedValue weight hazard 1)
    halfSecondRow_update_two halfSecondRow_update_three ?_ ?_ x y
  · intro hazard rate
    exact quittingExcludedValue_update_affine weight hazard 1 2 (by decide) rate
  · intro hazard rate
    exact quittingExcludedValue_update_affine weight hazard 1 3 (by decide) rate

private theorem first_continueMassExcl (x y : ℝ) :
    continueMassExcl (halfFirstRow x y) 0 = (1 / 2) * (1 - x) * (1 - y) := by
  rw [continueMassExcl,
    show Finset.univ.erase (0 : Fin 4) = {1, 2, 3} by decide]
  simp [halfFirstRow, Finset.prod_insert]
  ring_nf

private theorem second_continueMassExcl (x y : ℝ) :
    continueMassExcl (halfSecondRow x y) 1 = (1 / 2) * (1 - x) * (1 - y) := by
  rw [continueMassExcl,
    show Finset.univ.erase (1 : Fin 4) = {0, 2, 3} by decide]
  simp [halfSecondRow, Finset.prod_insert]
  ring_nf

/-- The actual first selected residual has the packet's biquadratic algebraic shape. -/
theorem quittingHalfFirst_displacement_eq_canonical
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (x y : ℝ) :
    quittingDiscountedDisplacement reward 0 (halfFirstRow x y) 0 =
      quittingHalfCanonicalResidual
        (fun x y => sigmaValue (weightOfReward reward) (halfFirstRow x y) 0)
        (fun x y => excludedValue (weightOfReward reward) (halfFirstRow x y) 0)
        x y := by
  rw [quittingDiscountedDisplacement, first_continueMassExcl]
  rw [quittingHalfFirst_sigmaValue_bilinear, quittingHalfFirst_excludedValue_bilinear]
  unfold quittingHalfCanonicalResidual quittingHalfBilinearInterpolation
  ring

/-- The actual second selected residual has the same biquadratic shape. -/
theorem quittingHalfSecond_displacement_eq_canonical
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (x y : ℝ) :
    quittingDiscountedDisplacement reward 0 (halfSecondRow x y) 1 =
      quittingHalfCanonicalResidual
        (fun x y => sigmaValue (weightOfReward reward) (halfSecondRow x y) 1)
        (fun x y => excludedValue (weightOfReward reward) (halfSecondRow x y) 1)
        x y := by
  rw [quittingDiscountedDisplacement, second_continueMassExcl]
  rw [quittingHalfSecond_sigmaValue_bilinear, quittingHalfSecond_excludedValue_bilinear]
  unfold quittingHalfCanonicalResidual quittingHalfBilinearInterpolation
  ring

end GameTheory
