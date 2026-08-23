/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.CyclicWeightRowDichotomy

/-!
# Division-free stationary face numerator

For a quitting-game hazard row, a player's pure-Quit endpoint is
`sigmaValue`, the unconditional absorbing contribution from continuing is
`excludedValue`, and `continueMassExcl` is the probability that every
opponent Continues.  The division-free numerator

`(1 - continueMassExcl) * sigmaValue - excludedValue`

vanishes exactly when using the pure-Quit endpoint as continuation value also
makes the pure-Continue endpoint equal to it.  Unlike the corresponding
conditional payoff quotient, this polynomial expression is defined and
continuous on every face of the hazard cube.
-/

noncomputable section

namespace GameTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The division-free difference between the pure-Quit endpoint, weighted by
opponent absorption, and the unconditional absorbing Continue contribution. -/
def quittingFaceNumerator
    (r : Finset ι → ι → ℝ) (hazard : ι → ℝ) (who : ι) : ℝ :=
  (1 - continueMassExcl hazard who) * sigmaValue r hazard who -
    excludedValue r hazard who

/-- The absorbing Continue contribution conditioned on at least one opponent
quitting.  The division-free numerator remains the canonical boundary object. -/
def quittingConditionalContinueValue
    (r : Finset ι → ι → ℝ) (hazard : ι → ℝ) (who : ι) : ℝ :=
  excludedValue r hazard who / (1 - continueMassExcl hazard who)

/-- Pure-Quit payoff minus the conditional continuer payoff. -/
def quittingConditionalFaceGap
    (r : Finset ι → ι → ℝ) (hazard : ι → ℝ) (who : ι) : ℝ :=
  sigmaValue r hazard who - quittingConditionalContinueValue r hazard who

/-- Away from the no-opponent-absorption face, the numerator is the positive
denominator times the conditional face gap. -/
theorem quittingFaceNumerator_eq_one_sub_continueMass_mul_conditionalFaceGap
    (r : Finset ι → ι → ℝ) (hazard : ι → ℝ) (who : ι)
    (hcontracts : continueMassExcl hazard who ≠ 1) :
    quittingFaceNumerator r hazard who =
      (1 - continueMassExcl hazard who) *
        quittingConditionalFaceGap r hazard who := by
  unfold quittingFaceNumerator quittingConditionalFaceGap
    quittingConditionalContinueValue
  have hdenominator : 1 - continueMassExcl hazard who ≠ 0 :=
    sub_ne_zero.mpr hcontracts.symm
  field_simp

/-- The face numerator is the endpoint gain evaluated at the pure-Quit
endpoint itself. -/
theorem quittingFaceNumerator_eq_gainValue
    (r : Finset ι → ι → ℝ) (hazard : ι → ℝ) (who : ι) :
    quittingFaceNumerator r hazard who =
      gainValue r hazard who (sigmaValue r hazard who) := by
  simp only [quittingFaceNumerator, gainValue, gammaValue]
  ring

/-- The face numerator is continuous in the finite hazard row. -/
theorem continuous_quittingFaceNumerator
    (r : Finset ι → ι → ℝ) (who : ι) :
    Continuous fun hazard : ι → ℝ => quittingFaceNumerator r hazard who := by
  unfold quittingFaceNumerator
  exact ((continuous_const.sub (continuous_continueMassExcl who)).mul
    (continuous_sigmaValue r who)).sub (continuous_excludedValue r who)

/-- Vanishing of the division-free numerator is exactly the endpoint algebra
needed for a stationary fixed point: the pure-Continue endpoint, evaluated at
the pure-Quit endpoint, agrees with it. -/
theorem gammaValue_sigmaValue_eq_of_quittingFaceNumerator_eq_zero
    (r : Finset ι → ι → ℝ) (hazard : ι → ℝ) (who : ι)
    (hzero : quittingFaceNumerator r hazard who = 0) :
    gammaValue r hazard who (sigmaValue r hazard who) =
      sigmaValue r hazard who := by
  rw [quittingFaceNumerator_eq_gainValue] at hzero
  unfold gainValue at hzero
  linarith

end GameTheory
