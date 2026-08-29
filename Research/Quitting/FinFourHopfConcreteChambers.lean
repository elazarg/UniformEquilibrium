/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors.
-/

import Research.Quitting.FinFourMaximalRayZeroMinimumRegressions
import Research.Quitting.StationaryCenteredFaceCertificate
import MathUE.Interval.PolynomialLipschitz
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Concrete Fin4 HOPF safe chambers and the sharp stationary certificate

The two zero-minimum HOPF completions of
`Research/Quitting/FinFourMaximalRayZeroMinimumRegressions.lean` already have
a literal pure-singleton chamber.  Thin aliases here make those chambers
visible from the HOPF completion namespace without duplicating their proofs.

The second half records a distinct sharp owner-risky completion of the same
four-player table.  Its exact table algebra and preconditioner determinant are
checked here.  The whole-box diagonal estimate and the eight strict face
inequalities are then obtained from a centered mean-value bound: on the
normalized unit box, dyadic automatic differentiation of the reflected error
polynomials supplies both the value envelope at the center and the gradient
row sums that control every displacement from it.
-/

noncomputable section

namespace GameTheory

open Math.Topology Set
open Math.Interval

namespace FinFourHopfConcreteChambers

abbrev Player := Fin 4

open FinFourMaximalRayZeroMinimumRegressions

/-! ## Safe completions of the active HOPF table -/

/-- Thin HOPF-facing alias for the rational safe solo chamber. -/
theorem rationalSingletonTwoChamber :
    QuittingPureSingletonChamber (rationalReward rationalScale) 2 :=
  rationalPureSingletonChamber

/-- Thin HOPF-facing alias for the full-binding safe solo chamber.  This is
the full-binding table, not the sharp owner-risky one. -/
theorem fullBindingSingletonTwoChamber (R : ℝ) :
    QuittingPureSingletonChamber (fullBindingReward R rationalScale) 2 :=
  fullBindingPureSingletonChamber R

/-! ## The distinct sharp owner-risky completion -/

def sharpScale : ℝ := 1 / 100

def sharpLoss : ℝ := 39 / 100

def indicator (proposition : Prop) [Decidable proposition] : ℝ :=
  if proposition then 1 else 0

/-- Passive active-player reward on a background not containing that player. -/
def sharpActivePassive (who : Player) (background : Finset Player) : ℝ :=
  if who = 0 then
    if 3 ∈ background then 0
    else -(1 / 2) * indicator (1 ∈ background) + indicator (2 ∈ background)
  else if who = 1 then
    if 3 ∉ background then
      -(1 / 2) * indicator (0 ∈ background) + indicator (2 ∈ background)
    else if background = {0, 3} then sharpScale - 1
    else 0
  else if who = 2 then
    if 3 ∈ background then 0
    else -(1 / 5) *
      (indicator (0 ∈ background) + indicator (1 ∈ background))
  else 0

/-- Membership gain of an active player on its opponent background. -/
def sharpActiveGain (who : Player) (background : Finset Player) : ℝ :=
  if who = 0 then
    indicator (1 ∈ background) - 2 * indicator (2 ∈ background) +
      sharpScale * indicator (3 ∈ background)
  else if who = 1 then
    indicator (0 ∈ background) - 2 * indicator (2 ∈ background)
  else if who = 2 then
    (2 / 5) *
        (indicator (0 ∈ background) + indicator (1 ∈ background)) -
      sharpLoss * indicator (3 ∈ background)
  else 0

/-- Spectator reward on a nonempty active coalition. -/
def sharpSpectatorPassive (R singletonLevel : ℝ)
    (active : Finset Player) : ℝ :=
  singletonLevel + R * indicator (0 ∈ active) -
    (R + 1) * indicator (1 ∈ active)

/-- The complete sharp owner-risky reward table.  The special singleton clause
is essential: the spectator membership formula is used only on a nonempty
active background. -/
def sharpReward (R singletonLevel : ℝ)
    (terminal : {S : Finset Player // S.Nonempty}) : Payoff Player :=
  fun who ↦
    if who = 3 then
      if terminal.val = {3} then singletonLevel
      else
        let active := terminal.val.erase 3
        sharpSpectatorPassive R singletonLevel active +
          if 3 ∈ terminal.val then
            -indicator (0 ∈ active) - indicator (1 ∈ active) +
              indicator (2 ∈ active)
          else 0
    else
      let background := terminal.val.erase who
      sharpActivePassive who background +
        if who ∈ terminal.val then sharpActiveGain who background else 0

def rationalSharpReward :
    {S : Finset Player // S.Nonempty} → Payoff Player :=
  sharpReward (1 / 74) 1

/-! ## The certified rational hazard box -/

/-- Center of the certified rational hazard box. -/
def sharpCenter : Player → ℚ :=
  fun who ↦
    if who = 0 then 1815 / 10000
    else if who = 1 then 2179 / 10000
    else if who = 2 then 1110 / 10000
    else 4664 / 10000

/-- Common half-width of the certified rational hazard box. -/
def sharpHalfWidth : Player → ℚ := fun _ ↦ 1 / 400

/-- Strict face margin retained inside the half-width. -/
def sharpFaceMargin : Player → ℚ := fun _ ↦ 1 / 4000

theorem sharpHalfWidth_pos (who : Player) :
    0 < (sharpHalfWidth who : ℝ) := by
  norm_num [sharpHalfWidth]

def sharpPreconditionerRat : Player → Player → ℚ :=
  fun row column ↦
    if row = 0 then
      if column = 0 then -3111 / 10000
      else if column = 1 then 2273 / 10000
      else if column = 2 then -3 / 250
      else -10311 / 10000
    else if row = 1 then
      if column = 0 then 1021 / 1000
      else if column = 1 then -10619 / 10000
      else if column = 2 then 451 / 10000
      else -10923 / 10000
    else if row = 2 then
      if column = 0 then -1725 / 10000
      else if column = 1 then -5358 / 10000
      else if column = 2 then 54 / 10000
      else -5571 / 10000
    else
      if column = 0 then 591 / 1000
      else if column = 1 then -6953 / 10000
      else if column = 2 then -30444 / 10000
      else -17754 / 10000

def sharpPreconditioner : Player → Player → ℝ :=
  fun row column ↦ sharpPreconditionerRat row column

def sharpPreconditionerMatrix : Matrix Player Player ℚ :=
  sharpPreconditionerRat

/-- Literal exact determinant of the displayed preconditioner. -/
theorem sharpPreconditionerMatrix_det :
    sharpPreconditionerMatrix.det =
      443076546006639 / 156250000000000 := by
  have hminorZero :
      sharpPreconditionerMatrix.submatrix Fin.succ (0 : Player).succAbove =
        !![-10619 / 10000, 451 / 10000, -10923 / 10000;
          -5358 / 10000, 54 / 10000, -5571 / 10000;
          -6953 / 10000, -30444 / 10000, -17754 / 10000] := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp +decide [sharpPreconditionerMatrix, sharpPreconditionerRat,
        ]
  have hminorOne :
      sharpPreconditionerMatrix.submatrix Fin.succ (1 : Player).succAbove =
        !![1021 / 1000, 451 / 10000, -10923 / 10000;
          -1725 / 10000, 54 / 10000, -5571 / 10000;
          591 / 1000, -30444 / 10000, -17754 / 10000] := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp +decide [sharpPreconditionerMatrix, sharpPreconditionerRat,
        ]
  have hminorTwo :
      sharpPreconditionerMatrix.submatrix Fin.succ (2 : Player).succAbove =
        !![1021 / 1000, -10619 / 10000, -10923 / 10000;
          -1725 / 10000, -5358 / 10000, -5571 / 10000;
          591 / 1000, -6953 / 10000, -17754 / 10000] := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp +decide [sharpPreconditionerMatrix, sharpPreconditionerRat,
        ]
  have hminorThree :
      sharpPreconditionerMatrix.submatrix Fin.succ (3 : Player).succAbove =
        !![1021 / 1000, -10619 / 10000, 451 / 10000;
          -1725 / 10000, -5358 / 10000, 54 / 10000;
          591 / 1000, -6953 / 10000, -30444 / 10000] := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp +decide [sharpPreconditionerMatrix, sharpPreconditionerRat,
        ]
  have hminorOneSucc :
      sharpPreconditionerMatrix.submatrix Fin.succ
          (Fin.succ 0).succAbove =
        !![1021 / 1000, 451 / 10000, -10923 / 10000;
          -1725 / 10000, 54 / 10000, -5571 / 10000;
          591 / 1000, -30444 / 10000, -17754 / 10000] := by
    simpa using hminorOne
  have hminorTwoSucc :
      sharpPreconditionerMatrix.submatrix Fin.succ
          (Fin.succ 0).succ.succAbove =
        !![1021 / 1000, -10619 / 10000, -10923 / 10000;
          -1725 / 10000, -5358 / 10000, -5571 / 10000;
          591 / 1000, -6953 / 10000, -17754 / 10000] := by
    simpa using hminorTwo
  have hminorThreeSucc :
      sharpPreconditionerMatrix.submatrix Fin.succ
          (Fin.succ 0).succ.succ.succAbove =
        !![1021 / 1000, -10619 / 10000, 451 / 10000;
          -1725 / 10000, -5358 / 10000, 54 / 10000;
          591 / 1000, -6953 / 10000, -30444 / 10000] := by
    simpa using hminorThree
  rw [Matrix.det_succ_row_zero]
  rw [Fin.sum_univ_succ, hminorZero, Fin.sum_univ_succ,
    hminorOneSucc, Fin.sum_univ_succ, hminorTwoSucc,
    Fin.sum_univ_succ, hminorThreeSucc]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  simp +decide [Matrix.det_fin_three, sharpPreconditionerMatrix,
    sharpPreconditionerRat]
  norm_num

theorem sharpPreconditionerMatrix_det_pos :
    0 < sharpPreconditionerMatrix.det := by
  rw [sharpPreconditionerMatrix_det]
  norm_num

def applySharpPreconditioner (value : Player → ℝ) : Player → ℝ :=
  fun row ↦ ∑ column, sharpPreconditioner row column * value column

/-- The displayed rational preconditioner is injective.  This is the exact
kernel form of the nonzero-determinant calculation used by zero transport. -/
theorem applySharpPreconditioner_injective :
    Function.Injective applySharpPreconditioner := by
  intro first second hequal
  have hzero := congrFun hequal (0 : Player)
  have hone := congrFun hequal (1 : Player)
  have htwo := congrFun hequal (2 : Player)
  have hthree := congrFun hequal (3 : Player)
  simp [applySharpPreconditioner, sharpPreconditioner,
    sharpPreconditionerRat, Fin.sum_univ_succ] at hzero hone htwo hthree
  norm_num at hzero hone htwo hthree
  funext who
  fin_cases who
  · change first 0 = second 0
    linear_combination
      (-5645443125 / 196922909336284) * hzero +
      (71760832708125 / 98461454668142) * hone +
      (-859640912980625 / 590768728008852) * htwo +
      (1617902119375 / 196922909336284) * hthree
  · change first 1 = second 1
    linear_combination
      (40629285540625 / 49230727334071) * hzero +
      (770268750 / 49230727334071) * hone +
      (-74269449150625 / 49230727334071) * htwo +
      (-291870881875 / 49230727334071) * hthree
  · change first 2 = second 2
    linear_combination
      (53728819771875 / 196922909336284) * hzero +
      (26738077833125 / 98461454668142) * hone +
      (-15594105625 / 590768728008852) * htwo +
      (-64103241565625 / 196922909336284) * hthree
  · change first 3 = second 3
    linear_combination
      (-467342893403125 / 590768728008852) * hzero +
      (-21962275070625 / 98461454668142) * hone +
      (20966969144375 / 196922909336284) * htwo +
      (1572719375 / 590768728008852) * hthree

/-- The oriented field is `-A F`, matching the lower-positive/upper-negative
convention of `QuittingRationalStationaryFaceBox`. -/
def sharpOrientedField (R singletonLevel : ℝ)
    (hazard : Player → ℝ) : Player → ℝ :=
  -applySharpPreconditioner
    (fun who ↦ quittingFaceNumerator
      (weightOfReward (sharpReward R singletonLevel)) hazard who)

/-! ## Normalized exact polynomial checker -/

abbrev SharpNormalizedCoordinate := Fin 5

abbrev SharpPolynomial :=
  Math.Interval.RationalPolynomial 5

private def sharpPolynomialConstant (value : ℚ) : SharpPolynomial :=
  .constant value

private def sharpPolynomialVariable
    (coordinate : SharpNormalizedCoordinate) : SharpPolynomial :=
  .var coordinate

/-- Embed a hazard coordinate among the first four normalized variables. -/
def sharpHazardCoordinate (who : Player) : SharpNormalizedCoordinate :=
  Fin.castSucc who

/-- The fifth normalized variable is `74 * R - 1`. -/
def sharpParameterCoordinate : SharpNormalizedCoordinate :=
  Fin.last 4

/-- Affine normalized hazard substitution `x_i=c_i+q_i*y_i`. -/
def sharpNormalizedHazardPolynomial (who : Player) : SharpPolynomial :=
  sharpPolynomialConstant (sharpCenter who) +
    sharpPolynomialConstant (sharpHalfWidth who) *
      sharpPolynomialVariable (sharpHazardCoordinate who)

/-- Affine normalized parameter substitution `R=(t+1)/74`. -/
def sharpNormalizedParameterPolynomial : SharpPolynomial :=
  sharpPolynomialConstant (1 / 74) *
    (sharpPolynomialVariable sharpParameterCoordinate +
      sharpPolynomialConstant 1)

private def sharpOne : SharpPolynomial := sharpPolynomialConstant 1

/-- The four face-numerator polynomials of `sharpFaceFormula` after the
normalized substitutions.  The player-three term is factored as
`R*(x0-x1)-x1`; this algebraically equal form prevents a dependency loss in
exact interval and coefficient checks. -/
def sharpNormalizedFacePolynomial (who : Player) : SharpPolynomial :=
  let x0 := sharpNormalizedHazardPolynomial 0
  let x1 := sharpNormalizedHazardPolynomial 1
  let x2 := sharpNormalizedHazardPolynomial 2
  let x3 := sharpNormalizedHazardPolynomial 3
  let parameter := sharpNormalizedParameterPolynomial
  let s0 := (sharpOne - x1) * (sharpOne - x2) * (sharpOne - x3)
  let s1 := (sharpOne - x0) * (sharpOne - x2) * (sharpOne - x3)
  let s2 := (sharpOne - x0) * (sharpOne - x1) * (sharpOne - x3)
  let s3 := (sharpOne - x0) * (sharpOne - x1) * (sharpOne - x2)
  ![(sharpOne - s0) *
        (x1 - sharpPolynomialConstant 2 * x2 +
          sharpPolynomialConstant (1 / 100) * x3) -
      s0 * (sharpOne - x3) *
        (sharpPolynomialConstant (-1 / 2) * x1 + x2),
    (sharpOne - s1) * (x0 - sharpPolynomialConstant 2 * x2) -
      s1 *
        ((sharpOne - x3) *
            (sharpPolynomialConstant (-1 / 2) * x0 + x2) +
          sharpPolynomialConstant (-99 / 100) * x0 * x3 *
            (sharpOne - x2)),
    (sharpOne - s2) *
        (sharpPolynomialConstant (2 / 5) * (x0 + x1) -
          sharpPolynomialConstant (39 / 100) * x3) -
      s2 * (sharpOne - x3) *
        (sharpPolynomialConstant (-1 / 5) * (x0 + x1)),
    (sharpOne - s3) * (-x0 - x1 + x2) -
      s3 * (parameter * (x0 - x1) - x1)] who

/-- Normalized diagonal error `x_i-c_i-(A F)_i`. -/
def sharpNormalizedPreconditionedFacePolynomial
    (who : Player) : SharpPolynomial :=
  let f0 := sharpNormalizedFacePolynomial 0
  let f1 := sharpNormalizedFacePolynomial 1
  let f2 := sharpNormalizedFacePolynomial 2
  let f3 := sharpNormalizedFacePolynomial 3
  ![sharpPolynomialConstant (sharpPreconditionerRat 0 0) * f0 +
        sharpPolynomialConstant (sharpPreconditionerRat 0 1) * f1 +
        sharpPolynomialConstant (sharpPreconditionerRat 0 2) * f2 +
        sharpPolynomialConstant (sharpPreconditionerRat 0 3) * f3,
    sharpPolynomialConstant (sharpPreconditionerRat 1 0) * f0 +
        sharpPolynomialConstant (sharpPreconditionerRat 1 1) * f1 +
        sharpPolynomialConstant (sharpPreconditionerRat 1 2) * f2 +
        sharpPolynomialConstant (sharpPreconditionerRat 1 3) * f3,
    sharpPolynomialConstant (sharpPreconditionerRat 2 0) * f0 +
        sharpPolynomialConstant (sharpPreconditionerRat 2 1) * f1 +
        sharpPolynomialConstant (sharpPreconditionerRat 2 2) * f2 +
        sharpPolynomialConstant (sharpPreconditionerRat 2 3) * f3,
    sharpPolynomialConstant (sharpPreconditionerRat 3 0) * f0 +
        sharpPolynomialConstant (sharpPreconditionerRat 3 1) * f1 +
        sharpPolynomialConstant (sharpPreconditionerRat 3 2) * f2 +
        sharpPolynomialConstant (sharpPreconditionerRat 3 3) * f3] who

def sharpNormalizedDiagonalErrorPolynomial
    (who : Player) : SharpPolynomial :=
  sharpPolynomialConstant (sharpHalfWidth who) *
      sharpPolynomialVariable (sharpHazardCoordinate who) -
    sharpNormalizedPreconditionedFacePolynomial who

/-! ## Dyadic evaluation boxes for the normalized coordinates -/

/-- Common dyadic precision of the normalized interval computations. -/
def sharpPrecision : ℕ := 40

/-- The normalized coordinates all range over `[-1,1]`, which is exact at
every dyadic precision. -/
def sharpUnitBox : SharpNormalizedCoordinate →
    Math.Interval.DyadicInterval sharpPrecision :=
  fun _ ↦ ⟨-(2 ^ sharpPrecision), 2 ^ sharpPrecision⟩

/-- The degenerate box at the origin of the normalized coordinates, that is at
the box center and at the parameter value `1/74`. -/
def sharpCenterBox : SharpNormalizedCoordinate →
    Math.Interval.DyadicInterval sharpPrecision :=
  fun _ ↦ ⟨0, 0⟩

theorem sharpCenterBox_contains_zero (coordinate : SharpNormalizedCoordinate) :
    (sharpCenterBox coordinate).Contains (0 : ℝ) := by
  constructor <;>
    norm_num [sharpCenterBox, Math.Interval.DyadicInterval.toRationalInterval]

theorem sharpUnitBox_contains_of_abs_le_one
    {value : ℝ} (hvalue : |value| ≤ 1)
    (coordinate : SharpNormalizedCoordinate) :
    (sharpUnitBox coordinate).Contains value := by
  rw [abs_le] at hvalue
  constructor <;>
    norm_num [sharpUnitBox, Math.Interval.DyadicInterval.toRationalInterval,
      Math.Interval.DyadicInterval.scale, sharpPrecision] <;>
    linarith [hvalue.1, hvalue.2]

/-! ## Exact semantic bridge to the face numerators -/

/-- The four division-free face-numerator polynomials of the sharp table. -/
def sharpFaceFormula (R : ℝ) (hazard : Player → ℝ)
    (who : Player) : ℝ :=
  let x0 := hazard 0
  let x1 := hazard 1
  let x2 := hazard 2
  let x3 := hazard 3
  let s0 := (1 - x1) * (1 - x2) * (1 - x3)
  let s1 := (1 - x0) * (1 - x2) * (1 - x3)
  let s2 := (1 - x0) * (1 - x1) * (1 - x3)
  let s3 := (1 - x0) * (1 - x1) * (1 - x2)
  ![(1 - s0) * (x1 - 2 * x2 + (1 / 100) * x3) -
      s0 * (1 - x3) * (-(1 / 2) * x1 + x2),
    (1 - s1) * (x0 - 2 * x2) -
      s1 * ((1 - x3) * (-(1 / 2) * x0 + x2) -
        (99 / 100) * x0 * x3 * (1 - x2)),
    (1 - s2) * ((2 / 5) * (x0 + x1) - (39 / 100) * x3) -
      s2 * (1 - x3) * (-(1 / 5) * (x0 + x1)),
    (1 - s3) * (-x0 - x1 + x2) -
      s3 * (R * (x0 - x1) - x1)] who

/-- Direct table expansion: the division-free face numerator of `sharpReward`
is exactly `sharpFaceFormula`.  In particular the singleton level cancels. -/
theorem quittingFaceNumerator_sharpReward_eq_formula
    (R singletonLevel : ℝ) (hazard : Player → ℝ) (who : Player) :
    quittingFaceNumerator (weightOfReward (sharpReward R singletonLevel))
        hazard who =
      sharpFaceFormula R hazard who := by
  fin_cases who
  · change quittingFaceNumerator
      (weightOfReward (sharpReward R singletonLevel)) hazard 0 =
        sharpFaceFormula R hazard 0
    unfold quittingFaceNumerator continueMassExcl sigmaValue excludedValue
    rw [show Finset.univ.erase (0 : Player) = {1, 2, 3} by decide]
    rw [show ({1, 2, 3} : Finset Player).powerset =
      {∅, {1}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}, {1, 2, 3}} by decide]
    simp +decide [Finset.sdiff_eq_filter, Finset.filter_insert,
      Finset.filter_singleton, weightOfReward, sharpReward, sharpActivePassive,
      sharpActiveGain, indicator, sharpScale, sharpFaceFormula]
    ring
  · change quittingFaceNumerator
      (weightOfReward (sharpReward R singletonLevel)) hazard 1 =
        sharpFaceFormula R hazard 1
    unfold quittingFaceNumerator continueMassExcl sigmaValue excludedValue
    rw [show Finset.univ.erase (1 : Player) = {0, 2, 3} by decide]
    rw [show ({0, 2, 3} : Finset Player).powerset =
      {∅, {0}, {2}, {3}, {0, 2}, {0, 3}, {2, 3}, {0, 2, 3}} by decide]
    simp +decide [Finset.sdiff_eq_filter, Finset.filter_insert,
      Finset.filter_singleton, weightOfReward, sharpReward, sharpActivePassive,
      sharpActiveGain, indicator, sharpScale, sharpFaceFormula]
    ring
  · change quittingFaceNumerator
      (weightOfReward (sharpReward R singletonLevel)) hazard 2 =
        sharpFaceFormula R hazard 2
    unfold quittingFaceNumerator continueMassExcl sigmaValue excludedValue
    rw [show Finset.univ.erase (2 : Player) = {0, 1, 3} by decide]
    rw [show ({0, 1, 3} : Finset Player).powerset =
      {∅, {0}, {1}, {3}, {0, 1}, {0, 3}, {1, 3}, {0, 1, 3}} by decide]
    simp +decide [Finset.sdiff_eq_filter, Finset.filter_insert,
      Finset.filter_singleton, weightOfReward, sharpReward, sharpActivePassive,
      sharpActiveGain, indicator, sharpLoss, sharpFaceFormula]
    ring
  · change quittingFaceNumerator
      (weightOfReward (sharpReward R singletonLevel)) hazard 3 =
        sharpFaceFormula R hazard 3
    unfold quittingFaceNumerator continueMassExcl sigmaValue excludedValue
    rw [show Finset.univ.erase (3 : Player) = {0, 1, 2} by decide]
    rw [show ({0, 1, 2} : Finset Player).powerset =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide]
    simp +decide [Finset.sdiff_eq_filter, Finset.filter_insert,
      Finset.filter_singleton, weightOfReward, sharpReward,
      sharpSpectatorPassive, indicator, sharpFaceFormula]
    ring

/-- Literal singleton-level cancellation for the stationary numerator. -/
theorem quittingFaceNumerator_sharpReward_independent_singletonLevel
    (R firstLevel secondLevel : ℝ) (hazard : Player → ℝ)
    (who : Player) :
    quittingFaceNumerator (weightOfReward (sharpReward R firstLevel))
        hazard who =
      quittingFaceNumerator (weightOfReward (sharpReward R secondLevel))
        hazard who := by
  rw [quittingFaceNumerator_sharpReward_eq_formula,
    quittingFaceNumerator_sharpReward_eq_formula]

/-- Normalized five-coordinate point attached to `(hazard,R)`. -/
def sharpNormalizedPoint (hazard : Player → ℝ) (R : ℝ) :
    SharpNormalizedCoordinate → ℝ :=
  fun coordinate ↦
    if hcoordinate : coordinate.val < 4 then
      (hazard ⟨coordinate.val, hcoordinate⟩ -
          sharpCenter ⟨coordinate.val, hcoordinate⟩) /
        sharpHalfWidth ⟨coordinate.val, hcoordinate⟩
    else 74 * R - 1

@[simp] theorem sharpNormalizedPoint_hazard
    (hazard : Player → ℝ) (R : ℝ) (who : Player) :
    sharpNormalizedPoint hazard R (sharpHazardCoordinate who) =
      (hazard who - sharpCenter who) / sharpHalfWidth who := by
  simp [sharpNormalizedPoint, sharpHazardCoordinate]

@[simp] theorem sharpNormalizedPoint_parameter
    (hazard : Player → ℝ) (R : ℝ) :
    sharpNormalizedPoint hazard R sharpParameterCoordinate = 74 * R - 1 := by
  simp [sharpNormalizedPoint, sharpParameterCoordinate]

@[simp] theorem evalReal_sharpNormalizedHazardPolynomial
    (hazard : Player → ℝ) (R : ℝ) (who : Player) :
    Math.Interval.RationalPolynomial.evalReal
        (sharpNormalizedPoint hazard R)
        (sharpNormalizedHazardPolynomial who) = hazard who := by
  simp [sharpNormalizedHazardPolynomial, sharpPolynomialConstant,
    sharpPolynomialVariable]
  have hwidth : (sharpHalfWidth who : ℝ) ≠ 0 :=
    ne_of_gt (sharpHalfWidth_pos who)
  field_simp
  ring

@[simp] theorem evalReal_sharpNormalizedParameterPolynomial
    (hazard : Player → ℝ) (R : ℝ) :
    Math.Interval.RationalPolynomial.evalReal
        (sharpNormalizedPoint hazard R)
        sharpNormalizedParameterPolynomial = R := by
  norm_num [sharpNormalizedParameterPolynomial, sharpPolynomialConstant,
    sharpPolynomialVariable, sharpNormalizedPoint, sharpParameterCoordinate,
    Math.Interval.RationalPolynomial.evalReal]
  ring

@[simp] theorem evalReal_sharpNormalizedFacePolynomial
    (hazard : Player → ℝ) (R : ℝ) (who : Player) :
    Math.Interval.RationalPolynomial.evalReal
        (sharpNormalizedPoint hazard R)
        (sharpNormalizedFacePolynomial who) =
      sharpFaceFormula R hazard who := by
  fin_cases who
  · change Math.Interval.RationalPolynomial.evalReal
        (sharpNormalizedPoint hazard R)
        (sharpNormalizedFacePolynomial 0) =
      sharpFaceFormula R hazard 0
    simp [sharpNormalizedFacePolynomial, sharpFaceFormula,
      sharpOne, sharpPolynomialConstant]
    ring_nf
    simp
  · change Math.Interval.RationalPolynomial.evalReal
        (sharpNormalizedPoint hazard R)
        (sharpNormalizedFacePolynomial 1) =
      sharpFaceFormula R hazard 1
    simp [sharpNormalizedFacePolynomial, sharpFaceFormula,
      sharpOne, sharpPolynomialConstant]
    ring_nf
    simp
  · change Math.Interval.RationalPolynomial.evalReal
        (sharpNormalizedPoint hazard R)
        (sharpNormalizedFacePolynomial 2) =
      sharpFaceFormula R hazard 2
    simp [sharpNormalizedFacePolynomial, sharpFaceFormula,
      sharpOne, sharpPolynomialConstant]
    ring_nf
  · change Math.Interval.RationalPolynomial.evalReal
        (sharpNormalizedPoint hazard R)
        (sharpNormalizedFacePolynomial 3) =
      sharpFaceFormula R hazard 3
    simp [sharpNormalizedFacePolynomial, sharpFaceFormula,
      sharpOne, sharpPolynomialConstant]

theorem evalReal_sharpNormalizedPreconditionedFacePolynomial
    (hazard : Player → ℝ) (R : ℝ) (who : Player) :
    Math.Interval.RationalPolynomial.evalReal
        (sharpNormalizedPoint hazard R)
        (sharpNormalizedPreconditionedFacePolynomial who) =
      applySharpPreconditioner (sharpFaceFormula R hazard) who := by
  fin_cases who
  · change Math.Interval.RationalPolynomial.evalReal
        (sharpNormalizedPoint hazard R)
        (sharpNormalizedPreconditionedFacePolynomial 0) =
      applySharpPreconditioner (sharpFaceFormula R hazard) 0
    simp [sharpNormalizedPreconditionedFacePolynomial,
      applySharpPreconditioner, sharpPreconditioner,
      sharpPreconditionerRat, sharpPolynomialConstant,
      Fin.sum_univ_succ]
    ring
  · change Math.Interval.RationalPolynomial.evalReal
        (sharpNormalizedPoint hazard R)
        (sharpNormalizedPreconditionedFacePolynomial 1) =
      applySharpPreconditioner (sharpFaceFormula R hazard) 1
    simp [sharpNormalizedPreconditionedFacePolynomial,
      applySharpPreconditioner, sharpPreconditioner,
      sharpPreconditionerRat, sharpPolynomialConstant,
      Fin.sum_univ_succ]
    ring
  · change Math.Interval.RationalPolynomial.evalReal
        (sharpNormalizedPoint hazard R)
        (sharpNormalizedPreconditionedFacePolynomial 2) =
      applySharpPreconditioner (sharpFaceFormula R hazard) 2
    simp [sharpNormalizedPreconditionedFacePolynomial,
      applySharpPreconditioner, sharpPreconditioner,
      sharpPreconditionerRat, sharpPolynomialConstant,
      Fin.sum_univ_succ]
    ring
  · change Math.Interval.RationalPolynomial.evalReal
        (sharpNormalizedPoint hazard R)
        (sharpNormalizedPreconditionedFacePolynomial 3) =
      applySharpPreconditioner (sharpFaceFormula R hazard) 3
    simp [sharpNormalizedPreconditionedFacePolynomial,
      applySharpPreconditioner, sharpPreconditioner,
      sharpPreconditionerRat, sharpPolynomialConstant,
      Fin.sum_univ_succ]
    ring

/-- The reflected normalized error evaluates to the exact oriented-field
diagonal error used by the centered face certificate. -/
theorem evalReal_sharpNormalizedDiagonalErrorPolynomial
    (hazard : Player → ℝ) (R singletonLevel : ℝ) (who : Player) :
    Math.Interval.RationalPolynomial.evalReal
        (sharpNormalizedPoint hazard R)
        (sharpNormalizedDiagonalErrorPolynomial who) =
      sharpOrientedField R singletonLevel hazard who -
        ((sharpCenter who : ℝ) - hazard who) := by
  have hwidth : (sharpHalfWidth who : ℝ) ≠ 0 :=
    ne_of_gt (sharpHalfWidth_pos who)
  unfold sharpNormalizedDiagonalErrorPolynomial
  unfold sharpPolynomialConstant sharpPolynomialVariable
  rw [Math.Interval.RationalPolynomial.evalReal_sub,
    Math.Interval.RationalPolynomial.evalReal_mul,
    Math.Interval.RationalPolynomial.evalReal_constant,
    Math.Interval.RationalPolynomial.evalReal_var,
    sharpNormalizedPoint_hazard,
    evalReal_sharpNormalizedPreconditionedFacePolynomial]
  unfold sharpOrientedField
  simp_rw [quittingFaceNumerator_sharpReward_eq_formula]
  simp only [Pi.neg_apply]
  field_simp
  ring

/-- The rational hazard box and parameter interval map into the normalized
five-dimensional unit box. -/
theorem abs_sharpNormalizedPoint_le_one
    (hazard : Player → ℝ)
    (hhazard : hazard ∈
      Icc
        (quittingRationalBoxLower
          (quittingCenteredRationalBoxLower sharpCenter sharpHalfWidth))
        (quittingRationalBoxUpper
          (quittingCenteredRationalBoxUpper sharpCenter sharpHalfWidth)))
    (R : ℝ) (hR : R ∈ Icc 0 (1 / 37)) :
    ∀ coordinate, |sharpNormalizedPoint hazard R coordinate| ≤ 1 := by
  intro coordinate
  by_cases hcoordinate : coordinate.val < 4
  · let who : Player := ⟨coordinate.val, hcoordinate⟩
    have hlower := hhazard.1 who
    have hupper := hhazard.2 who
    have hhalfWidth : 0 < (sharpHalfWidth who : ℝ) :=
      sharpHalfWidth_pos who
    have hlowerCast :
        ((sharpCenter who - sharpHalfWidth who : ℚ) : ℝ) =
          (sharpCenter who : ℝ) - sharpHalfWidth who := by
      norm_num
    have hupperCast :
        ((sharpCenter who + sharpHalfWidth who : ℚ) : ℝ) =
          (sharpCenter who : ℝ) + sharpHalfWidth who := by
      norm_num
    change
      ((sharpCenter who - sharpHalfWidth who : ℚ) : ℝ) ≤
        hazard who at hlower
    change hazard who ≤
      ((sharpCenter who + sharpHalfWidth who : ℚ) : ℝ) at hupper
    rw [hlowerCast] at hlower
    rw [hupperCast] at hupper
    rw [sharpNormalizedPoint, dif_pos hcoordinate, abs_le]
    constructor
    · rw [le_div_iff₀ hhalfWidth]
      linarith
    · rw [div_le_iff₀ hhalfWidth]
      linarith
  · have hlast : coordinate = sharpParameterCoordinate := by
      apply Fin.ext
      simp only [sharpParameterCoordinate, Fin.last]
      omega
    subst coordinate
    rw [sharpNormalizedPoint_parameter, abs_le]
    constructor <;> norm_num at hR ⊢ <;> linarith

/-- Centered mean-value bound on the normalized unit box for each of the four
reflected diagonal-error polynomials.  The center envelope and the four
gradient row sums are exact dyadic interval computations. -/
theorem abs_evalReal_sharpNormalizedDiagonalErrorPolynomial_le
    (point : SharpNormalizedCoordinate → ℝ)
    (hpoint : ∀ coordinate, |point coordinate| ≤ 1)
    (who : Player) :
    |Math.Interval.RationalPolynomial.evalReal point
        (sharpNormalizedDiagonalErrorPolynomial who)| ≤
      (sharpHalfWidth who : ℝ) - sharpFaceMargin who := by
  have hcast : ((sharpHalfWidth who - sharpFaceMargin who : ℚ) : ℝ) =
      (sharpHalfWidth who : ℝ) - sharpFaceMargin who := by
    push_cast
    ring
  rw [← hcast]
  refine
    Math.Interval.RationalPolynomial.abs_evalReal_le_of_centeredMeanValueNumerator_le
      (sharpNormalizedDiagonalErrorPolynomial who) sharpCenterBox sharpUnitBox
      (fun _ ↦ 0) point sharpCenterBox_contains_zero ?_ ?_ ?_ _ ?_
  · exact fun coordinate ↦
      sharpUnitBox_contains_of_abs_le_one (by norm_num) coordinate
  · exact fun coordinate ↦
      sharpUnitBox_contains_of_abs_le_one (hpoint coordinate) coordinate
  · intro coordinate
    simpa using hpoint coordinate
  · fin_cases who
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel

/-- Exact whole-box diagonal error bound, uniform in the full parameter range
`0 ≤ R ≤ 1/37` and independent of the singleton level. -/
theorem sharp_diagonal_error
    (R singletonLevel : ℝ) (hR : R ∈ Icc 0 (1 / 37))
    (hazard : Player → ℝ)
    (hhazard : hazard ∈
      Icc
        (quittingRationalBoxLower
          (quittingCenteredRationalBoxLower sharpCenter sharpHalfWidth))
        (quittingRationalBoxUpper
          (quittingCenteredRationalBoxUpper sharpCenter sharpHalfWidth)))
    (who : Player) :
    |sharpOrientedField R singletonLevel hazard who -
        ((sharpCenter who : ℝ) - hazard who)| ≤
      (sharpHalfWidth who : ℝ) - sharpFaceMargin who := by
  rw [← evalReal_sharpNormalizedDiagonalErrorPolynomial
    hazard R singletonLevel who]
  exact abs_evalReal_sharpNormalizedDiagonalErrorPolynomial_le
    (sharpNormalizedPoint hazard R)
    (abs_sharpNormalizedPoint_le_one hazard hhazard R hR) who

/-- The four mean-value bounds and the preconditioner determinant compile to
the generic centered stationary certificate for every parameter in the closed
range `0 ≤ R ≤ 1/37`.  The singleton level is unrestricted because it cancels
from all four face numerators. -/
def sharpCenteredCertificate
    (R singletonLevel : ℝ)
    (hR : R ∈ Icc 0 (1 / 37)) :
    QuittingCenteredStationaryFaceCertificate
      (sharpReward R singletonLevel) where
  center := sharpCenter
  halfWidth := sharpHalfWidth
  margin := sharpFaceMargin
  field := sharpOrientedField R singletonLevel
  lower_nonneg := by
    intro who
    fin_cases who <;> simp +decide [sharpCenter, sharpHalfWidth] <;>
      norm_num
  upper_le_one := by
    intro who
    fin_cases who <;> simp +decide [sharpCenter, sharpHalfWidth] <;>
      norm_num
  halfWidth_pos := by
    intro who
    norm_num [sharpHalfWidth]
  margin_pos := by
    intro who
    norm_num [sharpFaceMargin]
  continuous_field := by
    unfold sharpOrientedField applySharpPreconditioner
    apply continuous_pi
    intro row
    exact (continuous_finsetSum _ fun column _ =>
      continuous_const.mul
        (continuous_quittingFaceNumerator
          (weightOfReward (sharpReward R singletonLevel)) column)).neg
  diagonal_error := by
    intro hazard hhazard who
    exact sharp_diagonal_error R singletonLevel hR hazard hhazard who
  zero_to_numerator := by
    intro hazard _ hzero
    have hpreconditioned : applySharpPreconditioner
        (fun who ↦ quittingFaceNumerator
          (weightOfReward (sharpReward R singletonLevel)) hazard who) = 0 := by
      funext who
      have := hzero who
      simpa [sharpOrientedField, Pi.zero_apply] using neg_eq_zero.mp this
    have hzeroInput : applySharpPreconditioner (0 : Player → ℝ) = 0 := by
      funext who
      simp [applySharpPreconditioner]
    have hnumerator := applySharpPreconditioner_injective
      (hpreconditioned.trans hzeroInput.symm)
    intro who
    exact congrFun hnumerator who

/-- Stationary all-behavior consumer for every sharp table parameter in the
certified range. -/
theorem sharpReward_exists_uniformEquilibriumPayoff
    (R singletonLevel : ℝ) (hR : R ∈ Icc 0 (1 / 37)) :
    ∃ payoff : Payoff Player,
      (quittingGame (sharpReward R singletonLevel)).IsUniformEquilibriumPayoff
        none payoff := by
  exact QuittingCenteredStationaryFaceCertificate.exists_uniformEquilibriumPayoff
    (sharpCenteredCertificate R singletonLevel hR)

/-- Fixed rational specialization of the sharp table. -/
theorem rationalSharpReward_exists_uniformEquilibriumPayoff :
    ∃ payoff : Payoff Player,
      (quittingGame rationalSharpReward).IsUniformEquilibriumPayoff none payoff := by
  apply sharpReward_exists_uniformEquilibriumPayoff (1 / 74) 1
  norm_num

/-!
The compiler above does not identify
`sharpReward fullBindingInitialCap singletonLevel` with the older
`fullBindingReward`: those tables differ on passive active-player entries.
Consequently the maximal-ray regression is not silently transported to the
sharp table here.  Persistence under arbitrary nearby reward-table
perturbations is likewise a separate compact-uniformity theorem, not a
consequence of parameter-uniformity inside this two-parameter family.
-/

end FinFourHopfConcreteChambers

end GameTheory
