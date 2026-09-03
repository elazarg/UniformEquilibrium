/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Interval.PolynomialKrawczyk
import UniformEquilibrium.Quitting.Classification.LCP.FullCore.DeadlockChargedReturn
import UniformEquilibrium.Quitting.Cycles.BlockPeriodicProfile

/-!
# An exact period-three payoff for an integer full-core deadlock table

This file isolates a unique algebraic parameter in an explicit rational
parallelotope, uses it to build an exact three-phase product block, and feeds
the block to the unrestricted behavioral uniform-equilibrium consumer.

The uniqueness statement is local to the displayed parallelotope. The
separate stationary-profile exclusion for this reward table is not used here.
-/

noncomputable section

namespace GameTheory
namespace FullCoreDeadlock

open Function Metric Set
open Math.Interval
open Math.Interval.RationalPolynomial
open Math.Probability Math.PMFProduct Math.ProbabilityMassFunction
open scoped NNReal

/-! ## The exact algebraic parameter -/

/-- The rational center of the affine root chart. -/
def integerTableCenter : Player → ℚ :=
  ![2200649139 / 10 ^ 10,
    4455252923 / 10 ^ 10,
    598923293 / 10 ^ 10,
    415887857 / (2 * 10 ^ 9)]

/-- The rational matrix of the affine root chart. -/
def integerTableChartMatrix : Player → Player → ℚ :=
  ![![7 / 20, -323 / 1000, 137 / 500, 631 / 1000],
    ![213 / 250, 22 / 125, 309 / 1000, 59 / 125],
    ![7 / 100, 267 / 1000, -69 / 1000, 23 / 100],
    ![253 / 1000, -19 / 250, 101 / 250, 141 / 500]]

/-- The affine chart is nonsingular, with its exact rational determinant. -/
theorem integerTableChartMatrix_det :
    Matrix.det integerTableChartMatrix = -41914379009 / 10 ^ 12 := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply]
  simp +decide [Fin.sum_univ_succ, Fin.succAbove_of_le_castSucc,
    show (3 : Fin 4).succAbove (2 : Fin 3) = 2 by decide,
    integerTableChartMatrix]
  norm_num

/-- The affine chart carrying a small cube to the parameter parallelotope. -/
def integerTableAffineParameter (z : Player → ℝ) : Player → ℝ :=
  fun row ↦ (integerTableCenter row : ℝ) +
    ∑ column, (integerTableChartMatrix row column : ℝ) * z column

/-- The four polynomial block residuals in parameter coordinates. -/
def integerTableParameterResidual (parameter : Player → ℝ) : Player → ℝ :=
  let a := parameter 0
  let b := parameter 1
  let c := parameter 2
  let d := parameter 3
  ![3 * b * c + 3 * b * d + b - 3 * c - 3 * d,
    -2 * a * c * d + 2 * a * c + 2 * a * d - 2 * a + 2 * c + d,
    -a * b * d + a * b + 2 * a * d - 2 * a + b * d - b + 3 * d,
    -a * b * c + a * b - a * c + a + b * c - b + 2 * c]

/-- The residual pulled back to the affine cube. -/
def integerTableCubeResidual (z : Player → ℝ) : Player → ℝ :=
  integerTableParameterResidual (integerTableAffineParameter z)

private abbrev IntegerTablePolynomial :=
  Math.Interval.RationalPolynomial 4

private def integerTableAffineExpression
    (row : Player) : IntegerTablePolynomial :=
  let z0 : IntegerTablePolynomial := .var 0
  let z1 : IntegerTablePolynomial := .var 1
  let z2 : IntegerTablePolynomial := .var 2
  let z3 : IntegerTablePolynomial := .var 3
  match row with
  | 0 => .constant (2200649139 / 10 ^ 10) +
      .constant (7 / 20) * z0 + .constant (-323 / 1000) * z1 +
      .constant (137 / 500) * z2 + .constant (631 / 1000) * z3
  | 1 => .constant (4455252923 / 10 ^ 10) +
      .constant (213 / 250) * z0 + .constant (22 / 125) * z1 +
      .constant (309 / 1000) * z2 + .constant (59 / 125) * z3
  | 2 => .constant (598923293 / 10 ^ 10) +
      .constant (7 / 100) * z0 + .constant (267 / 1000) * z1 +
      .constant (-69 / 1000) * z2 + .constant (23 / 100) * z3
  | 3 => .constant (415887857 / (2 * 10 ^ 9)) +
      .constant (253 / 1000) * z0 + .constant (-19 / 250) * z1 +
      .constant (101 / 250) * z2 + .constant (141 / 500) * z3

private def integerTableResidualExpression
    (row : Player) : IntegerTablePolynomial :=
  let a := integerTableAffineExpression 0
  let b := integerTableAffineExpression 1
  let c := integerTableAffineExpression 2
  let d := integerTableAffineExpression 3
  match row with
  | 0 => .constant 3 * b * c + .constant 3 * b * d + b -
      .constant 3 * c - .constant 3 * d
  | 1 => -.constant 2 * a * c * d + .constant 2 * a * c +
      .constant 2 * a * d - .constant 2 * a + .constant 2 * c + d
  | 2 => -a * b * d + a * b + .constant 2 * a * d -
      .constant 2 * a + b * d - b + .constant 3 * d
  | 3 => -a * b * c + a * b - a * c + a + b * c - b +
      .constant 2 * c

private def integerTableStepExpression
    (row : Player) : IntegerTablePolynomial :=
  .var row - integerTableResidualExpression row

@[simp] theorem integerTableAffineExpression_evalReal
    (z : Player → ℝ) (row : Player) :
    Math.Interval.RationalPolynomial.evalReal z
        (integerTableAffineExpression row) =
      integerTableAffineParameter z row := by
  fin_cases row <;>
    simp [integerTableAffineExpression, integerTableAffineParameter,
      integerTableCenter, integerTableChartMatrix, Fin.sum_univ_succ] <;>
    ring

@[simp] theorem integerTableResidualExpression_evalReal
    (z : Player → ℝ) (row : Player) :
    Math.Interval.RationalPolynomial.evalReal z
        (integerTableResidualExpression row) =
      integerTableCubeResidual z row := by
  fin_cases row <;>
    simp [integerTableResidualExpression, integerTableCubeResidual,
      integerTableParameterResidual]

theorem integerTableStepExpression_evalReal (z : Player → ℝ) :
    (fun row ↦ Math.Interval.RationalPolynomial.evalReal z
      (integerTableStepExpression row)) =
        z - integerTableCubeResidual z := by
  funext row
  simp [integerTableStepExpression]

/-- Radius of the isolating affine cube. -/
def integerTableRadius : ℝ := 1 / 10 ^ 6

/-- The exact rational box underlying the isolating cube. -/
def integerTableRationalBox : Player → RationalInterval :=
  fun _ ↦ ⟨-1 / 10 ^ 6, 1 / 10 ^ 6⟩

/-- The fixed contraction constant used by the exact certificate. -/
def integerTableContraction : ℝ≥0 := 1 / 200

theorem integerTableRationalBox_endpoints (coordinate : Player) :
    (integerTableRationalBox coordinate).Contains
        ((0 : Player → ℝ) coordinate - integerTableRadius) ∧
      (integerTableRationalBox coordinate).Contains
        ((0 : Player → ℝ) coordinate + integerTableRadius) := by
  constructor <;>
    norm_num [integerTableRationalBox, RationalInterval.Contains,
      integerTableRadius]

@[simp] private theorem rationalInterval_point_lower_cast (value : ℚ) :
    ((((RationalInterval.point value).lower : ℚ) : ℝ)) = value := rfl

@[simp] private theorem rationalInterval_point_upper_cast (value : ℚ) :
    ((((RationalInterval.point value).upper : ℚ) : ℝ)) = value := rfl

@[simp] private theorem rationalInterval_add_lower_cast
    (first second : RationalInterval) :
    ((((first.add second).lower : ℚ) : ℝ)) =
      (first.lower : ℝ) + (second.lower : ℝ) := by
  simp [RationalInterval.add]

@[simp] private theorem rationalInterval_add_upper_cast
    (first second : RationalInterval) :
    ((((first.add second).upper : ℚ) : ℝ)) =
      (first.upper : ℝ) + (second.upper : ℝ) := by
  simp [RationalInterval.add]

@[simp] private theorem rationalInterval_neg_lower_cast
    (interval : RationalInterval) :
    ((((interval.neg).lower : ℚ) : ℝ)) = -(interval.upper : ℝ) := by
  simp [RationalInterval.neg]

@[simp] private theorem rationalInterval_neg_upper_cast
    (interval : RationalInterval) :
    ((((interval.neg).upper : ℚ) : ℝ)) = -(interval.lower : ℝ) := by
  simp [RationalInterval.neg]

@[simp] private theorem rationalInterval_mul_lower_cast
    (first second : RationalInterval) :
    ((((first.mul second).lower : ℚ) : ℝ)) =
      min ((first.lower : ℝ) * (second.lower : ℝ))
        (min ((first.lower : ℝ) * (second.upper : ℝ))
          (min ((first.upper : ℝ) * (second.lower : ℝ))
            ((first.upper : ℝ) * (second.upper : ℝ)))) := by
  simp [RationalInterval.mul, Rat.cast_min]

@[simp] private theorem rationalInterval_mul_upper_cast
    (first second : RationalInterval) :
    ((((first.mul second).upper : ℚ) : ℝ)) =
      max ((first.lower : ℝ) * (second.lower : ℝ))
        (max ((first.lower : ℝ) * (second.upper : ℝ))
          (max ((first.upper : ℝ) * (second.lower : ℝ))
            ((first.upper : ℝ) * (second.upper : ℝ)))) := by
  simp [RationalInterval.mul, Rat.cast_max]

/-- Cached exact interval values and derivatives of the affine chart. -/
def integerTableAffineDualCache : Player → IntervalDual 4
  | 0 => ⟨⟨2200633359 / 10 ^ 10, 2200664919 / 10 ^ 10⟩,
      ![RationalInterval.point (7 / 20),
        RationalInterval.point (-323 / 1000),
        RationalInterval.point (137 / 500),
        RationalInterval.point (631 / 1000)]⟩
  | 1 => ⟨⟨4455234833 / 10 ^ 10, 4455271013 / 10 ^ 10⟩,
      ![RationalInterval.point (213 / 250),
        RationalInterval.point (22 / 125),
        RationalInterval.point (309 / 1000),
        RationalInterval.point (59 / 125)]⟩
  | 2 => ⟨⟨598916933 / 10 ^ 10, 598929653 / 10 ^ 10⟩,
      ![RationalInterval.point (7 / 100),
        RationalInterval.point (267 / 1000),
        RationalInterval.point (-69 / 1000),
        RationalInterval.point (23 / 100)]⟩
  | 3 => ⟨⟨415885827 / (2 * 10 ^ 9), 415889887 / (2 * 10 ^ 9)⟩,
      ![RationalInterval.point (253 / 1000),
        RationalInterval.point (-19 / 250),
        RationalInterval.point (101 / 250),
        RationalInterval.point (141 / 500)]⟩

private theorem intervalDual_ext
    {variableCount : ℕ} {first second : IntervalDual variableCount}
    (hvalue : first.value = second.value)
    (hderivative : first.derivative = second.derivative) :
    first = second := by
  cases first with
  | mk firstValue firstDerivative =>
      cases second with
      | mk secondValue secondDerivative =>
          cases hvalue
          cases hderivative
          rfl

private theorem rationalInterval_ext_real
    {first second : RationalInterval}
    (hlower : ((first.lower : ℚ) : ℝ) = ((second.lower : ℚ) : ℝ))
    (hupper : ((first.upper : ℚ) : ℝ) = ((second.upper : ℚ) : ℝ)) :
    first = second := by
  cases first with
  | mk firstLower firstUpper =>
      cases second with
      | mk secondLower secondUpper =>
          have hlower' : firstLower = secondLower := by
            exact_mod_cast hlower
          have hupper' : firstUpper = secondUpper := by
            exact_mod_cast hupper
          cases hlower'
          cases hupper'
          rfl

private theorem integerTableAffineDualCache_eq_zero :
    evalDualInterval integerTableRationalBox
        (integerTableAffineExpression 0) =
      integerTableAffineDualCache 0 := by
  apply intervalDual_ext
  · apply rationalInterval_ext_real <;>
      simp [integerTableAffineDualCache, integerTableAffineExpression,
        integerTableRationalBox, evalDualInterval, IntervalDual.constant,
        IntervalDual.ofVariable, IntervalDual.add, IntervalDual.mul] <;>
      norm_num
  · funext column
    fin_cases column <;> apply rationalInterval_ext_real <;>
      simp [integerTableAffineDualCache, integerTableAffineExpression,
        integerTableRationalBox, evalDualInterval, IntervalDual.constant,
        IntervalDual.ofVariable, IntervalDual.add, IntervalDual.mul]

private theorem integerTableAffineDualCache_eq_one :
    evalDualInterval integerTableRationalBox
        (integerTableAffineExpression 1) =
      integerTableAffineDualCache 1 := by
  apply intervalDual_ext
  · apply rationalInterval_ext_real <;>
      simp [integerTableAffineDualCache, integerTableAffineExpression,
        integerTableRationalBox, evalDualInterval, IntervalDual.constant,
        IntervalDual.ofVariable, IntervalDual.add, IntervalDual.mul] <;>
      norm_num
  · funext column
    fin_cases column <;> apply rationalInterval_ext_real <;>
      simp [integerTableAffineDualCache, integerTableAffineExpression,
        integerTableRationalBox, evalDualInterval, IntervalDual.constant,
        IntervalDual.ofVariable, IntervalDual.add, IntervalDual.mul]

private theorem integerTableAffineDualCache_eq_two :
    evalDualInterval integerTableRationalBox
        (integerTableAffineExpression 2) =
      integerTableAffineDualCache 2 := by
  apply intervalDual_ext
  · apply rationalInterval_ext_real <;>
      simp [integerTableAffineDualCache, integerTableAffineExpression,
        integerTableRationalBox, evalDualInterval, IntervalDual.constant,
        IntervalDual.ofVariable, IntervalDual.add, IntervalDual.mul] <;>
      norm_num
  · funext column
    fin_cases column <;> apply rationalInterval_ext_real <;>
      simp [integerTableAffineDualCache, integerTableAffineExpression,
        integerTableRationalBox, evalDualInterval, IntervalDual.constant,
        IntervalDual.ofVariable, IntervalDual.add, IntervalDual.mul]

private theorem integerTableAffineDualCache_eq_three :
    evalDualInterval integerTableRationalBox
        (integerTableAffineExpression 3) =
      integerTableAffineDualCache 3 := by
  apply intervalDual_ext
  · apply rationalInterval_ext_real <;>
      simp [integerTableAffineDualCache, integerTableAffineExpression,
        integerTableRationalBox, evalDualInterval, IntervalDual.constant,
        IntervalDual.ofVariable, IntervalDual.add, IntervalDual.mul] <;>
      norm_num
  · funext column
    fin_cases column <;> apply rationalInterval_ext_real <;>
      simp [integerTableAffineDualCache, integerTableAffineExpression,
        integerTableRationalBox, evalDualInterval, IntervalDual.constant,
        IntervalDual.ofVariable, IntervalDual.add, IntervalDual.mul]

theorem integerTableAffineDualCache_eq (row : Player) :
    evalDualInterval integerTableRationalBox
        (integerTableAffineExpression row) =
      integerTableAffineDualCache row := by
  fin_cases row
  · exact integerTableAffineDualCache_eq_zero
  · exact integerTableAffineDualCache_eq_one
  · exact integerTableAffineDualCache_eq_two
  · exact integerTableAffineDualCache_eq_three

/-- Cached exact derivative enclosures for the reflected residual step. -/
def integerTableDerivativeCache : Player → Player → RationalInterval :=
  ![![⟨276217579 / (4 * 10 ^ 11), 1404979403 / (2 * 10 ^ 12)⟩,
      ⟨2937302047 / 10 ^ 13, 2991965827 / 10 ^ 13⟩,
      ⟨-412271901 / 10 ^ 13, -330322941 / 10 ^ 13⟩,
      ⟨32179183 / 78125000000, 131914507 / 312500000000⟩],
    ![⟨-42805220591677662609 / (5 * 10 ^ 22),
        -42554613506416821129 / (5 * 10 ^ 22)⟩,
      ⟨-16436813814175542021 / (25 * 10 ^ 21),
        -16310545833655365941 / (25 * 10 ^ 21)⟩,
      ⟨-53049025047442019227 / (5 * 10 ^ 22),
        -52778301579660115087 / (5 * 10 ^ 22)⟩,
      ⟨42043420541324992609 / (5 * 10 ^ 22),
        42476319225177342829 / (5 * 10 ^ 22)⟩],
    ![⟨-101546559172642572679 / 10 ^ 23,
        -100377073122414113379 / 10 ^ 23⟩,
      ⟨-110728182425138115497 / 10 ^ 23,
        -110239502995234700097 / 10 ^ 23⟩,
      ⟨-195660111207241744657 / 10 ^ 23,
        -194719864849129605557 / 10 ^ 23⟩,
      ⟨37359932379164864839 / 10 ^ 23,
        38587926598347562439 / 10 ^ 23⟩],
    ![⟨3778959509539597571 / (25 * 10 ^ 21),
        3948615105474751151 / (25 * 10 ^ 21)⟩,
      ⟨-1731905784014716123 / (5 * 10 ^ 22),
        -1482280696960271023 / (5 * 10 ^ 22)⟩,
      ⟨50180351152530666033 / (5 * 10 ^ 22),
        50364702620032358403 / (5 * 10 ^ 22)⟩,
      ⟨-72547878889567641947 / 10 ^ 23,
        -71752297466677879127 / 10 ^ 23⟩]]

theorem integerTableDerivativeCache_eq (row column : Player) :
    (evalDualInterval integerTableRationalBox
      (integerTableStepExpression row)).derivative column =
        integerTableDerivativeCache row column := by
  fin_cases row <;> fin_cases column <;>
    simp only [integerTableStepExpression,
      integerTableResidualExpression, HSub.hSub, Sub.sub,
      evalDualInterval, IntervalDual.add, IntervalDual.neg,
      IntervalDual.mul, IntervalDual.constant, IntervalDual.ofVariable,
      integerTableAffineDualCache_eq] <;>
    norm_num [integerTableDerivativeCache,
      integerTableAffineDualCache, RationalInterval.point,
      RationalInterval.add, RationalInterval.neg, RationalInterval.mul,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three]

/-- The four exact derivative row sums in the contraction certificate. -/
def integerTableDerivativeRowSum : Player → ℚ :=
  ![14650398967 / 10 ^ 13,
    171204192492648108707 / (5 * 10 ^ 22),
    55815347425421249409 / (125 * 10 ^ 20),
    192535556119560795603 / 10 ^ 23]

theorem integerTableStepExpression_rowSum_value (row : Player) :
    ∑ column,
        rationalAbsBound
          ((evalDualInterval integerTableRationalBox
            (integerTableStepExpression row)).derivative column) =
      (integerTableDerivativeRowSum row : ℝ) := by
  simp_rw [integerTableDerivativeCache_eq]
  fin_cases row <;>
    norm_num [integerTableDerivativeCache, integerTableDerivativeRowSum,
      rationalAbsBound, Fin.sum_univ_succ, Real.norm_eq_abs,
      abs_of_nonneg, abs_of_nonpos, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]

theorem integerTableStepExpression_rowSum (row : Player) :
    ∑ column,
        rationalAbsBound
          ((evalDualInterval integerTableRationalBox
            (integerTableStepExpression row)).derivative column) ≤
      (integerTableContraction : ℝ) := by
  rw [integerTableStepExpression_rowSum_value]
  fin_cases row <;>
    norm_num [integerTableDerivativeRowSum, integerTableContraction,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]

/-- Exact evaluation of the four residuals at the rational chart center. -/
theorem integerTableResidual_center_value :
    integerTableCubeResidual 0 =
      ![1732473241 / (5 * 10 ^ 19),
        7039082593629169961 / 10 ^ 29,
        12514868747864475471 / (2 * 10 ^ 29),
        -69568260756753837021 / 10 ^ 30] := by
  funext row
  fin_cases row <;>
    norm_num [integerTableCubeResidual, integerTableParameterResidual,
      integerTableAffineParameter, integerTableCenter,
      integerTableChartMatrix, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]

theorem integerTableResidual_center_bound :
    ‖integerTableCubeResidual 0‖ ≤
      (1 - (integerTableContraction : ℝ)) * integerTableRadius := by
  rw [pi_norm_le_iff_of_nonneg]
  · intro row
    rw [integerTableResidual_center_value]
    fin_cases row <;>
      norm_num [integerTableContraction, integerTableRadius,
        Real.norm_eq_abs, abs_of_nonneg, abs_of_nonpos,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three]
  · norm_num [integerTableContraction, integerTableRadius]

/-- There is exactly one pulled-back residual zero in the certified cube. -/
theorem existsUnique_integerTableCubeResidual_zero :
    ∃! z : Player → ℝ,
      z ∈ closedBall 0 integerTableRadius ∧
        integerTableCubeResidual z = 0 := by
  apply existsUnique_zero_in_closedBall_of_evalDualInterval_absRowSum
    integerTableCubeResidual (ContinuousLinearMap.id ℝ (Player → ℝ))
      integerTableStepExpression integerTableRationalBox 0 integerTableRadius
      integerTableContraction
  · norm_num [integerTableRadius]
  · norm_num [integerTableContraction]
  · exact injective_id
  · funext z
    exact integerTableStepExpression_evalReal z
  · exact integerTableRationalBox_endpoints
  · exact integerTableStepExpression_rowSum
  · simpa using integerTableResidual_center_bound

/-- The exact cube root selected from the contraction certificate. -/
noncomputable def integerTableCubeRoot : Player → ℝ :=
  Classical.choose existsUnique_integerTableCubeResidual_zero.exists

theorem integerTableCubeRoot_mem :
    integerTableCubeRoot ∈ closedBall 0 integerTableRadius :=
  (Classical.choose_spec existsUnique_integerTableCubeResidual_zero.exists).1

theorem integerTableCubeRoot_residual_zero :
    integerTableCubeResidual integerTableCubeRoot = 0 :=
  (Classical.choose_spec existsUnique_integerTableCubeResidual_zero.exists).2

/-- The exact algebraic parameter used by the period-three block. -/
noncomputable def integerTableParameter : Player → ℝ :=
  integerTableAffineParameter integerTableCubeRoot

theorem integerTableParameter_residual_zero :
    integerTableParameterResidual integerTableParameter = 0 := by
  exact integerTableCubeRoot_residual_zero

private theorem integerTableCubeRoot_abs_le (coordinate : Player) :
    |integerTableCubeRoot coordinate| ≤ integerTableRadius := by
  have hnorm : ‖integerTableCubeRoot‖ ≤ integerTableRadius := by
    simpa [mem_closedBall, dist_eq_norm] using integerTableCubeRoot_mem
  calc
    |integerTableCubeRoot coordinate| =
        ‖integerTableCubeRoot coordinate‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖integerTableCubeRoot‖ :=
      norm_le_pi_norm integerTableCubeRoot coordinate
    _ ≤ integerTableRadius := hnorm

/-- The selected parameter lies strictly inside the displayed rational
coordinate bounds. -/
theorem integerTableParameter_bounds :
    11 / 50 < integerTableParameter 0 ∧
      integerTableParameter 0 < 23 / 100 ∧
      11 / 25 < integerTableParameter 1 ∧
      integerTableParameter 1 < 9 / 20 ∧
      1 / 20 < integerTableParameter 2 ∧
      integerTableParameter 2 < 3 / 50 ∧
      1 / 5 < integerTableParameter 3 ∧
      integerTableParameter 3 < 21 / 100 := by
  rcases abs_le.mp (integerTableCubeRoot_abs_le 0) with ⟨hzeroLower, hzeroUpper⟩
  rcases abs_le.mp (integerTableCubeRoot_abs_le 1) with ⟨honeLower, honeUpper⟩
  rcases abs_le.mp (integerTableCubeRoot_abs_le 2) with ⟨htwoLower, htwoUpper⟩
  rcases abs_le.mp (integerTableCubeRoot_abs_le 3) with ⟨hthreeLower, hthreeUpper⟩
  norm_num [integerTableParameter, integerTableAffineParameter,
    integerTableCenter, integerTableChartMatrix, integerTableRadius,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three] at *
  change -(1 / 1000000) ≤ integerTableCubeRoot (Fin.succ 2) at hthreeLower
  change integerTableCubeRoot (Fin.succ 2) ≤ 1 / 1000000 at hthreeUpper
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The explicit affine parallelotope in which the parameter is isolated. -/
def integerTableParallelotope : Set (Player → ℝ) :=
  integerTableAffineParameter '' closedBall 0 integerTableRadius

/-- There is exactly one parameter in the displayed parallelotope at which
all four block residuals vanish.  No global uniqueness is asserted. -/
theorem existsUnique_integerTableParameterResidual_zero_in_parallelotope :
    ∃! parameter : Player → ℝ,
      parameter ∈ integerTableParallelotope ∧
        integerTableParameterResidual parameter = 0 := by
  refine ⟨integerTableParameter, ?_, ?_⟩
  · exact ⟨⟨integerTableCubeRoot, integerTableCubeRoot_mem, rfl⟩,
      integerTableParameter_residual_zero⟩
  · intro parameter hparameter
    rcases hparameter.1 with ⟨z, hz, rfl⟩
    have hzZero : integerTableCubeResidual z = 0 := hparameter.2
    have hroot : z = integerTableCubeRoot :=
      existsUnique_integerTableCubeResidual_zero.unique
        ⟨hz, hzZero⟩
        ⟨integerTableCubeRoot_mem, integerTableCubeRoot_residual_zero⟩
    simpa [integerTableParameter] using
      congrArg integerTableAffineParameter hroot

/-! ## The literal reward table and period-three block -/

/-- Binary mask of a quitting coalition. -/
def integerTableCoalitionMask (coalition : Finset Player) : Nat :=
  ∑ who ∈ coalition, 2 ^ who.val

/-- The fifteen literal payoff rows in binary mask order. -/
def integerTableRewardRow : Nat → Payoff Player
  | 1 => ![1, 3, 3, 0]
  | 2 => ![4, 1, -1, -1]
  | 3 => ![1, 1, 1, -2]
  | 4 => ![0, 2, 1, 2]
  | 5 => ![1, 4, 1, 1]
  | 6 => ![3, 1, 1, 0]
  | 7 => ![1, 1, 1, -1]
  | 8 => ![4, -2, 0, 1]
  | 9 => ![1, 0, 2, 1]
  | 10 => ![7, 1, -2, 1]
  | 11 => ![1, 1, 0, 1]
  | 12 => ![3, -1, 1, 1]
  | 13 => ![1, 1, 1, 1]
  | 14 => ![6, 1, 1, 1]
  | 15 => ![11, -1, 1, 0]
  | _ => 0

/-- The exact four-player quitting reward from the packet. -/
def integerTableReward :
    {coalition : Finset Player // coalition.Nonempty} → Payoff Player :=
  fun coalition ↦ integerTableRewardRow
    (integerTableCoalitionMask coalition.1)

@[simp] theorem integerTableReward_mask_one :
    integerTableReward ⟨{0}, by simp⟩ = ![1, 3, 3, 0] := by
  change integerTableRewardRow (integerTableCoalitionMask {0}) = _
  rw [show integerTableCoalitionMask {0} = 1 by decide]
  rfl

@[simp] theorem integerTableReward_mask_two :
    integerTableReward ⟨{1}, by simp⟩ = ![4, 1, -1, -1] := by
  change integerTableRewardRow (integerTableCoalitionMask {1}) = _
  rw [show integerTableCoalitionMask {1} = 2 by decide]
  rfl

@[simp] theorem integerTableReward_mask_three :
    integerTableReward ⟨{0, 1}, by simp⟩ = ![1, 1, 1, -2] := by
  change integerTableRewardRow (integerTableCoalitionMask {0, 1}) = _
  rw [show integerTableCoalitionMask {0, 1} = 3 by decide]
  rfl

@[simp] theorem integerTableReward_mask_four :
    integerTableReward ⟨{2}, by simp⟩ = ![0, 2, 1, 2] := by
  change integerTableRewardRow (integerTableCoalitionMask {2}) = _
  rw [show integerTableCoalitionMask {2} = 4 by decide]
  rfl

@[simp] theorem integerTableReward_mask_five :
    integerTableReward ⟨{0, 2}, by simp⟩ = ![1, 4, 1, 1] := by
  change integerTableRewardRow (integerTableCoalitionMask {0, 2}) = _
  rw [show integerTableCoalitionMask {0, 2} = 5 by decide]
  rfl

@[simp] theorem integerTableReward_mask_six :
    integerTableReward ⟨{1, 2}, by simp⟩ = ![3, 1, 1, 0] := by
  change integerTableRewardRow (integerTableCoalitionMask {1, 2}) = _
  rw [show integerTableCoalitionMask {1, 2} = 6 by decide]
  rfl

@[simp] theorem integerTableReward_mask_seven :
    integerTableReward ⟨{0, 1, 2}, by simp⟩ = ![1, 1, 1, -1] := by
  change integerTableRewardRow (integerTableCoalitionMask {0, 1, 2}) = _
  rw [show integerTableCoalitionMask {0, 1, 2} = 7 by decide]
  rfl

@[simp] theorem integerTableReward_mask_eight :
    integerTableReward ⟨{3}, by simp⟩ = ![4, -2, 0, 1] := by
  change integerTableRewardRow (integerTableCoalitionMask {3}) = _
  rw [show integerTableCoalitionMask {3} = 8 by decide]
  rfl

@[simp] theorem integerTableReward_mask_nine :
    integerTableReward ⟨{0, 3}, by simp⟩ = ![1, 0, 2, 1] := by
  change integerTableRewardRow (integerTableCoalitionMask {0, 3}) = _
  rw [show integerTableCoalitionMask {0, 3} = 9 by decide]
  rfl

@[simp] theorem integerTableReward_mask_ten :
    integerTableReward ⟨{1, 3}, by simp⟩ = ![7, 1, -2, 1] := by
  change integerTableRewardRow (integerTableCoalitionMask {1, 3}) = _
  rw [show integerTableCoalitionMask {1, 3} = 10 by decide]
  rfl

@[simp] theorem integerTableReward_mask_eleven :
    integerTableReward ⟨{0, 1, 3}, by simp⟩ = ![1, 1, 0, 1] := by
  change integerTableRewardRow (integerTableCoalitionMask {0, 1, 3}) = _
  rw [show integerTableCoalitionMask {0, 1, 3} = 11 by decide]
  rfl

@[simp] theorem integerTableReward_mask_twelve :
    integerTableReward ⟨{2, 3}, by simp⟩ = ![3, -1, 1, 1] := by
  change integerTableRewardRow (integerTableCoalitionMask {2, 3}) = _
  rw [show integerTableCoalitionMask {2, 3} = 12 by decide]
  rfl

@[simp] theorem integerTableReward_mask_thirteen :
    integerTableReward ⟨{0, 2, 3}, by simp⟩ = ![1, 1, 1, 1] := by
  change integerTableRewardRow (integerTableCoalitionMask {0, 2, 3}) = _
  rw [show integerTableCoalitionMask {0, 2, 3} = 13 by decide]
  rfl

@[simp] theorem integerTableReward_mask_fourteen :
    integerTableReward ⟨{1, 2, 3}, by simp⟩ = ![6, 1, 1, 1] := by
  change integerTableRewardRow (integerTableCoalitionMask {1, 2, 3}) = _
  rw [show integerTableCoalitionMask {1, 2, 3} = 14 by decide]
  rfl

@[simp] theorem integerTableReward_mask_fifteen :
    integerTableReward ⟨{0, 1, 2, 3}, by simp⟩ = ![11, -1, 1, 0] := by
  change integerTableRewardRow (integerTableCoalitionMask {0, 1, 2, 3}) = _
  rw [show integerTableCoalitionMask {0, 1, 2, 3} = 15 by decide]
  rfl

/-- The four exact algebraic parameters, in packet notation. -/
noncomputable abbrev integerTableA : ℝ := integerTableParameter 0
noncomputable abbrev integerTableB : ℝ := integerTableParameter 1
noncomputable abbrev integerTableC : ℝ := integerTableParameter 2
noncomputable abbrev integerTableD : ℝ := integerTableParameter 3

/-- Hazards supported successively on `{0}`, `{2}`, and `{1, 3}`. -/
noncomputable def integerTableHazard : Fin 3 → Player → ℝ :=
  ![![integerTableA, 0, 0, 0],
    ![0, 0, integerTableB, 0],
    ![0, integerTableC, 0, integerTableD]]

/-- The closed four-row path for the period-three block. -/
noncomputable def integerTableValue : Fin 4 → Payoff Player :=
  let a := integerTableA
  let b := integerTableB
  let c := integerTableC
  let d := integerTableD
  ![![1, 1 + 2 * a + b - a * b, 1 + 2 * a, (1 - a) * (1 + b)],
    ![1, 1 + b, 1, 1 + b],
    ![1 + 3 * c + 3 * d, 1, 1, 1],
    ![1, 1 + 2 * a + b - a * b, 1 + 2 * a, (1 - a) * (1 + b)]]

theorem integerTableHazard_nonneg :
    ∀ phase who, 0 ≤ integerTableHazard phase who := by
  intro phase who
  rcases integerTableParameter_bounds with
    ⟨ha0, ha1, hb0, hb1, hc0, hc1, hd0, hd1⟩
  fin_cases phase <;> fin_cases who <;>
    simp [integerTableHazard] <;> linarith

theorem integerTableHazard_le_one :
    ∀ phase who, integerTableHazard phase who ≤ 1 := by
  intro phase who
  rcases integerTableParameter_bounds with
    ⟨ha0, ha1, hb0, hb1, hc0, hc1, hd0, hd1⟩
  fin_cases phase <;> fin_cases who <;>
    simp [integerTableHazard] <;> linarith

@[simp] theorem integerTableValue_last :
    integerTableValue (Fin.last 3) = integerTableValue 0 := by
  rfl

private theorem integerTableRoot_zero_active :
    IsQuittingActiveRoot {0}
      (quittingBlockCycle integerTableHazard integerTableHazard_nonneg
        integerTableHazard_le_one 0) := by
  intro who hwho
  fin_cases who <;>
    simp [quittingBlockCycle, rootOfHazard, integerTableHazard] at hwho ⊢
  all_goals exact quittingHazardCoin_zero _ _

private theorem integerTableRoot_two_active :
    IsQuittingActiveRoot {2}
      (quittingBlockCycle integerTableHazard integerTableHazard_nonneg
        integerTableHazard_le_one 1) := by
  intro who hwho
  fin_cases who <;>
    simp [quittingBlockCycle, rootOfHazard, integerTableHazard] at hwho ⊢
  all_goals exact quittingHazardCoin_zero _ _

private theorem integerTableRoot_one_three_active :
    IsQuittingActiveRoot {1, 3}
      (quittingBlockCycle integerTableHazard integerTableHazard_nonneg
        integerTableHazard_le_one 2) := by
  intro who hwho
  fin_cases who <;>
    simp [quittingBlockCycle, rootOfHazard, integerTableHazard] at hwho ⊢
  all_goals exact quittingHazardCoin_zero _ _

theorem integerTableRoot_zero_successor :
    quittingRootSuccessorPayoff integerTableReward (integerTableValue 1)
        (quittingBlockCycle integerTableHazard integerTableHazard_nonneg
          integerTableHazard_le_one 0) =
      integerTableValue 0 := by
  funext who
  change quittingRootExpectedPayoff integerTableReward (integerTableValue 1)
    (quittingBlockCycle integerTableHazard integerTableHazard_nonneg
      integerTableHazard_le_one 0) who = _
  rw [quittingRootExpectedPayoff_singleton_active integerTableReward
    (integerTableValue 1) _ 0 who integerTableRoot_zero_active]
  rw [hazardOfRoot_quittingBlockCycle]
  fin_cases who <;>
    norm_num [integerTableHazard, integerTableValue, integerTableReward,
      integerTableRewardRow, integerTableCoalitionMask,
      Fin.sum_univ_succ] <;> ring

theorem integerTableRoot_two_successor :
    quittingRootSuccessorPayoff integerTableReward (integerTableValue 2)
        (quittingBlockCycle integerTableHazard integerTableHazard_nonneg
          integerTableHazard_le_one 1) =
      integerTableValue 1 := by
  funext who
  change quittingRootExpectedPayoff integerTableReward (integerTableValue 2)
    (quittingBlockCycle integerTableHazard integerTableHazard_nonneg
      integerTableHazard_le_one 1) who = _
  rw [quittingRootExpectedPayoff_singleton_active integerTableReward
    (integerTableValue 2) _ 2 who integerTableRoot_two_active]
  rw [hazardOfRoot_quittingBlockCycle]
  have hzero := congrFun integerTableParameter_residual_zero 0
  fin_cases who <;>
    simp +decide [integerTableHazard, integerTableValue, integerTableReward,
      integerTableRewardRow, integerTableCoalitionMask,
      integerTableParameterResidual, integerTableA, integerTableB,
      integerTableC, integerTableD] at hzero ⊢ <;>
    nlinarith

theorem integerTableRoot_one_three_successor :
    quittingRootSuccessorPayoff integerTableReward (integerTableValue 0)
        (quittingBlockCycle integerTableHazard integerTableHazard_nonneg
          integerTableHazard_le_one 2) =
      integerTableValue 2 := by
  funext who
  change quittingRootExpectedPayoff integerTableReward (integerTableValue 0)
    (quittingBlockCycle integerTableHazard integerTableHazard_nonneg
      integerTableHazard_le_one 2) who = _
  rw [quittingRootExpectedPayoff_pair_active integerTableReward
    (integerTableValue 0) _ 1 3 who (by decide)
    integerTableRoot_one_three_active]
  simp only [hazardOfRoot_quittingBlockCycle]
  have hone := congrFun integerTableParameter_residual_zero 1
  have htwo := congrFun integerTableParameter_residual_zero 2
  have hthree := congrFun integerTableParameter_residual_zero 3
  fin_cases who
  all_goals
    simp +decide [integerTableHazard, integerTableValue, integerTableReward,
      integerTableRewardRow, integerTableCoalitionMask,
      integerTableParameterResidual, integerTableA, integerTableB,
      integerTableC, integerTableD] at hone htwo hthree ⊢
  · nlinarith
  · linear_combination (integerTableC - 1) * htwo
  · nlinarith
  · linear_combination (integerTableD - 1) * hthree

/-! ## Exact endpoint differences -/

@[simp] private theorem expect_integerTableCoin
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Bool → ℝ) :
    expect (quittingHazardCoin p hp0 hp1) f =
      (1 - p) * f false + p * f true := by
  rw [expect_eq_sum, Fintype.sum_bool]
  simp
  ring

@[simp] private theorem integerTableQuitters_only_zero :
    {who : Player | ![true, false, false, false] who = true} = {0} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem integerTableQuitters_only_one :
    {who : Player | ![false, true, false, false] who = true} = {1} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem integerTableQuitters_only_two :
    {who : Player | ![false, false, true, false] who = true} = {2} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem integerTableQuitters_only_three :
    {who : Player | ![false, false, false, true] who = true} = {3} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem integerTableQuitters_zero_one :
    {who : Player | ![true, true, false, false] who = true} = {0, 1} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem integerTableQuitters_zero_two :
    {who : Player | ![true, false, true, false] who = true} = {0, 2} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem integerTableQuitters_zero_three :
    {who : Player | ![true, false, false, true] who = true} = {0, 3} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem integerTableQuitters_one_two :
    {who : Player | ![false, true, true, false] who = true} = {1, 2} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem integerTableQuitters_one_three :
    {who : Player | ![false, true, false, true] who = true} = {1, 3} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem integerTableQuitters_two_three :
    {who : Player | ![false, false, true, true] who = true} = {2, 3} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem integerTableQuitters_zero_one_three :
    {who : Player | ![true, true, false, true] who = true} = {0, 1, 3} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem integerTableQuitters_one_two_three :
    {who : Player | ![false, true, true, true] who = true} = {1, 2, 3} := by
  ext who
  fin_cases who <;> simp

@[simp] private theorem integerTableReward_quitters_only_zero
    (hne : ({who : Player | ![true, false, false, false] who = true} :
      Finset Player).Nonempty) (who : Player) :
    integerTableReward
        ⟨({player | ![true, false, false, false] player = true} : Finset Player), hne⟩ who =
      integerTableReward ⟨{0}, by simp⟩ who := by
  congr 1

@[simp] private theorem integerTableReward_quitters_only_one
    (hne : ({who : Player | ![false, true, false, false] who = true} :
      Finset Player).Nonempty) (who : Player) :
    integerTableReward
        ⟨({player | ![false, true, false, false] player = true} : Finset Player), hne⟩ who =
      integerTableReward ⟨{1}, by simp⟩ who := by
  congr 1

@[simp] private theorem integerTableReward_quitters_only_two
    (hne : ({who : Player | ![false, false, true, false] who = true} :
      Finset Player).Nonempty) (who : Player) :
    integerTableReward
        ⟨({player | ![false, false, true, false] player = true} : Finset Player), hne⟩ who =
      integerTableReward ⟨{2}, by simp⟩ who := by
  congr 1

@[simp] private theorem integerTableReward_quitters_only_three
    (hne : ({who : Player | ![false, false, false, true] who = true} :
      Finset Player).Nonempty) (who : Player) :
    integerTableReward
        ⟨({player | ![false, false, false, true] player = true} : Finset Player), hne⟩ who =
      integerTableReward ⟨{3}, by simp⟩ who := by
  congr 1

@[simp] private theorem integerTableReward_quitters_zero_one
    (hne : ({who : Player | ![true, true, false, false] who = true} :
      Finset Player).Nonempty) (who : Player) :
    integerTableReward
        ⟨({player | ![true, true, false, false] player = true} : Finset Player), hne⟩ who =
      integerTableReward ⟨{0, 1}, by simp⟩ who := by
  congr 1

@[simp] private theorem integerTableReward_quitters_zero_two
    (hne : ({who : Player | ![true, false, true, false] who = true} :
      Finset Player).Nonempty) (who : Player) :
    integerTableReward
        ⟨({player | ![true, false, true, false] player = true} : Finset Player), hne⟩ who =
      integerTableReward ⟨{0, 2}, by simp⟩ who := by
  congr 1

@[simp] private theorem integerTableReward_quitters_zero_three
    (hne : ({who : Player | ![true, false, false, true] who = true} :
      Finset Player).Nonempty) (who : Player) :
    integerTableReward
        ⟨({player | ![true, false, false, true] player = true} : Finset Player), hne⟩ who =
      integerTableReward ⟨{0, 3}, by simp⟩ who := by
  congr 1

@[simp] private theorem integerTableReward_quitters_one_two
    (hne : ({who : Player | ![false, true, true, false] who = true} :
      Finset Player).Nonempty) (who : Player) :
    integerTableReward
        ⟨({player | ![false, true, true, false] player = true} : Finset Player), hne⟩ who =
      integerTableReward ⟨{1, 2}, by simp⟩ who := by
  congr 1

@[simp] private theorem integerTableReward_quitters_one_three
    (hne : ({who : Player | ![false, true, false, true] who = true} :
      Finset Player).Nonempty) (who : Player) :
    integerTableReward
        ⟨({player | ![false, true, false, true] player = true} : Finset Player), hne⟩ who =
      integerTableReward ⟨{1, 3}, by simp⟩ who := by
  congr 1

@[simp] private theorem integerTableReward_quitters_two_three
    (hne : ({who : Player | ![false, false, true, true] who = true} :
      Finset Player).Nonempty) (who : Player) :
    integerTableReward
        ⟨({player | ![false, false, true, true] player = true} : Finset Player), hne⟩ who =
      integerTableReward ⟨{2, 3}, by simp⟩ who := by
  congr 1

@[simp] private theorem integerTableReward_quitters_zero_one_three
    (hne : ({who : Player | ![true, true, false, true] who = true} :
      Finset Player).Nonempty) (who : Player) :
    integerTableReward
        ⟨({player | ![true, true, false, true] player = true} : Finset Player), hne⟩ who =
      integerTableReward ⟨{0, 1, 3}, by simp⟩ who := by
  congr 1

@[simp] private theorem integerTableReward_quitters_one_two_three
    (hne : ({who : Player | ![false, true, true, true] who = true} :
      Finset Player).Nonempty) (who : Player) :
    integerTableReward
        ⟨({player | ![false, true, true, true] player = true} : Finset Player), hne⟩ who =
      integerTableReward ⟨{1, 2, 3}, by simp⟩ who := by
  congr 1

/-- The literal Quit-minus-Continue table.  In particular, it records the
inactive ties at `(1, 0)` and `(2, 2)` instead of calling them strict. -/
noncomputable def integerTableEndpointGap : Fin 3 → Player → ℝ :=
  let a := integerTableA
  let b := integerTableB
  let c := integerTableC
  let d := integerTableD
  ![![0, a * b - 2 * a - b, -2 * a, a * b + a - b],
    ![3 * b * c + 3 * b * d + b - 3 * c - 3 * d, -b, 0, -b],
    ![-3 * (c + d),
      -a * b * d + a * b + 2 * a * d - 2 * a + b * d - b + 3 * d,
      -2 * a * c * d + 2 * a * c + 2 * a * d - 2 * a + 2 * c + d,
      -a * b * c + a * b - a * c + a + b * c - b + 2 * c]]

private theorem integerTableRoot_endpointDifference_zero (who : Player) :
    quittingRootEndpointDifference integerTableReward
        (integerTableValue (Fin.succ 0))
        (quittingBlockCycle integerTableHazard integerTableHazard_nonneg
          integerTableHazard_le_one 0) who =
      integerTableEndpointGap 0 who := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4,
    Math.PMFProduct.expect_pmfPi_fin4]
  fin_cases who <;>
    simp +decide [quittingBlockCycle, rootOfHazard, integerTableHazard,
      quittingRootPayoff, quittingQuitters, integerTableValue,
      integerTableEndpointGap, integerTableA, integerTableB,
      integerTableC, integerTableD] <;> ring

private theorem integerTableRoot_endpointDifference_one (who : Player) :
    quittingRootEndpointDifference integerTableReward
        (integerTableValue (Fin.succ 1))
        (quittingBlockCycle integerTableHazard integerTableHazard_nonneg
          integerTableHazard_le_one 1) who =
      integerTableEndpointGap 1 who := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4,
    Math.PMFProduct.expect_pmfPi_fin4]
  fin_cases who <;>
    simp +decide [quittingBlockCycle, rootOfHazard, integerTableHazard,
      quittingRootPayoff, quittingQuitters, integerTableValue,
      integerTableEndpointGap, integerTableA, integerTableB,
      integerTableC, integerTableD] <;> ring

private theorem integerTableRoot_endpointDifference_two_zero :
    quittingRootEndpointDifference integerTableReward
        (integerTableValue (Fin.succ 2))
        (quittingBlockCycle integerTableHazard integerTableHazard_nonneg
          integerTableHazard_le_one 2) 0 =
      integerTableEndpointGap 2 0 := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4,
    Math.PMFProduct.expect_pmfPi_fin4]
  simp +decide [quittingBlockCycle, rootOfHazard, integerTableHazard,
    quittingRootPayoff, quittingQuitters, integerTableValue,
    integerTableEndpointGap, integerTableA, integerTableB,
    integerTableC, integerTableD]
  ring

private theorem integerTableRoot_endpointDifference_two_one :
    quittingRootEndpointDifference integerTableReward
        (integerTableValue (Fin.succ 2))
        (quittingBlockCycle integerTableHazard integerTableHazard_nonneg
          integerTableHazard_le_one 2) 1 =
      integerTableEndpointGap 2 1 := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4,
    Math.PMFProduct.expect_pmfPi_fin4]
  simp +decide [quittingBlockCycle, rootOfHazard, integerTableHazard,
    quittingRootPayoff, quittingQuitters, integerTableValue,
    integerTableEndpointGap, integerTableA, integerTableB,
    integerTableC, integerTableD]
  ring

private theorem integerTableRoot_endpointDifference_two_two :
    quittingRootEndpointDifference integerTableReward
        (integerTableValue (Fin.succ 2))
        (quittingBlockCycle integerTableHazard integerTableHazard_nonneg
          integerTableHazard_le_one 2) 2 =
      integerTableEndpointGap 2 2 := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4,
    Math.PMFProduct.expect_pmfPi_fin4]
  simp +decide [quittingBlockCycle, rootOfHazard, integerTableHazard,
    quittingRootPayoff, quittingQuitters, integerTableValue,
    integerTableEndpointGap, integerTableA, integerTableB,
    integerTableC, integerTableD]
  ring

private theorem integerTableRoot_endpointDifference_two_three :
    quittingRootEndpointDifference integerTableReward
        (integerTableValue (Fin.succ 2))
        (quittingBlockCycle integerTableHazard integerTableHazard_nonneg
          integerTableHazard_le_one 2) 3 =
      integerTableEndpointGap 2 3 := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4,
    Math.PMFProduct.expect_pmfPi_fin4]
  simp +decide [quittingBlockCycle, rootOfHazard, integerTableHazard,
    quittingRootPayoff, quittingQuitters, integerTableValue,
    integerTableEndpointGap, integerTableA, integerTableB,
    integerTableC, integerTableD]
  ring

private theorem integerTableRoot_endpointDifference_two (who : Player) :
    quittingRootEndpointDifference integerTableReward
        (integerTableValue (Fin.succ 2))
        (quittingBlockCycle integerTableHazard integerTableHazard_nonneg
          integerTableHazard_le_one 2) who =
      integerTableEndpointGap 2 who := by
  fin_cases who
  · exact integerTableRoot_endpointDifference_two_zero
  · exact integerTableRoot_endpointDifference_two_one
  · exact integerTableRoot_endpointDifference_two_two
  · exact integerTableRoot_endpointDifference_two_three

/-- Direct evaluation of all twelve endpoint comparisons for the literal
reward table. -/
theorem integerTableRoot_endpointDifference (phase : Fin 3) (who : Player) :
    quittingRootEndpointDifference integerTableReward
        (integerTableValue (Fin.succ phase))
        (quittingBlockCycle integerTableHazard integerTableHazard_nonneg
          integerTableHazard_le_one phase) who =
      integerTableEndpointGap phase who := by
  fin_cases phase
  · exact integerTableRoot_endpointDifference_zero who
  · exact integerTableRoot_endpointDifference_one who
  · exact integerTableRoot_endpointDifference_two who

theorem integerTableHazard_mul_endpointGap_zero (phase : Fin 3) (who : Player) :
    integerTableHazard phase who * integerTableEndpointGap phase who = 0 := by
  have htwo := congrFun integerTableParameter_residual_zero 2
  have hthree := congrFun integerTableParameter_residual_zero 3
  fin_cases phase
  · fin_cases who <;>
      simp [integerTableHazard, integerTableEndpointGap]
  · fin_cases who <;>
      simp [integerTableHazard, integerTableEndpointGap]
  · fin_cases who
    · simp [integerTableHazard, integerTableEndpointGap]
    · simp [integerTableHazard, integerTableEndpointGap,
        integerTableParameterResidual, integerTableA, integerTableB,
        integerTableC, integerTableD] at htwo ⊢
      exact Or.inr htwo
    · simp [integerTableHazard, integerTableEndpointGap]
    · simp [integerTableHazard, integerTableEndpointGap,
        integerTableParameterResidual, integerTableA, integerTableB,
        integerTableC, integerTableD] at hthree ⊢
      exact Or.inr hthree

theorem integerTableEndpointGap_nonpos (phase : Fin 3) (who : Player) :
    integerTableEndpointGap phase who ≤ 0 := by
  rcases integerTableParameter_bounds with
    ⟨ha0, ha1, hb0, hb1, hc0, hc1, hd0, hd1⟩
  have hzero := congrFun integerTableParameter_residual_zero 0
  have hone := congrFun integerTableParameter_residual_zero 1
  have htwo := congrFun integerTableParameter_residual_zero 2
  have hthree := congrFun integerTableParameter_residual_zero 3
  have habFirst :
      0 < (23 / 100 - integerTableA) * integerTableB :=
    mul_pos (by linarith) (by linarith)
  have habSecond :
      0 < (23 / 100) * (9 / 20 - integerTableB) :=
    mul_pos (by norm_num) (by linarith)
  fin_cases phase <;> fin_cases who <;>
    simp [integerTableEndpointGap, integerTableParameterResidual,
      integerTableA, integerTableB, integerTableC,
      integerTableD] at hzero hone htwo hthree ⊢ <;>
    nlinarith

/-- The two inactive comparisons which are exact structural ties. -/
theorem integerTableEndpointGap_inactive_ties :
    integerTableEndpointGap 1 0 = 0 ∧
      integerTableEndpointGap 2 2 = 0 := by
  have hzero := congrFun integerTableParameter_residual_zero 0
  have hone := congrFun integerTableParameter_residual_zero 1
  simp [integerTableEndpointGap, integerTableParameterResidual,
    integerTableA, integerTableB, integerTableC,
    integerTableD] at hzero hone ⊢
  exact ⟨hzero, hone⟩

/-- All six inactive comparisons other than the two structural ties have the
uniform strict margins stated in the packet. -/
theorem integerTableEndpointGap_strict_margins :
    integerTableEndpointGap 0 1 < -1 / 2 ∧
      integerTableEndpointGap 0 2 < -2 / 5 ∧
      integerTableEndpointGap 0 3 < -1 / 10 ∧
      integerTableEndpointGap 1 1 < -2 / 5 ∧
      integerTableEndpointGap 1 3 < -2 / 5 ∧
      integerTableEndpointGap 2 0 < -3 / 4 := by
  rcases integerTableParameter_bounds with
    ⟨ha0, ha1, hb0, hb1, hc0, hc1, hd0, hd1⟩
  have habFirst :
      0 < (23 / 100 - integerTableA) * integerTableB :=
    mul_pos (by linarith) (by linarith)
  have habSecond :
      0 < (23 / 100) * (9 / 20 - integerTableB) :=
    mul_pos (by norm_num) (by linarith)
  simp [integerTableEndpointGap, integerTableA, integerTableB,
    integerTableC, integerTableD]
  refine ⟨by nlinarith, ?_⟩
  refine ⟨by nlinarith, ?_⟩
  refine ⟨by nlinarith, ?_⟩
  refine ⟨by nlinarith, by nlinarith⟩

theorem integerTableRoot_isZeroEndpointNash (phase : Fin 3) :
    IsεQuittingRootEndpointNash integerTableReward
      (integerTableValue (Fin.succ phase)) 0
      (quittingBlockCycle integerTableHazard integerTableHazard_nonneg
        integerTableHazard_le_one phase) := by
  intro who
  rw [integerTableRoot_endpointDifference]
  rw [quittingBlockCycle_false, quittingBlockCycle_true, neg_zero]
  constructor
  · exact mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr (integerTableHazard_le_one phase who))
      (integerTableEndpointGap_nonpos phase who)
  · rw [integerTableHazard_mul_endpointGap_zero]

theorem integerTableValue_abs_le_two (stage : Fin 4) (who : Player) :
    |integerTableValue stage who| ≤ 2 := by
  rcases integerTableParameter_bounds with
    ⟨ha0, ha1, hb0, hb1, hc0, hc1, hd0, hd1⟩
  change 11 / 50 < integerTableA at ha0
  change integerTableA < 23 / 100 at ha1
  change 11 / 25 < integerTableB at hb0
  change integerTableB < 9 / 20 at hb1
  change 1 / 20 < integerTableC at hc0
  change integerTableC < 3 / 50 at hc1
  change 1 / 5 < integerTableD at hd0
  change integerTableD < 21 / 100 at hd1
  have hab0 : 0 ≤ integerTableA * integerTableB :=
    mul_nonneg (by linarith) (by linarith)
  have honeMinusA : 0 ≤ 1 - integerTableA := by linarith
  have honePlusB : 0 ≤ 1 + integerTableB := by linarith
  have hfirst :
      |1 + 2 * integerTableA + integerTableB -
        integerTableA * integerTableB| ≤ 2 := by
    rw [abs_of_nonneg (by nlinarith [hab0])]
    nlinarith [hab0]
  have hsecond : |1 + 2 * integerTableA| ≤ 2 := by
    rw [abs_of_nonneg (by nlinarith)]
    nlinarith
  have hthirdFactors :
      |1 - integerTableA| * |1 + integerTableB| ≤ 2 := by
    rw [abs_of_nonneg honeMinusA, abs_of_nonneg honePlusB]
    nlinarith [hab0]
  have hmiddle : |1 + integerTableB| ≤ 2 := by
    rw [abs_of_nonneg (by nlinarith)]
    nlinarith
  have hjoint : |1 + 3 * integerTableC + 3 * integerTableD| ≤ 2 := by
    rw [abs_of_nonneg (by nlinarith)]
    nlinarith
  fin_cases stage <;> fin_cases who <;>
    simp [integerTableValue] <;> assumption

theorem integerTableRewardBound_at_least_eleven :
    11 ≤ quittingRewardBound integerTableReward := by
  have h := abs_reward_le_quittingRewardBound integerTableReward
    ⟨{0, 1, 2, 3}, by simp⟩ 0
  simpa using h

theorem integerTableValue_box (stage : Fin 4) (who : Player) :
    |integerTableValue stage who| ≤
      quittingRewardBound integerTableReward := by
  exact (integerTableValue_abs_le_two stage who).trans
    ((by norm_num : (2 : ℝ) ≤ 11).trans
      integerTableRewardBound_at_least_eleven)

theorem integerTable_absorbing_phase :
    ∃ phase : Fin 3, continueMass (integerTableHazard phase) < 1 := by
  refine ⟨0, ?_⟩
  have ha0 := integerTableParameter_bounds.1
  simp [continueMass, integerTableHazard, Fin.prod_univ_succ]
  linarith

theorem integerTable_deletedSurvival_lt_one (who : Player) :
    (∏ phase : Fin 3,
      continueMass
        (quittingBlockDeletedHazard integerTableHazard who phase)) < 1 := by
  rcases integerTableParameter_bounds with
    ⟨ha0, ha1, hb0, hb1, hc0, hc1, hd0, hd1⟩
  change 11 / 50 < integerTableA at ha0
  change integerTableA < 23 / 100 at ha1
  change 11 / 25 < integerTableB at hb0
  change integerTableB < 9 / 20 at hb1
  change 1 / 20 < integerTableC at hc0
  change integerTableC < 3 / 50 at hc1
  change 1 / 5 < integerTableD at hd0
  change integerTableD < 21 / 100 at hd1
  have htriple (x y z : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1)
      (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
      x * (y * z) < 1 := by
    have hyz0 : 0 ≤ y * z := mul_nonneg hy0 hz0
    have hyz1 : y * z ≤ 1 := by
      calc
        y * z ≤ 1 * 1 := mul_le_mul hy1 hz1 hz0 (by norm_num)
        _ = 1 := by ring
    have hproduct : x * (y * z) ≤ x := by
      calc
        x * (y * z) ≤ x * 1 := mul_le_mul_of_nonneg_left hyz1 hx0
        _ = x := by ring
    exact hproduct.trans_lt hx1
  fin_cases who
  · simpa +decide [continueMass, quittingBlockDeletedHazard,
      integerTableHazard, Fin.prod_univ_succ, Function.update] using
      htriple (1 - integerTableB) (1 - integerTableC)
        (1 - integerTableD) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith)
  · simpa +decide [continueMass, quittingBlockDeletedHazard,
      integerTableHazard, Fin.prod_univ_succ, Function.update] using
      htriple (1 - integerTableA) (1 - integerTableB)
        (1 - integerTableD) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith)
  · simpa +decide [continueMass, quittingBlockDeletedHazard,
      integerTableHazard, Fin.prod_univ_succ, Function.update] using
      htriple (1 - integerTableA) (1 - integerTableC)
        (1 - integerTableD) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith)
  · simpa +decide [continueMass, quittingBlockDeletedHazard,
      integerTableHazard, Fin.prod_univ_succ, Function.update] using
      htriple (1 - integerTableA) (1 - integerTableB)
        (1 - integerTableC) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith)

theorem integerTable_admissible :
    ∀ who : Player,
      (∏ phase : Fin 3,
          continueMass
            (quittingBlockDeletedHazard integerTableHazard who phase)) < 1 ∨
        0 ≤ integerTableReward (quittingSingletonTerminal who) who := by
  intro who
  exact Or.inl (integerTable_deletedSurvival_lt_one who)

/-! ## Certificate and semantic conclusion -/

/-- The literal period-three profile is an exact admissible block. -/
theorem integerTable_isQuittingBlockCertificate :
    IsQuittingBlockCertificate (m := 2) integerTableReward
      integerTableHazard integerTableValue := by
  refine isQuittingBlockCertificate_of_root integerTableHazard_nonneg
    integerTableHazard_le_one integerTableValue_box integerTableValue_last
    ?_ integerTableRoot_isZeroEndpointNash integerTable_absorbing_phase
    integerTable_admissible
  intro phase
  fin_cases phase
  · exact integerTableRoot_zero_successor.symm
  · exact integerTableRoot_two_successor.symm
  · exact integerTableRoot_one_three_successor.symm

/-- The fixed payoff target displayed in the packet. -/
noncomputable def integerTableTarget : Payoff Player :=
  ![1,
    1 + 2 * integerTableA + integerTableB - integerTableA * integerTableB,
    1 + 2 * integerTableA,
    (1 - integerTableA) * (1 + integerTableB)]

@[simp] theorem integerTableValue_zero :
    integerTableValue 0 = integerTableTarget := by
  rfl

/-- The literal table has the displayed fixed uniform-equilibrium payoff.
The deviation quantifier is over all unilateral behavioral deviations. -/
theorem integerTableTarget_isUniformEquilibriumPayoff :
    (quittingGame integerTableReward).IsUniformEquilibriumPayoff none
      integerTableTarget := by
  rw [← integerTableValue_zero]
  exact isUniformEquilibriumPayoff_of_isQuittingBlockCertificate
    integerTable_isQuittingBlockCertificate

end FullCoreDeadlock
end GameTheory
