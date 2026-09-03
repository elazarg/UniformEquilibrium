import MathUE.Interval.PolynomialLipschitz
import Mathlib.Algebra.BigOperators.Fin

/-!
# Lipschitz bounds with fixed trailing parameters

This scratch module restricts a reflected polynomial in `variableCount +
parameterCount` variables to its leading `variableCount` coordinates.  Exact
interval derivative bounds may still range over a box in all coordinates,
while the resulting Lipschitz estimate varies only the leading coordinates.
-/

noncomputable section

namespace Math
namespace Interval

namespace DyadicInterval

/-- Public expansion of outward-rounded dyadic interval multiplication. -/
theorem mul_eq_outward_four_corners {precision : ℕ}
    (first second : DyadicInterval precision) :
    first.mul second =
      ⟨min (first.lower * second.lower)
          (min (first.lower * second.upper)
            (min (first.upper * second.lower)
              (first.upper * second.upper))) / scale precision,
        -((-max (first.lower * second.lower)
          (max (first.lower * second.upper)
            (max (first.upper * second.lower)
              (first.upper * second.upper)))) / scale precision)⟩ := by
  rfl

end DyadicInterval

namespace RationalPolynomial

open Function Metric Set
open scoped NNReal

variable {variableCount parameterCount : ℕ}

@[simp] theorem DyadicDual.value_constant {precision count : ℕ}
    (value : ℚ) :
    (DyadicDual.constant value : DyadicDual precision count).value =
      DyadicInterval.ofRat value := rfl

@[simp] theorem DyadicDual.value_add {precision count : ℕ}
    (first second : DyadicDual precision count) :
    (first.add second).value = first.value.add second.value := rfl

@[simp] theorem DyadicDual.value_neg {precision count : ℕ}
    (dual : DyadicDual precision count) :
    dual.neg.value = dual.value.neg := rfl

@[simp] theorem DyadicDual.value_mul {precision count : ℕ}
    (first second : DyadicDual precision count) :
    (first.mul second).value = first.value.mul second.value := rfl

@[simp] theorem DyadicDual.derivative_constant {precision count : ℕ}
    (value : ℚ) (coordinate : Fin count) :
    (DyadicDual.constant value : DyadicDual precision count).derivative
        coordinate = DyadicInterval.ofInt 0 := rfl

@[simp] theorem DyadicDual.derivative_add {precision count : ℕ}
    (first second : DyadicDual precision count) (coordinate : Fin count) :
    (first.add second).derivative coordinate =
      (first.derivative coordinate).add
        (second.derivative coordinate) := rfl

@[simp] theorem DyadicDual.derivative_neg {precision count : ℕ}
    (dual : DyadicDual precision count) (coordinate : Fin count) :
    dual.neg.derivative coordinate =
      (dual.derivative coordinate).neg := rfl

@[simp] theorem DyadicDual.derivative_mul {precision count : ℕ}
    (first second : DyadicDual precision count) (coordinate : Fin count) :
    (first.mul second).derivative coordinate =
      ((first.derivative coordinate).mul second.value).add
        (first.value.mul (second.derivative coordinate)) := rfl

/-! ## Exact automatic differentiation on a selected coordinate block -/

/-- One-pass interval evaluation carrying derivatives only in a selected
finite coordinate block.  This avoids materializing irrelevant parameter
derivatives in supplied parameterized data. -/
def evalSelectedDualInterval {ambientCount selectedCount : ℕ}
    (selected : Fin selectedCount → Fin ambientCount)
    (box : Fin ambientCount → RationalInterval) :
    RationalPolynomial ambientCount → IntervalDual selectedCount
  | .constant value => IntervalDual.constant value
  | .var index =>
      ⟨box index, fun coordinate ↦
        RationalInterval.point (if selected coordinate = index then 1 else 0)⟩
  | .add first second =>
      (evalSelectedDualInterval selected box first).add
        (evalSelectedDualInterval selected box second)
  | .neg expression =>
      (evalSelectedDualInterval selected box expression).neg
  | .mul first second =>
      (evalSelectedDualInterval selected box first).mul
        (evalSelectedDualInterval selected box second)

@[simp] theorem evalSelectedDualInterval_constant
    {ambientCount selectedCount : ℕ}
    (selected : Fin selectedCount → Fin ambientCount)
    (box : Fin ambientCount → RationalInterval) (value : ℚ) :
    evalSelectedDualInterval selected box (.constant value) =
      IntervalDual.constant value := rfl

@[simp] theorem evalSelectedDualInterval_var
    {ambientCount selectedCount : ℕ}
    (selected : Fin selectedCount → Fin ambientCount)
    (box : Fin ambientCount → RationalInterval) (index : Fin ambientCount) :
    evalSelectedDualInterval selected box (.var index) =
      ⟨box index, fun coordinate ↦
        RationalInterval.point
          (if selected coordinate = index then 1 else 0)⟩ := rfl

@[simp] theorem evalSelectedDualInterval_add
    {ambientCount selectedCount : ℕ}
    (selected : Fin selectedCount → Fin ambientCount)
    (box : Fin ambientCount → RationalInterval)
    (first second : RationalPolynomial ambientCount) :
    evalSelectedDualInterval selected box (.add first second) =
      (evalSelectedDualInterval selected box first).add
        (evalSelectedDualInterval selected box second) := rfl

@[simp] theorem evalSelectedDualInterval_neg
    {ambientCount selectedCount : ℕ}
    (selected : Fin selectedCount → Fin ambientCount)
    (box : Fin ambientCount → RationalInterval)
    (expression : RationalPolynomial ambientCount) :
    evalSelectedDualInterval selected box (.neg expression) =
      (evalSelectedDualInterval selected box expression).neg := rfl

@[simp] theorem evalSelectedDualInterval_mul
    {ambientCount selectedCount : ℕ}
    (selected : Fin selectedCount → Fin ambientCount)
    (box : Fin ambientCount → RationalInterval)
    (first second : RationalPolynomial ambientCount) :
    evalSelectedDualInterval selected box (.mul first second) =
      (evalSelectedDualInterval selected box first).mul
        (evalSelectedDualInterval selected box second) := rfl

theorem evalSelectedDualInterval_value {ambientCount selectedCount : ℕ}
    (selected : Fin selectedCount → Fin ambientCount)
    (box : Fin ambientCount → RationalInterval)
    (expression : RationalPolynomial ambientCount) :
    (evalSelectedDualInterval selected box expression).value =
      (evalDualInterval box expression).value := by
  induction expression with
  | constant value => rfl
  | var index => rfl
  | add first second hfirst hsecond =>
      simp [evalSelectedDualInterval, evalDualInterval, IntervalDual.add,
        hfirst, hsecond]
  | neg expression hexpression =>
      simp [evalSelectedDualInterval, evalDualInterval, IntervalDual.neg,
        hexpression]
  | mul first second hfirst hsecond =>
      simp [evalSelectedDualInterval, evalDualInterval, IntervalDual.mul,
        hfirst, hsecond]

theorem evalSelectedDualInterval_derivative
    {ambientCount selectedCount : ℕ}
    (selected : Fin selectedCount → Fin ambientCount)
    (box : Fin ambientCount → RationalInterval)
    (expression : RationalPolynomial ambientCount)
    (coordinate : Fin selectedCount) :
    (evalSelectedDualInterval selected box expression).derivative coordinate =
      (evalDualInterval box expression).derivative (selected coordinate) := by
  induction expression with
  | constant value => rfl
  | var index => rfl
  | add first second hfirst hsecond =>
      simp [evalSelectedDualInterval, evalDualInterval, IntervalDual.add,
        hfirst, hsecond]
  | neg expression hexpression =>
      simp [evalSelectedDualInterval, evalDualInterval, IntervalDual.neg,
        hexpression]
  | mul first second hfirst hsecond =>
      simp [evalSelectedDualInterval, evalDualInterval, IntervalDual.mul,
        evalSelectedDualInterval_value, hfirst, hsecond]

/-- Selected-coordinate interval evaluation encloses the polynomial value and
the requested formal partials. -/
theorem evalSelectedDualInterval_sound
    {ambientCount selectedCount : ℕ}
    (selected : Fin selectedCount → Fin ambientCount)
    (expression : RationalPolynomial ambientCount)
    (box : Fin ambientCount → RationalInterval)
    (point : Fin ambientCount → ℝ)
    (hpoint : point ∈ rationalBoxSet box) :
    (evalSelectedDualInterval selected box expression).value.Contains
        (evalReal point expression) ∧
      ∀ coordinate,
        ((evalSelectedDualInterval selected box expression).derivative
          coordinate).Contains
            (evalReal point
              (formalPartial (selected coordinate) expression)) := by
  rw [evalSelectedDualInterval_value]
  constructor
  · exact (evalDualInterval_sound expression box point hpoint).1
  · intro coordinate
    rw [evalSelectedDualInterval_derivative]
    exact (evalDualInterval_sound expression box point hpoint).2
      (selected coordinate)

/-- Dyadic interval evaluation carrying derivatives only in a selected
coordinate block. -/
def evalSelectedDualDyadic {precision ambientCount selectedCount : ℕ}
    (selected : Fin selectedCount → Fin ambientCount)
    (box : Fin ambientCount → DyadicInterval precision) :
    RationalPolynomial ambientCount → DyadicDual precision selectedCount
  | .constant value => DyadicDual.constant value
  | .var index =>
      ⟨box index, fun coordinate ↦
        DyadicInterval.ofRat
          (if selected coordinate = index then (1 : ℚ) else 0)⟩
  | .add first second =>
      (evalSelectedDualDyadic selected box first).add
        (evalSelectedDualDyadic selected box second)
  | .neg expression =>
      (evalSelectedDualDyadic selected box expression).neg
  | .mul first second =>
      (evalSelectedDualDyadic selected box first).mul
        (evalSelectedDualDyadic selected box second)

@[simp] theorem evalSelectedDualDyadic_constant
    {precision ambientCount selectedCount : ℕ}
    (selected : Fin selectedCount → Fin ambientCount)
    (box : Fin ambientCount → DyadicInterval precision) (value : ℚ) :
    evalSelectedDualDyadic selected box (.constant value) =
      DyadicDual.constant value := rfl

@[simp] theorem evalSelectedDualDyadic_var
    {precision ambientCount selectedCount : ℕ}
    (selected : Fin selectedCount → Fin ambientCount)
    (box : Fin ambientCount → DyadicInterval precision)
    (index : Fin ambientCount) :
    evalSelectedDualDyadic selected box (.var index) =
      ⟨box index, fun coordinate ↦
        DyadicInterval.ofRat
          (if selected coordinate = index then (1 : ℚ) else 0)⟩ := rfl

@[simp] theorem evalSelectedDualDyadic_add
    {precision ambientCount selectedCount : ℕ}
    (selected : Fin selectedCount → Fin ambientCount)
    (box : Fin ambientCount → DyadicInterval precision)
    (first second : RationalPolynomial ambientCount) :
    evalSelectedDualDyadic selected box (.add first second) =
      (evalSelectedDualDyadic selected box first).add
        (evalSelectedDualDyadic selected box second) := rfl

@[simp] theorem evalSelectedDualDyadic_neg
    {precision ambientCount selectedCount : ℕ}
    (selected : Fin selectedCount → Fin ambientCount)
    (box : Fin ambientCount → DyadicInterval precision)
    (expression : RationalPolynomial ambientCount) :
    evalSelectedDualDyadic selected box (.neg expression) =
      (evalSelectedDualDyadic selected box expression).neg := rfl

@[simp] theorem evalSelectedDualDyadic_mul
    {precision ambientCount selectedCount : ℕ}
    (selected : Fin selectedCount → Fin ambientCount)
    (box : Fin ambientCount → DyadicInterval precision)
    (first second : RationalPolynomial ambientCount) :
    evalSelectedDualDyadic selected box (.mul first second) =
      (evalSelectedDualDyadic selected box first).mul
        (evalSelectedDualDyadic selected box second) := rfl

theorem evalSelectedDualDyadic_value
    {precision ambientCount selectedCount : ℕ}
    (selected : Fin selectedCount → Fin ambientCount)
    (box : Fin ambientCount → DyadicInterval precision)
    (expression : RationalPolynomial ambientCount) :
    (evalSelectedDualDyadic selected box expression).value =
      (evalDualDyadic box expression).value := by
  induction expression with
  | constant value => rfl
  | var index => rfl
  | add first second hfirst hsecond =>
      simp [evalSelectedDualDyadic, evalDualDyadic, DyadicDual.add,
        hfirst, hsecond]
  | neg expression hexpression =>
      simp [evalSelectedDualDyadic, evalDualDyadic, DyadicDual.neg,
        hexpression]
  | mul first second hfirst hsecond =>
      simp [evalSelectedDualDyadic, evalDualDyadic, DyadicDual.mul,
        hfirst, hsecond]

theorem evalSelectedDualDyadic_derivative
    {precision ambientCount selectedCount : ℕ}
    (selected : Fin selectedCount → Fin ambientCount)
    (box : Fin ambientCount → DyadicInterval precision)
    (expression : RationalPolynomial ambientCount)
    (coordinate : Fin selectedCount) :
    (evalSelectedDualDyadic selected box expression).derivative coordinate =
      (evalDualDyadic box expression).derivative (selected coordinate) := by
  induction expression with
  | constant value => rfl
  | var index => rfl
  | add first second hfirst hsecond =>
      simp [evalSelectedDualDyadic, evalDualDyadic, DyadicDual.add,
        hfirst, hsecond]
  | neg expression hexpression =>
      simp [evalSelectedDualDyadic, evalDualDyadic, DyadicDual.neg,
        hexpression]
  | mul first second hfirst hsecond =>
      simp [evalSelectedDualDyadic, evalDualDyadic, DyadicDual.mul,
        evalSelectedDualDyadic_value, hfirst, hsecond]

/-! ## One selected partial without materializing the selected gradient -/

/-- A dyadic interval value together with one selected formal partial. -/
structure DyadicPartialEvaluation (precision : ℕ) where
  value : DyadicInterval precision
  derivative : DyadicInterval precision

namespace DyadicPartialEvaluation

def constant {precision : ℕ} (value : ℚ) :
    DyadicPartialEvaluation precision :=
  ⟨DyadicInterval.ofRat value, DyadicInterval.ofInt 0⟩

def ofVariable {precision ambientCount : ℕ}
    (box : Fin ambientCount → DyadicInterval precision)
    (selected index : Fin ambientCount) :
    DyadicPartialEvaluation precision :=
  ⟨box index, DyadicInterval.ofRat (if selected = index then 1 else 0)⟩

def add {precision : ℕ}
    (first second : DyadicPartialEvaluation precision) :
    DyadicPartialEvaluation precision :=
  ⟨first.value.add second.value,
    first.derivative.add second.derivative⟩

def neg {precision : ℕ} (evaluation : DyadicPartialEvaluation precision) :
    DyadicPartialEvaluation precision :=
  ⟨evaluation.value.neg, evaluation.derivative.neg⟩

def mul {precision : ℕ}
    (first second : DyadicPartialEvaluation precision) :
    DyadicPartialEvaluation precision :=
  ⟨first.value.mul second.value,
    (first.derivative.mul second.value).add
      (first.value.mul second.derivative)⟩

end DyadicPartialEvaluation

/-- Evaluate one formal partial alongside the polynomial value, without
materializing an entire gradient function. -/
def evalDyadicPartial {precision ambientCount : ℕ}
    (selected : Fin ambientCount)
    (box : Fin ambientCount → DyadicInterval precision) :
    RationalPolynomial ambientCount → DyadicPartialEvaluation precision
  | .constant value => .constant value
  | .var index => .ofVariable box selected index
  | .add first second =>
      (evalDyadicPartial selected box first).add
        (evalDyadicPartial selected box second)
  | .neg expression => (evalDyadicPartial selected box expression).neg
  | .mul first second =>
      (evalDyadicPartial selected box first).mul
        (evalDyadicPartial selected box second)

/-- The single-partial evaluator is exactly the selected-gradient evaluator
at the requested coordinate. -/
theorem evalDyadicPartial_eq_evalSelectedDualDyadic
    {precision ambientCount selectedCount : ℕ}
    (selected : Fin selectedCount → Fin ambientCount)
    (box : Fin ambientCount → DyadicInterval precision)
    (expression : RationalPolynomial ambientCount)
    (coordinate : Fin selectedCount) :
    evalDyadicPartial (selected coordinate) box expression =
      ⟨(evalSelectedDualDyadic selected box expression).value,
        (evalSelectedDualDyadic selected box expression).derivative
          coordinate⟩ := by
  induction expression with
  | constant value => rfl
  | var index => rfl
  | add first second hfirst hsecond =>
      simp [evalDyadicPartial, evalSelectedDualDyadic,
        DyadicPartialEvaluation.add, DyadicDual.add, hfirst, hsecond]
  | neg expression hexpression =>
      simp [evalDyadicPartial, evalSelectedDualDyadic,
        DyadicPartialEvaluation.neg, DyadicDual.neg, hexpression]
  | mul first second hfirst hsecond =>
      simp [evalDyadicPartial, evalSelectedDualDyadic,
        DyadicPartialEvaluation.mul, DyadicDual.mul, hfirst, hsecond]

theorem evalDyadicPartial_value_eq_evalSelectedDualDyadic
    {precision ambientCount selectedCount : ℕ}
    (selected : Fin selectedCount → Fin ambientCount)
    (box : Fin ambientCount → DyadicInterval precision)
    (expression : RationalPolynomial ambientCount)
    (coordinate : Fin selectedCount) :
    (evalDyadicPartial (selected coordinate) box expression).value =
      (evalSelectedDualDyadic selected box expression).value := by
  exact congrArg DyadicPartialEvaluation.value
    (evalDyadicPartial_eq_evalSelectedDualDyadic selected box expression
      coordinate)

theorem evalDyadicPartial_derivative_eq_evalSelectedDualDyadic
    {precision ambientCount selectedCount : ℕ}
    (selected : Fin selectedCount → Fin ambientCount)
    (box : Fin ambientCount → DyadicInterval precision)
    (expression : RationalPolynomial ambientCount)
    (coordinate : Fin selectedCount) :
    (evalDyadicPartial (selected coordinate) box expression).derivative =
      (evalSelectedDualDyadic selected box expression).derivative
        coordinate := by
  exact congrArg DyadicPartialEvaluation.derivative
    (evalDyadicPartial_eq_evalSelectedDualDyadic selected box expression
      coordinate)

theorem evalSelectedDualDyadic_sound
    {precision ambientCount selectedCount : ℕ}
    (selected : Fin selectedCount → Fin ambientCount)
    (expression : RationalPolynomial ambientCount)
    (box : Fin ambientCount → DyadicInterval precision)
    (point : Fin ambientCount → ℝ)
    (hpoint : point ∈ dyadicBoxSet box) :
    (evalSelectedDualDyadic selected box expression).value.Contains
        (evalReal point expression) ∧
      ∀ coordinate,
        ((evalSelectedDualDyadic selected box expression).derivative
          coordinate).Contains
            (evalReal point
              (formalPartial (selected coordinate) expression)) := by
  rw [evalSelectedDualDyadic_value]
  constructor
  · exact (evalDualDyadic_sound expression box point hpoint).1
  · intro coordinate
    rw [evalSelectedDualDyadic_derivative]
    exact (evalDualDyadic_sound expression box point hpoint).2
      (selected coordinate)

/-- Assemble varying leading coordinates and fixed trailing parameters. -/
def leadingCoordinatePoint
    (point : Fin variableCount → ℝ)
    (parameter : Fin parameterCount → ℝ) :
    Fin (variableCount + parameterCount) → ℝ :=
  Fin.addCases point parameter

/-- The continuous linear inclusion of the leading coordinate block. -/
def leadingCoordinateInclusion :
    (Fin variableCount → ℝ) →L[ℝ]
      (Fin (variableCount + parameterCount) → ℝ) :=
  ContinuousLinearMap.pi fun coordinate ↦
    Fin.addCases
      (fun input ↦ ContinuousLinearMap.proj input)
      (fun _ ↦ 0) coordinate

@[simp] theorem leadingCoordinateInclusion_apply_left
    (direction : Fin variableCount → ℝ)
    (coordinate : Fin variableCount) :
    leadingCoordinateInclusion (parameterCount := parameterCount) direction
        (Fin.castAdd parameterCount coordinate) =
      direction coordinate := by
  simp [leadingCoordinateInclusion]

@[simp] theorem leadingCoordinateInclusion_apply_right
    (direction : Fin variableCount → ℝ)
    (coordinate : Fin parameterCount) :
    leadingCoordinateInclusion (variableCount := variableCount) direction
        (Fin.natAdd variableCount coordinate) =
      0 := by
  simp [leadingCoordinateInclusion]

theorem hasFDerivAt_leadingCoordinatePoint
    (point : Fin variableCount → ℝ)
    (parameter : Fin parameterCount → ℝ) :
    HasFDerivAt (fun input ↦ leadingCoordinatePoint input parameter)
      leadingCoordinateInclusion point := by
  apply hasFDerivAt_pi.mpr
  intro coordinate
  refine Fin.addCases ?_ ?_ coordinate
  · intro input
    simpa [leadingCoordinatePoint] using hasFDerivAt_apply input point
  · intro fixed
    simpa [leadingCoordinatePoint] using
      (hasFDerivAt_const (x := point) (parameter fixed))

/-- The derivative of a reflected polynomial after fixing its trailing
parameters. -/
def leadingCoordinateDifferential
    (point : Fin (variableCount + parameterCount) → ℝ)
    (expression : RationalPolynomial (variableCount + parameterCount)) :
    (Fin variableCount → ℝ) →L[ℝ] ℝ :=
  (differential point expression).comp leadingCoordinateInclusion

theorem hasFDerivAt_evalReal_leadingCoordinatePoint
    (expression : RationalPolynomial (variableCount + parameterCount))
    (point : Fin variableCount → ℝ)
    (parameter : Fin parameterCount → ℝ) :
    HasFDerivAt
      (fun input ↦ evalReal (leadingCoordinatePoint input parameter) expression)
      (leadingCoordinateDifferential
        (leadingCoordinatePoint point parameter) expression) point := by
  exact (hasFDerivAt_evalReal expression
    (leadingCoordinatePoint point parameter)).comp point
      (hasFDerivAt_leadingCoordinatePoint point parameter)

theorem convex_preimage_leadingCoordinatePoint
    (box : Fin (variableCount + parameterCount) → RationalInterval)
    (parameter : Fin parameterCount → ℝ) :
    Convex ℝ
      ((rationalBoxSet box).preimage
        (fun point ↦ leadingCoordinatePoint point parameter)) := by
  intro first hfirst second hsecond a b ha hb hab
  have hcombination := convex_rationalBoxSet box
    hfirst hsecond ha hb hab
  change leadingCoordinatePoint (a • first + b • second) parameter ∈
    rationalBoxSet box
  rw [show leadingCoordinatePoint (a • first + b • second) parameter =
      a • leadingCoordinatePoint first parameter +
        b • leadingCoordinatePoint second parameter by
    funext coordinate
    refine Fin.addCases ?_ ?_ coordinate
    · intro input
      simp [leadingCoordinatePoint]
    · intro fixed
      simp [leadingCoordinatePoint, ← add_mul, hab]]
  exact hcombination

@[simp] theorem leadingCoordinateDifferential_piBasisVector
    (point : Fin (variableCount + parameterCount) → ℝ)
    (expression : RationalPolynomial (variableCount + parameterCount))
    (coordinate : Fin variableCount) :
    leadingCoordinateDifferential point expression (piBasisVector coordinate) =
      evalReal point
        (formalPartial (Fin.castAdd parameterCount coordinate) expression) := by
  rw [leadingCoordinateDifferential, ContinuousLinearMap.comp_apply,
    differential_apply]
  rw [Fin.sum_univ_add]
  simp only [leadingCoordinateInclusion_apply_left,
    leadingCoordinateInclusion_apply_right, mul_zero, Finset.sum_const_zero,
    add_zero]
  rw [Finset.sum_eq_single coordinate]
  · simp [piBasisVector]
  · intro other _ hother
    rw [piBasisVector, if_neg hother.symm, mul_zero]
  · simp

/-- Exact automatic-differentiation bounds in an ambient parameter box prove
a Lipschitz estimate in the leading variables with the trailing parameters
fixed. -/
theorem lipschitzOnWith_evalReal_leadingCoordinates_of_intervalBounds
    (expression : RationalPolynomial (variableCount + parameterCount))
    (box : Fin (variableCount + parameterCount) → RationalInterval)
    (parameter : Fin parameterCount → ℝ)
    (domain : Set (Fin variableCount → ℝ))
    (bound : Fin variableCount → ℝ)
    (constant : ℝ≥0)
    (hconvex : Convex ℝ domain)
    (hbox : ∀ point ∈ domain,
      leadingCoordinatePoint point parameter ∈ rationalBoxSet box)
    (hrow : ∑ coordinate, bound coordinate ≤ (constant : ℝ))
    (hlower : ∀ coordinate,
      |((((evalSelectedDualInterval (Fin.castAdd parameterCount) box
          expression).derivative coordinate).lower : ℚ) : ℝ)| ≤
        bound coordinate)
    (hupper : ∀ coordinate,
      |((((evalSelectedDualInterval (Fin.castAdd parameterCount) box
          expression).derivative coordinate).upper : ℚ) : ℝ)| ≤
        bound coordinate) :
    LipschitzOnWith constant
      (fun point ↦ evalReal (leadingCoordinatePoint point parameter) expression)
      domain := by
  have hvector : LipschitzOnWith constant
      (fun point (_ : Fin 1) ↦
        evalReal (leadingCoordinatePoint point parameter) expression)
      domain := by
    refine lipschitzOnWith_pi_of_hasFDerivAt_entrywise_rowSum
      (function := fun point (_ : Fin 1) ↦
        evalReal (leadingCoordinatePoint point parameter) expression)
      (derivative := fun point ↦
        ContinuousLinearMap.pi fun _ : Fin 1 ↦
          leadingCoordinateDifferential
            (leadingCoordinatePoint point parameter) expression)
      (bound := fun _ coordinate ↦ bound coordinate)
      (constant := constant) hconvex ?_ (fun _ ↦ hrow) ?_
    · intro point _
      exact hasFDerivAt_pi.mpr fun _ ↦
        hasFDerivAt_evalReal_leadingCoordinatePoint expression point parameter
    · intro point hpoint _ coordinate
      change ‖leadingCoordinateDifferential
        (leadingCoordinatePoint point parameter) expression
          (piBasisVector coordinate)‖ ≤ bound coordinate
      rw [leadingCoordinateDifferential_piBasisVector, Real.norm_eq_abs]
      exact abs_le_of_rationalContains_of_endpoints_le _ _ _
        ((evalSelectedDualInterval_sound (Fin.castAdd parameterCount)
          expression box (leadingCoordinatePoint point parameter)
          (hbox point hpoint)).2 coordinate)
        (hlower coordinate) (hupper coordinate)
  intro first hfirst second hsecond
  exact le_trans
    (edist_le_pi_edist
      (fun _ : Fin 1 ↦
        evalReal (leadingCoordinatePoint first parameter) expression)
      (fun _ : Fin 1 ↦
        evalReal (leadingCoordinatePoint second parameter) expression) 0)
    (hvector hfirst hsecond)

/-- Exact centered bound for a polynomial whose trailing coordinates are
parameters: the center-value envelope and only the leading-coordinate
derivative envelopes are charged. -/
def leadingCoordinateCenteredBound
    (centerBox box :
      Fin (variableCount + parameterCount) → RationalInterval)
    (expression : RationalPolynomial (variableCount + parameterCount)) : ℝ :=
  rationalAbsBound
      (evalSelectedDualInterval (Fin.castAdd parameterCount) centerBox
        expression).value +
    ∑ coordinate,
      rationalAbsBound
        ((evalSelectedDualInterval (Fin.castAdd parameterCount) box
          expression).derivative coordinate)

/-- A centered automatic-differentiation enclosure bounds a reflected
polynomial uniformly over leading variables and fixed admissible trailing
parameters. -/
theorem abs_evalReal_le_leadingCoordinateCenteredBound
    (expression : RationalPolynomial (variableCount + parameterCount))
    (centerBox box :
      Fin (variableCount + parameterCount) → RationalInterval)
    (center point : Fin variableCount → ℝ)
    (parameter : Fin parameterCount → ℝ)
    (hcenterBox :
      leadingCoordinatePoint center parameter ∈ rationalBoxSet centerBox)
    (hcenter : leadingCoordinatePoint center parameter ∈ rationalBoxSet box)
    (hpoint : leadingCoordinatePoint point parameter ∈ rationalBoxSet box)
    (hradius : dist point center ≤ 1) :
    |evalReal (leadingCoordinatePoint point parameter) expression| ≤
      leadingCoordinateCenteredBound centerBox box expression := by
  let derivativeBound : Fin variableCount → ℝ := fun coordinate ↦
    rationalAbsBound
      ((evalSelectedDualInterval (Fin.castAdd parameterCount) box
        expression).derivative coordinate)
  have hderivativeNonneg : ∀ coordinate, 0 ≤ derivativeBound coordinate :=
    fun coordinate ↦ (abs_nonneg _).trans (le_max_left _ _)
  let derivativeSum : ℝ≥0 :=
    ⟨∑ coordinate, derivativeBound coordinate,
      Finset.sum_nonneg fun coordinate _ ↦ hderivativeNonneg coordinate⟩
  have hlipschitz : LipschitzOnWith derivativeSum
      (fun input ↦
        evalReal (leadingCoordinatePoint input parameter) expression)
      {input | leadingCoordinatePoint input parameter ∈ rationalBoxSet box} := by
    apply lipschitzOnWith_evalReal_leadingCoordinates_of_intervalBounds
      expression box parameter _ derivativeBound derivativeSum
    · exact convex_preimage_leadingCoordinatePoint box parameter
    · intro input hinput
      exact hinput
    · rfl
    · intro coordinate
      exact le_max_left _ _
    · intro coordinate
      exact le_max_right _ _
  have hcenterValue :
      |evalReal (leadingCoordinatePoint center parameter) expression| ≤
        rationalAbsBound
          (evalSelectedDualInterval (Fin.castAdd parameterCount) centerBox
            expression).value :=
    abs_le_of_rationalContains_of_endpoints_le _ _ _
      (evalSelectedDualInterval_sound (Fin.castAdd parameterCount)
        expression centerBox
        (leadingCoordinatePoint center parameter) hcenterBox).1
      (le_max_left _ _) (le_max_right _ _)
  have hdifference := hlipschitz.dist_le_mul point hpoint center hcenter
  rw [Real.dist_eq] at hdifference
  have hsumNonneg : 0 ≤ (derivativeSum : ℝ) := derivativeSum.coe_nonneg
  have hdifferenceOne :
      |evalReal (leadingCoordinatePoint point parameter) expression -
          evalReal (leadingCoordinatePoint center parameter) expression| ≤
        (derivativeSum : ℝ) := by
    exact hdifference.trans <| by
      simpa using mul_le_mul_of_nonneg_left hradius hsumNonneg
  rw [leadingCoordinateCenteredBound]
  change _ ≤ _ + (derivativeSum : ℝ)
  rw [show evalReal (leadingCoordinatePoint point parameter) expression =
      (evalReal (leadingCoordinatePoint point parameter) expression -
        evalReal (leadingCoordinatePoint center parameter) expression) +
        evalReal (leadingCoordinatePoint center parameter) expression by ring]
  exact (abs_add_le _ _).trans <| by
    simpa [add_comm] using add_le_add hdifferenceOne hcenterValue

/-! ## Dyadic centered bounds on selected coordinates -/

/-- Fixing trailing coordinates preserves convexity of a dyadic box in the
leading coordinates. -/
theorem convex_preimage_dyadicBoxSet_leadingCoordinatePoint
    {precision : ℕ}
    (box : Fin (variableCount + parameterCount) → DyadicInterval precision)
    (parameter : Fin parameterCount → ℝ) :
    Convex ℝ
      ((dyadicBoxSet box).preimage
        (fun point => leadingCoordinatePoint point parameter)) := by
  intro first hfirst second hsecond a b ha hb hab
  have hcombination := convex_dyadicBoxSet box
    hfirst hsecond ha hb hab
  change leadingCoordinatePoint (a • first + b • second) parameter ∈
    dyadicBoxSet box
  rw [show leadingCoordinatePoint (a • first + b • second) parameter =
      a • leadingCoordinatePoint first parameter +
        b • leadingCoordinatePoint second parameter by
    funext coordinate
    refine Fin.addCases ?_ ?_ coordinate
    · intro input
      simp [leadingCoordinatePoint]
    · intro fixed
      simp [leadingCoordinatePoint, ← add_mul, hab]]
  exact hcombination

/-- Selected-coordinate dyadic derivative bounds prove a Lipschitz estimate
after fixing all trailing parameters. -/
theorem lipschitzOnWith_evalReal_leadingCoordinates_of_selectedDyadicBounds
    {precision : ℕ}
    (expression : RationalPolynomial (variableCount + parameterCount))
    (box : Fin (variableCount + parameterCount) → DyadicInterval precision)
    (parameter : Fin parameterCount → ℝ)
    (domain : Set (Fin variableCount → ℝ))
    (bound : Fin variableCount → ℝ)
    (constant : ℝ≥0)
    (hconvex : Convex ℝ domain)
    (hbox : ∀ point ∈ domain,
      leadingCoordinatePoint point parameter ∈ dyadicBoxSet box)
    (hrow : ∑ coordinate, bound coordinate ≤ (constant : ℝ))
    (hlower : ∀ coordinate,
      |((((evalSelectedDualDyadic (Fin.castAdd parameterCount) box
          expression).derivative coordinate).toRationalInterval.lower :
            ℚ) : ℝ)| ≤ bound coordinate)
    (hupper : ∀ coordinate,
      |((((evalSelectedDualDyadic (Fin.castAdd parameterCount) box
          expression).derivative coordinate).toRationalInterval.upper :
            ℚ) : ℝ)| ≤ bound coordinate) :
    LipschitzOnWith constant
      (fun point => evalReal (leadingCoordinatePoint point parameter) expression)
      domain := by
  have hvector : LipschitzOnWith constant
      (fun point (_ : Fin 1) =>
        evalReal (leadingCoordinatePoint point parameter) expression)
      domain := by
    refine lipschitzOnWith_pi_of_hasFDerivAt_entrywise_rowSum
      (function := fun point (_ : Fin 1) =>
        evalReal (leadingCoordinatePoint point parameter) expression)
      (derivative := fun point =>
        ContinuousLinearMap.pi fun _ : Fin 1 =>
          leadingCoordinateDifferential
            (leadingCoordinatePoint point parameter) expression)
      (bound := fun _ coordinate => bound coordinate)
      (constant := constant) hconvex ?_ (fun _ => hrow) ?_
    · intro point _
      exact hasFDerivAt_pi.mpr fun _ =>
        hasFDerivAt_evalReal_leadingCoordinatePoint expression point parameter
    · intro point hpoint _ coordinate
      change ‖leadingCoordinateDifferential
        (leadingCoordinatePoint point parameter) expression
          (piBasisVector coordinate)‖ ≤ bound coordinate
      rw [leadingCoordinateDifferential_piBasisVector, Real.norm_eq_abs]
      exact abs_le_of_dyadicContains_of_endpoints_le _ _ _
        ((evalSelectedDualDyadic_sound (Fin.castAdd parameterCount)
          expression box (leadingCoordinatePoint point parameter)
          (hbox point hpoint)).2 coordinate)
        (hlower coordinate) (hupper coordinate)
  intro first hfirst second hsecond
  exact le_trans
    (edist_le_pi_edist
      (fun _ : Fin 1 =>
        evalReal (leadingCoordinatePoint first parameter) expression)
      (fun _ : Fin 1 =>
        evalReal (leadingCoordinatePoint second parameter) expression) 0)
    (hvector hfirst hsecond)

/-- Integer numerator of the selected-coordinate centered mean-value bound.
Only the leading-coordinate derivatives are charged; the trailing parameters
may range independently inside both dyadic boxes. -/
def selectedCenteredMeanValueNumerator
    {precision : ℕ}
    (centerBox box :
      Fin (variableCount + parameterCount) → DyadicInterval precision)
    (expression : RationalPolynomial (variableCount + parameterCount)) : ℤ :=
  dyadicAbsNumerator
      (evalSelectedDualDyadic (Fin.castAdd parameterCount) centerBox
        expression).value +
    ∑ coordinate,
      dyadicAbsNumerator
        ((evalSelectedDualDyadic (Fin.castAdd parameterCount) box
          expression).derivative coordinate)

/-- A scaled integer bound on selected-coordinate dyadic automatic
differentiation gives a uniform centered bound with the trailing coordinates
held at any fixed admissible parameter value. -/
theorem abs_evalReal_le_of_selectedCenteredMeanValueNumerator_le
    {precision : ℕ}
    (expression : RationalPolynomial (variableCount + parameterCount))
    (centerBox box :
      Fin (variableCount + parameterCount) → DyadicInterval precision)
    (center point : Fin variableCount → ℝ)
    (parameter : Fin parameterCount → ℝ)
    (hcenterBox :
      leadingCoordinatePoint center parameter ∈ dyadicBoxSet centerBox)
    (hcenter : leadingCoordinatePoint center parameter ∈ dyadicBoxSet box)
    (hpoint : leadingCoordinatePoint point parameter ∈ dyadicBoxSet box)
    (hradius : dist point center ≤ 1)
    (bound : ℚ)
    (hbound :
      (selectedCenteredMeanValueNumerator centerBox box expression : ℚ) ≤
        bound * ((DyadicInterval.scale precision : ℤ) : ℚ)) :
    |evalReal (leadingCoordinatePoint point parameter) expression| ≤
      (bound : ℝ) := by
  let derivativeBound : Fin variableCount → ℝ := fun coordinate =>
    dyadicAbsBound
      ((evalSelectedDualDyadic (Fin.castAdd parameterCount) box
        expression).derivative coordinate)
  have hderivativeNonneg : ∀ coordinate, 0 ≤ derivativeBound coordinate :=
    fun coordinate => dyadicAbsBound_nonneg _
  let derivativeSum : ℝ≥0 :=
    ⟨∑ coordinate, derivativeBound coordinate,
      Finset.sum_nonneg fun coordinate _ => hderivativeNonneg coordinate⟩
  have hlipschitz : LipschitzOnWith derivativeSum
      (fun input =>
        evalReal (leadingCoordinatePoint input parameter) expression)
      {input |
        leadingCoordinatePoint input parameter ∈ dyadicBoxSet box} := by
    apply
      lipschitzOnWith_evalReal_leadingCoordinates_of_selectedDyadicBounds
        expression box parameter _ derivativeBound derivativeSum
    · exact convex_preimage_dyadicBoxSet_leadingCoordinatePoint box parameter
    · intro input hinput
      exact hinput
    · rfl
    · intro coordinate
      exact le_max_left _ _
    · intro coordinate
      exact le_max_right _ _
  have hcenterValue :
      |evalReal (leadingCoordinatePoint center parameter) expression| ≤
        dyadicAbsBound
          (evalSelectedDualDyadic (Fin.castAdd parameterCount) centerBox
            expression).value :=
    abs_le_of_dyadicContains_of_endpoints_le _ _ _
      (evalSelectedDualDyadic_sound (Fin.castAdd parameterCount)
        expression centerBox (leadingCoordinatePoint center parameter)
        hcenterBox).1
      (le_max_left _ _) (le_max_right _ _)
  have hdifference := hlipschitz.dist_le_mul point hpoint center hcenter
  rw [Real.dist_eq] at hdifference
  have hsumNonneg : 0 ≤ (derivativeSum : ℝ) := derivativeSum.coe_nonneg
  have hdifferenceOne :
      |evalReal (leadingCoordinatePoint point parameter) expression -
          evalReal (leadingCoordinatePoint center parameter) expression| ≤
        (derivativeSum : ℝ) :=
    hdifference.trans <| by
      simpa using mul_le_mul_of_nonneg_left hradius hsumNonneg
  have hscale : (0 : ℝ) < ((DyadicInterval.scale precision : ℤ) : ℝ) := by
    exact_mod_cast DyadicInterval.scale_pos precision
  have hderivativeSum : (derivativeSum : ℝ) =
      ∑ coordinate, derivativeBound coordinate := rfl
  have hsum :
      dyadicAbsBound
          (evalSelectedDualDyadic (Fin.castAdd parameterCount) centerBox
            expression).value +
          ∑ coordinate, derivativeBound coordinate =
        (selectedCenteredMeanValueNumerator centerBox box expression : ℝ) /
          ((DyadicInterval.scale precision : ℤ) : ℝ) := by
    rw [selectedCenteredMeanValueNumerator, Int.cast_add, add_div,
      dyadicAbsBound_eq_dyadicAbsNumerator_div_scale, Int.cast_sum,
      Finset.sum_div]
    exact congrArg _ (Finset.sum_congr rfl fun coordinate _ =>
      dyadicAbsBound_eq_dyadicAbsNumerator_div_scale _)
  rw [show evalReal (leadingCoordinatePoint point parameter) expression =
      (evalReal (leadingCoordinatePoint point parameter) expression -
        evalReal (leadingCoordinatePoint center parameter) expression) +
        evalReal (leadingCoordinatePoint center parameter) expression by ring]
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add hdifferenceOne hcenterValue).trans ?_
  rw [hderivativeSum, add_comm, hsum, div_le_iff₀ hscale]
  exact_mod_cast hbound

end RationalPolynomial
end Interval
end Math

end
