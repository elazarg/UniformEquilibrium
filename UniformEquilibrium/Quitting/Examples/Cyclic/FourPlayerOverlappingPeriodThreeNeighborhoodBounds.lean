import UniformEquilibrium.Quitting.Examples.Cyclic.FourPlayerOverlappingPeriodThreeIntervalArithmetic
import MathUE.Interval.SuppliedPartialEnclosureMeanValue

/-!
# Preconditioned active-gap neighborhood bounds

Separately checked active-gap values and partials are assembled at the real
semantic level.  This avoids conflating smart-constructor equivalence with
literal equality of outward-rounded interval evaluations.
-/

noncomputable section

namespace GameTheory.FourPlayerOverlappingPeriodThree

open Math.Interval Math.Interval.RationalPolynomial

def hazardCoordinates : List HazardCoordinate :=
  List.ofFn id

def linearCombinationValue
    (coefficient : HazardCoordinate → ℚ)
    (value : HazardCoordinate → ℝ) : ℝ :=
  (hazardCoordinates.map fun input ↦
    (coefficient input : ℝ) * value input).foldr
      (fun first second ↦ first + second) 0

@[simp] theorem evalReal_formalPartial_constant
    (point : NormalizedCoordinate → ℝ) (coordinate : NormalizedCoordinate)
    (value : ℚ) :
    evalReal point (formalPartial coordinate (.constant value)) = 0 := by
  simp [formalPartial, Math.Interval.RationalPolynomial.evalReal]

@[simp] theorem evalReal_formalPartial_var
    (point : NormalizedCoordinate → ℝ) (coordinate index : NormalizedCoordinate) :
    evalReal point (formalPartial coordinate (.var index)) =
      if coordinate = index then 1 else 0 := by
  by_cases heq : coordinate = index <;>
    simp [formalPartial, heq, Math.Interval.RationalPolynomial.evalReal]

@[simp] theorem evalReal_formalPartial_zero
    (point : NormalizedCoordinate → ℝ) (coordinate : NormalizedCoordinate) :
    evalReal point (formalPartial coordinate (0 : RationalPolynomial 68)) =
      0 := by
  change evalReal point
    (formalPartial coordinate (.constant 0 : RationalPolynomial 68)) = 0
  exact evalReal_formalPartial_constant point coordinate 0

@[simp] theorem evalReal_formalPartial_polynomialNeg
    (point : NormalizedCoordinate → ℝ) (coordinate : NormalizedCoordinate)
    (expression : RationalPolynomial 68) :
    evalReal point (formalPartial coordinate (polynomialNeg expression)) =
      -evalReal point (formalPartial coordinate expression) := by
  cases expression <;>
    simp [polynomialNeg, formalPartial, evalReal]

@[simp] theorem evalReal_formalPartial_polynomialAdd
    (point : NormalizedCoordinate → ℝ) (coordinate : NormalizedCoordinate)
    (first second : RationalPolynomial 68) :
    evalReal point
        (formalPartial coordinate (polynomialAdd first second)) =
      evalReal point (formalPartial coordinate first) +
        evalReal point (formalPartial coordinate second) := by
  cases first <;> cases second <;>
    simp only [polynomialAdd]
  all_goals (repeat' first | split) <;>
    simp_all [formalPartial, evalReal]

@[simp] theorem evalReal_formalPartial_polynomialSub
    (point : NormalizedCoordinate → ℝ) (coordinate : NormalizedCoordinate)
    (first second : RationalPolynomial 68) :
    evalReal point
        (formalPartial coordinate (polynomialSub first second)) =
      evalReal point (formalPartial coordinate first) -
        evalReal point (formalPartial coordinate second) := by
  simp [polynomialSub, sub_eq_add_neg]

@[simp] theorem evalReal_formalPartial_polynomialMul
    (point : NormalizedCoordinate → ℝ) (coordinate : NormalizedCoordinate)
    (first second : RationalPolynomial 68) :
    evalReal point
        (formalPartial coordinate (polynomialMul first second)) =
      evalReal point (formalPartial coordinate first) *
          evalReal point second +
        evalReal point first *
          evalReal point (formalPartial coordinate second) := by
  cases first <;> cases second <;>
    simp only [polynomialMul]
  all_goals (repeat' first | split) <;>
    simp_all [formalPartial, evalReal]
  all_goals split <;> simp_all [evalReal]
  all_goals split <;> simp_all [evalReal]

theorem evalReal_faceFieldExpression
    (point : NormalizedCoordinate → ℝ) (output : HazardCoordinate) :
    evalReal point (faceFieldExpression output) =
      linearCombinationValue (preconditioner output)
        (fun input ↦ evalReal point (activeResidualExpression input)) := by
  fin_cases output <;>
    simp [faceFieldExpression, polynomialSum, linearCombinationValue,
      preconditioner, hazardCoordinates, evalReal,
      Math.Interval.RationalPolynomial.evalReal]

theorem evalReal_normalizedHazardDisplacementExpression
    (point : NormalizedCoordinate → ℝ) (output : HazardCoordinate) :
    evalReal point (normalizedHazardDisplacementExpression output) =
      point (hazardVariableIndex output) -
        (1 / hazardRadius : ℚ) *
          linearCombinationValue (preconditioner output)
            (fun input ↦ evalReal point
              (activeResidualExpression input)) := by
  simp [normalizedHazardDisplacementExpression,
    evalReal_faceFieldExpression]

theorem evalReal_formalPartial_faceFieldExpression
    (point : NormalizedCoordinate → ℝ) (output input : HazardCoordinate) :
    evalReal point
        (formalPartial (hazardVariableIndex input)
          (faceFieldExpression output)) =
      linearCombinationValue (preconditioner output)
        (fun coordinate ↦ evalReal point
          (formalPartial (hazardVariableIndex input)
            (activeResidualExpression coordinate))) := by
  fin_cases output <;>
    simp [faceFieldExpression, polynomialSum, linearCombinationValue,
      preconditioner, hazardCoordinates,
      Math.Interval.RationalPolynomial.evalReal]

theorem evalReal_formalPartial_normalizedHazardDisplacementExpression
    (point : NormalizedCoordinate → ℝ) (output input : HazardCoordinate) :
    evalReal point (formalPartial (hazardVariableIndex input)
        (normalizedHazardDisplacementExpression output)) =
      (if output = input then 1 else 0) -
        (1 / hazardRadius : ℚ) *
          linearCombinationValue (preconditioner output)
            (fun coordinate ↦ evalReal point
              (formalPartial (hazardVariableIndex input)
                (activeResidualExpression coordinate))) := by
  rw [normalizedHazardDisplacementExpression,
    evalReal_formalPartial_polynomialSub,
    evalReal_formalPartial_polynomialMul,
    evalReal_formalPartial_faceFieldExpression]
  simp only [evalReal_formalPartial_constant,
    evalReal_formalPartial_var, evalReal_constant, zero_mul, zero_add]
  congr 1
  have hinjective : Function.Injective hazardVariableIndex := by
    intro first second heq
    rw [hazardVariableIndex_eq, hazardVariableIndex_eq] at heq
    exact Sum.inl.inj (normalizedCoordinateEquiv.injective heq)
  rw [if_congr (hinjective.eq_iff) rfl rfl]
  by_cases heq : output = input
  · subst input
    simp
  · have hreverse : input ≠ output := fun h ↦ heq h.symm
    simp [heq, hreverse]

theorem centeredActiveResidualEnclosure_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet rewardParameterCenterBox)
    (coordinate : HazardCoordinate) :
    (centeredActiveResidualEnclosure coordinate).Contains
      (evalReal point (activeResidualExpression coordinate)) := by
  rw [← centeredActiveResidualValue_exact]
  exact (evalSelectedDualDyadic_sound hazardVariableIndex
    (activeResidualExpression coordinate) rewardParameterCenterBox
    point hpoint).1

theorem fullBoxActiveResidualDerivativeEnclosure_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox)
    (coordinate input : HazardCoordinate) :
    (fullBoxActiveResidualDerivativeEnclosure coordinate input).Contains
      (evalReal point (formalPartial (hazardVariableIndex input)
        (activeResidualExpression coordinate))) := by
  rw [← fullBoxActiveResidualDerivative_exact]
  exact (evalSelectedDualDyadic_sound hazardVariableIndex
    (activeResidualExpression coordinate) fullNormalizedCoordinateBox
    point hpoint).2 input

theorem hazardCoordinate_eq_zero_of_mem_rewardParameterCenterBox
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet rewardParameterCenterBox)
    (coordinate : HazardCoordinate) :
    point (hazardVariableIndex coordinate) = 0 := by
  have hcontains := hpoint (hazardVariableIndex coordinate)
  rw [DyadicInterval.Contains, RationalInterval.Contains] at hcontains
  fin_cases coordinate <;>
    norm_num [rewardParameterCenterBox, hazardVariableIndex,
      DyadicInterval.toRationalInterval, DyadicInterval.ofInt,
      DyadicInterval.scale, neighborhoodPrecision] at hcontains ⊢ <;>
    linarith

local macro "verify_centered_normalized_displacement" point:ident hpoint:ident
    output:term : tactic => `(tactic|
  (rw [evalReal_normalizedHazardDisplacementExpression,
     hazardCoordinate_eq_zero_of_mem_rewardParameterCenterBox $point $hpoint $output]
   have hzero := centeredActiveResidualEnclosure_contains $point $hpoint 0
   have hone := centeredActiveResidualEnclosure_contains $point $hpoint 1
   have htwo := centeredActiveResidualEnclosure_contains $point $hpoint 2
   have hthree := centeredActiveResidualEnclosure_contains $point $hpoint 3
   have hfour := centeredActiveResidualEnclosure_contains $point $hpoint 4
   have hfive := centeredActiveResidualEnclosure_contains $point $hpoint 5
   have hsix := centeredActiveResidualEnclosure_contains $point $hpoint 6
   have hseven := centeredActiveResidualEnclosure_contains $point $hpoint 7
   rw [DyadicInterval.Contains, RationalInterval.Contains] at hzero hone htwo hthree
   rw [DyadicInterval.Contains, RationalInterval.Contains] at hfour hfive hsix hseven
   simp [centeredActiveResidualEnclosure] at hzero hone htwo hthree hfour hfive hsix hseven
   rw [DyadicInterval.Contains, RationalInterval.Contains]
   simp [centeredNormalizedHazardDisplacementEnclosure,
     linearCombinationValue, hazardCoordinates, preconditioner]
   norm_num [centeredActiveResidualEnclosure,
     centeredNormalizedHazardDisplacementEnclosure,
     linearCombinationValue, hazardCoordinates, preconditioner,
     DyadicInterval.toRationalInterval, DyadicInterval.scale,
     neighborhoodPrecision, hazardRadius] at hzero hone htwo hthree hfour hfive hsix hseven
   norm_num [centeredNormalizedHazardDisplacementEnclosure,
     linearCombinationValue, hazardCoordinates, preconditioner,
     DyadicInterval.toRationalInterval, DyadicInterval.scale,
     neighborhoodPrecision, hazardRadius]
   constructor <;> linarith))

@[simp] private theorem centeredNormalizedDisplacement_zero_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet rewardParameterCenterBox) :
    (centeredNormalizedHazardDisplacementEnclosure 0).Contains
      (evalReal point (normalizedHazardDisplacementExpression 0)) := by
  verify_centered_normalized_displacement point hpoint 0

@[simp] private theorem centeredNormalizedDisplacement_one_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet rewardParameterCenterBox) :
    (centeredNormalizedHazardDisplacementEnclosure 1).Contains
      (evalReal point (normalizedHazardDisplacementExpression 1)) := by
  verify_centered_normalized_displacement point hpoint 1

@[simp] private theorem centeredNormalizedDisplacement_two_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet rewardParameterCenterBox) :
    (centeredNormalizedHazardDisplacementEnclosure 2).Contains
      (evalReal point (normalizedHazardDisplacementExpression 2)) := by
  verify_centered_normalized_displacement point hpoint 2

@[simp] private theorem centeredNormalizedDisplacement_three_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet rewardParameterCenterBox) :
    (centeredNormalizedHazardDisplacementEnclosure 3).Contains
      (evalReal point (normalizedHazardDisplacementExpression 3)) := by
  verify_centered_normalized_displacement point hpoint 3

@[simp] private theorem centeredNormalizedDisplacement_four_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet rewardParameterCenterBox) :
    (centeredNormalizedHazardDisplacementEnclosure 4).Contains
      (evalReal point (normalizedHazardDisplacementExpression 4)) := by
  verify_centered_normalized_displacement point hpoint 4

@[simp] private theorem centeredNormalizedDisplacement_five_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet rewardParameterCenterBox) :
    (centeredNormalizedHazardDisplacementEnclosure 5).Contains
      (evalReal point (normalizedHazardDisplacementExpression 5)) := by
  verify_centered_normalized_displacement point hpoint 5

@[simp] private theorem centeredNormalizedDisplacement_six_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet rewardParameterCenterBox) :
    (centeredNormalizedHazardDisplacementEnclosure 6).Contains
      (evalReal point (normalizedHazardDisplacementExpression 6)) := by
  verify_centered_normalized_displacement point hpoint 6

@[simp] private theorem centeredNormalizedDisplacement_seven_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet rewardParameterCenterBox) :
    (centeredNormalizedHazardDisplacementEnclosure 7).Contains
      (evalReal point (normalizedHazardDisplacementExpression 7)) := by
  verify_centered_normalized_displacement point hpoint 7

theorem centeredNormalizedHazardDisplacementEnclosure_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet rewardParameterCenterBox)
    (output : HazardCoordinate) :
    (centeredNormalizedHazardDisplacementEnclosure output).Contains
      (evalReal point (normalizedHazardDisplacementExpression output)) := by
  fin_cases output <;> simp [*]

local macro "verify_normalized_displacement_derivative" point:ident hpoint:ident
    input:term : tactic => `(tactic|
  (rw [evalReal_formalPartial_normalizedHazardDisplacementExpression]
   have hzero :=
     fullBoxActiveResidualDerivativeEnclosure_contains $point $hpoint 0 $input
   have hone :=
     fullBoxActiveResidualDerivativeEnclosure_contains $point $hpoint 1 $input
   have htwo :=
     fullBoxActiveResidualDerivativeEnclosure_contains $point $hpoint 2 $input
   have hthree :=
     fullBoxActiveResidualDerivativeEnclosure_contains $point $hpoint 3 $input
   have hfour :=
     fullBoxActiveResidualDerivativeEnclosure_contains $point $hpoint 4 $input
   have hfive :=
     fullBoxActiveResidualDerivativeEnclosure_contains $point $hpoint 5 $input
   have hsix :=
     fullBoxActiveResidualDerivativeEnclosure_contains $point $hpoint 6 $input
   have hseven :=
     fullBoxActiveResidualDerivativeEnclosure_contains $point $hpoint 7 $input
   rw [DyadicInterval.Contains, RationalInterval.Contains] at hzero hone htwo hthree
   rw [DyadicInterval.Contains, RationalInterval.Contains] at hfour hfive hsix hseven
   simp [fullBoxActiveResidualDerivativeEnclosure] at hzero hone htwo hthree hfour hfive hsix hseven
   rw [DyadicInterval.Contains, RationalInterval.Contains]
   simp [fullBoxNormalizedHazardDisplacementDerivativeEnclosure,
     linearCombinationValue, hazardCoordinates, preconditioner]
   norm_num [fullBoxActiveResidualDerivativeEnclosure,
     fullBoxNormalizedHazardDisplacementDerivativeEnclosure,
     linearCombinationValue, hazardCoordinates, preconditioner,
     DyadicInterval.toRationalInterval, DyadicInterval.scale,
     neighborhoodPrecision, hazardRadius] at hzero hone htwo hthree hfour hfive hsix hseven
   norm_num [fullBoxNormalizedHazardDisplacementDerivativeEnclosure,
     linearCombinationValue, hazardCoordinates, preconditioner,
     DyadicInterval.toRationalInterval, DyadicInterval.scale,
     neighborhoodPrecision, hazardRadius]
   constructor <;> linarith))

@[simp] private theorem normalizedDisplacementDerivative_zero_zero_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 0 0).Contains
      (evalReal point (formalPartial (hazardVariableIndex 0)
        (normalizedHazardDisplacementExpression 0))) := by
  verify_normalized_displacement_derivative point hpoint 0

@[simp] private theorem normalizedDisplacementDerivative_zero_one_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 0 1).Contains
      (evalReal point (formalPartial (hazardVariableIndex 1)
        (normalizedHazardDisplacementExpression 0))) := by
  verify_normalized_displacement_derivative point hpoint 1

@[simp] private theorem normalizedDisplacementDerivative_zero_two_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 0 2).Contains
      (evalReal point (formalPartial (hazardVariableIndex 2)
        (normalizedHazardDisplacementExpression 0))) := by
  verify_normalized_displacement_derivative point hpoint 2

@[simp] private theorem normalizedDisplacementDerivative_zero_three_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 0 3).Contains
      (evalReal point (formalPartial (hazardVariableIndex 3)
        (normalizedHazardDisplacementExpression 0))) := by
  verify_normalized_displacement_derivative point hpoint 3

@[simp] private theorem normalizedDisplacementDerivative_zero_four_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 0 4).Contains
      (evalReal point (formalPartial (hazardVariableIndex 4)
        (normalizedHazardDisplacementExpression 0))) := by
  verify_normalized_displacement_derivative point hpoint 4

@[simp] private theorem normalizedDisplacementDerivative_zero_five_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 0 5).Contains
      (evalReal point (formalPartial (hazardVariableIndex 5)
        (normalizedHazardDisplacementExpression 0))) := by
  verify_normalized_displacement_derivative point hpoint 5

@[simp] private theorem normalizedDisplacementDerivative_zero_six_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 0 6).Contains
      (evalReal point (formalPartial (hazardVariableIndex 6)
        (normalizedHazardDisplacementExpression 0))) := by
  verify_normalized_displacement_derivative point hpoint 6

@[simp] private theorem normalizedDisplacementDerivative_zero_seven_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 0 7).Contains
      (evalReal point (formalPartial (hazardVariableIndex 7)
        (normalizedHazardDisplacementExpression 0))) := by
  verify_normalized_displacement_derivative point hpoint 7

@[simp] private theorem normalizedDisplacementDerivative_one_zero_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 1 0).Contains
      (evalReal point (formalPartial (hazardVariableIndex 0)
        (normalizedHazardDisplacementExpression 1))) := by
  verify_normalized_displacement_derivative point hpoint 0

@[simp] private theorem normalizedDisplacementDerivative_one_one_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 1 1).Contains
      (evalReal point (formalPartial (hazardVariableIndex 1)
        (normalizedHazardDisplacementExpression 1))) := by
  verify_normalized_displacement_derivative point hpoint 1

@[simp] private theorem normalizedDisplacementDerivative_one_two_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 1 2).Contains
      (evalReal point (formalPartial (hazardVariableIndex 2)
        (normalizedHazardDisplacementExpression 1))) := by
  verify_normalized_displacement_derivative point hpoint 2

@[simp] private theorem normalizedDisplacementDerivative_one_three_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 1 3).Contains
      (evalReal point (formalPartial (hazardVariableIndex 3)
        (normalizedHazardDisplacementExpression 1))) := by
  verify_normalized_displacement_derivative point hpoint 3

@[simp] private theorem normalizedDisplacementDerivative_one_four_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 1 4).Contains
      (evalReal point (formalPartial (hazardVariableIndex 4)
        (normalizedHazardDisplacementExpression 1))) := by
  verify_normalized_displacement_derivative point hpoint 4

@[simp] private theorem normalizedDisplacementDerivative_one_five_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 1 5).Contains
      (evalReal point (formalPartial (hazardVariableIndex 5)
        (normalizedHazardDisplacementExpression 1))) := by
  verify_normalized_displacement_derivative point hpoint 5

@[simp] private theorem normalizedDisplacementDerivative_one_six_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 1 6).Contains
      (evalReal point (formalPartial (hazardVariableIndex 6)
        (normalizedHazardDisplacementExpression 1))) := by
  verify_normalized_displacement_derivative point hpoint 6

@[simp] private theorem normalizedDisplacementDerivative_one_seven_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 1 7).Contains
      (evalReal point (formalPartial (hazardVariableIndex 7)
        (normalizedHazardDisplacementExpression 1))) := by
  verify_normalized_displacement_derivative point hpoint 7

@[simp] private theorem normalizedDisplacementDerivative_two_zero_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 2 0).Contains
      (evalReal point (formalPartial (hazardVariableIndex 0)
        (normalizedHazardDisplacementExpression 2))) := by
  verify_normalized_displacement_derivative point hpoint 0

@[simp] private theorem normalizedDisplacementDerivative_two_one_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 2 1).Contains
      (evalReal point (formalPartial (hazardVariableIndex 1)
        (normalizedHazardDisplacementExpression 2))) := by
  verify_normalized_displacement_derivative point hpoint 1

@[simp] private theorem normalizedDisplacementDerivative_two_two_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 2 2).Contains
      (evalReal point (formalPartial (hazardVariableIndex 2)
        (normalizedHazardDisplacementExpression 2))) := by
  verify_normalized_displacement_derivative point hpoint 2

@[simp] private theorem normalizedDisplacementDerivative_two_three_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 2 3).Contains
      (evalReal point (formalPartial (hazardVariableIndex 3)
        (normalizedHazardDisplacementExpression 2))) := by
  verify_normalized_displacement_derivative point hpoint 3

@[simp] private theorem normalizedDisplacementDerivative_two_four_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 2 4).Contains
      (evalReal point (formalPartial (hazardVariableIndex 4)
        (normalizedHazardDisplacementExpression 2))) := by
  verify_normalized_displacement_derivative point hpoint 4

@[simp] private theorem normalizedDisplacementDerivative_two_five_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 2 5).Contains
      (evalReal point (formalPartial (hazardVariableIndex 5)
        (normalizedHazardDisplacementExpression 2))) := by
  verify_normalized_displacement_derivative point hpoint 5

@[simp] private theorem normalizedDisplacementDerivative_two_six_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 2 6).Contains
      (evalReal point (formalPartial (hazardVariableIndex 6)
        (normalizedHazardDisplacementExpression 2))) := by
  verify_normalized_displacement_derivative point hpoint 6

@[simp] private theorem normalizedDisplacementDerivative_two_seven_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 2 7).Contains
      (evalReal point (formalPartial (hazardVariableIndex 7)
        (normalizedHazardDisplacementExpression 2))) := by
  verify_normalized_displacement_derivative point hpoint 7

@[simp] private theorem normalizedDisplacementDerivative_three_zero_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 3 0).Contains
      (evalReal point (formalPartial (hazardVariableIndex 0)
        (normalizedHazardDisplacementExpression 3))) := by
  verify_normalized_displacement_derivative point hpoint 0

@[simp] private theorem normalizedDisplacementDerivative_three_one_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 3 1).Contains
      (evalReal point (formalPartial (hazardVariableIndex 1)
        (normalizedHazardDisplacementExpression 3))) := by
  verify_normalized_displacement_derivative point hpoint 1

@[simp] private theorem normalizedDisplacementDerivative_three_two_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 3 2).Contains
      (evalReal point (formalPartial (hazardVariableIndex 2)
        (normalizedHazardDisplacementExpression 3))) := by
  verify_normalized_displacement_derivative point hpoint 2

@[simp] private theorem normalizedDisplacementDerivative_three_three_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 3 3).Contains
      (evalReal point (formalPartial (hazardVariableIndex 3)
        (normalizedHazardDisplacementExpression 3))) := by
  verify_normalized_displacement_derivative point hpoint 3

@[simp] private theorem normalizedDisplacementDerivative_three_four_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 3 4).Contains
      (evalReal point (formalPartial (hazardVariableIndex 4)
        (normalizedHazardDisplacementExpression 3))) := by
  verify_normalized_displacement_derivative point hpoint 4

@[simp] private theorem normalizedDisplacementDerivative_three_five_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 3 5).Contains
      (evalReal point (formalPartial (hazardVariableIndex 5)
        (normalizedHazardDisplacementExpression 3))) := by
  verify_normalized_displacement_derivative point hpoint 5

@[simp] private theorem normalizedDisplacementDerivative_three_six_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 3 6).Contains
      (evalReal point (formalPartial (hazardVariableIndex 6)
        (normalizedHazardDisplacementExpression 3))) := by
  verify_normalized_displacement_derivative point hpoint 6

@[simp] private theorem normalizedDisplacementDerivative_three_seven_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 3 7).Contains
      (evalReal point (formalPartial (hazardVariableIndex 7)
        (normalizedHazardDisplacementExpression 3))) := by
  verify_normalized_displacement_derivative point hpoint 7

@[simp] private theorem normalizedDisplacementDerivative_four_zero_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 4 0).Contains
      (evalReal point (formalPartial (hazardVariableIndex 0)
        (normalizedHazardDisplacementExpression 4))) := by
  verify_normalized_displacement_derivative point hpoint 0

@[simp] private theorem normalizedDisplacementDerivative_four_one_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 4 1).Contains
      (evalReal point (formalPartial (hazardVariableIndex 1)
        (normalizedHazardDisplacementExpression 4))) := by
  verify_normalized_displacement_derivative point hpoint 1

@[simp] private theorem normalizedDisplacementDerivative_four_two_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 4 2).Contains
      (evalReal point (formalPartial (hazardVariableIndex 2)
        (normalizedHazardDisplacementExpression 4))) := by
  verify_normalized_displacement_derivative point hpoint 2

@[simp] private theorem normalizedDisplacementDerivative_four_three_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 4 3).Contains
      (evalReal point (formalPartial (hazardVariableIndex 3)
        (normalizedHazardDisplacementExpression 4))) := by
  verify_normalized_displacement_derivative point hpoint 3

@[simp] private theorem normalizedDisplacementDerivative_four_four_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 4 4).Contains
      (evalReal point (formalPartial (hazardVariableIndex 4)
        (normalizedHazardDisplacementExpression 4))) := by
  verify_normalized_displacement_derivative point hpoint 4

@[simp] private theorem normalizedDisplacementDerivative_four_five_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 4 5).Contains
      (evalReal point (formalPartial (hazardVariableIndex 5)
        (normalizedHazardDisplacementExpression 4))) := by
  verify_normalized_displacement_derivative point hpoint 5

@[simp] private theorem normalizedDisplacementDerivative_four_six_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 4 6).Contains
      (evalReal point (formalPartial (hazardVariableIndex 6)
        (normalizedHazardDisplacementExpression 4))) := by
  verify_normalized_displacement_derivative point hpoint 6

@[simp] private theorem normalizedDisplacementDerivative_four_seven_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 4 7).Contains
      (evalReal point (formalPartial (hazardVariableIndex 7)
        (normalizedHazardDisplacementExpression 4))) := by
  verify_normalized_displacement_derivative point hpoint 7

@[simp] private theorem normalizedDisplacementDerivative_five_zero_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 5 0).Contains
      (evalReal point (formalPartial (hazardVariableIndex 0)
        (normalizedHazardDisplacementExpression 5))) := by
  verify_normalized_displacement_derivative point hpoint 0

@[simp] private theorem normalizedDisplacementDerivative_five_one_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 5 1).Contains
      (evalReal point (formalPartial (hazardVariableIndex 1)
        (normalizedHazardDisplacementExpression 5))) := by
  verify_normalized_displacement_derivative point hpoint 1

@[simp] private theorem normalizedDisplacementDerivative_five_two_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 5 2).Contains
      (evalReal point (formalPartial (hazardVariableIndex 2)
        (normalizedHazardDisplacementExpression 5))) := by
  verify_normalized_displacement_derivative point hpoint 2

@[simp] private theorem normalizedDisplacementDerivative_five_three_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 5 3).Contains
      (evalReal point (formalPartial (hazardVariableIndex 3)
        (normalizedHazardDisplacementExpression 5))) := by
  verify_normalized_displacement_derivative point hpoint 3

@[simp] private theorem normalizedDisplacementDerivative_five_four_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 5 4).Contains
      (evalReal point (formalPartial (hazardVariableIndex 4)
        (normalizedHazardDisplacementExpression 5))) := by
  verify_normalized_displacement_derivative point hpoint 4

@[simp] private theorem normalizedDisplacementDerivative_five_five_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 5 5).Contains
      (evalReal point (formalPartial (hazardVariableIndex 5)
        (normalizedHazardDisplacementExpression 5))) := by
  verify_normalized_displacement_derivative point hpoint 5

@[simp] private theorem normalizedDisplacementDerivative_five_six_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 5 6).Contains
      (evalReal point (formalPartial (hazardVariableIndex 6)
        (normalizedHazardDisplacementExpression 5))) := by
  verify_normalized_displacement_derivative point hpoint 6

@[simp] private theorem normalizedDisplacementDerivative_five_seven_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 5 7).Contains
      (evalReal point (formalPartial (hazardVariableIndex 7)
        (normalizedHazardDisplacementExpression 5))) := by
  verify_normalized_displacement_derivative point hpoint 7

@[simp] private theorem normalizedDisplacementDerivative_six_zero_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 6 0).Contains
      (evalReal point (formalPartial (hazardVariableIndex 0)
        (normalizedHazardDisplacementExpression 6))) := by
  verify_normalized_displacement_derivative point hpoint 0

@[simp] private theorem normalizedDisplacementDerivative_six_one_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 6 1).Contains
      (evalReal point (formalPartial (hazardVariableIndex 1)
        (normalizedHazardDisplacementExpression 6))) := by
  verify_normalized_displacement_derivative point hpoint 1

@[simp] private theorem normalizedDisplacementDerivative_six_two_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 6 2).Contains
      (evalReal point (formalPartial (hazardVariableIndex 2)
        (normalizedHazardDisplacementExpression 6))) := by
  verify_normalized_displacement_derivative point hpoint 2

@[simp] private theorem normalizedDisplacementDerivative_six_three_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 6 3).Contains
      (evalReal point (formalPartial (hazardVariableIndex 3)
        (normalizedHazardDisplacementExpression 6))) := by
  verify_normalized_displacement_derivative point hpoint 3

@[simp] private theorem normalizedDisplacementDerivative_six_four_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 6 4).Contains
      (evalReal point (formalPartial (hazardVariableIndex 4)
        (normalizedHazardDisplacementExpression 6))) := by
  verify_normalized_displacement_derivative point hpoint 4

@[simp] private theorem normalizedDisplacementDerivative_six_five_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 6 5).Contains
      (evalReal point (formalPartial (hazardVariableIndex 5)
        (normalizedHazardDisplacementExpression 6))) := by
  verify_normalized_displacement_derivative point hpoint 5

@[simp] private theorem normalizedDisplacementDerivative_six_six_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 6 6).Contains
      (evalReal point (formalPartial (hazardVariableIndex 6)
        (normalizedHazardDisplacementExpression 6))) := by
  verify_normalized_displacement_derivative point hpoint 6

@[simp] private theorem normalizedDisplacementDerivative_six_seven_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 6 7).Contains
      (evalReal point (formalPartial (hazardVariableIndex 7)
        (normalizedHazardDisplacementExpression 6))) := by
  verify_normalized_displacement_derivative point hpoint 7

@[simp] private theorem normalizedDisplacementDerivative_seven_zero_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 7 0).Contains
      (evalReal point (formalPartial (hazardVariableIndex 0)
        (normalizedHazardDisplacementExpression 7))) := by
  verify_normalized_displacement_derivative point hpoint 0

@[simp] private theorem normalizedDisplacementDerivative_seven_one_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 7 1).Contains
      (evalReal point (formalPartial (hazardVariableIndex 1)
        (normalizedHazardDisplacementExpression 7))) := by
  verify_normalized_displacement_derivative point hpoint 1

@[simp] private theorem normalizedDisplacementDerivative_seven_two_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 7 2).Contains
      (evalReal point (formalPartial (hazardVariableIndex 2)
        (normalizedHazardDisplacementExpression 7))) := by
  verify_normalized_displacement_derivative point hpoint 2

@[simp] private theorem normalizedDisplacementDerivative_seven_three_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 7 3).Contains
      (evalReal point (formalPartial (hazardVariableIndex 3)
        (normalizedHazardDisplacementExpression 7))) := by
  verify_normalized_displacement_derivative point hpoint 3

@[simp] private theorem normalizedDisplacementDerivative_seven_four_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 7 4).Contains
      (evalReal point (formalPartial (hazardVariableIndex 4)
        (normalizedHazardDisplacementExpression 7))) := by
  verify_normalized_displacement_derivative point hpoint 4

@[simp] private theorem normalizedDisplacementDerivative_seven_five_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 7 5).Contains
      (evalReal point (formalPartial (hazardVariableIndex 5)
        (normalizedHazardDisplacementExpression 7))) := by
  verify_normalized_displacement_derivative point hpoint 5

@[simp] private theorem normalizedDisplacementDerivative_seven_six_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 7 6).Contains
      (evalReal point (formalPartial (hazardVariableIndex 6)
        (normalizedHazardDisplacementExpression 7))) := by
  verify_normalized_displacement_derivative point hpoint 6

@[simp] private theorem normalizedDisplacementDerivative_seven_seven_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure 7 7).Contains
      (evalReal point (formalPartial (hazardVariableIndex 7)
        (normalizedHazardDisplacementExpression 7))) := by
  verify_normalized_displacement_derivative point hpoint 7


theorem fullBoxNormalizedHazardDisplacementDerivativeEnclosure_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox)
    (output input : HazardCoordinate) :
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure
        output input).Contains
      (evalReal point (formalPartial (hazardVariableIndex input)
        (normalizedHazardDisplacementExpression output))) := by
  fin_cases output <;> fin_cases input <;> simp [*]

end GameTheory.FourPlayerOverlappingPeriodThree

end
