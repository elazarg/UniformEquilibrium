import UniformEquilibrium.Quitting.Examples.Cyclic.FourPlayerOverlappingPeriodThreeIntervalArithmetic

/-!
# Exact denominator and inactive-gap screens

This file checks the denominator away from zero and the four inactive
Continue inequalities throughout the full 68-coordinate neighborhood.
-/

noncomputable section

namespace GameTheory.FourPlayerOverlappingPeriodThree

open Math.Interval Math.Interval.RationalPolynomial

abbrev InactiveSlot := Fin 4

def inactivePhasePlayer : InactiveSlot → Fin 3 × Player :=
  ![(0, 0), (0, 3), (1, 2), (2, 1)]

def fullBoxValue (expression : RationalPolynomial 68) :
    DyadicInterval neighborhoodPrecision :=
  (evalSelectedDualDyadic hazardVariableIndex
    fullNormalizedCoordinateBox expression).value

def denominatorEnclosure : DyadicInterval neighborhoodPrecision :=
  ⟨16921564715779817904, 16921568080711504555⟩

def inactiveClearedGapEnclosure : InactiveSlot →
    DyadicInterval neighborhoodPrecision :=
  ![⟨-8786926883513355958, -8786875023564182876⟩,
    ⟨-5399030146343031354, -5398980921338889595⟩,
    ⟨-5659232525623993001, -5659141034159709814⟩,
    ⟨-6895703460605005572, -6895624544913677447⟩]

local macro "verify_full_box_value" : tactic => `(tactic|
  (simp [fullBoxValue, inactivePhasePlayer, inactiveClearedGapEnclosure,
      denominatorEnclosure, supportedClearedGapExpression,
      supportedWindowExpression, supportedImmediateExpression,
      supportedPureQuitExpression, supportedExcludedExpression,
      supportedImmediateTerm, supportedEndpointTerm,
      supportedCoalitionMassExpression, supportedOpponentMassExpression,
      rowHazardFactor, rowContains, supportRows, pureQuitRows, excludedRows,
      polynomialListSum, denominatorExpression,
      opponentContinueExpression, continueExpression, hazardExpression,
      rewardExpression, activeSlot, nextPhase, hazardVariableIndex,
      rewardVariableIndex, hazardCenter, hazardRadius, rewardRadius,
      overlappingPeriodThreeRewardRow] <;>
    norm_num1 <;>
    simp [polynomialProduct, polynomialAdd, polynomialSub,
      polynomialNeg, polynomialMul, evalSelectedDualDyadic,
      DyadicDual.constant, DyadicDual.add, DyadicDual.neg,
      DyadicDual.mul] <;>
    norm_num [fullNormalizedCoordinateBox, DyadicInterval.ofRat,
      DyadicInterval.ofInt, DyadicInterval.add, DyadicInterval.neg,
      DyadicInterval.mul_eq_outward_four_corners,
      DyadicInterval.scale, Rat.floor_def, Rat.ceil,
      neighborhoodPrecision]))

private theorem denominatorValue_exact :
    fullBoxValue denominatorExpression = denominatorEnclosure := by
  verify_full_box_value

@[simp] private theorem inactiveClearedGapValue_zero_exact :
    fullBoxValue (supportedClearedGapExpression 0 0) =
      inactiveClearedGapEnclosure 0 := by
  verify_full_box_value

@[simp] private theorem inactiveClearedGapValue_one_exact :
    fullBoxValue (supportedClearedGapExpression 0 3) =
      inactiveClearedGapEnclosure 1 := by
  verify_full_box_value

@[simp] private theorem inactiveClearedGapValue_two_exact :
    fullBoxValue (supportedClearedGapExpression 1 2) =
      inactiveClearedGapEnclosure 2 := by
  verify_full_box_value

@[simp] private theorem inactiveClearedGapValue_three_exact :
    fullBoxValue (supportedClearedGapExpression 2 1) =
      inactiveClearedGapEnclosure 3 := by
  verify_full_box_value

theorem inactiveClearedGapValue_exact (slot : InactiveSlot) :
    fullBoxValue
        (supportedClearedGapExpression
          (inactivePhasePlayer slot).1 (inactivePhasePlayer slot).2) =
      inactiveClearedGapEnclosure slot := by
  fin_cases slot
  · exact inactiveClearedGapValue_zero_exact
  · exact inactiveClearedGapValue_one_exact
  · exact inactiveClearedGapValue_two_exact
  · exact inactiveClearedGapValue_three_exact

theorem denominatorEnclosure_contains
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    denominatorEnclosure.Contains (evalReal point denominatorExpression) := by
  rw [← denominatorValue_exact]
  exact (evalSelectedDualDyadic_sound hazardVariableIndex
    denominatorExpression fullNormalizedCoordinateBox point hpoint).1

theorem denominator_strict_bounds
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox) :
    (9 : ℝ) / 10 < evalReal point denominatorExpression ∧
      evalReal point denominatorExpression < 19 / 20 := by
  have hcontains := denominatorEnclosure_contains point hpoint
  rw [DyadicInterval.Contains, RationalInterval.Contains] at hcontains
  constructor
  · exact lt_of_lt_of_le (by
      norm_num [denominatorEnclosure, DyadicInterval.toRationalInterval,
        neighborhoodPrecision, DyadicInterval.scale]) hcontains.1
  · exact lt_of_le_of_lt hcontains.2 (by
      norm_num [denominatorEnclosure, DyadicInterval.toRationalInterval,
        neighborhoodPrecision, DyadicInterval.scale])

theorem inactiveClearedGap_lt_negative_twenty_nine_hundredths
    (point : NormalizedCoordinate → ℝ)
    (hpoint : point ∈ dyadicBoxSet fullNormalizedCoordinateBox)
    (slot : InactiveSlot) :
    evalReal point
        (supportedClearedGapExpression
          (inactivePhasePlayer slot).1 (inactivePhasePlayer slot).2) <
      -(29 : ℝ) / 100 := by
  have hcontains := (evalSelectedDualDyadic_sound hazardVariableIndex
    (supportedClearedGapExpression
      (inactivePhasePlayer slot).1 (inactivePhasePlayer slot).2)
    fullNormalizedCoordinateBox point hpoint).1
  change (fullBoxValue
      (supportedClearedGapExpression
        (inactivePhasePlayer slot).1 (inactivePhasePlayer slot).2)).Contains
    (evalReal point
      (supportedClearedGapExpression
        (inactivePhasePlayer slot).1 (inactivePhasePlayer slot).2)) at hcontains
  rw [inactiveClearedGapValue_exact] at hcontains
  rw [DyadicInterval.Contains, RationalInterval.Contains] at hcontains
  exact lt_of_le_of_lt hcontains.2 (by
    fin_cases slot <;>
      norm_num [inactiveClearedGapEnclosure,
        DyadicInterval.toRationalInterval,
        neighborhoodPrecision, DyadicInterval.scale])

end GameTheory.FourPlayerOverlappingPeriodThree

end
