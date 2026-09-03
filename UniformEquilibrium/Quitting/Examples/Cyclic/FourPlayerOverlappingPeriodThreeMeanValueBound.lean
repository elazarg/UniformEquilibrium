import UniformEquilibrium.Quitting.Examples.Cyclic.FourPlayerOverlappingPeriodThreeNeighborhoodBounds

/-!
# Mean-value bound for the preconditioned active-gap field

The integer bound below is assembled only from the separately checked center
and hazard-partial enclosures.  Reward coordinates remain independent fixed
parameters throughout each mean-value argument.
-/

noncomputable section

namespace GameTheory.FourPlayerOverlappingPeriodThree

open Function Metric Set
open Math.Interval Math.Interval.RationalPolynomial

/-- Common-scale integer numerator for the center envelope plus the eight
hazard-partial envelopes of one normalized displacement coordinate. -/
def preconditionedActiveGapMeanValueNumerator
    (output : HazardCoordinate) : ℤ :=
  dyadicAbsNumerator (centeredNormalizedHazardDisplacementEnclosure output) +
    ∑ input, dyadicAbsNumerator
      (fullBoxNormalizedHazardDisplacementDerivativeEnclosure output input)

/-- Literal exact numerators in active-coordinate order. -/
def preconditionedActiveGapMeanValueNumeratorValue :
    HazardCoordinate → ℤ :=
  ![9681562770299551616,
    14443404674829551616,
    14322042623460448384,
    4592253211369551616,
    6993881516960448384,
    8630663034379551616,
    15185063543559551616,
    7406500604670448384]

private theorem preconditionedActiveGapMeanValueNumerator_zero_exact :
    preconditionedActiveGapMeanValueNumerator 0 =
      preconditionedActiveGapMeanValueNumeratorValue 0 := by
  decide

private theorem preconditionedActiveGapMeanValueNumerator_one_exact :
    preconditionedActiveGapMeanValueNumerator 1 =
      preconditionedActiveGapMeanValueNumeratorValue 1 := by
  decide

private theorem preconditionedActiveGapMeanValueNumerator_two_exact :
    preconditionedActiveGapMeanValueNumerator 2 =
      preconditionedActiveGapMeanValueNumeratorValue 2 := by
  decide

private theorem preconditionedActiveGapMeanValueNumerator_three_exact :
    preconditionedActiveGapMeanValueNumerator 3 =
      preconditionedActiveGapMeanValueNumeratorValue 3 := by
  decide

private theorem preconditionedActiveGapMeanValueNumerator_four_exact :
    preconditionedActiveGapMeanValueNumerator 4 =
      preconditionedActiveGapMeanValueNumeratorValue 4 := by
  decide

private theorem preconditionedActiveGapMeanValueNumerator_five_exact :
    preconditionedActiveGapMeanValueNumerator 5 =
      preconditionedActiveGapMeanValueNumeratorValue 5 := by
  decide

private theorem preconditionedActiveGapMeanValueNumerator_six_exact :
    preconditionedActiveGapMeanValueNumerator 6 =
      preconditionedActiveGapMeanValueNumeratorValue 6 := by
  decide

private theorem preconditionedActiveGapMeanValueNumerator_seven_exact :
    preconditionedActiveGapMeanValueNumerator 7 =
      preconditionedActiveGapMeanValueNumeratorValue 7 := by
  decide

/-- The exact integer row sums used in the supplied-partial mean-value
estimate. -/
theorem preconditionedActiveGapMeanValueNumerator_exact
    (output : HazardCoordinate) :
    preconditionedActiveGapMeanValueNumerator output =
      preconditionedActiveGapMeanValueNumeratorValue output := by
  fin_cases output
  · exact preconditionedActiveGapMeanValueNumerator_zero_exact
  · exact preconditionedActiveGapMeanValueNumerator_one_exact
  · exact preconditionedActiveGapMeanValueNumerator_two_exact
  · exact preconditionedActiveGapMeanValueNumerator_three_exact
  · exact preconditionedActiveGapMeanValueNumerator_four_exact
  · exact preconditionedActiveGapMeanValueNumerator_five_exact
  · exact preconditionedActiveGapMeanValueNumerator_six_exact
  · exact preconditionedActiveGapMeanValueNumerator_seven_exact

/-- Every exact numerator is strictly below five sixths of the common dyadic
scale. -/
theorem preconditionedActiveGapMeanValueNumerator_lt_five_sixths
    (output : HazardCoordinate) :
    6 * preconditionedActiveGapMeanValueNumerator output <
      5 * (DyadicInterval.scale neighborhoodPrecision : ℤ) := by
  rw [preconditionedActiveGapMeanValueNumerator_exact]
  fin_cases output <;>
    norm_num [preconditionedActiveGapMeanValueNumeratorValue,
      DyadicInterval.scale, neighborhoodPrecision]

/-- The checked center and partial enclosures give the uniform five-sixths
bound for any fixed choice of the sixty trailing reward parameters. -/
theorem normalizedHazardDisplacement_abs_le_five_sixths
    (output : HazardCoordinate)
    (center point : HazardCoordinate → ℝ)
    (parameter : Fin 60 → ℝ)
    (hcenterBox : leadingCoordinatePoint center parameter ∈
      dyadicBoxSet fullNormalizedCoordinateBox)
    (hpoint : leadingCoordinatePoint point parameter ∈
      dyadicBoxSet fullNormalizedCoordinateBox)
    (hcenterParameter : leadingCoordinatePoint center parameter ∈
      dyadicBoxSet rewardParameterCenterBox)
    (hradius : dist point center ≤ 1) :
    |evalReal (leadingCoordinatePoint point parameter)
      (normalizedHazardDisplacementExpression output)| ≤ (5 : ℝ) / 6 := by
  have hcenterContains :=
    centeredNormalizedHazardDisplacementEnclosure_contains
      (leadingCoordinatePoint center parameter) hcenterParameter output
  have hderivativeContains : ∀ varying,
      leadingCoordinatePoint varying parameter ∈
          dyadicBoxSet fullNormalizedCoordinateBox →
        ∀ input, (fullBoxNormalizedHazardDisplacementDerivativeEnclosure
            output input).Contains
          (evalReal (leadingCoordinatePoint varying parameter)
            (formalPartial (Fin.castAdd 60 input)
              (normalizedHazardDisplacementExpression output))) := by
    intro varying hvarying input
    rw [show Fin.castAdd 60 input = hazardVariableIndex input by
      apply Fin.ext
      rfl]
    exact
      fullBoxNormalizedHazardDisplacementDerivativeEnclosure_contains
        (leadingCoordinatePoint varying parameter) hvarying output input
  have hbound :
      (dyadicAbsNumerator
          (centeredNormalizedHazardDisplacementEnclosure output) +
        ∑ input, dyadicAbsNumerator
          (fullBoxNormalizedHazardDisplacementDerivativeEnclosure
            output input) : ℚ) ≤
      (5 : ℚ) / 6 *
        ((DyadicInterval.scale neighborhoodPrecision : ℤ) : ℚ) := by
    rw [← Int.cast_add]
    change (preconditionedActiveGapMeanValueNumerator output : ℚ) ≤ _
    rw [preconditionedActiveGapMeanValueNumerator_exact]
    fin_cases output <;>
      norm_num [preconditionedActiveGapMeanValueNumeratorValue,
        DyadicInterval.scale, neighborhoodPrecision]
  have hresult := abs_evalReal_le_of_suppliedCenteredPartialEnclosures
    (normalizedHazardDisplacementExpression output)
    fullNormalizedCoordinateBox center point parameter
    (centeredNormalizedHazardDisplacementEnclosure output)
    (fullBoxNormalizedHazardDisplacementDerivativeEnclosure output)
    hcenterBox hpoint hcenterContains hderivativeContains hradius
    ((5 : ℚ) / 6) hbound
  norm_num at hresult ⊢
  exact hresult

end GameTheory.FourPlayerOverlappingPeriodThree

end
