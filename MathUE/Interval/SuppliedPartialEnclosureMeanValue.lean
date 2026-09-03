import MathUE.Interval.SelectedCoordinatePolynomialLipschitz

/-!
# Centered mean-value bounds from supplied partial enclosures

This layer combines separately checked value and partial-derivative
enclosures.  It is useful when a polynomial system is assembled linearly
from expensive components whose interval enclosures have already been
checked independently.
-/

noncomputable section

namespace Math
namespace Interval
namespace RationalPolynomial

open Function Metric Set
open scoped NNReal

variable {variableCount parameterCount precision : ℕ}

/-- Supplied dyadic enclosures of each leading formal partial prove a
Lipschitz estimate after the trailing parameters are fixed. -/
theorem lipschitzOnWith_evalReal_leadingCoordinates_of_suppliedPartialEnclosures
    (expression : RationalPolynomial (variableCount + parameterCount))
    (parameter : Fin parameterCount → ℝ)
    (domain : Set (Fin variableCount → ℝ))
    (enclosure : Fin variableCount → DyadicInterval precision)
    (constant : ℝ≥0)
    (hconvex : Convex ℝ domain)
    (hcontains : ∀ point ∈ domain, ∀ coordinate,
      (enclosure coordinate).Contains
        (evalReal (leadingCoordinatePoint point parameter)
          (formalPartial (Fin.castAdd parameterCount coordinate)
            expression)))
    (hrow : ∑ coordinate, dyadicAbsBound (enclosure coordinate) ≤
      (constant : ℝ)) :
    LipschitzOnWith constant
      (fun point ↦ evalReal (leadingCoordinatePoint point parameter)
        expression) domain := by
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
      (bound := fun _ coordinate ↦
        dyadicAbsBound (enclosure coordinate))
      (constant := constant) hconvex ?_ (fun _ ↦ hrow) ?_
    · intro point _
      exact hasFDerivAt_pi.mpr fun _ ↦
        hasFDerivAt_evalReal_leadingCoordinatePoint expression point parameter
    · intro point hpoint _ coordinate
      change ‖leadingCoordinateDifferential
        (leadingCoordinatePoint point parameter) expression
          (piBasisVector coordinate)‖ ≤
            dyadicAbsBound (enclosure coordinate)
      rw [leadingCoordinateDifferential_piBasisVector, Real.norm_eq_abs]
      exact abs_le_of_dyadicContains_of_endpoints_le _ _ _
        (hcontains point hpoint coordinate)
        (le_max_left _ _) (le_max_right _ _)
  intro first hfirst second hsecond
  exact le_trans
    (edist_le_pi_edist
      (fun _ : Fin 1 ↦
        evalReal (leadingCoordinatePoint first parameter) expression)
      (fun _ : Fin 1 ↦
        evalReal (leadingCoordinatePoint second parameter) expression) 0)
    (hvector hfirst hsecond)

/-- A supplied center enclosure and supplied leading-partial enclosures give
a centered absolute bound, with independent trailing parameters. -/
theorem abs_evalReal_le_of_suppliedCenteredPartialEnclosures
    (expression : RationalPolynomial (variableCount + parameterCount))
    (box : Fin (variableCount + parameterCount) → DyadicInterval precision)
    (center point : Fin variableCount → ℝ)
    (parameter : Fin parameterCount → ℝ)
    (centerEnclosure : DyadicInterval precision)
    (derivativeEnclosure : Fin variableCount → DyadicInterval precision)
    (hcenterBox : leadingCoordinatePoint center parameter ∈
      dyadicBoxSet box)
    (hpoint : leadingCoordinatePoint point parameter ∈ dyadicBoxSet box)
    (hcenterContains : centerEnclosure.Contains
      (evalReal (leadingCoordinatePoint center parameter) expression))
    (hderivativeContains : ∀ varying,
      leadingCoordinatePoint varying parameter ∈ dyadicBoxSet box →
        ∀ input, (derivativeEnclosure input).Contains
          (evalReal (leadingCoordinatePoint varying parameter)
            (formalPartial (Fin.castAdd parameterCount input) expression)))
    (hradius : dist point center ≤ 1)
    (bound : ℚ)
    (hbound :
      (dyadicAbsNumerator centerEnclosure +
          ∑ input, dyadicAbsNumerator (derivativeEnclosure input) : ℚ) ≤
        bound * ((DyadicInterval.scale precision : ℤ) : ℚ)) :
    |evalReal (leadingCoordinatePoint point parameter) expression| ≤
      (bound : ℝ) := by
  let derivativeSum : ℝ≥0 :=
    ⟨∑ input, dyadicAbsBound (derivativeEnclosure input),
      Finset.sum_nonneg fun input _ ↦ dyadicAbsBound_nonneg _⟩
  have hlipschitz : LipschitzOnWith derivativeSum
      (fun input ↦
        evalReal (leadingCoordinatePoint input parameter) expression)
      {input | leadingCoordinatePoint input parameter ∈ dyadicBoxSet box} := by
    apply
      lipschitzOnWith_evalReal_leadingCoordinates_of_suppliedPartialEnclosures
        expression parameter _ derivativeEnclosure derivativeSum
    · exact convex_preimage_dyadicBoxSet_leadingCoordinatePoint box parameter
    · intro input hinput coordinate
      exact hderivativeContains input hinput coordinate
    · rfl
  have hcenterValue :
      |evalReal (leadingCoordinatePoint center parameter) expression| ≤
        dyadicAbsBound centerEnclosure :=
    abs_le_of_dyadicContains_of_endpoints_le _ _ _ hcenterContains
      (le_max_left _ _) (le_max_right _ _)
  have hdifference := hlipschitz.dist_le_mul point hpoint center hcenterBox
  rw [Real.dist_eq] at hdifference
  have hsumNonneg : 0 ≤ (derivativeSum : ℝ) := derivativeSum.coe_nonneg
  have hdifferenceOne :
      |evalReal (leadingCoordinatePoint point parameter) expression -
          evalReal (leadingCoordinatePoint center parameter) expression| ≤
        (derivativeSum : ℝ) :=
    hdifference.trans <| by
      simpa using mul_le_mul_of_nonneg_left hradius hsumNonneg
  have hscale : (0 : ℝ) <
      ((DyadicInterval.scale precision : ℤ) : ℝ) := by
    exact_mod_cast DyadicInterval.scale_pos precision
  have hsum :
      dyadicAbsBound centerEnclosure +
          ∑ input, dyadicAbsBound (derivativeEnclosure input) =
        ((dyadicAbsNumerator centerEnclosure +
            ∑ input, dyadicAbsNumerator
              (derivativeEnclosure input) : ℤ) : ℝ) /
          ((DyadicInterval.scale precision : ℤ) : ℝ) := by
    rw [Int.cast_add, add_div,
      dyadicAbsBound_eq_dyadicAbsNumerator_div_scale, Int.cast_sum,
      Finset.sum_div]
    exact congrArg _ (Finset.sum_congr rfl fun input _ ↦
      dyadicAbsBound_eq_dyadicAbsNumerator_div_scale
        (derivativeEnclosure input))
  rw [show evalReal (leadingCoordinatePoint point parameter) expression =
      (evalReal (leadingCoordinatePoint point parameter) expression -
        evalReal (leadingCoordinatePoint center parameter) expression) +
        evalReal (leadingCoordinatePoint center parameter) expression by ring]
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add hdifferenceOne hcenterValue).trans ?_
  change (∑ input, dyadicAbsBound (derivativeEnclosure input)) +
    dyadicAbsBound centerEnclosure ≤ _
  rw [add_comm, hsum, div_le_iff₀ hscale]
  exact_mod_cast hbound

end RationalPolynomial
end Interval
end Math

end
