import Research.Quitting.BlockPair.K11.KrawczykConditionalSemantic

namespace GameTheory.BlockPairK11.DyadicCertificate

open Function Metric Set
open Math.Interval
open scoped NNReal

noncomputable def canonicalResidual
    (point : HazardIndex → ℝ) : HazardIndex → ℝ :=
  fun row ↦ RationalPolynomial.evalReal point (activeEquation row)

noncomputable def preconditionerLinear :
    (HazardIndex → ℝ) →L[ℝ] (HazardIndex → ℝ) :=
  ContinuousLinearMap.pi fun row ↦
    ∑ column, (preconditioner row column : ℝ) •
      (ContinuousLinearMap.proj column :
        (HazardIndex → ℝ) →L[ℝ] ℝ)

@[simp] theorem preconditionerLinear_apply
    (vector : HazardIndex → ℝ) (row : HazardIndex) :
    preconditionerLinear vector row =
      ∑ column, (preconditioner row column : ℝ) * vector column := by
  simp [preconditionerLinear, smul_eq_mul]

theorem evalReal_expressionSum_krawczyk {count : ℕ}
    (point : HazardIndex → ℝ) (term : Fin count → Expression) :
    RationalPolynomial.evalReal point (expressionSum term) =
      ∑ index, RationalPolynomial.evalReal point (term index) := by
  induction count with
  | zero => simp [expressionSum, RationalPolynomial.evalReal]
  | succ count ih =>
      simp only [expressionSum, RationalPolynomial.evalReal]
      rw [ih, Fin.sum_univ_castSucc]

theorem evalReal_preconditionedResidualExpression
    (point : HazardIndex → ℝ) (row : HazardIndex) :
    RationalPolynomial.evalReal point
      (preconditionedResidualExpression row) =
        preconditionerLinear (canonicalResidual point) row := by
  rw [preconditionedResidualExpression,
    evalReal_expressionSum_krawczyk, preconditionerLinear_apply]
  apply Finset.sum_congr rfl
  intro equation _
  rfl

theorem preconditionedStepExpression_evalReal
    (point : HazardIndex → ℝ) :
    (fun row ↦ RationalPolynomial.evalReal point
      (preconditionedStepExpression row)) =
        point - preconditionerLinear (canonicalResidual point) := by
  funext row
  change point row - RationalPolynomial.evalReal point
    (preconditionedResidualExpression row) =
      point row - preconditionerLinear (canonicalResidual point) row
  rw [evalReal_preconditionedResidualExpression]

noncomputable def canonicalResidualDerivativeAtCenter :
    (HazardIndex → ℝ) →L[ℝ] (HazardIndex → ℝ) :=
  ContinuousLinearMap.pi fun row ↦
    RationalPolynomial.differential
      (fun index ↦ (center index : ℝ)) (activeEquation row)

/-- The finite arithmetic interface consumed by the conditional K11
Krawczyk theorem.  Every field is a direct exact interval/rational check;
the semantic links to the canonical system are separate assumptions. -/
structure K11KrawczykArithmeticCertificate where
  contraction : ℝ≥0
  contraction_lt_one : contraction < 1
  endpoints : ∀ coordinate,
    (box coordinate).Contains ((center coordinate : ℝ) - (radius : ℝ)) ∧
      (box coordinate).Contains ((center coordinate : ℝ) + (radius : ℝ))
  row_sum : ∀ row,
    ∑ column, RationalPolynomial.dyadicAbsBound
      (conditionalBCache row column) ≤ (contraction : ℝ)
  center_correction : ∀ row,
    RationalPolynomial.dyadicAbsBound (conditionalAH0Cache row) ≤
      (1 - (contraction : ℝ)) * (radius : ℝ)
  near_identity :
    ‖1 - preconditionerLinear.comp canonicalResidualDerivativeAtCenter‖ < 1

theorem preconditionerLinear_injective
    (certificate : K11KrawczykArithmeticCertificate) :
    Injective preconditionerLinear :=
  Math.preconditioner_injective_of_norm_one_sub_comp_lt_one
    preconditionerLinear canonicalResidualDerivativeAtCenter
      certificate.near_identity

theorem centerEvaluationBox_contains_center (coordinate : HazardIndex) :
    (centerEvaluationBox coordinate).Contains (center coordinate : ℝ) :=
  DyadicInterval.contains_ofRat _

theorem conditionalAH0Cache_contains_preconditionedResidual
    (hH0 : ∀ row,
      (RationalPolynomial.evalDualDyadic centerEvaluationBox
        (activeEquation row)).value = residualAtCenterCache.get row)
    (row : HazardIndex) :
    (conditionalAH0Cache row).Contains
      (preconditionerLinear
        (canonicalResidual (fun index ↦ (center index : ℝ))) row) := by
  rw [← evalReal_preconditionedResidualExpression]
  rw [← preconditionedResidualExpression_value_center_eq_AH0 hH0]
  exact (RationalPolynomial.evalDualDyadic_sound
    (preconditionedResidualExpression row) centerEvaluationBox
      (fun index ↦ (center index : ℝ))
      centerEvaluationBox_contains_center).1

theorem preconditioner_center_correction_norm
    (certificate : K11KrawczykArithmeticCertificate)
    (hH0 : ∀ row,
      (RationalPolynomial.evalDualDyadic centerEvaluationBox
        (activeEquation row)).value = residualAtCenterCache.get row) :
    ‖preconditionerLinear
      (canonicalResidual (fun index ↦ (center index : ℝ)))‖ ≤
        (1 - (certificate.contraction : ℝ)) * (radius : ℝ) := by
  rw [pi_norm_le_iff_of_nonneg]
  · intro row
    rw [Real.norm_eq_abs]
    exact RationalPolynomial.abs_le_of_dyadicContains_of_endpoints_le
      (conditionalAH0Cache row)
      (preconditionerLinear
        (canonicalResidual (fun index ↦ (center index : ℝ))) row)
      ((1 - (certificate.contraction : ℝ)) * (radius : ℝ))
      (conditionalAH0Cache_contains_preconditionedResidual hH0 row)
      ((le_max_left _ _).trans (certificate.center_correction row))
      ((le_max_right _ _).trans (certificate.center_correction row))
  · exact mul_nonneg
      (sub_nonneg.mpr (le_of_lt certificate.contraction_lt_one))
      (by norm_num [radius])

/-- Conditional exact K11 zero theorem.  Its only semantic assumptions are
the authoritative raw Jacobian and center-residual cache equalities; every
other input is exposed in `K11KrawczykArithmeticCertificate`. -/
theorem exists_canonicalResidual_zero_in_box
    (certificate : K11KrawczykArithmeticCertificate)
    (hJ : ∀ row column,
      (RationalPolynomial.evalDualDyadic box
        (activeEquation row)).derivative column =
          (jacobianBoxCache.get row).get column)
    (hH0 : ∀ row,
      (RationalPolynomial.evalDualDyadic centerEvaluationBox
        (activeEquation row)).value = residualAtCenterCache.get row) :
    ∃ root ∈ closedBall (fun index ↦ (center index : ℝ)) (radius : ℝ),
      canonicalResidual root = 0 := by
  apply RationalPolynomial.exists_zero_in_closedBall_of_evalDualDyadic_absRowSum
    canonicalResidual preconditionerLinear preconditionedStepExpression box
      (fun index ↦ (center index : ℝ)) (radius : ℝ)
      certificate.contraction
  · norm_num [radius]
  · exact certificate.contraction_lt_one
  · exact preconditionerLinear_injective certificate
  · funext point
    exact preconditionedStepExpression_evalReal point
  · exact certificate.endpoints
  · intro row
    simpa only [preconditionedStepExpression_derivative_eq_B hJ] using
      certificate.row_sum row
  · exact preconditioner_center_correction_norm certificate hH0

end GameTheory.BlockPairK11.DyadicCertificate
