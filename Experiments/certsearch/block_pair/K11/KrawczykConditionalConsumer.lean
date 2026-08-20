import Experiments.certsearch.block_pair.K11.KrawczykConditionalSemantic

namespace GameTheory.BlockPairK11.DyadicCertificate

open Function Metric Set
open Math.Interval
open scoped NNReal

noncomputable def canonicalResidual
    (point : HazardIndex → ℝ) : HazardIndex → ℝ :=
  fun row ↦ RationalPolynomial.evalReal point (activeEquation row)

noncomputable def preconditionerLinear (data : K11KrawczykData) :
    (HazardIndex → ℝ) →L[ℝ] (HazardIndex → ℝ) :=
  ContinuousLinearMap.pi fun row ↦
    ∑ column, (data.preconditioner row column : ℝ) •
      (ContinuousLinearMap.proj column :
        (HazardIndex → ℝ) →L[ℝ] ℝ)

@[simp] theorem preconditionerLinear_apply
    (data : K11KrawczykData)
    (vector : HazardIndex → ℝ) (row : HazardIndex) :
    preconditionerLinear data vector row =
      ∑ column, (data.preconditioner row column : ℝ) * vector column := by
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
    (data : K11KrawczykData)
    (point : HazardIndex → ℝ) (row : HazardIndex) :
    RationalPolynomial.evalReal point
      (preconditionedResidualExpression data row) =
        preconditionerLinear data (canonicalResidual point) row := by
  rw [preconditionedResidualExpression,
    evalReal_expressionSum_krawczyk, preconditionerLinear_apply]
  apply Finset.sum_congr rfl
  intro equation _
  rfl

theorem preconditionedStepExpression_evalReal
    (data : K11KrawczykData) (point : HazardIndex → ℝ) :
    (fun row ↦ RationalPolynomial.evalReal point
      (preconditionedStepExpression data row)) =
        point - preconditionerLinear data (canonicalResidual point) := by
  funext row
  change point row - RationalPolynomial.evalReal point
    (preconditionedResidualExpression data row) =
      point row - preconditionerLinear data (canonicalResidual point) row
  rw [evalReal_preconditionedResidualExpression]

/-- The finite arithmetic interface consumed by the conditional K11
Krawczyk theorem. Every field is a direct exact interval/rational check;
injectivity and the semantic links to the canonical system are separate
premises. -/
structure K11KrawczykArithmeticCertificate
    (data : K11KrawczykData) where
  contraction : ℝ≥0
  contraction_lt_one : contraction < 1
  endpoints : ∀ coordinate,
    (data.box coordinate).Contains
        ((data.center coordinate : ℝ) - (data.radius : ℝ)) ∧
      (data.box coordinate).Contains
        ((data.center coordinate : ℝ) + (data.radius : ℝ))
  row_sum : ∀ row,
    ∑ column, RationalPolynomial.dyadicAbsBound
      (conditionalBCache data row column) ≤ (contraction : ℝ)
  center_correction : ∀ row,
    RationalPolynomial.dyadicAbsBound (conditionalAH0Cache data row) ≤
      (1 - (contraction : ℝ)) * (data.radius : ℝ)

theorem centerEvaluationBox_contains_center
    (data : K11KrawczykData) (coordinate : HazardIndex) :
    (centerEvaluationBox data coordinate).Contains
      (data.center coordinate : ℝ) :=
  DyadicInterval.contains_ofRat _

theorem conditionalAH0Cache_contains_preconditionedResidual
    (data : K11KrawczykData)
    (hH0 : ∀ row,
      (RationalPolynomial.evalDualDyadic (centerEvaluationBox data)
        (activeEquation row)).value = data.residualAtCenterCache row)
    (row : HazardIndex) :
    (conditionalAH0Cache data row).Contains
      (preconditionerLinear data
        (canonicalResidual (fun index ↦ (data.center index : ℝ))) row) := by
  rw [← evalReal_preconditionedResidualExpression]
  rw [← preconditionedResidualExpression_value_center_eq_AH0 data hH0]
  exact (RationalPolynomial.evalDualDyadic_sound
    (preconditionedResidualExpression data row) (centerEvaluationBox data)
      (fun index ↦ (data.center index : ℝ))
      (centerEvaluationBox_contains_center data)).1

theorem preconditioner_center_correction_norm
    (data : K11KrawczykData)
    (certificate : K11KrawczykArithmeticCertificate data)
    (hH0 : ∀ row,
      (RationalPolynomial.evalDualDyadic (centerEvaluationBox data)
        (activeEquation row)).value = data.residualAtCenterCache row) :
    ‖preconditionerLinear data
      (canonicalResidual (fun index ↦ (data.center index : ℝ)))‖ ≤
        (1 - (certificate.contraction : ℝ)) * (data.radius : ℝ) := by
  rw [pi_norm_le_iff_of_nonneg]
  · intro row
    rw [Real.norm_eq_abs]
    exact RationalPolynomial.abs_le_of_dyadicContains_of_endpoints_le
      (conditionalAH0Cache data row)
      (preconditionerLinear data
        (canonicalResidual (fun index ↦ (data.center index : ℝ))) row)
      ((1 - (certificate.contraction : ℝ)) * (data.radius : ℝ))
      (conditionalAH0Cache_contains_preconditionedResidual data hH0 row)
      ((le_max_left _ _).trans (certificate.center_correction row))
      ((le_max_right _ _).trans (certificate.center_correction row))
  · exact mul_nonneg
      (sub_nonneg.mpr (le_of_lt certificate.contraction_lt_one))
      (by exact_mod_cast data.radius_nonneg)

/-- The conditional K11 checker proves a unique exact canonical zero in the
certified ball and exposes that the zero also belongs to the interval box.
The only analytic premise not checked by the finite arithmetic certificate is
the weakest one used by the zero argument: injectivity of the preconditioner. -/
theorem existsUnique_canonicalResidual_zero_in_box
    (data : K11KrawczykData)
    (certificate : K11KrawczykArithmeticCertificate data)
    (hpreconditioner : Injective (preconditionerLinear data))
    (hJ : ∀ row column,
      (RationalPolynomial.evalDualDyadic data.box
        (activeEquation row)).derivative column =
          data.jacobianBoxCache row column)
    (hH0 : ∀ row,
      (RationalPolynomial.evalDualDyadic (centerEvaluationBox data)
        (activeEquation row)).value = data.residualAtCenterCache row) :
    ∃! root,
      root ∈ closedBall (fun index ↦ (data.center index : ℝ))
          (data.radius : ℝ) ∧
        (∀ coordinate, (data.box coordinate).Contains (root coordinate)) ∧
        canonicalResidual root = 0 := by
  let center : HazardIndex → ℝ :=
    fun index ↦ (data.center index : ℝ)
  let step : (HazardIndex → ℝ) → (HazardIndex → ℝ) :=
    fun point ↦ point - preconditionerLinear data (canonicalResidual point)
  have hstep :
      (fun point row ↦ RationalPolynomial.evalReal point
        (preconditionedStepExpression data row)) = step := by
    funext point
    exact preconditionedStepExpression_evalReal data point
  have hrow : ∀ row,
      ∑ column, RationalPolynomial.dyadicAbsBound
        ((RationalPolynomial.evalDualDyadic data.box
          (preconditionedStepExpression data row)).derivative column) ≤
            (certificate.contraction : ℝ) := by
    intro row
    simpa only [preconditionedStepExpression_derivative_eq_B data hJ] using
      certificate.row_sum row
  have hlipschitz : LipschitzOnWith certificate.contraction step
      (closedBall center (data.radius : ℝ)) := by
    rw [← hstep]
    exact
      RationalPolynomial.lipschitzOnWith_evalRealVector_closedBall_of_evalDualDyadic_absRowSum
        (preconditionedStepExpression data) data.box center
        (data.radius : ℝ) certificate.contraction certificate.endpoints hrow
  obtain ⟨root, hrootBall, hrootZero⟩ :=
    RationalPolynomial.exists_zero_in_closedBall_of_evalDualDyadic_absRowSum
    canonicalResidual (preconditionerLinear data)
      (preconditionedStepExpression data) data.box
      center (data.radius : ℝ)
      certificate.contraction
      (by exact_mod_cast data.radius_nonneg)
      certificate.contraction_lt_one hpreconditioner hstep
      certificate.endpoints hrow
      (preconditioner_center_correction_norm data certificate hH0)
  have hrootBox :
      ∀ coordinate, (data.box coordinate).Contains (root coordinate) :=
    RationalPolynomial.closedBall_subset_dyadicBoxSet_of_endpoints_mem
      data.box center (data.radius : ℝ) certificate.endpoints hrootBall
  refine ⟨root, ⟨hrootBall, hrootBox, hrootZero⟩, ?_⟩
  intro other hother
  have hfixedRoot : step root = root := by
    simp [step, hrootZero]
  have hfixedOther : step other = other := by
    simp [step, hother.2.2]
  have hdistance := hlipschitz.dist_le_mul root hrootBall other hother.1
  rw [hfixedRoot, hfixedOther] at hdistance
  by_contra hne
  have hdistancePositive : 0 < dist root other :=
    dist_pos.mpr fun equality ↦ hne equality.symm
  have hstrict :
      (certificate.contraction : ℝ) * dist root other < dist root other :=
    (mul_lt_iff_lt_one_left hdistancePositive).mpr
      certificate.contraction_lt_one
  exact (not_lt_of_ge hdistance) hstrict

end GameTheory.BlockPairK11.DyadicCertificate
