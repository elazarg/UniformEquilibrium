import Research.Quitting.BlockPair.K11.KrawczykConditionalData

namespace GameTheory.BlockPairK11.DyadicCertificate

open Math.Interval

theorem evalDualDyadic_expressionSum_derivative {count : ℕ}
    (term : Fin count → Expression) (coordinate : HazardIndex) :
    (RationalPolynomial.evalDualDyadic box
      (expressionSum term)).derivative coordinate =
      intervalSum (fun index ↦
        (RationalPolynomial.evalDualDyadic box
          (term index)).derivative coordinate) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [expressionSum, intervalSum,
        RationalPolynomial.evalDualDyadic, RationalPolynomial.DyadicDual.add]
      rw [ih]

theorem evalDualDyadic_constant_mul_derivative
    (coefficient : ℚ) (expression : Expression)
    (coordinate : HazardIndex) :
    (RationalPolynomial.evalDualDyadic box
      (.constant coefficient * expression)).derivative coordinate =
      (DyadicInterval.ofRat coefficient).mul
        ((RationalPolynomial.evalDualDyadic box expression).derivative
          coordinate) := by
  simp [RationalPolynomial.evalDualDyadic,
    RationalPolynomial.DyadicDual.mul,
    RationalPolynomial.DyadicDual.constant]

theorem preconditionedResidualExpression_derivative_eq_AJ
    (hJ : ∀ row column,
      (RationalPolynomial.evalDualDyadic box
        (activeEquation row)).derivative column =
          (jacobianBoxCache.get row).get column)
    (row column : HazardIndex) :
    (RationalPolynomial.evalDualDyadic box
      (preconditionedResidualExpression row)).derivative column =
        conditionalAJCache row column := by
  rw [preconditionedResidualExpression,
    evalDualDyadic_expressionSum_derivative]
  unfold conditionalAJCache
  apply congrArg intervalSum
  funext equation
  rw [evalDualDyadic_constant_mul_derivative, hJ]

theorem preconditionedStepExpression_derivative_eq_B
    (hJ : ∀ row column,
      (RationalPolynomial.evalDualDyadic box
        (activeEquation row)).derivative column =
          (jacobianBoxCache.get row).get column)
    (row column : HazardIndex) :
    (RationalPolynomial.evalDualDyadic box
      (preconditionedStepExpression row)).derivative column =
        conditionalBCache row column := by
  unfold preconditionedStepExpression conditionalBCache
  simp only [HSub.hSub, Sub.sub, RationalPolynomial.evalDualDyadic,
    RationalPolynomial.DyadicDual.add,
    RationalPolynomial.DyadicDual.neg,
    RationalPolynomial.DyadicDual.ofVariable]
  rw [preconditionedResidualExpression_derivative_eq_AJ hJ]
  congr 1
  by_cases h : row = column
  · simp [h]
  · have h' : column ≠ row := fun equality ↦ h equality.symm
    simp [h, h']

theorem evalDualDyadic_expressionSum_value_center {count : ℕ}
    (term : Fin count → Expression) :
    (RationalPolynomial.evalDualDyadic centerEvaluationBox
      (expressionSum term)).value =
      intervalSum (fun index ↦
        (RationalPolynomial.evalDualDyadic centerEvaluationBox
          (term index)).value) := by
  induction count with
  | zero =>
      simp [expressionSum, intervalSum,
        RationalPolynomial.evalDualDyadic,
        RationalPolynomial.DyadicDual.constant]
  | succ count ih =>
      simp only [expressionSum, intervalSum,
        RationalPolynomial.evalDualDyadic, RationalPolynomial.DyadicDual.add]
      rw [ih]

theorem evalDualDyadic_constant_mul_value_center
    (coefficient : ℚ) (expression : Expression) :
    (RationalPolynomial.evalDualDyadic centerEvaluationBox
      (.constant coefficient * expression)).value =
      (DyadicInterval.ofRat coefficient).mul
        ((RationalPolynomial.evalDualDyadic centerEvaluationBox
          expression).value) := by
  rfl

theorem preconditionedResidualExpression_value_center_eq_AH0
    (hH0 : ∀ row,
      (RationalPolynomial.evalDualDyadic centerEvaluationBox
        (activeEquation row)).value = residualAtCenterCache.get row)
    (row : HazardIndex) :
    (RationalPolynomial.evalDualDyadic centerEvaluationBox
      (preconditionedResidualExpression row)).value =
        conditionalAH0Cache row := by
  rw [preconditionedResidualExpression,
    evalDualDyadic_expressionSum_value_center]
  unfold conditionalAH0Cache
  apply congrArg intervalSum
  funext equation
  rw [evalDualDyadic_constant_mul_value_center, hH0]

end GameTheory.BlockPairK11.DyadicCertificate
