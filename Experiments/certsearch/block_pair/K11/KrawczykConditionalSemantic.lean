import Experiments.certsearch.block_pair.K11.KrawczykConditionalData

namespace GameTheory.BlockPairK11.DyadicCertificate

open Math.Interval

theorem evalDualDyadic_expressionSum_derivative
    {precision count : ℕ}
    (box : HazardIndex → DyadicInterval precision)
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
    {precision : ℕ}
    (box : HazardIndex → DyadicInterval precision)
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
    (data : K11KrawczykData)
    (hJ : ∀ row column,
      (RationalPolynomial.evalDualDyadic data.box
        (activeEquation row)).derivative column =
          data.jacobianBoxCache row column)
    (row column : HazardIndex) :
    (RationalPolynomial.evalDualDyadic data.box
      (preconditionedResidualExpression data row)).derivative column =
        conditionalAJCache data row column := by
  rw [preconditionedResidualExpression,
    evalDualDyadic_expressionSum_derivative]
  unfold conditionalAJCache
  apply congrArg intervalSum
  funext equation
  rw [evalDualDyadic_constant_mul_derivative, hJ]

theorem preconditionedStepExpression_derivative_eq_B
    (data : K11KrawczykData)
    (hJ : ∀ row column,
      (RationalPolynomial.evalDualDyadic data.box
        (activeEquation row)).derivative column =
          data.jacobianBoxCache row column)
    (row column : HazardIndex) :
    (RationalPolynomial.evalDualDyadic data.box
      (preconditionedStepExpression data row)).derivative column =
        conditionalBCache data row column := by
  unfold preconditionedStepExpression conditionalBCache
  simp only [HSub.hSub, Sub.sub, RationalPolynomial.evalDualDyadic,
    RationalPolynomial.DyadicDual.add,
    RationalPolynomial.DyadicDual.neg,
    RationalPolynomial.DyadicDual.ofVariable]
  rw [preconditionedResidualExpression_derivative_eq_AJ data hJ]
  congr 1
  by_cases h : row = column
  · simp [h]
  · have h' : column ≠ row := fun equality ↦ h equality.symm
    simp [h, h']

theorem evalDualDyadic_expressionSum_value_center
    {precision count : ℕ}
    (box : HazardIndex → DyadicInterval precision)
    (term : Fin count → Expression) :
    (RationalPolynomial.evalDualDyadic box
      (expressionSum term)).value =
      intervalSum (fun index ↦
        (RationalPolynomial.evalDualDyadic box (term index)).value) := by
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
    {precision : ℕ}
    (box : HazardIndex → DyadicInterval precision)
    (coefficient : ℚ) (expression : Expression) :
    (RationalPolynomial.evalDualDyadic box
      (.constant coefficient * expression)).value =
      (DyadicInterval.ofRat coefficient).mul
        ((RationalPolynomial.evalDualDyadic box expression).value) := by
  rfl

theorem preconditionedResidualExpression_value_center_eq_AH0
    (data : K11KrawczykData)
    (hH0 : ∀ row,
      (RationalPolynomial.evalDualDyadic (centerEvaluationBox data)
        (activeEquation row)).value = data.residualAtCenterCache row)
    (row : HazardIndex) :
    (RationalPolynomial.evalDualDyadic (centerEvaluationBox data)
      (preconditionedResidualExpression data row)).value =
        conditionalAH0Cache data row := by
  rw [preconditionedResidualExpression,
    evalDualDyadic_expressionSum_value_center]
  unfold conditionalAH0Cache
  apply congrArg intervalSum
  funext equation
  rw [evalDualDyadic_constant_mul_value_center, hH0]

end GameTheory.BlockPairK11.DyadicCertificate
