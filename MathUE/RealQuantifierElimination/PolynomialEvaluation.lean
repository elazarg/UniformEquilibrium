import MathUE.RealQuantifierElimination.RingExpression
import MathUE.Polynomial.DensePolynomial

/-! Operation-preserving interpretation of polynomial coefficient expressions. -/

namespace MathUE.RealQuantifierElimination

namespace RingExpression

variable {n : Nat}

/-- Operation-preserving evaluation of coefficient expressions into the reals. -/
noncomputable def realEvaluator (environment : Fin n → ℝ) :
    Math.DensePolynomial.Evaluator (RingExpression n) ℝ where
  toFun := evalReal environment
  map_zero := by simp [evalReal, eval]
  map_one := by simp [evalReal, eval]
  map_add _ _ := rfl
  map_neg _ := rfl
  map_mul _ _ := rfl

@[simp]
theorem realEvaluator_apply
    (environment : Fin n → ℝ) (expression : RingExpression n) :
    realEvaluator environment expression = expression.evalReal environment :=
  rfl

end RingExpression

end MathUE.RealQuantifierElimination
