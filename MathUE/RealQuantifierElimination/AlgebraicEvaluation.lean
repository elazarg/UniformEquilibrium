import MathUE.Polynomial.AlgebraicRoot
import MathUE.RealQuantifierElimination.PolynomialEvaluation
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Algebra.Algebra.Rat

/-! # Algebraicity of rational expression and coefficient evaluation -/

namespace MathUE.RealQuantifierElimination

namespace RingExpression

/-- A rational ring expression evaluated at algebraic real coordinates is
again algebraic over the rationals. -/
theorem isAlgebraic_evalReal (environment : Fin n → ℝ)
    (henvironment : ∀ index, IsAlgebraic ℚ (environment index))
    (expression : RingExpression n) :
    IsAlgebraic ℚ (expression.evalReal environment) := by
  induction expression with
  | const value =>
      exact isAlgebraic_rat ℚ value
  | var index =>
      exact henvironment index
  | neg expression ih =>
      exact ih.neg
  | add left right ihLeft ihRight =>
      exact ihLeft.add ihRight
  | mul left right ihLeft ihRight =>
      exact ihLeft.mul ihRight

end RingExpression

end MathUE.RealQuantifierElimination

namespace Math.DensePolynomial

open MathUE.RealQuantifierElimination

/-- Every coefficient of a dense polynomial specialized at algebraic real
parameters is algebraic over the rationals. -/
theorem toPolynomial_realEvaluator_coeff_isAlgebraic
    (environment : Fin n → ℝ)
    (henvironment : ∀ index, IsAlgebraic ℚ (environment index))
    (polynomial : Math.DensePolynomial (RingExpression n)) (degree : ℕ) :
    IsAlgebraic ℚ
      ((toPolynomial (RingExpression.realEvaluator environment) polynomial).coeff degree) := by
  rw [toPolynomial_coeff, RingExpression.realEvaluator_apply]
  exact RingExpression.isAlgebraic_evalReal environment henvironment _

end Math.DensePolynomial
