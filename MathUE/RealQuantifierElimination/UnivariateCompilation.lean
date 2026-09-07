import MathUE.Polynomial.DensePolynomial
import MathUE.RealQuantifierElimination.PolynomialEvaluation

/-!
# Compile one ring-expression variable to a dense polynomial

Variable zero becomes the univariate indeterminate.  Every successor variable
becomes a constant coefficient expression in the remaining parameter
variables.  The compiler itself performs no semantic equality test.
-/

namespace MathUE.RealQuantifierElimination

namespace RingExpression

open Math.DensePolynomial

/-- Compile an expression in one bound variable and `n` shifted parameters to
an ascending dense polynomial whose coefficients are expressions in only the
parameters. -/
def toUnivariateDense : RingExpression (n + 1) → Math.DensePolynomial (RingExpression n)
  | .const value => [.const value]
  | .var index => Fin.cases [0, 1] (fun parameter => [.var parameter]) index
  | .neg expression => (toUnivariateDense expression).neg
  | .add left right => (toUnivariateDense left).add (toUnivariateDense right)
  | .mul left right => (toUnivariateDense left).mul (toUnivariateDense right)

@[simp]
theorem toUnivariateDense_const (value : ℚ) :
    toUnivariateDense (n := n) (.const value) = [.const value] :=
  rfl

@[simp]
theorem toUnivariateDense_var_zero :
    toUnivariateDense (.var (0 : Fin (n + 1))) = [0, 1] :=
  rfl

@[simp]
theorem toUnivariateDense_var_succ (parameter : Fin n) :
    toUnivariateDense (.var parameter.succ) = [.var parameter] :=
  rfl

@[simp]
theorem toUnivariateDense_neg (expression : RingExpression (n + 1)) :
    toUnivariateDense (-expression) = (toUnivariateDense expression).neg :=
  rfl

@[simp]
theorem toUnivariateDense_add (left right : RingExpression (n + 1)) :
    toUnivariateDense (left + right) =
      (toUnivariateDense left).add (toUnivariateDense right) :=
  rfl

@[simp]
theorem toUnivariateDense_mul (left right : RingExpression (n + 1)) :
    toUnivariateDense (left * right) =
      (toUnivariateDense left).mul (toUnivariateDense right) :=
  rfl

/-- Correctness against any coefficient evaluator that agrees with real
ring-expression evaluation at the parameter environment. -/
theorem evalMap_toUnivariateDense_of_apply_eq
    (coefficientEvaluator :
      Math.DensePolynomial.Evaluator (RingExpression n) ℝ)
    (parameters : Fin n → ℝ)
    (hcoefficient : ∀ coefficient, coefficientEvaluator coefficient =
      coefficient.evalReal parameters)
    (boundValue : ℝ) (expression : RingExpression (n + 1)) :
    Math.DensePolynomial.evalMap coefficientEvaluator
        expression.toUnivariateDense boundValue =
      expression.evalReal (Fin.cases boundValue parameters) := by
  induction expression with
  | const value =>
      rw [toUnivariateDense_const, evalMap_cons, evalMap_nil, mul_zero, add_zero,
        hcoefficient]
      rfl
  | var index =>
      refine Fin.cases ?_ (fun parameter => ?_) index
      · rw [toUnivariateDense_var_zero, evalMap_cons, evalMap_cons, evalMap_nil,
          Evaluator.apply_zero, Evaluator.apply_one]
        simp
      · rw [toUnivariateDense_var_succ, evalMap_cons, evalMap_nil, mul_zero, add_zero,
          hcoefficient]
        rfl
  | neg expression ih =>
      rw [toUnivariateDense, evalMap_neg]
      change -Math.DensePolynomial.evalMap coefficientEvaluator
          expression.toUnivariateDense boundValue =
        -expression.evalReal (Fin.cases boundValue parameters)
      rw [ih]
  | add left right ihLeft ihRight =>
      rw [toUnivariateDense, evalMap_add]
      change Math.DensePolynomial.evalMap coefficientEvaluator
            left.toUnivariateDense boundValue +
          Math.DensePolynomial.evalMap coefficientEvaluator
            right.toUnivariateDense boundValue =
        left.evalReal (Fin.cases boundValue parameters) +
          right.evalReal (Fin.cases boundValue parameters)
      rw [ihLeft, ihRight]
  | mul left right ihLeft ihRight =>
      rw [toUnivariateDense, evalMap_mul]
      change Math.DensePolynomial.evalMap coefficientEvaluator
            left.toUnivariateDense boundValue *
          Math.DensePolynomial.evalMap coefficientEvaluator
            right.toUnivariateDense boundValue =
        left.evalReal (Fin.cases boundValue parameters) *
          right.evalReal (Fin.cases boundValue parameters)
      rw [ihLeft, ihRight]

/-- The compiled dense polynomial evaluates exactly as the source expression
at the environment obtained by placing the bound value at variable zero and
the parameter environment at successor variables. -/
theorem evalMap_toUnivariateDense
    (parameters : Fin n → ℝ) (boundValue : ℝ)
    (expression : RingExpression (n + 1)) :
    Math.DensePolynomial.evalMap (realEvaluator parameters)
        expression.toUnivariateDense boundValue =
      expression.evalReal (Fin.cases boundValue parameters) := by
  exact evalMap_toUnivariateDense_of_apply_eq (realEvaluator parameters)
    parameters (realEvaluator_apply parameters) boundValue expression

/-- The proof-level Mathlib polynomial interpretation has the same evaluation;
this is the direct bridge to real sign-cell geometry. -/
theorem toPolynomial_toUnivariateDense_eval
    (parameters : Fin n → ℝ) (boundValue : ℝ)
    (expression : RingExpression (n + 1)) :
    (Math.DensePolynomial.toPolynomial (realEvaluator parameters)
      expression.toUnivariateDense).eval boundValue =
      expression.evalReal (Fin.cases boundValue parameters) := by
  rw [Math.DensePolynomial.toPolynomial_eval, evalMap_toUnivariateDense]

end RingExpression

end MathUE.RealQuantifierElimination
