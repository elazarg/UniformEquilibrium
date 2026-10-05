import MathUE.Interval.RationalPolynomial

/-! # Executable rational evaluation of the actual candidate expression -/

namespace Math.Interval.RationalPolynomial

variable {dimension : ℕ}

/-- Exact rational arithmetic evaluation; normalization is not needed at runtime. -/
def evalRat (point : Fin dimension → ℚ) : RationalPolynomial dimension → ℚ
  | .constant value => value
  | .var index => point index
  | .add first second => evalRat point first + evalRat point second
  | .neg expression => -evalRat point expression
  | .mul first second => evalRat point first * evalRat point second

theorem ratCast_evalRat (expression : RationalPolynomial dimension)
    (point : Fin dimension → ℚ) :
    (evalRat point expression : ℝ) = evalReal (fun who => (point who : ℝ)) expression := by
  induction expression with
  | constant value => rfl
  | var index => rfl
  | add first second hfirst hsecond => simp [evalRat, evalReal, hfirst, hsecond]
  | neg expression hexpression => simp [evalRat, evalReal, hexpression]
  | mul first second hfirst hsecond => simp [evalRat, evalReal, hfirst, hsecond]

end Math.Interval.RationalPolynomial
