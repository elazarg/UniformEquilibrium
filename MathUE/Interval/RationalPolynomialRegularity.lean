import MathUE.Interval.RationalPolynomialL1
import MathUE.Polynomial.MvPolynomialFDeriv

/-! # Smoothness of actual reflected rational-polynomial evaluation

Regularity is delegated to the existing normalized multivariate polynomial
and its canonical smoothness theorem, rather than reproved on syntax trees.
-/

noncomputable section

namespace Math.Interval.RationalPolynomial

variable {dimension : ℕ}

/-- Every actual rational expression evaluates to a real function smooth at
every order, including after arbitrary coefficient cancellation. -/
theorem contDiff_evalReal (expression : RationalPolynomial dimension)
    (order : WithTop ℕ∞) :
    ContDiff ℝ order (fun point => evalReal point expression) := by
  let polynomial := MvPolynomial.map (Rat.castHom ℝ) expression.toMvPolynomial
  have hevaluation : (fun point => evalReal point expression) =
      (fun point => MvPolynomial.eval point polynomial) := by
    funext point
    rw [evalReal_eq_eval₂_toMvPolynomial, MvPolynomial.eval₂_eq_eval_map]
  rw [hevaluation]
  exact Math.contDiff_eval_mvPolynomial polynomial order

end Math.Interval.RationalPolynomial
