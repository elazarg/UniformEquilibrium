import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # Actual derivatives of real multivariate polynomials -/

noncomputable section

namespace Math

variable {dimension : ℕ}

/-- Formal partial derivatives agree with the actual derivatives along coordinate lines. -/
theorem hasDerivAt_eval_mvPolynomial_update (polynomial : MvPolynomial (Fin dimension) ℝ)
    (point : Fin dimension → ℝ) (coordinate : Fin dimension) :
    HasDerivAt (fun value ↦ MvPolynomial.eval (Function.update point coordinate value) polynomial)
      (MvPolynomial.eval point (MvPolynomial.pderiv coordinate polynomial)) (point coordinate) := by
  classical
  induction polynomial using MvPolynomial.induction_on with
  | C coefficient =>
      simpa using hasDerivAt_const (point coordinate) coefficient
  | add first second hfirst hsecond =>
      simpa using! hfirst.add hsecond
  | mul_X polynomial axis hpolynomial =>
      by_cases haxis : axis = coordinate
      · subst axis
        simpa [MvPolynomial.pderiv_mul, add_comm, mul_comm] using!
          hpolynomial.mul (hasDerivAt_id (point coordinate))
      · simpa [MvPolynomial.pderiv_mul, Function.update_of_ne haxis,
          MvPolynomial.pderiv_X_of_ne haxis, mul_comm] using!
          hpolynomial.mul_const (point axis)

/-- Evaluation of an actual multivariate real polynomial is smooth of every order. -/
theorem contDiff_eval_mvPolynomial (polynomial : MvPolynomial (Fin dimension) ℝ)
    (order : WithTop ℕ∞) : ContDiff ℝ order (fun point ↦ MvPolynomial.eval point polynomial) := by
  induction polynomial using MvPolynomial.induction_on with
  | C coefficient => simpa using contDiff_const (c := coefficient)
  | add first second hfirst hsecond => simpa using hfirst.add hsecond
  | mul_X polynomial coordinate hpolynomial =>
      simpa using hpolynomial.mul (contDiff_apply ℝ ℝ coordinate)

/-- Formal partial evaluation is the actual Fréchet derivative on a coordinate vector. -/
theorem fderiv_eval_mvPolynomial_apply_single (polynomial : MvPolynomial (Fin dimension) ℝ)
    (point : Fin dimension → ℝ) (coordinate : Fin dimension) :
    fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point (Pi.single coordinate 1) =
      MvPolynomial.eval point (MvPolynomial.pderiv coordinate polynomial) := by
  have hderivative :=
    ((contDiff_eval_mvPolynomial polynomial 1).differentiable_one point).hasFDerivAt
  have hderivative' : HasFDerivAt (fun input ↦ MvPolynomial.eval input polynomial)
      (fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point)
      (Function.update point coordinate (point coordinate)) := by simpa using hderivative
  have hline := hderivative'.comp_hasDerivAt (point coordinate)
    (hasDerivAt_update point coordinate (point coordinate))
  simpa only [Function.update_eq_self] using
    hline.unique (hasDerivAt_eval_mvPolynomial_update polynomial point coordinate)

end Math
