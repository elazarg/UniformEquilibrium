import MathUE.Polynomial.MvPolynomialFDeriv
import Mathlib.RingTheory.Polynomial.Basic

/-! # Reflection identity for multivariate polynomials of total degree at most two

The degree is that of the actual polynomial, so coefficient cancellation is
respected. The existing affine-substitution degree bound owns the degree step.
-/

noncomputable section

namespace Math

open scoped Polynomial

variable {dimension : ℕ}

/-- Actual univariate restriction to an affine line. -/
def mvPolynomialAffineLine (polynomial : MvPolynomial (Fin dimension) ℝ)
    (point direction : Fin dimension → ℝ) : Polynomial ℝ :=
  MvPolynomial.aeval
    (fun coordinate => Polynomial.C (point coordinate) +
      Polynomial.C (direction coordinate) * Polynomial.X) polynomial

theorem eval_mvPolynomialAffineLine
    (polynomial : MvPolynomial (Fin dimension) ℝ)
    (point direction : Fin dimension → ℝ) (time : ℝ) :
    (mvPolynomialAffineLine polynomial point direction).eval time =
      MvPolynomial.eval (point + time • direction) polynomial := by
  induction polynomial using MvPolynomial.induction_on with
  | C coefficient => simp [mvPolynomialAffineLine]
  | add first second hfirst hsecond =>
      simpa [mvPolynomialAffineLine] using congrArg₂ (fun a b : ℝ => a + b) hfirst hsecond
  | mul_X polynomial coordinate hpolynomial =>
      simpa only [mvPolynomialAffineLine, map_mul, MvPolynomial.aeval_X,
        Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
        MvPolynomial.eval_mul, MvPolynomial.eval_X, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, mul_comm (direction coordinate) time] using
        congrArg (fun value => value * (point coordinate + time * direction coordinate))
          hpolynomial

theorem natDegree_mvPolynomialAffineLine_le_two
    (polynomial : MvPolynomial (Fin dimension) ℝ)
    (hdegree : polynomial.totalDegree ≤ 2)
    (point direction : Fin dimension → ℝ) :
    (mvPolynomialAffineLine polynomial point direction).natDegree ≤ 2 := by
  have hlinear : ∀ coordinate : Fin dimension,
      (Polynomial.C (point coordinate) +
        Polynomial.C (direction coordinate) * Polynomial.X).natDegree ≤ 1 := by
    intro coordinate
    apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  simpa [mvPolynomialAffineLine] using
    MvPolynomial.aeval_natDegree_le polynomial hdegree _ hlinear

/-- The one-dimensional quadratic identity needs no coefficient signs. -/
theorem polynomial_eval_two_sub_eval_zero_eq_twice_deriv_one
    (polynomial : Polynomial ℝ) (hdegree : polynomial.natDegree ≤ 2) :
    polynomial.eval 2 - polynomial.eval 0 =
      2 * deriv (fun time => polynomial.eval time) 1 := by
  have heval : ∀ time : ℝ, polynomial.eval time =
      polynomial.coeff 0 + polynomial.coeff 1 * time + polynomial.coeff 2 * time ^ 2 := by
    intro time
    rw [Polynomial.eval_eq_sum_range' (show polynomial.natDegree < 3 by omega)]
    simp [Finset.sum_range_succ]
  have hderivative : HasDerivAt (fun time : ℝ => polynomial.eval time)
      (polynomial.coeff 1 + 2 * polynomial.coeff 2) 1 := by
    have hformula : (fun time : ℝ => polynomial.eval time) =
        (fun time => polynomial.coeff 0 + polynomial.coeff 1 * time +
          polynomial.coeff 2 * time ^ 2) := funext heval
    rw [hformula]
    convert ((hasDerivAt_const (1 : ℝ) (polynomial.coeff 0)).add
      ((hasDerivAt_id (1 : ℝ)).const_mul (polynomial.coeff 1))).add
      ((hasDerivAt_pow 2 (1 : ℝ)).const_mul (polynomial.coeff 2)) using 1
    · funext time
      rfl
    · norm_num
      ring_nf
  rw [hderivative.deriv, heval 2, heval 0]
  ring

/-- Reflection about any point cancels the quadratic part in the radial
direction. The Hessian may be indefinite or degenerate. -/
theorem eval_mvPolynomial_reflection_sub_eq_twice_fderiv
    (polynomial : MvPolynomial (Fin dimension) ℝ)
    (hdegree : polynomial.totalDegree ≤ 2)
    (minimum point : Fin dimension → ℝ) :
    MvPolynomial.eval (2 • point - minimum) polynomial -
      MvPolynomial.eval minimum polynomial =
        2 * fderiv ℝ (fun input => MvPolynomial.eval input polynomial) point
          (point - minimum) := by
  let direction := point - minimum
  let line := mvPolynomialAffineLine polynomial minimum direction
  have hidentity := polynomial_eval_two_sub_eval_zero_eq_twice_deriv_one line
    (natDegree_mvPolynomialAffineLine_le_two polynomial hdegree minimum direction)
  have hline : (fun time : ℝ => line.eval time) =
      (fun time => MvPolynomial.eval (minimum + time • direction) polynomial) := by
    funext time
    exact eval_mvPolynomialAffineLine polynomial minimum direction time
  have hpath : HasDerivAt (fun time : ℝ => minimum + time • direction) direction 1 := by
    simpa using ((hasDerivAt_id (1 : ℝ)).smul_const direction).const_add minimum
  have hderivative : HasDerivAt
      (fun time : ℝ => MvPolynomial.eval (minimum + time • direction) polynomial)
      (fderiv ℝ (fun input => MvPolynomial.eval input polynomial) point direction) 1 := by
    have hpolynomialDerivative :=
      ((contDiff_eval_mvPolynomial polynomial 1).differentiable_one point).hasFDerivAt
    apply hpolynomialDerivative.comp_hasDerivAt_of_eq 1 hpath
    simp [direction]
  rw [hline, hderivative.deriv] at hidentity
  have hendpoint : minimum + (2 : ℝ) • direction = 2 • point - minimum := by
    rw [two_nsmul]
    ext coordinate
    simp only [direction, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simpa [line, eval_mvPolynomialAffineLine, hendpoint, direction] using hidentity

end Math
