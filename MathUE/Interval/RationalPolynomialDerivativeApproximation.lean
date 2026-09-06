import MathUE.Interval.PolynomialLipschitz
import MathUE.Polynomial.MvPolynomialFDeriv
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Instances.Rat

/-! # Rational coefficient approximation of an actual polynomial's derivative

Only finitely many coefficients of an already supplied real polynomial are
approximated. No approximation theorem for arbitrary smooth functions is assumed.
-/

noncomputable section

namespace Math.Interval.RationalPolynomial

open Set

variable {variableCount : ℕ}

/-- Every rational multivariate polynomial has an exact representative in the native syntax. -/
theorem exists_evalReal_eq_eval₂ (polynomial : MvPolynomial (Fin variableCount) ℚ) :
    ∃ expression : RationalPolynomial variableCount,
      ∀ point, evalReal point expression =
        MvPolynomial.eval₂ (Rat.castHom ℝ) point polynomial := by
  induction polynomial using MvPolynomial.induction_on with
  | C coefficient =>
      exact ⟨.constant coefficient, fun _ ↦ by simp [evalReal]⟩
  | add first second hfirst hsecond =>
      obtain ⟨firstExpression, hfirst⟩ := hfirst
      obtain ⟨secondExpression, hsecond⟩ := hsecond
      refine ⟨firstExpression + secondExpression, ?_⟩
      intro point
      simp [evalReal_add, MvPolynomial.eval₂_add, hfirst, hsecond]
  | mul_X polynomial index hpolynomial =>
      obtain ⟨expression, hexpression⟩ := hpolynomial
      refine ⟨expression * .var index, ?_⟩
      intro point
      simp [evalReal_mul, evalReal_var, MvPolynomial.eval₂_mul, hexpression]

private def monomialFunction (exponent : Fin variableCount →₀ ℕ) :
    (Fin variableCount → ℝ) → ℝ :=
  fun point ↦ MvPolynomial.eval point (MvPolynomial.monomial exponent (1 : ℝ))

private theorem differentiable_monomialFunction (exponent : Fin variableCount →₀ ℕ) :
    Differentiable ℝ (monomialFunction exponent) :=
  (Math.contDiff_eval_mvPolynomial (MvPolynomial.monomial exponent 1) 1).differentiable_one

private theorem continuous_fderiv_monomialFunction (exponent : Fin variableCount →₀ ℕ) :
    Continuous (fderiv ℝ (monomialFunction exponent)) :=
  (Math.contDiff_eval_mvPolynomial (MvPolynomial.monomial exponent 1) 1).continuous_fderiv
    (by norm_num)

private theorem eval_eq_sum_monomialFunction
    (polynomial : MvPolynomial (Fin variableCount) ℝ) (point : Fin variableCount → ℝ) :
    MvPolynomial.eval point polynomial =
      ∑ exponent ∈ polynomial.support,
        polynomial.coeff exponent * monomialFunction exponent point := by
  simpa [monomialFunction, MvPolynomial.eval_monomial] using
    MvPolynomial.eval_eq' point polynomial

private theorem fderiv_sum_monomialFunction
    (support : Finset (Fin variableCount →₀ ℕ))
    (coefficient : (Fin variableCount →₀ ℕ) → ℝ) (point : Fin variableCount → ℝ) :
    fderiv ℝ (fun input ↦ ∑ exponent ∈ support,
        coefficient exponent * monomialFunction exponent input) point =
      ∑ exponent ∈ support,
        coefficient exponent • fderiv ℝ (monomialFunction exponent) point := by
  rw [fderiv_fun_sum]
  · apply Finset.sum_congr rfl
    intro exponent _
    exact fderiv_const_mul (differentiable_monomialFunction exponent point) _
  · intro exponent _
    exact (differentiable_monomialFunction exponent point).const_mul _

private theorem norm_piBasisVector_le_one (coordinate : Fin variableCount) :
    ‖piBasisVector coordinate‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro index
  simp [piBasisVector]
  split_ifs <;> norm_num

/-- The summed coordinate-direction errors are bounded by dimension times operator error. -/
theorem sum_abs_apply_piBasisVector_le
    (linear : (Fin variableCount → ℝ) →L[ℝ] ℝ) :
    ∑ coordinate, |linear (piBasisVector coordinate)| ≤ variableCount * ‖linear‖ := by
  calc
    _ ≤ ∑ _coordinate : Fin variableCount, ‖linear‖ := by
      apply Finset.sum_le_sum
      intro coordinate _
      calc
        |linear (piBasisVector coordinate)| = ‖linear (piBasisVector coordinate)‖ :=
          (Real.norm_eq_abs _).symm
        _ ≤ ‖linear‖ * ‖piBasisVector coordinate‖ := linear.le_opNorm _
        _ ≤ ‖linear‖ * 1 := mul_le_mul_of_nonneg_left
          (norm_piBasisVector_le_one coordinate) (norm_nonneg _)
        _ = ‖linear‖ := mul_one _
    _ = variableCount * ‖linear‖ := by simp

/-- Perturb the finite coefficients of an actual real polynomial to rationals, uniformly in
derivative operator norm on any compact set. The compact set need not have rational coordinates. -/
theorem exists_rational_mvPolynomial_fderiv_close_on_compact
    (polynomial : MvPolynomial (Fin variableCount) ℝ)
    (domain : Set (Fin variableCount → ℝ)) (hcompact : IsCompact domain)
    {error : ℝ} (herror : 0 < error) :
    ∃ rational : MvPolynomial (Fin variableCount) ℚ,
      ∀ point ∈ domain,
        ‖fderiv ℝ (fun input ↦ MvPolynomial.eval₂ (Rat.castHom ℝ) input rational) point -
          fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point‖ < error := by
  classical
  have hbounds : ∀ exponent : Fin variableCount →₀ ℕ,
      ∃ bound : ℝ, 0 ≤ bound ∧ ∀ point ∈ domain,
        ‖fderiv ℝ (monomialFunction exponent) point‖ ≤ bound := by
    intro exponent
    obtain ⟨bound, hbound⟩ := hcompact.exists_bound_of_continuousOn
      (continuous_fderiv_monomialFunction exponent).continuousOn
    exact ⟨max 0 bound, le_max_left _ _, fun point hpoint ↦
      (hbound point hpoint).trans (le_max_right _ _)⟩
  choose bound hboundNonneg hbound using hbounds
  let totalBound : ℝ := ∑ exponent ∈ polynomial.support, bound exponent
  have htotal : 0 ≤ totalBound := Finset.sum_nonneg fun exponent _ ↦ hboundNonneg exponent
  let tolerance := error / (totalBound + 1)
  have htolerance : 0 < tolerance := div_pos herror (by positivity)
  have hcoefficients : ∀ exponent : Fin variableCount →₀ ℕ, ∃ coefficient : ℚ,
      |(coefficient : ℝ) - polynomial.coeff exponent| < tolerance := by
    intro exponent
    obtain ⟨coefficient, hlower, hupper⟩ := exists_rat_btwn
      (show polynomial.coeff exponent - tolerance < polynomial.coeff exponent + tolerance by
        linarith)
    exact ⟨coefficient, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  choose coefficient hcoefficient using hcoefficients
  let rational : MvPolynomial (Fin variableCount) ℚ :=
    ∑ exponent ∈ polynomial.support, MvPolynomial.monomial exponent (coefficient exponent)
  have hrational : (fun input ↦ MvPolynomial.eval₂ (Rat.castHom ℝ) input rational) =
      fun input ↦ ∑ exponent ∈ polynomial.support,
        (coefficient exponent : ℝ) * monomialFunction exponent input := by
    funext input
    simp [rational, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_monomial,
      monomialFunction, MvPolynomial.eval_monomial]
  have hpolynomial : (fun input ↦ MvPolynomial.eval input polynomial) =
      fun input ↦ ∑ exponent ∈ polynomial.support,
        polynomial.coeff exponent * monomialFunction exponent input := by
    funext input
    exact eval_eq_sum_monomialFunction polynomial input
  refine ⟨rational, ?_⟩
  intro point hpoint
  rw [hrational, hpolynomial, fderiv_sum_monomialFunction,
    fderiv_sum_monomialFunction, ← Finset.sum_sub_distrib]
  calc
    _ = ‖∑ exponent ∈ polynomial.support,
        ((coefficient exponent : ℝ) - polynomial.coeff exponent) •
          fderiv ℝ (monomialFunction exponent) point‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro exponent _
      exact (sub_smul _ _ _).symm
    _ ≤ ∑ exponent ∈ polynomial.support,
        ‖((coefficient exponent : ℝ) - polynomial.coeff exponent) •
          fderiv ℝ (monomialFunction exponent) point‖ := norm_sum_le _ _
    _ = ∑ exponent ∈ polynomial.support,
        |(coefficient exponent : ℝ) - polynomial.coeff exponent| *
          ‖fderiv ℝ (monomialFunction exponent) point‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ exponent ∈ polynomial.support, tolerance * bound exponent := by
      apply Finset.sum_le_sum
      intro exponent _
      exact mul_le_mul (hcoefficient exponent).le (hbound exponent point hpoint)
        (norm_nonneg _) htolerance.le
    _ = tolerance * totalBound := by rw [Finset.mul_sum]
    _ < error := by
      have heq : tolerance * (totalBound + 1) = error := by
        exact div_mul_cancel₀ error (by positivity : totalBound + 1 ≠ 0)
      nlinarith

/-- A native rational expression simultaneously approximates every coordinate derivative of a
supplied real polynomial. Both the summed directional error and operator error are retained. -/
theorem exists_evalReal_fderiv_close_on_compact
    (polynomial : MvPolynomial (Fin variableCount) ℝ)
    (domain : Set (Fin variableCount → ℝ)) (hcompact : IsCompact domain)
    {error : ℝ} (herror : 0 < error) :
    ∃ expression : RationalPolynomial variableCount,
      ∀ point ∈ domain,
        (∑ coordinate,
          |evalReal point (formalPartial coordinate expression) -
            fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point
              (piBasisVector coordinate)|) < error ∧
        ‖fderiv ℝ (fun input ↦ evalReal input expression) point -
          fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point‖ < error := by
  have hdimension : (0 : ℝ) < variableCount + 1 := by positivity
  have hscaled : 0 < error / (variableCount + 1) := div_pos herror hdimension
  obtain ⟨rational, hrational⟩ :=
    exists_rational_mvPolynomial_fderiv_close_on_compact polynomial domain hcompact hscaled
  obtain ⟨expression, hexpression⟩ := exists_evalReal_eq_eval₂ rational
  have hfunction : (fun input ↦ evalReal input expression) =
      (fun input ↦ MvPolynomial.eval₂ (Rat.castHom ℝ) input rational) := funext hexpression
  refine ⟨expression, ?_⟩
  intro point hpoint
  let difference := fderiv ℝ (fun input ↦ evalReal input expression) point -
    fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point
  have hsmall : ‖difference‖ < error / (variableCount + 1) := by
    simpa only [difference, hfunction] using hrational point hpoint
  have hscaledSmall : (variableCount + 1) * ‖difference‖ < error := by
    exact (mul_comm _ _).trans_lt ((lt_div_iff₀ hdimension).mp hsmall)
  have hsum := sum_abs_apply_piBasisVector_le difference
  have hderivative : fderiv ℝ (fun input ↦ evalReal input expression) point =
      differential point expression := (hasFDerivAt_evalReal expression point).fderiv
  have heq : (∑ coordinate,
      |evalReal point (formalPartial coordinate expression) -
        fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point
          (piBasisVector coordinate)|) =
      ∑ coordinate, |difference (piBasisVector coordinate)| := by
    simp only [difference, sub_apply, hderivative, differential_piBasisVector]
  constructor
  · rw [heq]
    exact hsum.trans_lt (by nlinarith [norm_nonneg difference])
  · change ‖difference‖ < error
    nlinarith [norm_nonneg difference, Nat.cast_nonneg (α := ℝ) variableCount]

/-- Cube specialization with an arbitrary real radius, including degenerate cubes. -/
theorem exists_evalReal_fderiv_close_on_cube
    (polynomial : MvPolynomial (Fin variableCount) ℝ) (radius : ℝ)
    {error : ℝ} (herror : 0 < error) :
    ∃ expression : RationalPolynomial variableCount,
      ∀ point, (∀ coordinate, |point coordinate| ≤ radius) →
        (∑ coordinate,
          |evalReal point (formalPartial coordinate expression) -
            fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point
              (piBasisVector coordinate)|) < error ∧
        ‖fderiv ℝ (fun input ↦ evalReal input expression) point -
          fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point‖ < error := by
  have hcompact : IsCompact {point : Fin variableCount → ℝ |
      ∀ coordinate, |point coordinate| ≤ radius} := by
    have hproduct := isCompact_univ_pi (ι := Fin variableCount)
      (fun _ ↦ (isCompact_Icc : IsCompact (Icc (-radius) radius)))
    convert hproduct using 1
    ext point
    simp only [mem_setOf_eq, mem_pi, mem_univ, true_implies, mem_Icc, abs_le]
  exact exists_evalReal_fderiv_close_on_compact polynomial _ hcompact herror

end Math.Interval.RationalPolynomial
