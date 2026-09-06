import MathUE.Polynomial.PolynomialDerivativeApproximation
import MathUE.Interval.RationalPolynomialDerivativeApproximation

/-! # Rational polynomial derivative approximation for actual C¹ functions

The real polynomial is produced by tensor Bernstein approximation and affine transport.
Only then are its finitely many coefficients perturbed to rationals. No function-value
approximation is asserted.
-/

noncomputable section

namespace Math.Interval.RationalPolynomial

open Set
open scoped BigOperators

variable {dimension : ℕ}

/-- A single native rational polynomial approximates every coordinate derivative and the
derivative operator of a C¹ function, uniformly on an arbitrary compact real set. -/
theorem exists_evalReal_fderiv_close_of_contDiff_on_compact
    (function : (Fin dimension → ℝ) → ℝ) (hsmooth : ContDiff ℝ 1 function)
    (domain : Set (Fin dimension → ℝ)) (hcompact : IsCompact domain)
    {error : ℝ} (herror : 0 < error) :
    ∃ expression : RationalPolynomial dimension, ∀ point ∈ domain,
      (∑ coordinate, |evalReal point (formalPartial coordinate expression) -
        fderiv ℝ function point (piBasisVector coordinate)|) < error ∧
      ‖fderiv ℝ (fun input ↦ evalReal input expression) point -
        fderiv ℝ function point‖ < error := by
  obtain ⟨polynomial, hpolynomial⟩ := Math.exists_mvPolynomial_fderiv_close_on_bounded
    function hsmooth domain hcompact.isBounded (half_pos herror)
  obtain ⟨expression, hexpression⟩ := exists_evalReal_fderiv_close_on_compact
    polynomial domain hcompact (half_pos herror)
  have hbasis (coordinate : Fin dimension) :
      piBasisVector coordinate = Pi.single coordinate (1 : ℝ) := by
    ext index
    simp [piBasisVector, Pi.single_apply, eq_comm]
  refine ⟨expression, ?_⟩
  intro point hpoint
  obtain ⟨hrealSum, hrealNorm⟩ := hpolynomial point hpoint
  obtain ⟨hrationalSum, hrationalNorm⟩ := hexpression point hpoint
  constructor
  · have htriangle : (∑ coordinate,
        |evalReal point (formalPartial coordinate expression) -
          fderiv ℝ function point (piBasisVector coordinate)|) ≤
        (∑ coordinate, |evalReal point (formalPartial coordinate expression) -
          fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point
            (piBasisVector coordinate)|) +
        ∑ coordinate, |fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point
            (Pi.single coordinate 1) - fderiv ℝ function point (Pi.single coordinate 1)| := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro coordinate _
      simpa only [hbasis] using abs_sub_le
        (evalReal point (formalPartial coordinate expression))
        (fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point
          (piBasisVector coordinate))
        (fderiv ℝ function point (piBasisVector coordinate))
    linarith
  · have htriangle := dist_triangle
      (fderiv ℝ (fun input ↦ evalReal input expression) point)
      (fderiv ℝ (fun input ↦ MvPolynomial.eval input polynomial) point)
      (fderiv ℝ function point)
    simp only [dist_eq_norm] at htriangle
    linarith

/-- The coordinate box may have arbitrary real endpoints, zero widths, or be empty. -/
theorem exists_evalReal_fderiv_close_of_contDiff_on_box
    (function : (Fin dimension → ℝ) → ℝ) (hsmooth : ContDiff ℝ 1 function)
    (lower upper : Fin dimension → ℝ) {error : ℝ} (herror : 0 < error) :
    ∃ expression : RationalPolynomial dimension, ∀ point ∈ Icc lower upper,
      (∑ coordinate, |evalReal point (formalPartial coordinate expression) -
        fderiv ℝ function point (piBasisVector coordinate)|) < error ∧
      ‖fderiv ℝ (fun input ↦ evalReal input expression) point -
        fderiv ℝ function point‖ < error :=
  exists_evalReal_fderiv_close_of_contDiff_on_compact function hsmooth (Icc lower upper)
    isCompact_Icc herror

end Math.Interval.RationalPolynomial
