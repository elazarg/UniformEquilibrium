import MathUE.Analysis.CoordinateAffineBoxMinimum
import MathUE.Polynomial.MvPolynomialFDeriv
import MathUE.Interval.RationalPolynomialL1
import Mathlib.Algebra.Polynomial.BigOperators

/-! # Coordinate affinity of actual square-free multivariate polynomials

Individual degree is measured on the normalized polynomial after cancellation.
No restriction on total degree or on higher-coordinate interactions is imposed.
-/

noncomputable section

namespace Math

variable {dimension : ℕ}

/-- Multi-affinity is the actual individual degree bound, after cancellation. -/
def IsMultiAffineMvPolynomial (polynomial : MvPolynomial (Fin dimension) ℝ) : Prop :=
  ∀ coordinate, polynomial.degreeOf coordinate ≤ 1

private def mvPolynomialCoordinateLine (polynomial : MvPolynomial (Fin dimension) ℝ)
    (point : Fin dimension → ℝ) (coordinate : Fin dimension) : Polynomial ℝ :=
  MvPolynomial.aeval (fun axis => if axis = coordinate then Polynomial.X else
    Polynomial.C (point axis)) polynomial

private theorem eval_mvPolynomialCoordinateLine
    (polynomial : MvPolynomial (Fin dimension) ℝ)
    (point : Fin dimension → ℝ) (coordinate : Fin dimension) (value : ℝ) :
    (mvPolynomialCoordinateLine polynomial point coordinate).eval value =
      MvPolynomial.eval (Function.update point coordinate value) polynomial := by
  induction polynomial using MvPolynomial.induction_on with
  | C coefficient => simp [mvPolynomialCoordinateLine]
  | add first second hfirst hsecond =>
      simpa [mvPolynomialCoordinateLine] using
        congrArg₂ (fun a b : ℝ => a + b) hfirst hsecond
  | mul_X polynomial axis hpolynomial =>
      by_cases heq : axis = coordinate
      · subst axis
        simpa [mvPolynomialCoordinateLine] using congrArg (fun result => result * value)
          hpolynomial
      · simpa [mvPolynomialCoordinateLine, heq] using
          congrArg (fun result => result * point axis) hpolynomial

private theorem natDegree_mvPolynomialCoordinateLine_le_one
    (polynomial : MvPolynomial (Fin dimension) ℝ)
    (coordinate : Fin dimension) (hdegree : polynomial.degreeOf coordinate ≤ 1)
    (point : Fin dimension → ℝ) :
    (mvPolynomialCoordinateLine polynomial point coordinate).natDegree ≤ 1 := by
  rw [mvPolynomialCoordinateLine, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro exponent hexponent
  simp only [← Polynomial.C_eq_algebraMap]
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply (Polynomial.natDegree_prod_le _ _).trans
  have hsum : (∑ axis ∈ exponent.support,
      ((if axis = coordinate then Polynomial.X else Polynomial.C (point axis)) ^
        exponent axis).natDegree) ≤
      ∑ axis ∈ exponent.support, if axis = coordinate then exponent axis else 0 := by
    apply Finset.sum_le_sum
    intro axis _
    by_cases heq : axis = coordinate
    · simp [heq]
    · simp [heq]
  apply hsum.trans
  simp only [Finset.sum_ite_eq']
  split_ifs with hmem
  · exact (MvPolynomial.degreeOf_le_iff.mp hdegree) exponent hexponent
  · exact Nat.zero_le _

/-- The actual individual-degree bound produces an affine function on every
coordinate line, including all high-order square-free interaction terms. -/
theorem isCoordinateAffine_eval_mvPolynomial
    (polynomial : MvPolynomial (Fin dimension) ℝ)
    (haffine : IsMultiAffineMvPolynomial polynomial) :
    IsCoordinateAffine (fun point => MvPolynomial.eval point polynomial) := by
  intro point coordinate
  let line := mvPolynomialCoordinateLine polynomial point coordinate
  have hdegree : line.natDegree ≤ 1 := natDegree_mvPolynomialCoordinateLine_le_one
    polynomial coordinate (haffine coordinate) point
  refine ⟨line.coeff 0, line.coeff 1, fun value => ?_⟩
  change MvPolynomial.eval (Function.update point coordinate value) polynomial =
    line.coeff 0 + line.coeff 1 * value
  rw [← eval_mvPolynomialCoordinateLine polynomial point coordinate value]
  change line.eval value = _
  rw [Polynomial.eval_eq_sum_range' (show line.natDegree < 2 by omega)]
  simp [Finset.sum_range_succ]

/-- The rational facade checks degrees after actual syntax normalization. -/
theorem isCoordinateAffine_evalReal_of_degreeOf_le_one
    (expression : Math.Interval.RationalPolynomial dimension)
    (haffine : ∀ coordinate, expression.toMvPolynomial.degreeOf coordinate ≤ 1) :
    IsCoordinateAffine
      (fun point => Math.Interval.RationalPolynomial.evalReal point expression) := by
  let polynomial := MvPolynomial.map (Rat.castHom ℝ) expression.toMvPolynomial
  have hreal : IsMultiAffineMvPolynomial polynomial := by
    intro coordinate
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro exponent hexponent
    exact (MvPolynomial.degreeOf_le_iff.mp (haffine coordinate)) exponent
      (MvPolynomial.support_map_subset (Rat.castHom ℝ) expression.toMvPolynomial hexponent)
  have hevaluation : (fun point => Math.Interval.RationalPolynomial.evalReal point expression) =
      (fun point => MvPolynomial.eval point polynomial) := by
    funext point
    rw [Math.Interval.RationalPolynomial.evalReal_eq_eval₂_toMvPolynomial,
      MvPolynomial.eval₂_eq_eval_map]
  rw [hevaluation]
  exact isCoordinateAffine_eval_mvPolynomial polynomial hreal

end Math
