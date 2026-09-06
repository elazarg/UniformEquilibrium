import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # Algebraic tensor Bernstein polynomials

These exact finite identities do not assert approximation of a smooth function.
-/

noncomputable section

namespace Math

open scoped BigOperators

section Univariate

variable {R : Type*} [CommRing R]

/-- A Bernstein polynomial with a supplied coefficient at each grid index. -/
def bernsteinCoefficientPolynomial (degree : ℕ) (coefficient : ℕ → R) : Polynomial R :=
  ∑ index ∈ Finset.range (degree + 1),
    Polynomial.C (coefficient index) * bernsteinPolynomial R degree index

/-- Differentiation replaces coefficients by consecutive differences. -/
theorem derivative_bernsteinCoefficientPolynomial (degree : ℕ) (coefficient : ℕ → R) :
    Polynomial.derivative (bernsteinCoefficientPolynomial (degree + 1) coefficient) =
      (degree + 1 : Polynomial R) *
        bernsteinCoefficientPolynomial degree (fun index ↦
          coefficient (index + 1) - coefficient index) := by
  have hshift :
      (∑ index ∈ Finset.range (degree + 1),
        Polynomial.C (coefficient (index + 1)) *
          bernsteinPolynomial R degree (index + 1)) =
      (∑ index ∈ Finset.range (degree + 1),
        Polynomial.C (coefficient index) * bernsteinPolynomial R degree index) -
        Polynomial.C (coefficient 0) * bernsteinPolynomial R degree 0 := by
    have h := Finset.sum_range_succ'
      (fun index ↦ Polynomial.C (coefficient index) * bernsteinPolynomial R degree index)
      (degree + 1)
    rw [Finset.sum_range_succ] at h
    simp only [bernsteinPolynomial.eq_zero_of_lt R (Nat.lt_succ_self degree),
      mul_zero, add_zero] at h
    exact eq_sub_of_add_eq h.symm
  unfold bernsteinCoefficientPolynomial
  rw [Finset.sum_range_succ']
  simp only [map_add, map_sum, Polynomial.derivative_C_mul,
    bernsteinPolynomial.derivative_succ_aux, bernsteinPolynomial.derivative_zero,
    Nat.add_sub_cancel]
  simp only [mul_sub, Finset.sum_sub_distrib]
  simp only [mul_left_comm (Polynomial.C _) (degree + 1 : Polynomial R),
    ← Finset.mul_sum, map_sub, sub_mul, Finset.sum_sub_distrib, Nat.cast_add, Nat.cast_one]
  rw [hshift]
  ring

end Univariate

section Tensor

variable {dimension : ℕ}

/-- The finite grid index type; each coordinate may have its own degree. -/
abbrev BernsteinGridIndex (degree : Fin dimension → ℕ) :=
  (coordinate : Fin dimension) → Fin (degree coordinate + 1)

/-- The canonical real grid point, with the degree-zero convention `0 / 0 = 0`. -/
def bernsteinGridPoint (degree : Fin dimension → ℕ) (index : BernsteinGridIndex degree) :
    Fin dimension → ℝ :=
  fun coordinate ↦ (index coordinate : ℝ) / degree coordinate

/-- A genuine multivariate polynomial obtained by tensoring univariate Bernstein factors. -/
def tensorBernsteinBasis (degree : Fin dimension → ℕ) (index : BernsteinGridIndex degree) :
    MvPolynomial (Fin dimension) ℝ :=
  ∏ coordinate, Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X coordinate)
    (bernsteinPolynomial ℝ (degree coordinate) (index coordinate))

/-- The real tensor weight at a point. -/
def tensorBernsteinWeight (degree : Fin dimension → ℕ) (index : BernsteinGridIndex degree)
    (point : Fin dimension → ℝ) : ℝ :=
  ∏ coordinate,
    (bernsteinPolynomial ℝ (degree coordinate) (index coordinate)).eval (point coordinate)

/-- An actual multivariate polynomial with arbitrary supplied grid coefficients. -/
def tensorBernsteinPolynomial (degree : Fin dimension → ℕ)
    (coefficient : BernsteinGridIndex degree → ℝ) : MvPolynomial (Fin dimension) ℝ :=
  ∑ index, MvPolynomial.C (coefficient index) * tensorBernsteinBasis degree index

/-- The usual tensor Bernstein polynomial of a real function. -/
def tensorBernsteinApproximation (degree : Fin dimension → ℕ)
    (function : (Fin dimension → ℝ) → ℝ) : MvPolynomial (Fin dimension) ℝ :=
  tensorBernsteinPolynomial degree (fun index ↦ function (bernsteinGridPoint degree index))

theorem eval_tensorBernsteinBasis (degree : Fin dimension → ℕ)
    (index : BernsteinGridIndex degree) (point : Fin dimension → ℝ) :
    MvPolynomial.eval point (tensorBernsteinBasis degree index) =
      tensorBernsteinWeight degree index point := by
  simp [tensorBernsteinBasis, tensorBernsteinWeight, bernsteinPolynomial,
    Polynomial.eval₂_pow, Polynomial.eval₂_sub]

theorem eval_tensorBernsteinPolynomial (degree : Fin dimension → ℕ)
    (coefficient : BernsteinGridIndex degree → ℝ) (point : Fin dimension → ℝ) :
    MvPolynomial.eval point (tensorBernsteinPolynomial degree coefficient) =
      ∑ index, coefficient index * tensorBernsteinWeight degree index point := by
  simp [tensorBernsteinPolynomial, eval_tensorBernsteinBasis]

theorem eval_tensorBernsteinApproximation (degree : Fin dimension → ℕ)
    (function : (Fin dimension → ℝ) → ℝ) (point : Fin dimension → ℝ) :
    MvPolynomial.eval point (tensorBernsteinApproximation degree function) =
      ∑ index, function (bernsteinGridPoint degree index) *
        tensorBernsteinWeight degree index point :=
  eval_tensorBernsteinPolynomial degree _ point

theorem bernsteinGridPoint_mem_unitCube (degree : Fin dimension → ℕ)
    (index : BernsteinGridIndex degree) (coordinate : Fin dimension) :
    bernsteinGridPoint degree index coordinate ∈ Set.Icc (0 : ℝ) 1 :=
  (bernstein.z (index coordinate)).property

theorem tensorBernsteinWeight_nonneg (degree : Fin dimension → ℕ)
    (index : BernsteinGridIndex degree) (point : Fin dimension → ℝ)
    (hpoint : ∀ coordinate, point coordinate ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ tensorBernsteinWeight degree index point := by
  apply Finset.prod_nonneg
  intro coordinate _
  exact bernstein_nonneg (x := ⟨point coordinate, hpoint coordinate⟩)

/-- Tensor weights have total mass one, including zero degrees and dimension zero. -/
theorem sum_tensorBernsteinWeight (degree : Fin dimension → ℕ)
    (point : Fin dimension → ℝ) :
    ∑ index, tensorBernsteinWeight degree index point = 1 := by
  unfold tensorBernsteinWeight
  rw [← Fintype.prod_sum (fun coordinate (index : Fin (degree coordinate + 1)) ↦
    (bernsteinPolynomial ℝ (degree coordinate) index).eval (point coordinate))]
  have hsum (coordinate : Fin dimension) :
      (∑ index : Fin (degree coordinate + 1),
        (bernsteinPolynomial ℝ (degree coordinate) index).eval (point coordinate)) = 1 := by
    simp only [← Polynomial.eval_finsetSum, Fin.sum_univ_eq_sum_range,
      bernsteinPolynomial.sum, Polynomial.eval_one]
  simp [hsum]

/-- A tensor average of one coordinate reduces exactly to its univariate average. -/
theorem sum_tensorBernsteinWeight_mul_coordinate (degree : Fin dimension → ℕ)
    (point : Fin dimension → ℝ)
    (test : (coordinate : Fin dimension) → Fin (degree coordinate + 1) → ℝ)
    (coordinate : Fin dimension) :
    (∑ index, test coordinate (index coordinate) *
      tensorBernsteinWeight degree index point) =
      ∑ index : Fin (degree coordinate + 1), test coordinate index *
        (bernsteinPolynomial ℝ (degree coordinate) index).eval (point coordinate) := by
  classical
  let weight (axis : Fin dimension) (index : Fin (degree axis + 1)) :=
    (bernsteinPolynomial ℝ (degree axis) index).eval (point axis)
  have hmass (axis : Fin dimension) : ∑ index, weight axis index = 1 := by
    simp only [weight, ← Polynomial.eval_finsetSum, Fin.sum_univ_eq_sum_range,
      bernsteinPolynomial.sum, Polynomial.eval_one]
  calc
    _ = ∑ index : BernsteinGridIndex degree,
        ∏ axis, (if axis = coordinate then test axis (index axis) else 1) *
          weight axis (index axis) := by
      apply Finset.sum_congr rfl
      intro index _
      rw [Finset.prod_mul_distrib]
      simp only [Fintype.prod_ite_eq']
      rfl
    _ = ∏ axis, ∑ index : Fin (degree axis + 1),
        (if axis = coordinate then test axis index else 1) * weight axis index :=
      (Fintype.prod_sum (fun axis (index : Fin (degree axis + 1)) ↦
        (if axis = coordinate then test axis index else 1) * weight axis index)).symm
    _ = ∏ axis, if axis = coordinate then
        ∑ index : Fin (degree axis + 1), test axis index * weight axis index else 1 := by
      apply Finset.prod_congr rfl
      intro axis _
      by_cases haxis : axis = coordinate
      · simp only [haxis, if_true]
      · simp only [haxis, if_false, one_mul, hmass]
    _ = _ := Fintype.prod_ite_eq' coordinate _

/-- Each tensor coordinate has the ordinary Bernstein squared-distance moment. -/
theorem sum_tensorBernsteinWeight_mul_coordinate_sq (degree : Fin dimension → ℕ)
    (point : Fin dimension → ℝ) (coordinate : Fin dimension)
    (hdegree : degree coordinate ≠ 0)
    (hpoint : point coordinate ∈ Set.Icc (0 : ℝ) 1) :
    (∑ index, (point coordinate - bernsteinGridPoint degree index coordinate) ^ 2 *
      tensorBernsteinWeight degree index point) =
      point coordinate * (1 - point coordinate) / degree coordinate := by
  rw [show (fun index : BernsteinGridIndex degree ↦
      (point coordinate - bernsteinGridPoint degree index coordinate) ^ 2 *
        tensorBernsteinWeight degree index point) =
      (fun index ↦ (point coordinate - (index coordinate : ℝ) / degree coordinate) ^ 2 *
        tensorBernsteinWeight degree index point) from rfl]
  rw [sum_tensorBernsteinWeight_mul_coordinate degree point
    (fun axis index ↦ (point axis - (index : ℝ) / degree axis) ^ 2)]
  exact bernstein.variance hdegree ⟨point coordinate, hpoint⟩

/-- Univariate polynomial substitution respects the corresponding formal partial derivative. -/
theorem pderiv_eval₂_coordinate (polynomial : Polynomial ℝ) (coordinate : Fin dimension) :
    MvPolynomial.pderiv coordinate
      (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X coordinate) polynomial) =
      Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X coordinate) polynomial.derivative := by
  induction polynomial using Polynomial.induction_on' with
  | add first second hfirst hsecond => simp [hfirst, hsecond]
  | monomial exponent coefficient =>
      simp [Polynomial.eval₂_monomial, Polynomial.derivative_monomial, map_mul]
      ring

/-- Substitution into a different coordinate has zero formal partial derivative. -/
theorem pderiv_eval₂_other_coordinate (polynomial : Polynomial ℝ)
    (coordinate axis : Fin dimension) (haxis : axis ≠ coordinate) :
    MvPolynomial.pderiv coordinate
      (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X axis) polynomial) = 0 := by
  induction polynomial using Polynomial.induction_on' with
  | add first second hfirst hsecond => simp [hfirst, hsecond]
  | monomial exponent coefficient =>
      simp [Polynomial.eval₂_monomial, MvPolynomial.pderiv_X_of_ne haxis]

private theorem pderiv_prod_eq_zero (coordinate : Fin dimension)
    (axes : Finset (Fin dimension)) (factor : Fin dimension → MvPolynomial (Fin dimension) ℝ)
    (hfactor : ∀ axis ∈ axes, MvPolynomial.pderiv coordinate (factor axis) = 0) :
    MvPolynomial.pderiv coordinate (∏ axis ∈ axes, factor axis) = 0 := by
  induction axes using Finset.induction_on with
  | empty => simp
  | @insert axis axes haxis hinduction =>
      rw [Finset.prod_insert haxis, MvPolynomial.pderiv_mul,
        hfactor axis (Finset.mem_insert_self axis axes),
        hinduction (fun other hother ↦ hfactor other (Finset.mem_insert_of_mem hother))]
      simp

/-- Differentiate precisely one tensor factor; all other factors remain unchanged. -/
theorem pderiv_tensorBernsteinBasis (degree : Fin dimension → ℕ)
    (index : BernsteinGridIndex degree) (coordinate : Fin dimension) :
    MvPolynomial.pderiv coordinate (tensorBernsteinBasis degree index) =
      Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X coordinate)
        (bernsteinPolynomial ℝ (degree coordinate) (index coordinate)).derivative *
      ∏ axis ∈ Finset.univ.erase coordinate,
        Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X axis)
          (bernsteinPolynomial ℝ (degree axis) (index axis)) := by
  classical
  unfold tensorBernsteinBasis
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ coordinate), MvPolynomial.pderiv_mul]
  rw [pderiv_eval₂_coordinate, pderiv_prod_eq_zero]
  · simp
  · intro axis haxis
    exact pderiv_eval₂_other_coordinate _ coordinate axis (Finset.mem_erase.mp haxis).1

/-- The exact coordinate-derivative formula for a tensor polynomial with supplied coefficients. -/
theorem pderiv_tensorBernsteinPolynomial (degree : Fin dimension → ℕ)
    (coefficient : BernsteinGridIndex degree → ℝ) (coordinate : Fin dimension) :
    MvPolynomial.pderiv coordinate (tensorBernsteinPolynomial degree coefficient) =
      ∑ index, MvPolynomial.C (coefficient index) *
        (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X coordinate)
          (bernsteinPolynomial ℝ (degree coordinate) (index coordinate)).derivative *
        ∏ axis ∈ Finset.univ.erase coordinate,
          Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X axis)
            (bernsteinPolynomial ℝ (degree axis) (index axis))) := by
  simp only [tensorBernsteinPolynomial, map_sum, MvPolynomial.pderiv_C_mul,
    pderiv_tensorBernsteinBasis]

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

end Tensor

end Math

