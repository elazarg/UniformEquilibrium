import MathUE.Polynomial.TensorBernstein
import Mathlib.Logic.Equiv.Prod

/-! # Coordinate differences of tensor Bernstein polynomials

Exact reindexing identities, not a smooth-function approximation theorem.
-/

noncomputable section

namespace Math

open scoped BigOperators

variable {dimension : ℕ}

/-- The grid on all coordinates other than the distinguished one. -/
abbrev BernsteinComplementIndex (degree : Fin dimension → ℕ) (coordinate : Fin dimension) :=
  (axis : {axis : Fin dimension // axis ≠ coordinate}) → Fin (degree axis + 1)

/-- Insert one natural index into a complementary grid. -/
def bernsteinCoordinateIndex (degree : Fin dimension → ℕ) (coordinate : Fin dimension)
    (value : ℕ) (complement : BernsteinComplementIndex degree coordinate) : Fin dimension → ℕ :=
  fun axis ↦ if haxis : axis = coordinate then value else complement ⟨axis, haxis⟩

/-- Split a dependent grid at one coordinate, with the complementary degrees unchanged. -/
def bernsteinGridSplitEquiv (degree : Fin dimension → ℕ) (coordinate : Fin dimension)
    (selectedDegree : ℕ) :
    BernsteinGridIndex (Function.update degree coordinate selectedDegree) ≃
      Fin (selectedDegree + 1) × BernsteinComplementIndex degree coordinate where
  toFun index :=
    (⟨index coordinate, by simpa using (index coordinate).isLt⟩,
      fun axis ↦ ⟨index axis, by simpa [Function.update_of_ne axis.property] using
        (index axis).isLt⟩)
  invFun pair axis :=
    ⟨bernsteinCoordinateIndex degree coordinate pair.1 pair.2 axis, by
      by_cases haxis : axis = coordinate
      · simpa [bernsteinCoordinateIndex, haxis] using pair.1.isLt
      · simpa [bernsteinCoordinateIndex, haxis, Function.update_of_ne haxis] using
          (pair.2 ⟨axis, haxis⟩).isLt⟩
  left_inv index := by
    funext axis
    apply Fin.ext
    by_cases haxis : axis = coordinate
    · subst axis
      simp [bernsteinCoordinateIndex]
    · simp [bernsteinCoordinateIndex, haxis]
  right_inv pair := by
    apply Prod.ext
    · apply Fin.ext
      simp [bernsteinCoordinateIndex]
    · funext axis
      apply Fin.ext
      simp [bernsteinCoordinateIndex, axis.property]

/-- Natural-index coefficients are an exact adapter into the existing tensor polynomial. -/
def tensorBernsteinCoefficientPolynomial (degree : Fin dimension → ℕ)
    (coefficient : (Fin dimension → ℕ) → ℝ) : MvPolynomial (Fin dimension) ℝ :=
  tensorBernsteinPolynomial degree (fun index ↦ coefficient (fun axis ↦ index axis))

/-- The product of factors outside one coordinate. -/
def tensorBernsteinComplementBasis (degree : Fin dimension → ℕ) (coordinate : Fin dimension)
    (complement : BernsteinComplementIndex degree coordinate) : MvPolynomial (Fin dimension) ℝ :=
  ∏ axis : {axis : Fin dimension // axis ≠ coordinate},
    Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X axis.val)
    (bernsteinPolynomial ℝ (degree axis) (complement axis))

theorem tensorBernsteinBasis_gridSplit (degree : Fin dimension → ℕ)
    (coordinate : Fin dimension) (selectedDegree : ℕ)
    (pair : Fin (selectedDegree + 1) × BernsteinComplementIndex degree coordinate) :
    tensorBernsteinBasis (Function.update degree coordinate selectedDegree)
      ((bernsteinGridSplitEquiv degree coordinate selectedDegree).symm pair) =
      Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X coordinate)
        (bernsteinPolynomial ℝ selectedDegree pair.1) *
        tensorBernsteinComplementBasis degree coordinate pair.2 := by
  classical
  unfold tensorBernsteinBasis
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ coordinate)]
  congr 1
  · simp [bernsteinGridSplitEquiv, bernsteinCoordinateIndex]
  · unfold tensorBernsteinComplementBasis
    rw [Finset.prod_subtype (p := fun axis ↦ axis ≠ coordinate) _ (by simp)]
    apply Finset.prod_congr rfl
    intro axis _
    simp [bernsteinGridSplitEquiv, bernsteinCoordinateIndex, axis.property]

/-- Slice a tensor polynomial into univariate coefficient polynomials on one coordinate. -/
theorem tensorBernsteinCoefficientPolynomial_coordinate_slices
    (degree : Fin dimension → ℕ) (coordinate : Fin dimension) (selectedDegree : ℕ)
    (coefficient : (Fin dimension → ℕ) → ℝ) :
    tensorBernsteinCoefficientPolynomial (Function.update degree coordinate selectedDegree)
      coefficient =
      ∑ complement : BernsteinComplementIndex degree coordinate,
        Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X coordinate)
          (bernsteinCoefficientPolynomial selectedDegree (fun value ↦
            coefficient (bernsteinCoordinateIndex degree coordinate value complement))) *
        tensorBernsteinComplementBasis degree coordinate complement := by
  classical
  unfold tensorBernsteinCoefficientPolynomial tensorBernsteinPolynomial
  rw [← (bernsteinGridSplitEquiv degree coordinate selectedDegree).symm.sum_comp]
  simp only [tensorBernsteinBasis_gridSplit]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro complement _
  simp only [bernsteinGridSplitEquiv, Equiv.coe_fn_symm_mk]
  simp only [← mul_assoc, ← Finset.sum_mul]
  congr 1
  simp only [bernsteinCoefficientPolynomial, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C]
  exact Fin.sum_univ_eq_sum_range (fun value ↦
    MvPolynomial.C (coefficient (bernsteinCoordinateIndex degree coordinate value complement)) *
      Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X coordinate)
        (bernsteinPolynomial ℝ selectedDegree value)) (selectedDegree + 1)

theorem pderiv_tensorBernsteinComplementBasis (degree : Fin dimension → ℕ)
    (coordinate : Fin dimension) (complement : BernsteinComplementIndex degree coordinate) :
    MvPolynomial.pderiv coordinate
      (tensorBernsteinComplementBasis degree coordinate complement) = 0 := by
  classical
  unfold tensorBernsteinComplementBasis
  induction (Finset.univ : Finset {axis : Fin dimension // axis ≠ coordinate})
      using Finset.induction_on with
  | empty => simp
  | @insert axis axes haxis hinduction =>
      rw [Finset.prod_insert haxis, MvPolynomial.pderiv_mul,
        pderiv_eval₂_other_coordinate _ coordinate axis.val axis.property, hinduction]
      simp

/-- Consecutive coefficient difference in one coordinate, with all others fixed. -/
def bernsteinCoordinateDifference (coordinate : Fin dimension)
    (coefficient : (Fin dimension → ℕ) → ℝ) (index : Fin dimension → ℕ) : ℝ :=
  coefficient (Function.update index coordinate (index coordinate + 1)) - coefficient index

theorem bernsteinCoordinateDifference_coordinateIndex (degree : Fin dimension → ℕ)
    (coordinate : Fin dimension) (coefficient : (Fin dimension → ℕ) → ℝ)
    (value : ℕ) (complement : BernsteinComplementIndex degree coordinate) :
    bernsteinCoordinateDifference coordinate coefficient
      (bernsteinCoordinateIndex degree coordinate value complement) =
      coefficient (bernsteinCoordinateIndex degree coordinate (value + 1) complement) -
        coefficient (bernsteinCoordinateIndex degree coordinate value complement) := by
  unfold bernsteinCoordinateDifference
  congr 2
  funext axis
  by_cases haxis : axis = coordinate
  · subst axis
    simp [bernsteinCoordinateIndex]
  · simp [bernsteinCoordinateIndex, haxis]

/-- A coordinate derivative is a lower-degree tensor with consecutive coefficient differences. -/
theorem pderiv_tensorBernsteinCoefficientPolynomial (degree : Fin dimension → ℕ)
    (coordinate : Fin dimension) (selectedDegree : ℕ)
    (coefficient : (Fin dimension → ℕ) → ℝ) :
    MvPolynomial.pderiv coordinate
      (tensorBernsteinCoefficientPolynomial
        (Function.update degree coordinate (selectedDegree + 1)) coefficient) =
      (selectedDegree + 1 : MvPolynomial (Fin dimension) ℝ) *
        tensorBernsteinCoefficientPolynomial (Function.update degree coordinate selectedDegree)
          (bernsteinCoordinateDifference coordinate coefficient) := by
  rw [tensorBernsteinCoefficientPolynomial_coordinate_slices,
    tensorBernsteinCoefficientPolynomial_coordinate_slices]
  simp only [map_sum, MvPolynomial.pderiv_mul, pderiv_tensorBernsteinComplementBasis,
    mul_zero, add_zero, pderiv_eval₂_coordinate, derivative_bernsteinCoefficientPolynomial]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_add, Polynomial.eval₂_natCast,
    Polynomial.eval₂_one, mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro complement _
  congr 4
  funext value
  exact (bernsteinCoordinateDifference_coordinateIndex degree coordinate coefficient value
    complement).symm

theorem eval_tensorBernsteinCoefficientPolynomial (degree : Fin dimension → ℕ)
    (coefficient : (Fin dimension → ℕ) → ℝ) (point : Fin dimension → ℝ) :
    MvPolynomial.eval point (tensorBernsteinCoefficientPolynomial degree coefficient) =
      ∑ index : BernsteinGridIndex degree,
        coefficient (fun axis ↦ index axis) * tensorBernsteinWeight degree index point :=
  eval_tensorBernsteinPolynomial degree _ point

/-- The function-sampling construction is literally the natural-index coefficient adapter. -/
theorem tensorBernsteinApproximation_eq_coefficientPolynomial (degree : Fin dimension → ℕ)
    (function : (Fin dimension → ℝ) → ℝ) :
    tensorBernsteinApproximation degree function =
      tensorBernsteinCoefficientPolynomial degree (fun index ↦
        function (fun axis ↦ (index axis : ℝ) / degree axis)) := rfl

/-- Evaluation of the partial derivative is a tensor average of consecutive differences. -/
theorem eval_pderiv_tensorBernsteinCoefficientPolynomial (degree : Fin dimension → ℕ)
    (coordinate : Fin dimension) (selectedDegree : ℕ)
    (coefficient : (Fin dimension → ℕ) → ℝ) (point : Fin dimension → ℝ) :
    MvPolynomial.eval point (MvPolynomial.pderiv coordinate
      (tensorBernsteinCoefficientPolynomial
        (Function.update degree coordinate (selectedDegree + 1)) coefficient)) =
      (selectedDegree + 1 : ℝ) *
        ∑ index : BernsteinGridIndex (Function.update degree coordinate selectedDegree),
          bernsteinCoordinateDifference coordinate coefficient (fun axis ↦ index axis) *
            tensorBernsteinWeight (Function.update degree coordinate selectedDegree)
              index point := by
  rw [pderiv_tensorBernsteinCoefficientPolynomial]
  simp only [MvPolynomial.eval_mul, map_add, map_natCast, map_one,
    eval_tensorBernsteinCoefficientPolynomial]

/-- The reindexed difference formula computes the actual derivative along a coordinate line. -/
theorem hasDerivAt_eval_tensorBernsteinCoefficientPolynomial_update
    (degree : Fin dimension → ℕ) (coordinate : Fin dimension) (selectedDegree : ℕ)
    (coefficient : (Fin dimension → ℕ) → ℝ) (point : Fin dimension → ℝ) :
    HasDerivAt (fun value ↦ MvPolynomial.eval (Function.update point coordinate value)
      (tensorBernsteinCoefficientPolynomial
        (Function.update degree coordinate (selectedDegree + 1)) coefficient))
      ((selectedDegree + 1 : ℝ) *
        ∑ index : BernsteinGridIndex (Function.update degree coordinate selectedDegree),
          bernsteinCoordinateDifference coordinate coefficient (fun axis ↦ index axis) *
            tensorBernsteinWeight (Function.update degree coordinate selectedDegree) index point)
      (point coordinate) := by
  rw [← eval_pderiv_tensorBernsteinCoefficientPolynomial]
  exact hasDerivAt_eval_mvPolynomial_update _ point coordinate

end Math

