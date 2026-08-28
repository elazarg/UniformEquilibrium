/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors.
-/

import MathUE.Interval.RationalPolynomial
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Exact coefficient-L1 bounds for reflected rational polynomials

Interval evaluation can lose cancellations when a polynomial is presented in
a deliberately factored syntax tree.  This file supplies a small complementary
checker: normalize that tree in `MvPolynomial`, sum the absolute values of the
resulting rational coefficients, and use that sum as an exact bound on the
unit box.  The normalization is semantic; no floating-point calculation or
untrusted generated witness enters the theorem.
-/

namespace Math.Interval.RationalPolynomial

noncomputable section

variable {variableCount : ℕ}

@[simp] theorem evalReal_constant
    (point : Fin variableCount → ℝ) (value : ℚ) :
    evalReal point (.constant value) = value := rfl

@[simp] theorem evalReal_var
    (point : Fin variableCount → ℝ) (coordinate : Fin variableCount) :
    evalReal point (.var coordinate) = point coordinate := rfl

@[simp] theorem evalReal_add
    (point : Fin variableCount → ℝ)
    (first second : RationalPolynomial variableCount) :
    evalReal point (first + second) =
      evalReal point first + evalReal point second := rfl

@[simp] theorem evalReal_neg
    (point : Fin variableCount → ℝ)
    (expression : RationalPolynomial variableCount) :
    evalReal point (-expression) = -evalReal point expression := rfl

@[simp] theorem evalReal_sub
    (point : Fin variableCount → ℝ)
    (first second : RationalPolynomial variableCount) :
    evalReal point (first - second) =
      evalReal point first - evalReal point second := rfl

@[simp] theorem evalReal_mul
    (point : Fin variableCount → ℝ)
    (first second : RationalPolynomial variableCount) :
    evalReal point (first * second) =
      evalReal point first * evalReal point second := rfl

/-- Canonical multivariate-polynomial normalization of the reflected syntax. -/
def toMvPolynomial :
    RationalPolynomial variableCount → MvPolynomial (Fin variableCount) ℚ
  | .constant value => MvPolynomial.C value
  | .var index => MvPolynomial.X index
  | .add first second => toMvPolynomial first + toMvPolynomial second
  | .neg expression => -toMvPolynomial expression
  | .mul first second => toMvPolynomial first * toMvPolynomial second

/-- Normalization preserves real evaluation. -/
theorem evalReal_eq_eval₂_toMvPolynomial
    (point : Fin variableCount → ℝ)
    (expression : RationalPolynomial variableCount) :
    evalReal point expression =
      MvPolynomial.eval₂ (Rat.castHom ℝ) point
        (toMvPolynomial expression) := by
  induction expression with
  | constant value => simp [evalReal, toMvPolynomial]
  | var index => simp [evalReal, toMvPolynomial]
  | add first second hfirst hsecond =>
      simp [evalReal, toMvPolynomial, hfirst, hsecond]
  | neg expression hexpression =>
      simp [evalReal, toMvPolynomial, hexpression]
  | mul first second hfirst hsecond =>
      simp [evalReal, toMvPolynomial, hfirst, hsecond]

/-- Exact rational coefficient-L1 size of a normalized reflected polynomial. -/
def coefficientL1 (expression : RationalPolynomial variableCount) : ℚ :=
  ∑ monomial ∈ (toMvPolynomial expression).support,
    |(toMvPolynomial expression).coeff monomial|

/-- On the real unit box, evaluation is bounded by the normalized rational
coefficient-L1 size. -/
theorem abs_evalReal_le_coefficientL1
    (point : Fin variableCount → ℝ)
    (hpoint : ∀ coordinate, |point coordinate| ≤ 1)
    (expression : RationalPolynomial variableCount) :
    |evalReal point expression| ≤ coefficientL1 expression := by
  rw [evalReal_eq_eval₂_toMvPolynomial]
  rw [MvPolynomial.eval₂_eq']
  calc
    |∑ monomial ∈ (toMvPolynomial expression).support,
        Rat.castHom ℝ ((toMvPolynomial expression).coeff monomial) *
          ∏ coordinate, point coordinate ^ monomial coordinate| ≤
        ∑ monomial ∈ (toMvPolynomial expression).support,
          |Rat.castHom ℝ
              ((toMvPolynomial expression).coeff monomial) *
            ∏ coordinate, point coordinate ^ monomial coordinate| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ monomial ∈ (toMvPolynomial expression).support,
          (((|(toMvPolynomial expression).coeff monomial| : ℚ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro monomial _
      rw [abs_mul, Finset.abs_prod]
      have hmonomial :
          ∏ coordinate, |point coordinate ^ monomial coordinate| ≤ 1 := by
        apply Finset.prod_le_one
        · intro coordinate _
          positivity
        · intro coordinate _
          simpa only [abs_pow] using
            pow_le_one₀ (abs_nonneg (point coordinate))
              (hpoint coordinate)
      calc
        |Rat.castHom ℝ
            ((toMvPolynomial expression).coeff monomial)| *
            ∏ coordinate,
              |point coordinate ^ monomial coordinate| ≤
            |Rat.castHom ℝ
              ((toMvPolynomial expression).coeff monomial)| * 1 :=
          mul_le_mul_of_nonneg_left hmonomial
            (abs_nonneg
              (Rat.castHom ℝ
                ((toMvPolynomial expression).coeff monomial)))
        _ = (((|(toMvPolynomial expression).coeff monomial| : ℚ) : ℝ)) := by
          rw [mul_one]
          simpa only [Rat.coe_castHom] using
            (Rat.cast_abs
              (K := ℝ)
              ((toMvPolynomial expression).coeff monomial)).symm
    _ = coefficientL1 expression := by
      simp only [coefficientL1, Rat.cast_sum, Rat.cast_abs]

/-- A checked rational coefficient comparison is an executable real bound. -/
theorem abs_evalReal_le_of_coefficientL1_le
    (point : Fin variableCount → ℝ)
    (hpoint : ∀ coordinate, |point coordinate| ≤ 1)
    (expression : RationalPolynomial variableCount) (bound : ℚ)
    (hbound : coefficientL1 expression ≤ bound) :
    |evalReal point expression| ≤ bound :=
  (abs_evalReal_le_coefficientL1 point hpoint expression).trans
    (by exact_mod_cast hbound)

end

end Math.Interval.RationalPolynomial
