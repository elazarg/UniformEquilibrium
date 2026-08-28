/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors.
-/

import MathUE.Interval.RationalPolynomial
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Fintype.Pi

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

/-! ## Executable dense coefficient reflection -/

/-- Coefficient extraction directly from the reflected syntax.  Multiplication
uses the finite monomial antidiagonal, so evaluating one coefficient never
constructs the support of the normalized `MvPolynomial`. -/
def reflectedCoefficient :
    RationalPolynomial variableCount → (Fin variableCount →₀ ℕ) → ℚ
  | .constant value, monomial => if monomial = 0 then value else 0
  | .var coordinate, monomial =>
      if monomial = Finsupp.single coordinate 1 then 1 else 0
  | .add first second, monomial =>
      reflectedCoefficient first monomial + reflectedCoefficient second monomial
  | .neg expression, monomial => -reflectedCoefficient expression monomial
  | .mul first second, monomial =>
      ∑ split ∈ Finset.antidiagonal monomial,
        reflectedCoefficient first split.1 *
          reflectedCoefficient second split.2

/-- The multiplication branch is literally the finite coefficient
convolution used by the executable reflector. -/
theorem reflectedCoefficient_mul
    (first second : RationalPolynomial variableCount)
    (monomial : Fin variableCount →₀ ℕ) :
    reflectedCoefficient (first * second) monomial =
      ∑ split ∈ Finset.antidiagonal monomial,
        reflectedCoefficient first split.1 *
          reflectedCoefficient second split.2 := rfl

/-- The executable coefficient reflector agrees with canonical
`MvPolynomial` normalization. -/
theorem reflectedCoefficient_eq_coeff
    (expression : RationalPolynomial variableCount)
    (monomial : Fin variableCount →₀ ℕ) :
    reflectedCoefficient expression monomial =
      (toMvPolynomial expression).coeff monomial := by
  induction expression generalizing monomial with
  | constant value =>
      simp [reflectedCoefficient, toMvPolynomial, MvPolynomial.coeff_C,
        eq_comm]
  | var coordinate =>
      simp [reflectedCoefficient, toMvPolynomial, MvPolynomial.coeff_X,
        eq_comm]
  | add first second hfirst hsecond =>
      simp [reflectedCoefficient, toMvPolynomial, MvPolynomial.coeff_add,
        hfirst, hsecond]
  | neg expression hexpression =>
      simp [reflectedCoefficient, toMvPolynomial, hexpression]
  | mul first second hfirst hsecond =>
      rw [reflectedCoefficient, toMvPolynomial, MvPolynomial.coeff_mul]
      apply Finset.sum_congr rfl
      intro split _
      rw [hfirst, hsecond]

/-- Turn a dense exponent vector into its finitely supported monomial without
using a classical finite-support choice. -/
def exponentMonomial (exponent : Fin variableCount → ℕ) :
    Fin variableCount →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm exponent

@[simp] theorem exponentMonomial_apply
    (exponent : Fin variableCount → ℕ) (coordinate : Fin variableCount) :
    exponentMonomial exponent coordinate = exponent coordinate := by
  simp [exponentMonomial]

/-- The finite box of monomials with coordinatewise exponents at most
`bound`.  Its source is visibly `Fintype.piFinset`; the mapped finitely
supported representation is used only by coefficient evaluation. -/
def boundedMonomials (bound : Fin variableCount → ℕ) :
    Finset (Fin variableCount →₀ ℕ) :=
  (Fintype.piFinset fun coordinate ↦ Finset.range (bound coordinate + 1)).map
    ⟨exponentMonomial, Finsupp.equivFunOnFinite.symm.injective⟩

theorem mem_boundedMonomials_iff
    (bound : Fin variableCount → ℕ)
    (monomial : Fin variableCount →₀ ℕ) :
    monomial ∈ boundedMonomials bound ↔
      ∀ coordinate, monomial coordinate ≤ bound coordinate := by
  constructor
  · intro hmonomial coordinate
    rcases Finset.mem_map.mp hmonomial with
      ⟨exponent, hexponent, rfl⟩
    have hcoordinate := Fintype.mem_piFinset.mp hexponent coordinate
    simpa [Nat.lt_succ_iff] using hcoordinate
  · intro hmonomial
    apply Finset.mem_map.mpr
    refine ⟨fun coordinate ↦ monomial coordinate, ?_, ?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro coordinate
      simpa [Nat.lt_succ_iff] using hmonomial coordinate
    · ext coordinate
      simp

/-- Coordinatewise syntactic degree bound.  Unlike normalized support, this
function is small and executable on a reflected expression tree. -/
def coordinateDegree (coordinate : Fin variableCount) :
    RationalPolynomial variableCount → ℕ
  | .constant _ => 0
  | .var index => if coordinate = index then 1 else 0
  | .add first second =>
      max (coordinateDegree coordinate first)
        (coordinateDegree coordinate second)
  | .neg expression => coordinateDegree coordinate expression
  | .mul first second =>
      coordinateDegree coordinate first + coordinateDegree coordinate second

/-- Canonical normalization never exceeds the executable syntactic degree. -/
theorem degreeOf_toMvPolynomial_le_coordinateDegree
    (coordinate : Fin variableCount)
    (expression : RationalPolynomial variableCount) :
    (toMvPolynomial expression).degreeOf coordinate ≤
      coordinateDegree coordinate expression := by
  induction expression with
  | constant value =>
      simp [toMvPolynomial, coordinateDegree,
        MvPolynomial.degreeOf_C]
  | var index =>
      simp [toMvPolynomial, coordinateDegree,
        MvPolynomial.degreeOf_X]
  | add first second hfirst hsecond =>
      exact (MvPolynomial.degreeOf_add_le coordinate _ _).trans
        (max_le_max hfirst hsecond)
  | neg expression hexpression =>
      simpa [toMvPolynomial, coordinateDegree,
        MvPolynomial.degreeOf_neg] using hexpression
  | mul first second hfirst hsecond =>
      exact (MvPolynomial.degreeOf_mul_le coordinate _ _).trans
        (Nat.add_le_add hfirst hsecond)

/-- A reflected polynomial fits inside one explicit exponent box. -/
def FitsExponentBound (bound : Fin variableCount → ℕ)
    (expression : RationalPolynomial variableCount) : Prop :=
  ∀ coordinate, coordinateDegree coordinate expression ≤ bound coordinate

/-- A syntactic exponent bound contains the complete normalized support. -/
theorem support_toMvPolynomial_subset_boundedMonomials
    (bound : Fin variableCount → ℕ)
    (expression : RationalPolynomial variableCount)
    (hbound : FitsExponentBound bound expression) :
    (toMvPolynomial expression).support ⊆ boundedMonomials bound := by
  intro monomial hmonomial
  rw [mem_boundedMonomials_iff]
  intro coordinate
  exact (MvPolynomial.monomial_le_degreeOf coordinate hmonomial).trans
    ((degreeOf_toMvPolynomial_le_coordinateDegree coordinate expression).trans
      (hbound coordinate))

/-- Dense coefficient-L1 evaluation over one explicit finite exponent box. -/
def boundedCoefficientL1 (bound : Fin variableCount → ℕ)
    (expression : RationalPolynomial variableCount) : ℚ :=
  ∑ monomial ∈ boundedMonomials bound,
    |reflectedCoefficient expression monomial|

/-- If the supplied box dominates the syntactic degrees, the executable
dense sum is exactly the canonical normalized coefficient-L1 value. -/
theorem boundedCoefficientL1_eq_coefficientL1
    (bound : Fin variableCount → ℕ)
    (expression : RationalPolynomial variableCount)
    (hbound : FitsExponentBound bound expression) :
    boundedCoefficientL1 bound expression = coefficientL1 expression := by
  simp_rw [boundedCoefficientL1, reflectedCoefficient_eq_coeff]
  unfold coefficientL1
  symm
  apply Finset.sum_subset
    (support_toMvPolynomial_subset_boundedMonomials bound expression hbound)
  intro monomial _ hmonomial
  rw [MvPolynomial.notMem_support_iff.mp hmonomial, abs_zero]

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
