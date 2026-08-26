/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Kernel-checked polynomial nonnegativity certificates

This file verifies supplied algebraic certificates for finite polynomial
constraint systems.  Equality constraints evaluate to zero and inequality
constraints evaluate to nonnegative values.  A certificate expresses a target
as a sum of squares, plus sum-of-squares multiples of the inequalities, plus
arbitrary polynomial multiples of the equalities.

The verifier checks a supplied exact polynomial identity.  It neither finds
certificates nor asserts completeness, Positivstellensatz, CAD, or
quantifier-elimination results.
-/

noncomputable section

namespace Math

def polynomialSumSquares {σ R : Type*} [CommRing R]
    (terms : List (MvPolynomial σ R)) : MvPolynomial σ R :=
  (terms.map fun term => term ^ 2).sum

theorem eval₂_polynomialSumSquares_nonneg
    {σ R S : Type*} [CommRing R] [Field S] [LinearOrder S]
    [IsStrictOrderedRing S] (coeff : R →+* S) (assign : σ → S)
    (terms : List (MvPolynomial σ R)) :
    0 ≤ MvPolynomial.eval₂ coeff assign (polynomialSumSquares terms) := by
  induction terms with
  | nil => simp [polynomialSumSquares]
  | cons term terms ih =>
      simp only [polynomialSumSquares, List.map_cons, List.sum_cons,
        MvPolynomial.eval₂_add, MvPolynomial.eval₂_pow]
      exact add_nonneg (sq_nonneg _) ih

structure PolynomialNonnegativeCertificate
    {σ R : Type*} [CommRing R]
    (EqualityIndex InequalityIndex : Type*)
    [Fintype EqualityIndex] [Fintype InequalityIndex]
    (equality : EqualityIndex → MvPolynomial σ R)
    (inequality : InequalityIndex → MvPolynomial σ R)
    (target : MvPolynomial σ R) where
  freeSquares : List (MvPolynomial σ R)
  inequalitySquares : InequalityIndex → List (MvPolynomial σ R)
  equalityMultiplier : EqualityIndex → MvPolynomial σ R
  identity :
    target = polynomialSumSquares freeSquares +
      (∑ index, polynomialSumSquares (inequalitySquares index) *
        inequality index) +
      ∑ index, equalityMultiplier index * equality index

def polynomialNonnegativeCertificate_of_inequality
    {σ R EqualityIndex InequalityIndex : Type*} [CommRing R]
    [Fintype EqualityIndex] [Fintype InequalityIndex]
    [DecidableEq InequalityIndex]
    (equality : EqualityIndex → MvPolynomial σ R)
    (inequality : InequalityIndex → MvPolynomial σ R)
    (chosen : InequalityIndex) :
    PolynomialNonnegativeCertificate EqualityIndex InequalityIndex
      equality inequality (inequality chosen) where
  freeSquares := []
  inequalitySquares index := if index = chosen then [1] else []
  equalityMultiplier _ := 0
  identity := by
    classical
    simp only [polynomialSumSquares, List.map_nil, List.sum_nil,
      zero_add, zero_mul, Finset.sum_const_zero, add_zero]
    symm
    calc
      (∑ index, (List.map (fun term => term ^ 2)
          (if index = chosen then [1] else [])).sum * inequality index) =
          ∑ index, if chosen = index then inequality index else 0 := by
        apply Finset.sum_congr rfl
        intro index _
        by_cases hindex : index = chosen
        · subst index
          simp
        · simp [hindex, Ne.symm hindex]
      _ = inequality chosen := by
        simp

theorem eval₂_nonneg_of_polynomialCertificate
    {σ R S EqualityIndex InequalityIndex : Type*}
    [CommRing R] [Field S] [LinearOrder S] [IsStrictOrderedRing S]
    [Fintype EqualityIndex] [Fintype InequalityIndex]
    (coeff : R →+* S) (assign : σ → S)
    (equality : EqualityIndex → MvPolynomial σ R)
    (inequality : InequalityIndex → MvPolynomial σ R)
    (target : MvPolynomial σ R)
    (certificate : PolynomialNonnegativeCertificate EqualityIndex
      InequalityIndex equality inequality target)
    (hequality : ∀ index,
      MvPolynomial.eval₂ coeff assign (equality index) = 0)
    (hinequality : ∀ index,
      0 ≤ MvPolynomial.eval₂ coeff assign (inequality index)) :
    0 ≤ MvPolynomial.eval₂ coeff assign target := by
  classical
  rw [certificate.identity, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_add, MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_sum]
  have hfree : 0 ≤ MvPolynomial.eval₂ coeff assign
      (polynomialSumSquares certificate.freeSquares) :=
    eval₂_polynomialSumSquares_nonneg coeff assign _
  have hinequalitySum : 0 ≤ ∑ index,
      MvPolynomial.eval₂ coeff assign
        (polynomialSumSquares (certificate.inequalitySquares index) *
          inequality index) := by
    apply Finset.sum_nonneg
    intro index _
    rw [MvPolynomial.eval₂_mul]
    exact mul_nonneg
      (eval₂_polynomialSumSquares_nonneg coeff assign _)
      (hinequality index)
  have hequalitySum : (∑ index,
      MvPolynomial.eval₂ coeff assign
        (certificate.equalityMultiplier index * equality index)) = 0 := by
    apply Finset.sum_eq_zero
    intro index _
    rw [MvPolynomial.eval₂_mul, hequality index, mul_zero]
  rw [hequalitySum, add_zero]
  exact add_nonneg hfree hinequalitySum

abbrev PolynomialInfeasibilityCertificate
    {σ R : Type*} [CommRing R]
    (EqualityIndex InequalityIndex : Type*)
    [Fintype EqualityIndex] [Fintype InequalityIndex]
    (equality : EqualityIndex → MvPolynomial σ R)
    (inequality : InequalityIndex → MvPolynomial σ R) :=
  PolynomialNonnegativeCertificate EqualityIndex InequalityIndex
    equality inequality (MvPolynomial.C (-1))

theorem not_exists_of_polynomialInfeasibilityCertificate
    {σ R S EqualityIndex InequalityIndex : Type*}
    [CommRing R] [Field S] [LinearOrder S] [IsStrictOrderedRing S]
    [Fintype EqualityIndex] [Fintype InequalityIndex]
    (coeff : R →+* S)
    (equality : EqualityIndex → MvPolynomial σ R)
    (inequality : InequalityIndex → MvPolynomial σ R)
    (certificate : PolynomialInfeasibilityCertificate EqualityIndex
      InequalityIndex equality inequality) :
    ¬ ∃ assign : σ → S,
      (∀ index, MvPolynomial.eval₂ coeff assign (equality index) = 0) ∧
      (∀ index, 0 ≤ MvPolynomial.eval₂ coeff assign
        (inequality index)) := by
  rintro ⟨assign, hequality, hinequality⟩
  have hnonneg := eval₂_nonneg_of_polynomialCertificate coeff assign
    equality inequality (MvPolynomial.C (-1)) certificate
    hequality hinequality
  rw [MvPolynomial.eval₂_C] at hnonneg
  have himpossible : (0 : S) ≤ -1 := by
    simpa using hnonneg
  exact (not_lt_of_ge himpossible) (by simp)

end Math
