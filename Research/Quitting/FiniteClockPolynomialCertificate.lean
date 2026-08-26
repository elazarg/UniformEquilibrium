/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Polynomial.NonnegativeCertificate
import Research.Quitting.FiniteClockPolynomialCenter

/-!
# Checked rational certificates for finite-clock centers

This file indexes the equality and inequality rows of the exact finite-clock
polynomial presentation.  It connects supplied sum-of-squares identities to
the existing satisfaction predicate, both for nonnegative polynomial
consequences and for infeasibility after adding any finite rational family of
query constraints.

The certificate is a proof object checked by polynomial equality and ordered
ring reasoning.  No certificate search, completeness theorem, CAD, or
quantifier-elimination procedure is asserted.
-/

noncomputable section

namespace GameTheory

open Math Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

inductive FiniteClockCenterEqualityIndex (ι : Type) : Type where
  | simplex (player : ι)
  | auxiliary (player : ι)
  | payoff (player : ι)
  | capTight (player : ι)
deriving DecidableEq, Fintype

inductive FiniteClockCenterInequalityIndex (ι : Type)
    (clockBound : ℕ) : Type where
  | mass (player : ι) (atom : FiniteClockAtom clockBound)
  | capUpper (player : ι) (candidate : FiniteClockAtom clockBound)
deriving DecidableEq, Fintype

def finiteClockCenterEqualityPolynomial
    {R : Type*} [CommRing R]
    (reward : {T : Finset ι // T.Nonempty} → ι → R)
    (clockBound : ℕ) :
    FiniteClockCenterEqualityIndex ι →
      MvPolynomial (FiniteClockCenterVar ι clockBound) R
  | .simplex player => finiteClockSimplexSumPoly clockBound player
  | .auxiliary player =>
      finiteClockMassPoly clockBound player (finiteClockAuxAtom clockBound)
  | .payoff player =>
      finiteClockPayoffConsistencyPoly reward clockBound player
  | .capTight player => finiteClockCapTightPoly reward clockBound player

def finiteClockCenterInequalityPolynomial
    {R : Type*} [CommRing R]
    (reward : {T : Finset ι // T.Nonempty} → ι → R)
    (clockBound : ℕ) :
    FiniteClockCenterInequalityIndex ι clockBound →
      MvPolynomial (FiniteClockCenterVar ι clockBound) R
  | .mass player atom => finiteClockMassPoly clockBound player atom
  | .capUpper player candidate =>
      finiteClockCapUpperPoly reward clockBound player candidate

theorem satisfiesFiniteClockCenterPolynomials_iff_indexed
    {R S : Type*} [CommRing R] [Field S] [LinearOrder S]
    [IsStrictOrderedRing S]
    (coeff : R →+* S)
    (reward : {T : Finset ι // T.Nonempty} → ι → R)
    (clockBound : ℕ)
    (assign : FiniteClockCenterVar ι clockBound → S) :
    SatisfiesFiniteClockCenterPolynomials coeff reward clockBound assign ↔
      (∀ index, MvPolynomial.eval₂ coeff assign
        (finiteClockCenterEqualityPolynomial reward clockBound index) = 0) ∧
      (∀ index, 0 ≤ MvPolynomial.eval₂ coeff assign
        (finiteClockCenterInequalityPolynomial reward clockBound index)) := by
  constructor
  · intro hsolution
    constructor
    · intro index
      cases index with
      | simplex player => exact hsolution.1 player
      | auxiliary player => exact hsolution.2.2.1 player
      | payoff player => exact hsolution.2.2.2.1 player
      | capTight player => exact hsolution.2.2.2.2.2 player
    · intro index
      cases index with
      | mass player atom => exact hsolution.2.1 player atom
      | capUpper player candidate => exact hsolution.2.2.2.2.1 player candidate
  · rintro ⟨hequality, hinequality⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro player
      exact hequality (.simplex player)
    · intro player atom
      exact hinequality (.mass player atom)
    · intro player
      exact hequality (.auxiliary player)
    · intro player
      exact hequality (.payoff player)
    · intro player candidate
      exact hinequality (.capUpper player candidate)
    · intro player
      exact hequality (.capTight player)

abbrev RationalFiniteClockCenterNonnegativeCertificate
    (reward : {T : Finset ι // T.Nonempty} → ι → ℚ)
    (clockBound : ℕ)
    (target : MvPolynomial (FiniteClockCenterVar ι clockBound) ℚ) :=
  Math.PolynomialNonnegativeCertificate
    (FiniteClockCenterEqualityIndex ι)
    (FiniteClockCenterInequalityIndex ι clockBound)
    (finiteClockCenterEqualityPolynomial reward clockBound)
    (finiteClockCenterInequalityPolynomial reward clockBound)
    target

theorem eval₂_nonneg_of_rationalFiniteClockCenterCertificate
    (reward : {T : Finset ι // T.Nonempty} → ι → ℚ)
    (clockBound : ℕ)
    (target : MvPolynomial (FiniteClockCenterVar ι clockBound) ℚ)
    (certificate : RationalFiniteClockCenterNonnegativeCertificate
      reward clockBound target)
    (assign : FiniteClockCenterVar ι clockBound → ℝ)
    (hsolution : SatisfiesFiniteClockCenterPolynomials
      (Rat.castHom ℝ) reward clockBound assign) :
    0 ≤ MvPolynomial.eval₂ (Rat.castHom ℝ) assign target := by
  rw [satisfiesFiniteClockCenterPolynomials_iff_indexed] at hsolution
  exact Math.eval₂_nonneg_of_polynomialCertificate
    (Rat.castHom ℝ) assign
    (finiteClockCenterEqualityPolynomial reward clockBound)
    (finiteClockCenterInequalityPolynomial reward clockBound)
    target certificate hsolution.1 hsolution.2

def finiteClockAugmentedEqualityPolynomial
    {R ExtraEquality : Type*} [CommRing R]
    (reward : {T : Finset ι // T.Nonempty} → ι → R)
    (clockBound : ℕ)
    (extraEquality : ExtraEquality →
      MvPolynomial (FiniteClockCenterVar ι clockBound) R) :
    Sum (FiniteClockCenterEqualityIndex ι) ExtraEquality →
      MvPolynomial (FiniteClockCenterVar ι clockBound) R
  | .inl index => finiteClockCenterEqualityPolynomial reward clockBound index
  | .inr index => extraEquality index

def finiteClockAugmentedInequalityPolynomial
    {R ExtraInequality : Type*} [CommRing R]
    (reward : {T : Finset ι // T.Nonempty} → ι → R)
    (clockBound : ℕ)
    (extraInequality : ExtraInequality →
      MvPolynomial (FiniteClockCenterVar ι clockBound) R) :
    Sum (FiniteClockCenterInequalityIndex ι clockBound) ExtraInequality →
      MvPolynomial (FiniteClockCenterVar ι clockBound) R
  | .inl index => finiteClockCenterInequalityPolynomial reward clockBound index
  | .inr index => extraInequality index

abbrev RationalFiniteClockAugmentedInfeasibilityCertificate
    {ExtraEquality ExtraInequality : Type*}
    [Fintype ExtraEquality] [Fintype ExtraInequality]
    (reward : {T : Finset ι // T.Nonempty} → ι → ℚ)
    (clockBound : ℕ)
    (extraEquality : ExtraEquality →
      MvPolynomial (FiniteClockCenterVar ι clockBound) ℚ)
    (extraInequality : ExtraInequality →
      MvPolynomial (FiniteClockCenterVar ι clockBound) ℚ) :=
  Math.PolynomialInfeasibilityCertificate
    (Sum (FiniteClockCenterEqualityIndex ι) ExtraEquality)
    (Sum (FiniteClockCenterInequalityIndex ι clockBound) ExtraInequality)
    (finiteClockAugmentedEqualityPolynomial reward clockBound extraEquality)
    (finiteClockAugmentedInequalityPolynomial reward clockBound extraInequality)

theorem not_exists_rationalFiniteClockCenter_of_augmentedCertificate
    {ExtraEquality ExtraInequality : Type*}
    [Fintype ExtraEquality] [Fintype ExtraInequality]
    (reward : {T : Finset ι // T.Nonempty} → ι → ℚ)
    (clockBound : ℕ)
    (extraEquality : ExtraEquality →
      MvPolynomial (FiniteClockCenterVar ι clockBound) ℚ)
    (extraInequality : ExtraInequality →
      MvPolynomial (FiniteClockCenterVar ι clockBound) ℚ)
    (certificate : RationalFiniteClockAugmentedInfeasibilityCertificate
      reward clockBound extraEquality extraInequality) :
    ¬ ∃ assign : FiniteClockCenterVar ι clockBound → ℝ,
      SatisfiesFiniteClockCenterPolynomials
        (Rat.castHom ℝ) reward clockBound assign ∧
      (∀ index, MvPolynomial.eval₂ (Rat.castHom ℝ) assign
        (extraEquality index) = 0) ∧
      (∀ index, 0 ≤ MvPolynomial.eval₂ (Rat.castHom ℝ) assign
        (extraInequality index)) := by
  intro hexists
  apply Math.not_exists_of_polynomialInfeasibilityCertificate
    (Rat.castHom ℝ)
    (finiteClockAugmentedEqualityPolynomial reward clockBound extraEquality)
    (finiteClockAugmentedInequalityPolynomial reward clockBound extraInequality)
    certificate
  rcases hexists with ⟨assign, hbase, hextraEquality, hextraInequality⟩
  rw [satisfiesFiniteClockCenterPolynomials_iff_indexed] at hbase
  refine ⟨assign, ?_, ?_⟩
  · intro index
    cases index with
    | inl index => exact hbase.1 index
    | inr index => exact hextraEquality index
  · intro index
    cases index with
    | inl index => exact hbase.2 index
    | inr index => exact hextraInequality index

end GameTheory
