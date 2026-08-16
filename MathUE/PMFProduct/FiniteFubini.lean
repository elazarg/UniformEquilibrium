/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.PMFProduct.Update

/-!
# Fubini formulas for finite product PMFs

This file gives a recursive expectation formula for a `Fin (n + 1)`-indexed
independent product, followed by convenient two-, three-, and four-coordinate
specializations.  The recursive theorem supports dependent coordinate types;
the displayed-vector corollaries use one homogeneous coordinate type.
-/

namespace Math.PMFProduct

open Math.Probability Math.ProbabilityMassFunction

/-- Split the expectation of a `Fin (n + 1)`-indexed independent product into
the first marginal and the independent product of the remaining marginals. -/
theorem expect_pmfPi_fin_succ {n : ℕ} {A : Fin (n + 1) → Type*}
    [∀ i, Fintype (A i)] (sigma : ∀ i, PMF (A i))
    (f : (∀ i, A i) → ℝ) :
    expect (pmfPi sigma) f =
      expect (sigma 0) fun a ↦
        expect (pmfPi (fun i : Fin n ↦ sigma i.succ)) fun tail ↦
          f (Fin.cons a tail) := by
  classical
  rw [expect_eq_sum]
  calc
    (∑ joint, ((pmfPi sigma) joint).toReal * f joint) =
        ∑ pair : A 0 × ((i : Fin n) → A i.succ),
          ((pmfPi sigma) (Fin.cons pair.1 pair.2)).toReal *
            f (Fin.cons pair.1 pair.2) :=
      ((Fin.consEquiv A).sum_comp fun joint ↦
        ((pmfPi sigma) joint).toReal * f joint).symm
    _ = expect (sigma 0) fun a ↦
          expect (pmfPi (fun i : Fin n ↦ sigma i.succ)) fun tail ↦
            f (Fin.cons a tail) := by
      rw [Fintype.sum_prod_type]
      simp [expect_eq_sum, pmfPi_apply, Fin.prod_univ_succ,
        ENNReal.toReal_mul, Finset.mul_sum, mul_assoc]

/-- The expectation of an empty product is evaluation at the unique empty
assignment. -/
theorem expect_pmfPi_fin_zero {A : Fin 0 → Type*} [∀ i, Fintype (A i)]
    (sigma : ∀ i, PMF (A i)) (f : (∀ i, A i) → ℝ) :
    expect (pmfPi sigma) f = f fun i ↦ Fin.elim0 i := by
  have hsigma : sigma = fun i ↦ PMF.pure (Fin.elim0 i) := by
    funext i
    exact Fin.elim0 i
  rw [hsigma, pmfPi_pure, expect_pure]

/-- Fubini expansion of a homogeneous two-coordinate product PMF. -/
theorem expect_pmfPi_fin2 {A : Type*} [Fintype A]
    (sigma : Fin 2 → PMF A) (f : (Fin 2 → A) → ℝ) :
    expect (pmfPi sigma) f =
      expect (sigma 0) fun a ↦ expect (sigma 1) fun b ↦ f ![a, b] := by
  have hvec (a b : A) :
      Fin.cons a (Fin.cons b (fun i ↦ Fin.elim0 i)) = ![a, b] := by
    funext i
    fin_cases i <;> rfl
  rw [expect_pmfPi_fin_succ]
  simp_rw [expect_pmfPi_fin_succ]
  simp [expect_pmfPi_fin_zero, hvec]

/-- Fubini expansion of a homogeneous three-coordinate product PMF. -/
theorem expect_pmfPi_fin3 {A : Type*} [Fintype A]
    (sigma : Fin 3 → PMF A) (f : (Fin 3 → A) → ℝ) :
    expect (pmfPi sigma) f =
      expect (sigma 0) fun a ↦
        expect (sigma 1) fun b ↦
          expect (sigma 2) fun c ↦ f ![a, b, c] := by
  have hvec (a b c : A) :
      Fin.cons a (Fin.cons b (Fin.cons c fun i ↦ Fin.elim0 i)) = ![a, b, c] := by
    funext i
    fin_cases i <;> rfl
  rw [expect_pmfPi_fin_succ]
  simp_rw [expect_pmfPi_fin_succ]
  simp [expect_pmfPi_fin_zero, hvec]

/-- Fubini expansion of a homogeneous four-coordinate product PMF. -/
theorem expect_pmfPi_fin4 {A : Type*} [Fintype A]
    (sigma : Fin 4 → PMF A) (f : (Fin 4 → A) → ℝ) :
    expect (pmfPi sigma) f =
      expect (sigma 0) fun a ↦
        expect (sigma 1) fun b ↦
          expect (sigma 2) fun c ↦
            expect (sigma 3) fun d ↦ f ![a, b, c, d] := by
  have hvec (a b c d : A) :
      Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d fun i ↦ Fin.elim0 i))) =
        ![a, b, c, d] := by
    funext i
    fin_cases i <;> rfl
  rw [expect_pmfPi_fin_succ]
  simp_rw [expect_pmfPi_fin_succ]
  simp [expect_pmfPi_fin_zero, hvec]

/-- A four-coordinate Boolean vector has a true coordinate exactly when its
    true-coordinate finset is nonempty. -/
@[simp] theorem fin4_bool_true_finset_nonempty (a b c d : Bool) :
    ({who | ![a, b, c, d] who = true} : Finset (Fin 4)).Nonempty ↔
      a = true ∨ b = true ∨ c = true ∨ d = true := by
  constructor
  · rintro ⟨who, hwho⟩
    fin_cases who <;> simp_all
  · rintro (ha | hb | hc | hd)
    · exact ⟨0, by simp [ha]⟩
    · exact ⟨1, by simp [hb]⟩
    · exact ⟨2, by simp [hc]⟩
    · exact ⟨3, by simp [hd]⟩

end Math.PMFProduct
