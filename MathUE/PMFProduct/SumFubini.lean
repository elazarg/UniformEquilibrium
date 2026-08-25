/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.Basic

/-!
# Fubini over a sum-indexed finite product PMF

An independent product indexed by `I ⊕ J` is the iterated independent product
over its two coordinate blocks.  The result is stated for arbitrary finite
coordinate values and real expectations.
-/

namespace Math.PMFProduct

open Math.Probability Math.ProbabilityMassFunction

/-- Split the expectation of a finite product indexed by `I ⊕ J` into the
iterated expectations over the two coordinate blocks. -/
theorem expect_pmfPi_sum
    {I J A : Type*} [Fintype I] [Fintype J] [Fintype A]
    (sigma : I ⊕ J → PMF A) (f : (I ⊕ J → A) → ℝ) :
    expect (pmfPi sigma) f =
      expect (pmfPi (fun i : I => sigma (.inl i))) fun old =>
        expect (pmfPi (fun j : J => sigma (.inr j))) fun fresh =>
          f (Sum.elim old fresh) := by
  classical
  rw [expect_eq_sum]
  let e := Equiv.sumPiEquivProdPi (fun _ : I ⊕ J => A)
  calc
    (∑ joint, ((pmfPi sigma) joint).toReal * f joint) =
        ∑ pair : (I → A) × (J → A),
          ((pmfPi sigma) (e.symm pair)).toReal * f (e.symm pair) := by
      simpa using e.sum_comp
        (fun pair => ((pmfPi sigma) (e.symm pair)).toReal * f (e.symm pair))
    _ = expect (pmfPi (fun i : I => sigma (.inl i))) fun old =>
          expect (pmfPi (fun j : J => sigma (.inr j))) fun fresh =>
            f (Sum.elim old fresh) := by
      have he (old : I → A) (fresh : J → A) :
          e.symm (old, fresh) = Sum.elim old fresh := rfl
      rw [Fintype.sum_prod_type]
      simp_rw [he]
      simp [expect_eq_sum, pmfPi_apply, Fintype.prod_sum_type,
        ENNReal.toReal_mul, Finset.mul_sum, mul_assoc]

end Math.PMFProduct
