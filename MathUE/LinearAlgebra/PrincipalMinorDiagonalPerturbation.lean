/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Diagonal perturbations and principal minors

The determinant of a scalar diagonal perturbation is the generating
polynomial of the principal minors.  This is the elementary identity needed
to justify that a positive diagonal perturbation of a `P₀` matrix is a
`P` matrix.
-/

namespace Math.LinearAlgebra

open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The determinant of `M + r I` is the sum of the principal minors of `M`,
weighted by the complementary powers of `r`.  The empty principal minor is
definitionally the determinant of the unique empty matrix, hence one. -/
theorem det_add_smul_one_eq_sum_principalMinors
    (M : Matrix ι ι R) (r : R) :
    (M + r • (1 : Matrix ι ι R)).det =
      ∑ s : Finset ι, r ^ (Fintype.card ι - s.card) *
        (M.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)).det := by
  let D := (detRowAlternating : (ι → R) [⋀^ι]→ₗ[R] R)
  change D (fun i ↦ M i + (r • (1 : Matrix ι ι R)) i) = _
  conv_lhs => rw [show
    (fun i ↦ M i + (r • (1 : Matrix ι ι R)) i) =
      (fun i ↦ M i) + (fun i ↦ (r • (1 : Matrix ι ι R)) i) from rfl]
  conv_lhs => rw [D.map_add_univ]
  apply Finset.sum_congr rfl
  intro s _
  have hrow :
      s.piecewise (fun i ↦ M i)
          (fun i ↦ (r • (1 : Matrix ι ι R)) i) =
        fun i ↦ (if i ∈ s then 1 else r) •
          s.piecewise (fun i ↦ M i) (fun i ↦ (1 : Matrix ι ι R) i) i := by
    funext i j
    simp only [Finset.piecewise, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hrow, D.map_smul_univ]
  change (∏ i, if i ∈ s then 1 else r) *
      det (Matrix.of <| s.piecewise M.row (1 : Matrix ι ι R).row) = _
  rw [Matrix.det_piecewise_one_eq_submatrix_det]
  congr 1
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  apply congrArg (r ^ ·)
  have hfilter : Finset.univ.filter (fun x : ι ↦ x ∉ s) = sᶜ := by
    ext x
    simp
  exact congrArg Finset.card hfilter |>.trans (Finset.card_compl s)

/-- A positive scalar diagonal perturbation has positive determinant when
all principal minors of the original real matrix are nonnegative. -/
theorem det_add_smul_one_pos_of_principalMinors_nonneg
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (M : Matrix ι ι K) {r : K} (hr : 0 < r)
    (hminor : ∀ s : Finset ι,
      0 ≤ (M.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)).det) :
    0 < (M + r • (1 : Matrix ι ι K)).det := by
  rw [det_add_smul_one_eq_sum_principalMinors]
  apply Finset.sum_pos'
  · intro s _
    exact mul_nonneg (pow_nonneg hr.le _) (hminor s)
  · refine ⟨∅, Finset.mem_univ _, ?_⟩
    simp
    exact pow_pos hr _

end Math.LinearAlgebra
