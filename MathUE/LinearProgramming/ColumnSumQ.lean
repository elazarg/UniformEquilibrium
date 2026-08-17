/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.LinearAlgebra.Matrix.Circulant
import MathUE.LinearProgramming.CopositiveQ

/-!
# Column sums, row sums, and the standard `Q` property

Two elementary obstructions to the textbook nonhomogeneous LCP of
`MathUE/LinearProgramming/CopositiveQ.lean`, both read off from the aggregate
of a matrix rather than from any of its entries, in the repository's row
convention `(Mz) i = ∑ j, z j * M i j`.

* If every column of `M` sums to a nonpositive number, then the total residual
  `𝟙ᵀ(q + Mz)` at a nonnegative `z` never exceeds `𝟙ᵀq`.  Taking `q = -𝟙`
  makes that total strictly negative, so some coordinate of the residual is
  negative and `LCP(M, -𝟙)` is unsolvable: `M` is not a `Q`-matrix.
* If every row of `M` sums to zero, the uniform simplex point has vanishing
  residual and therefore solves the homogeneous simplex LCP of
  `MathUE/LinearProgramming/SingletonLCP.lean`.

Both apply to the circulant matrix of a margin vector on a finite additive
group, whose row sums and column sums are all equal to the total margin.

## Main definitions

* `rowCirculant` — the circulant matrix of a margin vector, in the row
  convention: row `i`, column `j` carries the margin at the difference `j - i`

## Main results

* `not_isStandardQ_of_forall_column_sum_nonpos` — nonpositive column sums
  obstruct standard `Q`
* `singletonLCPFeasible_of_forall_row_sum_eq_zero` — vanishing row sums make
  the uniform simplex point a homogeneous solution
* `exists_ne_zero_margin_nonpos` — a margin vector vanishing at `0` with
  nonpositive total has a nonpositive value at some nonzero group element
* `not_isStandardQ_rowCirculant` and `singletonLCPFeasible_rowCirculant` — the
  two obstructions for a circulant matrix, in terms of its total margin
-/

noncomputable section

namespace Math.LinearProgramming

variable {ι : Type*} [Fintype ι]

/-! ## Nonpositive column sums obstruct standard `Q` -/

/-- **The all-ones right-hand side.**  If no column of `M` has positive total,
then `LCP(M, -𝟙)` is unsolvable: summing the residual over all coordinates
gives `σ·∑z - card ι` with `σ·∑z ≤ 0`, which is negative, while a solution
would make every coordinate of the residual nonnegative. -/
theorem not_standardLCPSolvable_neg_one_of_forall_column_sum_nonpos [Nonempty ι]
    (M : ι → ι → ℝ) (hcol : ∀ j, (∑ i, M i j) ≤ 0) :
    ¬StandardLCPSolvable M (fun _ => -1) := by
  classical
  rintro ⟨z, hz⟩
  have hsum : (0 : ℝ) ≤ ∑ i, lcpResidual M (fun _ => -1) z i :=
    Finset.sum_nonneg fun i _ => hz.residual_nonneg i
  have hsplit : (∑ i, lcpResidual M (fun _ => (-1 : ℝ)) z i) =
      (∑ _i : ι, (-1 : ℝ)) + ∑ i, ∑ j, z j * M i j := by
    rw [← Finset.sum_add_distrib]
    rfl
  have hswap : (∑ i, ∑ j, z j * M i j) = ∑ j, z j * ∑ i, M i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
  have hnonpos : (∑ j, z j * ∑ i, M i j) ≤ 0 :=
    Finset.sum_nonpos fun j _ =>
      mul_nonpos_of_nonneg_of_nonpos (hz.weight_nonneg j) (hcol j)
  have hconst : (∑ _i : ι, (-1 : ℝ)) = -(Fintype.card ι : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [hsplit, hswap, hconst] at hsum
  linarith

/-- **Nonpositive column sums obstruct standard `Q`.**  A `Q`-matrix solves
`LCP(M, q)` for every right-hand side, and the all-ones right-hand side is
already out of reach. -/
theorem not_isStandardQ_of_forall_column_sum_nonpos [Nonempty ι]
    (M : ι → ι → ℝ) (hcol : ∀ j, (∑ i, M i j) ≤ 0) : ¬IsStandardQ M :=
  fun hQ =>
    not_standardLCPSolvable_neg_one_of_forall_column_sum_nonpos M hcol (hQ _)

/-- The constant-column-sum form: a matrix all of whose columns sum to one
nonpositive number `σ` is not a standard `Q`-matrix. -/
theorem not_isStandardQ_of_column_sums_eq [Nonempty ι] (M : ι → ι → ℝ) {σ : ℝ}
    (hcol : ∀ j, (∑ i, M i j) = σ) (hσ : σ ≤ 0) : ¬IsStandardQ M :=
  not_isStandardQ_of_forall_column_sum_nonpos M fun j => (hcol j).trans_le hσ

/-! ## Vanishing row sums give a homogeneous simplex solution -/

/-- **The uniform homogeneous witness.**  If every row of `M` sums to zero,
the uniform simplex point has zero residual, hence is nonnegative and
complementary: the homogeneous simplex LCP is feasible. -/
theorem singletonLCPFeasible_of_forall_row_sum_eq_zero [Nonempty ι]
    (M : ι → ι → ℝ) (hrow : ∀ i, (∑ j, M i j) = 0) : SingletonLCPFeasible M := by
  classical
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hmem : (fun _ : ι => (Fintype.card ι : ℝ)⁻¹) ∈ stdSimplex ℝ ι := by
    refine ⟨fun _ => inv_nonneg.mpr hcard.le, ?_⟩
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hcard.ne'
  refine ⟨⟨_, hmem⟩, fun i => ?_, fun i => ?_⟩
  · have hzero : singletonLCPResidual M ⟨_, hmem⟩ i = 0 := by
      show (∑ j, (Fintype.card ι : ℝ)⁻¹ * M i j) = 0
      rw [← Finset.mul_sum, hrow i, mul_zero]
    rw [hzero]
  · have hzero : singletonLCPResidual M ⟨_, hmem⟩ i = 0 := by
      show (∑ j, (Fintype.card ι : ℝ)⁻¹ * M i j) = 0
      rw [← Finset.mul_sum, hrow i, mul_zero]
    rw [hzero, mul_zero]

/-! ## Circulant matrices of a margin vector -/

variable [AddCommGroup ι]

/-- The circulant matrix of a margin vector `m`, in the repository's row
convention: row `i`, column `j` carries the margin at the group difference
`j - i`.  It is the transpose of `Matrix.circulant m`. -/
def rowCirculant (m : ι → ℝ) : ι → ι → ℝ := fun i j => m (j - i)

omit [Fintype ι] in
@[simp] theorem rowCirculant_apply (m : ι → ℝ) (i j : ι) :
    rowCirculant m i j = m (j - i) := rfl

omit [Fintype ι] in
/-- The row-convention circulant is the transpose of Mathlib's column
convention. -/
theorem rowCirculant_eq_transpose_circulant (m : ι → ℝ) :
    rowCirculant m = (Matrix.circulant m).transpose := rfl

omit [Fintype ι] in
@[simp] theorem rowCirculant_diagonal (m : ι → ℝ) (i : ι) :
    rowCirculant m i i = m 0 := by
  rw [rowCirculant_apply, sub_self]

/-- Every column of a circulant matrix sums to the total margin. -/
theorem sum_rowCirculant_column (m : ι → ℝ) (j : ι) :
    (∑ i, rowCirculant m i j) = ∑ d, m d :=
  Fintype.sum_equiv (Equiv.subLeft j) _ _ fun _ => rfl

/-- Every row of a circulant matrix sums to the total margin. -/
theorem sum_rowCirculant_row (m : ι → ℝ) (i : ι) :
    (∑ j, rowCirculant m i j) = ∑ d, m d :=
  Fintype.sum_equiv (Equiv.subRight i) _ _ fun _ => rfl

/-- A margin vector vanishing at the group identity and with nonpositive total
is nonpositive at some nonzero group element. -/
theorem exists_ne_zero_margin_nonpos [Nontrivial ι] {m : ι → ℝ} (hzero : m 0 = 0)
    (hσ : (∑ d, m d) ≤ 0) : ∃ d : ι, d ≠ 0 ∧ m d ≤ 0 := by
  classical
  by_contra hcon
  have hpos : ∀ d ∈ Finset.univ.erase (0 : ι), 0 < m d := by
    intro d hd
    exact not_le.mp fun h => hcon ⟨d, (Finset.mem_erase.mp hd).1, h⟩
  have hne : (Finset.univ.erase (0 : ι)).Nonempty := by
    obtain ⟨a, ha⟩ := exists_ne (0 : ι)
    exact ⟨a, Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩⟩
  have hsplit : (∑ d, m d) = m 0 + ∑ d ∈ Finset.univ.erase (0 : ι), m d :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
  have hsum_pos : 0 < ∑ d ∈ Finset.univ.erase (0 : ι), m d :=
    Finset.sum_pos hpos hne
  rw [hsplit, hzero] at hσ
  linarith

/-- **The circulant non-`Q` obstruction.**  A circulant matrix with
nonpositive total margin is not a standard `Q`-matrix. -/
theorem not_isStandardQ_rowCirculant [Nonempty ι] (m : ι → ℝ)
    (hσ : (∑ d, m d) ≤ 0) : ¬IsStandardQ (rowCirculant m) :=
  not_isStandardQ_of_column_sums_eq _ (sum_rowCirculant_column m) hσ

/-- **The circulant homogeneous witness.**  A circulant matrix with vanishing
total margin admits the uniform homogeneous simplex solution. -/
theorem singletonLCPFeasible_rowCirculant [Nonempty ι] (m : ι → ℝ)
    (hσ : (∑ d, m d) = 0) : SingletonLCPFeasible (rowCirculant m) :=
  singletonLCPFeasible_of_forall_row_sum_eq_zero _ fun i =>
    (sum_rowCirculant_row m i).trans hσ

end Math.LinearProgramming
