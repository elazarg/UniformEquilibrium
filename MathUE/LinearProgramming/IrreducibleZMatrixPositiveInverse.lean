import MathUE.LinearProgramming.PositiveInverseOpenness
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! # Positive inverses from contracting nonnegative matrices

The Neumann-series criterion below derives nonsingularity, rather than assuming
it. Its power-positivity premise is supplied by irreducibility. The positive
vector Z-matrix criterion will use diagonal similarity to supply contraction.
-/

noncomputable section

namespace Math.LinearProgramming

open scoped Matrix Matrix.Norms.Operator

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A strictly positive image of a positive vector forces a Z-matrix's
diagonal to be strictly positive. -/
theorem diagonal_pos_of_zMatrix_positive_vector
    (matrix : Matrix ι ι ℝ) (vector : ι → ℝ)
    (hoff : ∀ i j, i ≠ j → matrix i j ≤ 0)
    (hvector : ∀ i, 0 < vector i)
    (himage : ∀ i, 0 < (matrix *ᵥ vector) i) (i : ι) :
    0 < matrix i i := by
  have hrest : ∑ j ∈ Finset.univ.erase i, matrix i j * vector j ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    exact mul_nonpos_of_nonpos_of_nonneg
      (hoff i j (Ne.symm (Finset.ne_of_mem_erase hj))) (hvector j).le
  have hsplit : (matrix *ᵥ vector) i =
      matrix i i * vector i + ∑ j ∈ Finset.univ.erase i, matrix i j * vector j := by
    simp only [Matrix.mulVec, dotProduct]
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hproduct : 0 < matrix i i * vector i := by
    have := himage i
    rw [hsplit] at this
    linarith
  exact pos_of_mul_pos_left hproduct (hvector i).le

/-- A contracting nonnegative matrix with a positive power at every entry
has a strictly positive Neumann inverse. Zero-dimensional matrices are allowed. -/
theorem hasStrictlyPositiveInverse_one_sub_of_nonnegative_contraction
    (matrix : Matrix ι ι ℝ) (hnonnegative : ∀ i j, 0 ≤ matrix i j)
    (hnorm : ‖matrix‖ < 1)
    (hpowers : ∀ i j, ∃ power : ℕ, 0 < (matrix ^ power) i j) :
    HasStrictlyPositiveInverse (1 - matrix) := by
  let series : Matrix ι ι ℝ := ∑' power : ℕ, matrix ^ power
  have hsummable : Summable (fun power : ℕ => matrix ^ power) :=
    summable_geometric_of_norm_lt_one hnorm
  have hright : (1 - matrix) * series = 1 := mul_neg_geom_series matrix hnorm
  apply hasStrictlyPositiveInverse_of_rightInverse _ series hright
  intro i j
  have hnonnegPow (power : ℕ) : ∀ row column, 0 ≤ (matrix ^ power) row column := by
    induction power with
    | zero =>
      intro row column
      simp only [pow_zero, Matrix.one_apply]
      split_ifs <;> norm_num
    | succ power ih =>
      intro row column
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (ih row k) (hnonnegative k column)
  have hentry : HasSum (fun power : ℕ => (matrix ^ power) i j) (series i j) :=
    Pi.hasSum.mp (Pi.hasSum.mp hsummable.hasSum i) j
  obtain ⟨power, hpositive⟩ := hpowers i j
  have hpos := hentry.summable.tsum_pos (fun n => hnonnegPow n i j) power hpositive
  rwa [hentry.tsum_eq] at hpos

theorem hasStrictlyPositiveInverse_one_sub_of_irreducible_contraction
    (matrix : Matrix ι ι ℝ) (hirreducible : matrix.IsIrreducible)
    (hnorm : ‖matrix‖ < 1) : HasStrictlyPositiveInverse (1 - matrix) := by
  apply hasStrictlyPositiveInverse_one_sub_of_nonnegative_contraction matrix
    hirreducible.1 hnorm
  intro i j
  obtain ⟨power, _, hpositive⟩ :=
    (Matrix.isIrreducible_iff_exists_pow_pos hirreducible.1).mp hirreducible i j
  exact ⟨power, hpositive⟩

end Math.LinearProgramming
