import MathUE.LinearProgramming.IrreducibleZMatrixPositiveInverse

/-! # A positive vector produces a strictly positive Z-matrix inverse

The normalized nonnegative matrix is explicitly defined by diagonal similarity.
No nonsingularity or positive diagonal assumption is supplied by the caller.
-/

noncomputable section

namespace Math.LinearProgramming

open scoped Matrix Matrix.Norms.Operator NNReal

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def zMatrixPositiveVectorContraction (matrix : Matrix ι ι ℝ) (vector : ι → ℝ) :
    Matrix ι ι ℝ :=
  1 - Matrix.diagonal (fun i => (matrix i i * vector i)⁻¹) * matrix *
    Matrix.diagonal vector

theorem zMatrixPositiveVectorContraction_nonnegative
    (matrix : Matrix ι ι ℝ) (vector : ι → ℝ)
    (hoff : ∀ i j, i ≠ j → matrix i j ≤ 0)
    (hvector : ∀ i, 0 < vector i)
    (himage : ∀ i, 0 < (matrix *ᵥ vector) i) :
    ∀ i j, 0 ≤ zMatrixPositiveVectorContraction matrix vector i j := by
  intro i j
  have hdiag := diagonal_pos_of_zMatrix_positive_vector matrix vector hoff hvector himage i
  by_cases hij : i = j
  · subst j
    simp only [zMatrixPositiveVectorContraction, Matrix.sub_apply, Matrix.one_apply,
      Matrix.mul_diagonal, Matrix.diagonal_mul]
    have hzero : (matrix i i * vector i)⁻¹ * matrix i i * vector i = 1 := by
      rw [mul_assoc, inv_mul_cancel₀ (mul_pos hdiag (hvector i)).ne']
    rw [hzero]
    norm_num
  · simp only [zMatrixPositiveVectorContraction, Matrix.sub_apply, Matrix.one_apply,
      Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [hij, ite_false, zero_sub]
    exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (mul_pos hdiag (hvector i)).le)
        (hoff i j hij)) (hvector j).le)

theorem zMatrixPositiveVectorContraction_row_sum_lt_one
    (matrix : Matrix ι ι ℝ) (vector : ι → ℝ)
    (hoff : ∀ i j, i ≠ j → matrix i j ≤ 0)
    (hvector : ∀ i, 0 < vector i)
    (himage : ∀ i, 0 < (matrix *ᵥ vector) i) (i : ι) :
    ∑ j, zMatrixPositiveVectorContraction matrix vector i j < 1 := by
  have hdiag := diagonal_pos_of_zMatrix_positive_vector matrix vector hoff hvector himage i
  have hsum : ∑ j, zMatrixPositiveVectorContraction matrix vector i j =
      1 - (matrix i i * vector i)⁻¹ * (matrix *ᵥ vector) i := by
    simp only [zMatrixPositiveVectorContraction, Matrix.sub_apply, Matrix.one_apply,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Finset.sum_sub_distrib,
      Matrix.mulVec, dotProduct, mul_assoc, ← Finset.mul_sum]
    simp
  rw [hsum]
  exact sub_lt_self _ (mul_pos (inv_pos.mpr (mul_pos hdiag (hvector i))) (himage i))

theorem zMatrixPositiveVectorContraction_norm_lt_one
    (matrix : Matrix ι ι ℝ) (vector : ι → ℝ)
    (hoff : ∀ i j, i ≠ j → matrix i j ≤ 0)
    (hvector : ∀ i, 0 < vector i)
    (himage : ∀ i, 0 < (matrix *ᵥ vector) i) :
    ‖zMatrixPositiveVectorContraction matrix vector‖ < 1 := by
  rw [Matrix.linfty_opNorm_def]
  have hnonnegative := zMatrixPositiveVectorContraction_nonnegative
    matrix vector hoff hvector himage
  have hrows : ∀ i, ∑ j, ‖zMatrixPositiveVectorContraction matrix vector i j‖₊ < 1 := by
    intro i
    have hsum := zMatrixPositiveVectorContraction_row_sum_lt_one
      matrix vector hoff hvector himage i
    have hnorm : ∀ j, ‖zMatrixPositiveVectorContraction matrix vector i j‖ =
        zMatrixPositiveVectorContraction matrix vector i j := by
      intro j
      exact Real.norm_of_nonneg (hnonnegative i j)
    apply NNReal.coe_lt_coe.mp
    simpa only [NNReal.coe_sum, coe_nnnorm, NNReal.coe_one, hnorm] using hsum
  have hsup : Finset.sup (Finset.univ : Finset ι) (fun i : ι =>
      ∑ j : ι, ‖zMatrixPositiveVectorContraction matrix vector i j‖₊) < (1 : ℝ≥0) :=
    (Finset.sup_lt_iff (by norm_num)).mpr (fun i _ => hrows i)
  exact_mod_cast hsup

/-- Irreducibility is imposed on the actual normalized matrix above. All
other hypotheses concern the raw Z-matrix and its positive vector. -/
theorem hasStrictlyPositiveInverse_of_zMatrix_positive_vector
    (matrix : Matrix ι ι ℝ) (vector : ι → ℝ)
    (hoff : ∀ i j, i ≠ j → matrix i j ≤ 0)
    (hvector : ∀ i, 0 < vector i)
    (himage : ∀ i, 0 < (matrix *ᵥ vector) i)
    (hirreducible : (zMatrixPositiveVectorContraction matrix vector).IsIrreducible) :
    HasStrictlyPositiveInverse matrix := by
  let A := zMatrixPositiveVectorContraction matrix vector
  let B : Matrix ι ι ℝ := 1 - A
  let U : Matrix ι ι ℝ := Matrix.diagonal vector
  let V : Matrix ι ι ℝ := Matrix.diagonal (fun i => matrix i i * vector i)
  let L : Matrix ι ι ℝ := Matrix.diagonal (fun i => (matrix i i * vector i)⁻¹)
  have hdiag : ∀ i, 0 < matrix i i * vector i := fun i => mul_pos
    (diagonal_pos_of_zMatrix_positive_vector matrix vector hoff hvector himage i) (hvector i)
  have hB : HasStrictlyPositiveInverse B :=
    hasStrictlyPositiveInverse_one_sub_of_irreducible_contraction A hirreducible
      (zMatrixPositiveVectorContraction_norm_lt_one matrix vector hoff hvector himage)
  have hfactor : matrix * U = V * B := by
    ext i j
    simp only [B, A, zMatrixPositiveVectorContraction, sub_sub_cancel, U, V,
      Matrix.mul_diagonal, Matrix.diagonal_mul]
    have hmatrixNe :=
      (diagonal_pos_of_zMatrix_positive_vector matrix vector hoff hvector himage i).ne'
    field_simp [hmatrixNe, (hvector i).ne']
  have hVL : V * L = 1 := by
    change Matrix.diagonal (fun i => matrix i i * vector i) *
      Matrix.diagonal (fun i => (matrix i i * vector i)⁻¹) = 1
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      have hcancel := mul_inv_cancel₀ (hdiag i).ne'
      simpa only [Matrix.diagonal_apply, Matrix.one_apply, ite_true, eq_self] using hcancel
    · simp [hij]
  have hright : matrix * (U * B⁻¹ * L) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hfactor, Matrix.mul_assoc V B B⁻¹,
      Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB.1), mul_one, hVL]
  apply hasStrictlyPositiveInverse_of_rightInverse _ _ hright
  intro i j
  simp only [U, L, Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact mul_pos (mul_pos (hvector i) (hB.2 i j)) (inv_pos.mpr (hdiag j))

end Math.LinearProgramming
