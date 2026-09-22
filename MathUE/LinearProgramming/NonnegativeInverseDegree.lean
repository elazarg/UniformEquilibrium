import MathUE.LinearProgramming.R0DegreeSum

/-!
# Complementarity degree for matrices with nonnegative inverse

An invertible matrix with entrywise nonnegative inverse has exactly one LCP
root at offset minus one: its inverse times the all-ones vector. Every
coordinate of this root is positive, since an invertible nonnegative matrix
has no zero row. With the separate R0 hypothesis, the canonical degree is
the sign of the full determinant.

Uniqueness at this one offset is not asserted to imply R0. Zero entries in
the inverse are allowed, and dimension zero is included.
-/

noncomputable section

namespace Math.LinearProgramming

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every row sum of an invertible entrywise nonnegative inverse is positive. -/
theorem inverse_mulVec_one_pos_of_nonnegative
    (matrix : Matrix ι ι ℝ) (hdet : matrix.det ≠ 0)
    (hinverse : ∀ row column, 0 ≤ matrix⁻¹ row column) (who : ι) :
    0 < matrix⁻¹.mulVec (1 : ι → ℝ) who := by
  have hpositive : ∃ column, 0 < matrix⁻¹ who column := by
    by_contra hnone
    have hzero (column : ι) : matrix⁻¹ who column = 0 := by
      exact le_antisymm (le_of_not_gt (fun hpos => hnone ⟨column, hpos⟩))
        (hinverse who column)
    have hproduct := congrFun (congrFun
      (Matrix.nonsing_inv_mul matrix (isUnit_iff_ne_zero.mpr hdet)) who) who
    simp only [Matrix.mul_apply, hzero, zero_mul, Finset.sum_const_zero,
      Matrix.one_apply_eq] at hproduct
    exact zero_ne_one hproduct
  obtain ⟨column, hcolumn⟩ := hpositive
  change 0 < ∑ coordinate, matrix⁻¹ who coordinate * (1 : ℝ)
  simp only [mul_one]
  exact Finset.sum_pos' (fun coordinate _ => hinverse who coordinate)
    ⟨column, Finset.mem_univ column, hcolumn⟩

/-- The unique actual root at minus one; no R0 premise is required. -/
theorem isStandardLCPSolution_neg_one_iff_of_nonnegative_inverse
    (matrix : Matrix ι ι ℝ) (hdet : matrix.det ≠ 0)
    (hinverse : ∀ row column, 0 ≤ matrix⁻¹ row column) (root : ι → ℝ) :
    IsStandardLCPSolution matrix (-1) root ↔ root = matrix⁻¹.mulVec 1 := by
  have hunit : IsUnit matrix.det := isUnit_iff_ne_zero.mpr hdet
  have hpositive := inverse_mulVec_one_pos_of_nonnegative matrix hdet hinverse
  constructor
  · intro hroot
    have hproduct : matrix.mulVec root = 1 + lcpResidual matrix (-1) root := by
      rw [lcpResidual_eq_add_mulVec]
      abel
    have hidentity : root = matrix⁻¹.mulVec 1 +
        matrix⁻¹.mulVec (lcpResidual matrix (-1) root) := by
      calc
        root = matrix⁻¹.mulVec (matrix.mulVec root) := by
          rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
        _ = _ := by rw [hproduct, Matrix.mulVec_add]
    have hrootPositive (who : ι) : 0 < root who := by
      have hnonnegative : 0 ≤ matrix⁻¹.mulVec (lcpResidual matrix (-1) root) who :=
        Finset.sum_nonneg (fun coordinate _ =>
          mul_nonneg (hinverse who coordinate) (hroot.residual_nonneg coordinate))
      have hcoordinate := congrFun hidentity who
      simp only [Pi.add_apply] at hcoordinate
      linarith [hpositive who]
    have hresidual : lcpResidual matrix (-1) root = 0 := by
      funext who
      exact (mul_eq_zero.mp (hroot.complementary who)).resolve_left
        (hrootPositive who).ne'
    simpa only [hresidual, Matrix.mulVec_zero, add_zero] using hidentity
  · rintro rfl
    have hresidual : lcpResidual matrix (-1) (matrix⁻¹.mulVec 1) = 0 := by
      rw [lcpResidual_eq_add_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec, neg_add_cancel]
    refine ⟨fun who => (hpositive who).le, ?_, ?_⟩
    · intro who
      rw [hresidual]
      exact le_rfl
    · intro who
      rw [hresidual]
      exact mul_zero _

/-- For an R0 matrix with nonnegative inverse, the one-root test computes the
canonical degree as the full determinant sign. R0 remains a separate premise. -/
theorem r0Degree_eq_sign_det_of_nonnegative_inverse
    {n : ℕ} (matrix : Matrix (Fin n) (Fin n) ℝ) (hR0 : IsR0Matrix matrix)
    (hdet : matrix.det ≠ 0) (hinverse : ∀ row column, 0 ≤ matrix⁻¹ row column) :
    r0Degree matrix hR0 = (SignType.sign matrix.det : ℤ) := by
  classical
  let root := matrix⁻¹.mulVec (1 : Fin n → ℝ)
  have hpositive : ∀ who, 0 < root who :=
    inverse_mulVec_one_pos_of_nonnegative matrix hdet hinverse
  have hrootIff := isStandardLCPSolution_neg_one_iff_of_nonnegative_inverse
    matrix hdet hinverse
  have hactiveDet : (matrix.toSquareBlockProp (fun who => 0 < root who)).det =
      matrix.det := by
    have hselected : lcpSelectedMatrix matrix root = matrix := by
      ext who coordinate
      simp only [lcpSelectedMatrix, ite_eq_left (hpositive who)]
    exact (det_lcpSelectedMatrix matrix root).symm.trans (congrArg Matrix.det hselected)
  obtain ⟨roots, hroots, hdegree⟩ := exists_finset_r0Degree_eq_sum_sign_det
    matrix hR0 (-1) (fun candidate hcandidate who hzero => by
      have hequal := (hrootIff candidate).mp hcandidate
      have hpos : 0 < candidate who := hequal.symm ▸ hpositive who
      exact False.elim (hpos.ne' hzero)) (fun candidate hcandidate => by
        have hequal := (hrootIff candidate).mp hcandidate
        change candidate = root at hequal
        rw [hequal, hactiveDet]
        exact hdet)
  have hrootsEq : roots = {root} := by
    ext candidate
    rw [hroots, hrootIff, Finset.mem_singleton]
  simpa only [hrootsEq, Finset.sum_singleton, hactiveDet] using hdegree

end Math.LinearProgramming
