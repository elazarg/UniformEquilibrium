import MathUE.LinearProgramming.PositiveInverseOpenness

/-!
# Positive left inverses and the R0 property

An entrywise strictly positive left inverse rules out every nonzero
homogeneous complementarity solution.  In particular, a matrix with an
entrywise strictly positive actual inverse is R0.
-/

noncomputable section

namespace Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- An entrywise strictly positive left inverse forces the original matrix
to be R0. -/
theorem isR0Matrix_of_positive_leftInverse
    (matrix inverse : Matrix ι ι ℝ) (hleft : inverse * matrix = 1)
    (hpositive : HasStrictlyPositiveEntries inverse) : IsR0Matrix matrix := by
  intro weight solution
  let residual := matrix.mulVec weight
  have hresidualNonneg : ∀ i, 0 ≤ residual i := by
    intro i
    change 0 ≤ ∑ j, matrix i j * weight j
    convert solution.residual_nonneg i using 1
    simp only [lcpResidual, Pi.zero_apply, zero_add]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hinverseResidual : inverse.mulVec residual = weight := by
    dsimp only [residual]
    rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
  have hresidualZero : residual = 0 := by
    by_contra hne
    have hexists : ∃ k, 0 < residual k := by
      by_contra hnone
      push Not at hnone
      apply hne
      funext i
      exact le_antisymm (hnone i) (hresidualNonneg i)
    obtain ⟨k, hk⟩ := hexists
    have hweightPos : ∀ i, 0 < weight i := by
      intro i
      rw [← hinverseResidual]
      simp only [Matrix.mulVec]
      apply Finset.sum_pos'
      · intro j _
        exact mul_nonneg (hpositive i j).le (hresidualNonneg j)
      · exact ⟨k, Finset.mem_univ k, mul_pos (hpositive i k) hk⟩
    have hzero : ∀ i, residual i = 0 := by
      intro i
      have hcomplementary := solution.complementary i
      have heq : lcpResidual matrix 0 weight i = residual i := by
        simp [lcpResidual, residual, Matrix.mulVec, dotProduct, mul_comm]
      rw [heq] at hcomplementary
      exact (mul_eq_zero.mp hcomplementary).resolve_left (hweightPos i).ne'
    exact hne (funext hzero)
  intro i
  rw [← hinverseResidual, hresidualZero]
  simp

/-- A matrix with an entrywise strictly positive actual inverse is R0. -/
theorem isR0Matrix_of_strictlyPositiveInverse
    (matrix : Matrix ι ι ℝ) (hpositive : HasStrictlyPositiveInverse matrix) :
    IsR0Matrix matrix := by
  apply isR0Matrix_of_positive_leftInverse matrix matrix⁻¹
  · exact Matrix.nonsing_inv_mul matrix (isUnit_iff_ne_zero.mpr hpositive.1)
  · exact hpositive.2

end Math.LinearProgramming
