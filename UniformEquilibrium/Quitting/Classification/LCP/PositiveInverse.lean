import MathUE.LinearProgramming.PositiveInverseR0
import UniformEquilibrium.Quitting.Classification.LCP.CopositiveQBridge

noncomputable section

namespace GameTheory.QuittingLCPClassification

open Math.LinearProgramming

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Standard-Q transfers from a right inverse to the original matrix. -/
theorem isStandardQMatrix_of_rightInverse_standardQ
    (M B : Matrix I I ℝ) (hMB : M * B = 1)
    (hQ : IsStandardQMatrix B) : IsStandardQMatrix M := by
  intro q
  obtain ⟨solution⟩ := hQ (-(B.mulVec q))
  let z : I → ℝ := fun i ↦
    -(B.mulVec q) i + ∑ j, solution.weight j * B i j
  have hzdef : z = -(B.mulVec q) + B.mulVec solution.weight := by
    funext i
    simp only [z, Pi.add_apply, Pi.neg_apply, Matrix.mulVec]
    apply congrArg (fun x ↦ -(∑ x, B i x * q x) + x)
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hMBq : M.mulVec (B.mulVec q) = q := by
    rw [Matrix.mulVec_mulVec, hMB, Matrix.one_mulVec]
  have hMBweight : M.mulVec (B.mulVec solution.weight) = solution.weight := by
    rw [Matrix.mulVec_mulVec, hMB, Matrix.one_mulVec]
  have hz : M.mulVec z = solution.weight - q := by
    rw [hzdef, Matrix.mulVec_add, Matrix.mulVec_neg, hMBq, hMBweight]
    abel
  refine ⟨{
    weight := z
    weight_nonneg := solution.residual_nonneg
    residual_nonneg := ?_
    complementary := ?_
  }⟩
  · intro i
    rw [show q i + ∑ j, z j * M i j = q i + M.mulVec z i by
      simp only [Matrix.mulVec]
      apply congrArg (fun x ↦ q i + x)
      apply Finset.sum_congr rfl
      intro j _
      ring]
    rw [hz]
    simp
    exact solution.weight_nonneg i
  · intro i
    have hresidual : q i + ∑ j, z j * M i j = solution.weight i := by
      rw [show q i + ∑ j, z j * M i j = q i + M.mulVec z i by
        simp only [Matrix.mulVec]
        apply congrArg (fun x ↦ q i + x)
        apply Finset.sum_congr rfl
        intro j _
        ring]
      rw [hz]
      simp
    rw [hresidual]
    have hc := solution.complementary i
    change solution.weight i * z i = 0 at hc
    nlinarith

theorem isStandardQMatrix_of_positive_rightInverse
    (M B : Matrix I I ℝ) (hMB : M * B = 1)
    (hB : HasStrictlyPositiveEntries B) : IsStandardQMatrix M := by
  apply isStandardQMatrix_of_rightInverse_standardQ M B hMB
  exact isStandardQMatrix_of_copositive_of_isR0Matrix B
    (copositive_of_positiveEntries B hB) (isR0Matrix_of_positiveEntries B hB)

theorem noHomogeneousSimplexSolution_of_positive_leftInverse
    (M B : Matrix I I ℝ) (hBM : B * M = 1)
    (hB : HasStrictlyPositiveEntries B) : ¬HasHomogeneousSimplexSolution M := by
  exact (isR0Matrix_iff_not_singletonLCPFeasible M).mp
    (isR0Matrix_of_positive_leftInverse M B hBM hB)

end GameTheory.QuittingLCPClassification
