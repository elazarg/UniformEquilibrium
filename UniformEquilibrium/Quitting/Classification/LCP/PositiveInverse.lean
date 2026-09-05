import MathUE.LinearProgramming.PositiveEntries
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
  rw [← isR0Matrix_iff_not_singletonLCPFeasible]
  intro z hz
  let w := M.mulVec z
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    change 0 ≤ ∑ j, M i j * z j
    convert hz.residual_nonneg i using 1
    simp only [lcpResidual, Pi.zero_apply, zero_add]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hzw : B.mulVec w = z := by
    dsimp only [w]
    rw [Matrix.mulVec_mulVec, hBM, Matrix.one_mulVec]
  have hwZero : w = 0 := by
    by_contra hwne
    have hexists : ∃ k, 0 < w k := by
      by_contra hnone
      push Not at hnone
      apply hwne
      funext i
      exact le_antisymm (hnone i) (hw i)
    obtain ⟨k, hk⟩ := hexists
    have hzpos : ∀ i, 0 < z i := by
      intro i
      rw [← hzw]
      simp only [Matrix.mulVec]
      apply Finset.sum_pos'
      · intro j _
        exact mul_nonneg (hB i j).le (hw j)
      · exact ⟨k, Finset.mem_univ k, mul_pos (hB i k) hk⟩
    have hwzero : ∀ i, w i = 0 := by
      intro i
      have hc := hz.complementary i
      have hwi : lcpResidual M 0 z i = w i := by
        simp [lcpResidual, w, Matrix.mulVec, dotProduct, mul_comm]
      rw [hwi] at hc
      exact (mul_eq_zero.mp hc).resolve_left (ne_of_gt (hzpos i))
    exact hwne (funext hwzero)
  intro i
  rw [← hzw, hwZero]
  simp

end GameTheory.QuittingLCPClassification
