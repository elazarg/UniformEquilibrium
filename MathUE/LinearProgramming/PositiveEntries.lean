import MathUE.LinearProgramming.CopositiveQCorollaries

/-! # Positive-entry matrices and strict copositivity -/

noncomputable section

namespace Math.LinearProgramming

variable {I : Type} [Fintype I] [DecidableEq I]

def HasStrictlyPositiveEntries (B : Matrix I I ℝ) : Prop :=
  ∀ i j, 0 < B i j

omit [DecidableEq I] in
theorem quadratic_pos_of_positiveEntries
    (B : Matrix I I ℝ) (hB : HasStrictlyPositiveEntries B)
    (z : I → ℝ) (hz : ∀ i, 0 ≤ z i) (hne : z ≠ 0) :
    0 < ∑ i, z i * ∑ j, z j * B i j := by
  have hexists : ∃ k, 0 < z k := by
    by_contra hnone
    push Not at hnone
    apply hne
    funext i
    exact le_antisymm (hnone i) (hz i)
  obtain ⟨k, hk⟩ := hexists
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (hz i) (Finset.sum_nonneg fun j _ ↦
      mul_nonneg (hz j) (hB i j).le)
  · refine ⟨k, Finset.mem_univ k, mul_pos hk ?_⟩
    apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (hz j) (hB k j).le
    · exact ⟨k, Finset.mem_univ k, mul_pos hk (hB k k)⟩

omit [DecidableEq I] in
theorem copositive_of_positiveEntries
    (B : Matrix I I ℝ) (hB : HasStrictlyPositiveEntries B) : IsCopositive B := by
  intro z hz
  by_cases hzero : z = 0
  · simp [hzero]
  · exact (quadratic_pos_of_positiveEntries B hB z hz hzero).le

omit [DecidableEq I] in
theorem isR0Matrix_of_strictQuadratic
    (B : Matrix I I ℝ)
    (hstrict : ∀ z : I → ℝ, (∀ i, 0 ≤ z i) → z ≠ 0 →
      0 < ∑ i, z i * ∑ j, z j * B i j) : IsR0Matrix B := by
  intro z hz
  have hsumZero : (∑ i, z i * ∑ j, z j * B i j) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simpa [lcpResidual_zero] using hz.complementary i
  have hzero : z = 0 := by
    by_contra hne
    have := hstrict z hz.weight_nonneg hne
    linarith
  intro i
  exact congrFun hzero i

omit [DecidableEq I] in
theorem isR0Matrix_of_positiveEntries
    (B : Matrix I I ℝ) (hB : HasStrictlyPositiveEntries B) : IsR0Matrix B :=
  isR0Matrix_of_strictQuadratic B (quadratic_pos_of_positiveEntries B hB)

end Math.LinearProgramming
