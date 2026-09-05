import UniformEquilibrium.Quitting.Classification.LCP.MatrixClasses
import UniformEquilibrium.Quitting.Classification.LCP.NormalCore

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def StandardLCPSolution.posScale (c : ℝ) {M : ι → ι → ℝ}
    {q : ι → ℝ} (hc : 0 < c)
    (solution : StandardLCPSolution M (fun i => q i / c)) :
    StandardLCPSolution (fun i j => c * M i j) q where
  weight := solution.weight
  weight_nonneg := solution.weight_nonneg
  residual_nonneg := by
    intro i
    have h := solution.residual_nonneg i
    have hsum : (∑ j, solution.weight j * (c * M i j)) =
        c * ∑ j, solution.weight j * M i j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hfactor : q i + ∑ j, solution.weight j * (c * M i j) =
        c * (q i / c + ∑ j, solution.weight j * M i j) := by
      rw [hsum, mul_add]
      field_simp [ne_of_gt hc]
    rw [hfactor]
    exact mul_nonneg hc.le h
  complementary := by
    intro i
    have h := solution.complementary i
    change solution.weight i *
      (q i + ∑ j, solution.weight j * (c * M i j)) = 0
    have hsum : (∑ j, solution.weight j * (c * M i j)) =
        c * ∑ j, solution.weight j * M i j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hfactor : q i + ∑ j, solution.weight j * (c * M i j) =
        c * (q i / c + ∑ j, solution.weight j * M i j) := by
      rw [hsum, mul_add]
      field_simp [ne_of_gt hc]
    rw [hfactor]
    calc
      solution.weight i * (c *
          (q i / c + ∑ j, solution.weight j * M i j)) =
          c * (solution.weight i *
            (q i / c + ∑ j, solution.weight j * M i j)) := by ring
      _ = 0 := by rw [h]; ring

omit [DecidableEq ι] in
theorem isStandardQMatrix_posScale_iff (c : ℝ) (hc : 0 < c)
    (M : ι → ι → ℝ) :
    IsStandardQMatrix (fun i j => c * M i j) ↔ IsStandardQMatrix M := by
  have forward : ∀ (d : ℝ), 0 < d → ∀ N : ι → ι → ℝ,
      IsStandardQMatrix N → IsStandardQMatrix (fun i j => d * N i j) := by
    intro d hd N hQ q
    obtain ⟨solution⟩ := hQ (fun i => q i / d)
    exact ⟨solution.posScale d hd⟩
  constructor
  · intro hscaled
    have h := forward (1 / c) (one_div_pos.mpr hc)
      (fun i j => c * M i j) hscaled
    have heq : (fun i j => (1 / c) * (c * M i j)) = M := by
      funext i j
      field_simp [ne_of_gt hc]
    rwa [heq] at h
  · exact forward c hc M

omit [DecidableEq ι] in
theorem hasHomogeneousSimplexSolution_posScale_iff (c : ℝ) (hc : 0 < c)
    (M : ι → ι → ℝ) :
    HasHomogeneousSimplexSolution (fun i j => c * M i j) ↔
      HasHomogeneousSimplexSolution M :=
  singletonLCPFeasible_smul_iff hc M

omit [DecidableEq ι] in
theorem isProjectiveQMatrix_posScale_iff (c : ℝ) (hc : 0 < c)
    (M : ι → ι → ℝ) :
    IsProjectiveQMatrix (fun i j => c * M i j) ↔ IsProjectiveQMatrix M := by
  rw [isProjectiveQMatrix_iff_standard_or_homogeneous,
    isProjectiveQMatrix_iff_standard_or_homogeneous,
    isStandardQMatrix_posScale_iff c hc M,
    hasHomogeneousSimplexSolution_posScale_iff c hc M]

theorem normalLayer_posScale (c : ℝ) (hc : 0 < c)
    (M : ι → ι → ℝ) (n : ℕ) :
    normalLayer (fun i j => c * M i j) n = normalLayer M n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      ext i
      simp only [mem_normalLayer_succ, ih]
      constructor <;> rintro ⟨hi, j, hj, hne, hsign⟩
      · have : M i j ≤ 0 := by nlinarith
        exact ⟨hi, j, hj, hne, this⟩
      · exact ⟨hi, j, hj, hne, mul_nonpos_of_nonneg_of_nonpos hc.le hsign⟩

theorem normalCore_posScale (c : ℝ) (hc : 0 < c)
    (M : ι → ι → ℝ) :
    normalCore (fun i j => c * M i j) = normalCore M := by
  ext i
  simp only [mem_normalCore, normalLayer_posScale c hc M]

omit [Fintype ι] [DecidableEq ι] in
theorem isProjectiveQBarMatrix_posScale_iff (c : ℝ) (hc : 0 < c)
    (M : ι → ι → ℝ) :
    IsProjectiveQBarMatrix (fun i j => c * M i j) ↔
      IsProjectiveQBarMatrix M := by
  constructor
  · intro h players hplayers
    have hs := h players hplayers
    change IsProjectiveQMatrix
      (fun i j : players => c * principalMatrix M players i j) at hs
    exact (isProjectiveQMatrix_posScale_iff c hc _).1 hs
  · intro h players hplayers
    have hs := h players hplayers
    change IsProjectiveQMatrix
      (fun i j : players => c * principalMatrix M players i j)
    exact (isProjectiveQMatrix_posScale_iff c hc _).2 hs

omit [Fintype ι] [DecidableEq ι] in
theorem matrix_entry_posScale_sign_iff (c : ℝ) (hc : 0 < c)
    (M : ι → ι → ℝ) (i j : ι) :
    (c * M i j < 0 ↔ M i j < 0) ∧
      (c * M i j = 0 ↔ M i j = 0) ∧
      (0 < c * M i j ↔ 0 < M i j) := by
  constructor
  · constructor <;> intro h <;> nlinarith
  constructor
  · constructor <;> intro h
    · rcases mul_eq_zero.mp h with h | h
      · exact (ne_of_gt hc h).elim
      · exact h
    · rw [h, mul_zero]
  · constructor <;> intro h <;> nlinarith

end QuittingLCPClassification
end GameTheory
