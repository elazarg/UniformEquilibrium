import UniformEquilibrium.Quitting.Classification.LCP.PrincipalRestriction
import UniformEquilibrium.Quitting.Classification.LCP.NormalCore

noncomputable section

namespace GameTheory.QuittingLCPClassification

def negativePairMatrix (u v : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -u; -v, 0]

theorem negativePairMatrix_not_projectiveQ (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    ¬IsProjectiveQMatrix (negativePairMatrix u v) := by
  intro hQ
  obtain ⟨solution⟩ := hQ (fun _ ↦ -1)
  have hzero : solution.cemetery = 0 := by
    have h := solution.residual_nonneg 0
    have hy := solution.singleton_nonneg 1
    simp [negativePairMatrix, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    nlinarith [solution.cemetery_nonneg]
  have hx : solution.singleton 0 = 0 := by
    have h := solution.residual_nonneg 1
    have hxnonneg := solution.singleton_nonneg 0
    simp [negativePairMatrix, Matrix.cons_val_zero, Matrix.cons_val_one, hzero] at h
    nlinarith
  have hy : solution.singleton 1 = 0 := by
    have h := solution.residual_nonneg 0
    have hynonneg := solution.singleton_nonneg 1
    simp [negativePairMatrix, Matrix.cons_val_zero, Matrix.cons_val_one, hzero] at h
    nlinarith
  have htotal := solution.total
  simp [Fin.sum_univ_two, hzero, hx, hy] at htotal

variable {I : Type} [Fintype I] [DecidableEq I]

theorem normalCore_eq_univ_of_fixed_blocker
    (M : Matrix I I ℝ) (next : I → I)
    (hne : ∀ i, next i ≠ i) (hentry : ∀ i, M i (next i) ≤ 0) :
    normalCore M = Finset.univ := by
  have hlayer : ∀ n : ℕ, normalLayer M n = Finset.univ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        ext i
        simp only [mem_normalLayer_succ, ih, Finset.mem_univ, true_and, iff_true]
        exact ⟨next i, hne i, hentry i⟩
  ext i
  simp only [mem_normalCore, Finset.mem_univ, iff_true]
  intro n
  rw [hlayer n]
  exact Finset.mem_univ i

end GameTheory.QuittingLCPClassification
