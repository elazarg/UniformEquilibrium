import MathUE.CyclicChildExteriorDegree

/-! # Shared positive-charge cyclic-child fixture

The literal receiver-first matrix has one root at the displayed regular offset.
This is the positive-charge fixture used by several reward tables, not the
negative-charge exterior whose degree is zero.
-/

noncomputable section

namespace Math.CyclicChildJointPhase.SharedFixture

open Matrix Math.LinearProgramming

def matrix : Matrix (Fin 4) (Fin 4) ℝ :=
  exteriorMatrix 2 2 2 1 1 1 ![1, 1, -1]

def offset : Fin 4 → ℝ := exteriorOffset 1 1 1 1 1

def root : Fin 4 → ℝ := ![0, 1, 1, 1]

theorem matrix_eq : matrix =
    !![0, 1, 1, -1; -1, 0, -1, 2; -1, 2, 0, -1; -1, -1, 2, 0] := rfl

theorem balance_eq : balanceVector 2 2 2 1 1 1 = ![1, 1, 1] := by
  norm_num [balanceVector_eq, gap]

theorem matrix_det : matrix.det = 7 := by
  have hdet := exteriorMatrix_det (a := 2) (b := 2) (c := 2)
    (h₁ := 1) (h₂ := 1) (h₃ := 1) (by norm_num [gap]) ![1, 1, -1]
  norm_num [matrix, balance_eq, dotProduct, Fin.sum_univ_succ, gap] at hdet ⊢
  exact hdet

theorem child_inverse : (childMatrix 2 2 2)⁻¹ =
    (1 / 7 : ℝ) • !![2, 4, 1; 1, 2, 4; 4, 1, 2] := by
  rw [childMatrix_inverse]
  norm_num [gap]

/-- The deleted-pivot inverse row is not nonnegative. -/
theorem pivot_row_inverse : ![1, 1, -1] ᵥ* (childMatrix 2 2 2)⁻¹ =
    ![-1 / 7, 5 / 7, 3 / 7] := by
  rw [child_inverse]
  funext who
  fin_cases who <;> norm_num [vecMul, dotProduct, Fin.sum_univ_succ]

theorem matrix_isR0 : IsR0Matrix matrix := by
  apply exterior_isR0_of_row_balance_ne_zero (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [gap])
  norm_num [balance_eq, dotProduct, Fin.sum_univ_succ]

theorem root_residual : lcpResidual matrix offset root = ![2, 0, 0, 0] := by
  funext who
  fin_cases who <;>
    norm_num [lcpResidual, matrix_eq, offset, exteriorOffset, root,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem solution_iff (weights : Fin 4 → ℝ) :
    IsStandardLCPSolution matrix offset weights ↔ weights = root := by
  constructor
  · intro hsolution
    have hcases := exterior_positiveOffset_solution_cases
      (a := 2) (b := 2) (c := 2) (h₁ := 1) (h₂ := 1) (h₃ := 1)
      (scale := 1) (pivot := 1) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [gap]) ![1, 1, -1]
      (by norm_num [balance_eq, dotProduct, Fin.sum_univ_succ]) weights hsolution
    norm_num [balance_eq, dotProduct, Fin.sum_univ_succ] at hcases
    rcases hcases with hfirst | hsecond
    · exact hfirst
    · have hnonneg := hsolution.weight_nonneg 0
      rw [hsecond] at hnonneg
      norm_num at hnonneg
  · rintro rfl
    refine ⟨?_, ?_, ?_⟩
    · intro who
      fin_cases who <;> norm_num [root]
    · intro who
      rw [root_residual]
      fin_cases who <;> norm_num
    · intro who
      rw [root_residual]
      fin_cases who <;> norm_num [root]

theorem root_active_det :
    (matrix.toSquareBlockProp (fun who => 0 < root who)).det = 7 := by
  have hdet := exterior_childOnly_active_det
    (a := 2) (b := 2) (c := 2) (h₁ := 1) (h₂ := 1) (h₃ := 1)
    ![1, 1, -1] ![1, 1, 1] (by intro who; fin_cases who <;> norm_num)
  have hweights : exteriorBalancedWeights ![1, 1, 1] 1 0 = root := by
    funext who
    fin_cases who <;> norm_num [root, exteriorBalancedWeights]
  rw [hweights] at hdet
  norm_num [gap] at hdet
  exact hdet

theorem matrix_r0Degree_eq_one : r0Degree matrix matrix_isR0 = 1 := by
  classical
  have hstrict : ∀ weights, IsStandardLCPSolution matrix offset weights →
      ∀ who, weights who = 0 → 0 < lcpResidual matrix offset weights who := by
    intro weights hsolution who hzero
    rw [(solution_iff weights).mp hsolution] at hzero ⊢
    rw [root_residual]
    fin_cases who
    · norm_num
    · norm_num [root] at hzero
    · norm_num [root] at hzero
    · norm_num [root] at hzero
  have hnonsingular : ∀ weights, IsStandardLCPSolution matrix offset weights →
      (matrix.toSquareBlockProp (fun who => 0 < weights who)).det ≠ 0 := by
    intro weights hsolution
    rw [(solution_iff weights).mp hsolution, root_active_det]
    norm_num
  obtain ⟨roots, hroots, hsum⟩ := exists_finset_r0Degree_eq_sum_sign_det
    matrix matrix_isR0 offset hstrict hnonsingular
  have hset : roots = {root} := by
    ext weights
    rw [hroots, solution_iff]
    simp only [Finset.mem_singleton]
  rw [hsum, hset, Finset.sum_singleton, root_active_det]
  norm_num

end Math.CyclicChildJointPhase.SharedFixture
