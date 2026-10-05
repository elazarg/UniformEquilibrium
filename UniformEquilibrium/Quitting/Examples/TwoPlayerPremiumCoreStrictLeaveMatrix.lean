import MathUE.LinearProgramming.R0DegreeSum
import UniformEquilibrium.Quitting.Classification.LCP.ElementaryMatrixObstructions
import UniformEquilibrium.Quitting.Classification.LCP.QuittingRewardAdapter
import UniformEquilibrium.Quitting.Examples.TwoPlayerPremiumCoreStrictLeave

/-! # Singleton matrix and degree of the strict-leave premium-core example

The homogeneous LCP has only the zero solution. The entire solution set at
one regular offset is a singleton with positive active determinant, so the
canonical root-sum formula gives degree one and standard Q.
-/

noncomputable section

namespace GameTheory.TwoPlayerPremiumCoreStrictLeave

open Math.LinearProgramming QuittingLCPClassification

def matrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, -1, -1, 3; -1, 0, -1, 2; -1, 2, 0, -1; -1, -1, 2, 0]

theorem quittingSingletonMatrix_eq :
    quittingSingletonMatrix reward = matrix := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num +decide [quittingSingletonMatrix, reward, coalitionCode, matrix]

theorem normalCore_eq_univ : normalCore matrix = Finset.univ := by
  apply normalCore_eq_univ_of_fixed_blocker matrix
    (![1, 0, 0, 0] : Fin 4 → Fin 4)
  · intro who
    fin_cases who <;> decide
  · intro who
    fin_cases who <;> norm_num [matrix]

theorem residual_eq (offset root : Fin 4 → ℝ) :
    lcpResidual matrix offset root =
      ![offset 0 - root 1 - root 2 + 3 * root 3,
        offset 1 - root 0 - root 2 + 2 * root 3,
        offset 2 - root 0 + 2 * root 1 - root 3,
        offset 3 - root 0 - root 1 + 2 * root 2] := by
  funext who
  fin_cases who <;>
    norm_num [lcpResidual, matrix, Fin.sum_univ_succ] <;> ring

/-- The homogeneous LCP has only the zero vector. -/
theorem matrix_isR0 : IsR0Matrix matrix := by
  intro root hroot
  have hn0 := hroot.weight_nonneg (0 : Fin 4)
  have hn1 := hroot.weight_nonneg (1 : Fin 4)
  have hn2 := hroot.weight_nonneg (2 : Fin 4)
  have hn3 := hroot.weight_nonneg (3 : Fin 4)
  have hw1 := hroot.residual_nonneg (1 : Fin 4)
  have hw2 := hroot.residual_nonneg (2 : Fin 4)
  have hw3 := hroot.residual_nonneg (3 : Fin 4)
  have hc0 := hroot.complementary (0 : Fin 4)
  norm_num [residual_eq] at hw1 hw2 hw3 hc0
  by_cases h1 : 0 < root 1
  · by_cases h2 : 0 < root 2
    · by_cases h3 : 0 < root 3
      · have he1 := (mul_eq_zero.mp (hroot.complementary (1 : Fin 4))).resolve_left
          h1.ne'
        have he2 := (mul_eq_zero.mp (hroot.complementary (2 : Fin 4))).resolve_left
          h2.ne'
        have he3 := (mul_eq_zero.mp (hroot.complementary (3 : Fin 4))).resolve_left
          h3.ne'
        norm_num [residual_eq] at he1 he2 he3
        have hx1 : root 1 = root 0 := by linarith
        have hx2 : root 2 = root 0 := by linarith
        have hx3 : root 3 = root 0 := by linarith
        rw [hx1, hx2, hx3] at hc0
        have hx0 : root 0 = 0 := by
          rcases hc0 with hzero | hzero
          · exact hzero
          · linarith
        intro who
        fin_cases who <;> dsimp only <;> linarith
      · have hn3' := le_of_not_gt h3
        intro who
        fin_cases who <;> dsimp only <;> linarith
    · have hn2' := le_of_not_gt h2
      intro who
      fin_cases who <;> dsimp only <;> linarith
  · have hn1' := le_of_not_gt h1
    intro who
    fin_cases who
    · change root 0 = 0
      linarith
    · change root 1 = 0
      linarith
    · change root 2 = 0
      linarith
    · change root 3 = 0
      linarith

theorem not_singletonLCPFeasible : ¬ SingletonLCPFeasible matrix :=
  (isR0Matrix_iff_not_singletonLCPFeasible matrix).mp matrix_isR0

def testOffset : Fin 4 → ℝ := ![1, -1, -1, -1]

def testRoot : Fin 4 → ℝ := ![0, 1, 1, 1]

theorem testRoot_isSolution :
    IsStandardLCPSolution matrix testOffset testRoot := by
  refine ⟨?_, ?_, ?_⟩ <;> intro who <;> fin_cases who <;>
    norm_num [residual_eq, testOffset, testRoot]

/-- The entire actual solution set at the test offset is a singleton. -/
theorem test_solution_iff (root : Fin 4 → ℝ) :
    IsStandardLCPSolution matrix testOffset root ↔ root = testRoot := by
  constructor
  · intro hroot
    have hn0 := hroot.weight_nonneg (0 : Fin 4)
    have hn1 := hroot.weight_nonneg (1 : Fin 4)
    have hn2 := hroot.weight_nonneg (2 : Fin 4)
    have hn3 := hroot.weight_nonneg (3 : Fin 4)
    have hw1 := hroot.residual_nonneg (1 : Fin 4)
    have hw2 := hroot.residual_nonneg (2 : Fin 4)
    have hw3 := hroot.residual_nonneg (3 : Fin 4)
    norm_num [residual_eq, testOffset] at hw1 hw2 hw3
    have h1 : 0 < root 1 := by linarith
    have h2 : 0 < root 2 := by linarith
    have h3 : 0 < root 3 := by linarith
    have he1 := (mul_eq_zero.mp (hroot.complementary (1 : Fin 4))).resolve_left h1.ne'
    have he2 := (mul_eq_zero.mp (hroot.complementary (2 : Fin 4))).resolve_left h2.ne'
    have he3 := (mul_eq_zero.mp (hroot.complementary (3 : Fin 4))).resolve_left h3.ne'
    norm_num [residual_eq, testOffset] at he1 he2 he3
    have hx1 : root 1 = 1 + root 0 := by linarith
    have hx2 : root 2 = 1 + root 0 := by linarith
    have hx3 : root 3 = 1 + root 0 := by linarith
    have hc0 := hroot.complementary (0 : Fin 4)
    norm_num [residual_eq, testOffset] at hc0
    rw [hx1, hx2, hx3] at hc0
    have hx0 : root 0 = 0 := by
      rcases hc0 with hzero | hzero
      · exact hzero
      · linarith
    funext who
    fin_cases who <;> norm_num [testRoot] <;> linarith
  · rintro rfl
    exact testRoot_isSolution

theorem testRoot_inactiveResidual :
    lcpResidual matrix testOffset testRoot 0 = 2 := by
  norm_num [residual_eq, testOffset, testRoot]

theorem test_strict (root : Fin 4 → ℝ)
    (hroot : IsStandardLCPSolution matrix testOffset root) :
    ∀ who, root who = 0 → 0 < lcpResidual matrix testOffset root who := by
  rw [(test_solution_iff root).mp hroot]
  intro who hzero
  fin_cases who <;>
    norm_num [testRoot, testOffset, residual_eq] at *

theorem testRoot_active_det :
    (matrix.toSquareBlockProp (fun who => 0 < testRoot who)).det = 7 := by
  classical
  rw [← det_lcpSelectedMatrix matrix testRoot, Matrix.det_succ_row_zero]
  norm_num [lcpSelectedMatrix, matrix, testRoot, Matrix.det_fin_three,
    Fin.sum_univ_succ, Fin.succAbove, Matrix.submatrix, Matrix.one_apply]

theorem matrix_r0Degree_eq_one : r0Degree matrix matrix_isR0 = 1 := by
  classical
  obtain ⟨roots, hroots, hdegree⟩ :=
    exists_finset_r0Degree_eq_sum_sign_det matrix matrix_isR0 testOffset test_strict
      (fun root hroot => by
        rw [(test_solution_iff root).mp hroot, testRoot_active_det]
        norm_num)
  have hrootsEq : roots = {testRoot} := by
    ext root
    rw [hroots, test_solution_iff, Finset.mem_singleton]
  rw [hrootsEq, Finset.sum_singleton, testRoot_active_det] at hdegree
  norm_num at hdegree
  exact hdegree

theorem matrix_isStandardQ : IsStandardQ matrix := by
  apply isStandardQ_of_r0Degree_ne_zero matrix matrix_isR0
  rw [matrix_r0Degree_eq_one]
  norm_num

end GameTheory.TwoPlayerPremiumCoreStrictLeave
