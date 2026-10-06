import MathUE.LinearProgramming.CyclicChildSharedFixture
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # Arbitrary-label partition classification for the shared matrix

Equal block row sums force either the discrete partition or the sole pivot
with all three child players in one block. No enumeration of labelings is
assumed, and unused labels are unrestricted.
-/

noncomputable section

namespace Math.CyclicChildJointPhase.SharedFixture

variable {κ : Type*} [DecidableEq κ]

def labelRowSum (block : Fin 4 → κ) (receiver : Fin 4) (coordinate : κ) : ℝ :=
  ∑ owner, if block owner = coordinate then matrix receiver owner else 0

private theorem sum_labelRowSum (block : Fin 4 → κ) (receiver : Fin 4) :
    (∑ coordinate ∈ Finset.univ.image block, labelRowSum block receiver coordinate) =
      ∑ owner, matrix receiver owner := by
  unfold labelRowSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro owner _
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, exists_apply_eq_apply, ite_true]

private theorem total_row (receiver : Fin 4) :
    (∑ owner, matrix receiver owner) = if receiver = 0 then 1 else 0 := by
  fin_cases receiver <;> norm_num [matrix_eq, Fin.sum_univ_succ]

theorem injective_or_child_block_of_labelRowSum_eq (block : Fin 4 → κ)
    (hrows : ∀ first second, block first = block second →
      ∀ coordinate, labelRowSum block first coordinate = labelRowSum block second coordinate) :
    Function.Injective block ∨
      (block 0 ≠ block 1 ∧ block 1 = block 2 ∧ block 2 = block 3) := by
  have hpivot (player : Fin 4) (hne : player ≠ 0) : block 0 ≠ block player := by
    intro heq
    have htotal := congrArg
      (fun row : κ → ℝ => ∑ coordinate ∈ Finset.univ.image block, row coordinate)
      (funext (hrows 0 player heq))
    rw [sum_labelRowSum, sum_labelRowSum, total_row, total_row] at htotal
    simp only [ite_true, hne, ite_false] at htotal
    norm_num at htotal
  have hzeroOne := hpivot 1 (by decide)
  have hzeroTwo := hpivot 2 (by decide)
  have hzeroThree := hpivot 3 (by decide)
  by_cases honeTwo : block 1 = block 2
  · right
    refine ⟨hzeroOne, honeTwo, ?_⟩
    have heq := hrows 1 2 honeTwo (block 1)
    by_contra htwoThree
    norm_num [labelRowSum, matrix_eq, Fin.sum_univ_succ,
      hzeroOne, honeTwo, Ne.symm htwoThree] at heq
  · by_cases honeThree : block 1 = block 3
    · have heq := hrows 1 3 honeThree (block 1)
      have htwoOne := Ne.symm honeTwo
      have htwoThree : block 2 ≠ block 3 := fun h => honeTwo (honeThree.trans h.symm)
      norm_num [labelRowSum, matrix_eq, Fin.sum_univ_succ,
        hzeroOne, honeThree, htwoOne, htwoThree] at heq
    · by_cases htwoThree : block 2 = block 3
      · have heq := hrows 2 3 htwoThree (block 2)
        norm_num [labelRowSum, matrix_eq, Fin.sum_univ_succ,
          hzeroTwo, honeThree, htwoThree] at heq
      · left
        intro first second hsame
        fin_cases first <;> fin_cases second
        all_goals first | rfl | exact False.elim (hzeroOne hsame) |
          exact False.elim (hzeroTwo hsame) | exact False.elim (hzeroThree hsame) |
          exact False.elim (honeTwo hsame) | exact False.elim (honeThree hsame) |
          exact False.elim (htwoThree hsame) | exact False.elim (hzeroOne hsame.symm) |
          exact False.elim (hzeroTwo hsame.symm) | exact False.elim (hzeroThree hsame.symm) |
          exact False.elim (honeTwo hsame.symm) | exact False.elim (honeThree hsame.symm) |
          exact False.elim (htwoThree hsame.symm)

end Math.CyclicChildJointPhase.SharedFixture
