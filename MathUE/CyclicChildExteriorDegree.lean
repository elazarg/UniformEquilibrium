import MathUE.CyclicChildComplementarity
import MathUE.LinearProgramming.R0DegreeSum

/-! # Actual degree zero for a negative cyclic-child exterior balance

The canonical complementarity census supplies every root at the displayed
regular offset. Its child-only root contributes +1, and its fully active root
contributes -1. No chosen root set, R0 certificate or degree value is an input.
-/

noncomputable section

namespace Math.CyclicChildJointPhase

open Matrix Math.LinearProgramming

theorem exterior_childOnly_active_det {a b c h₁ h₂ h₃ : ℝ}
    (row : Fin 3 → ℝ) (ν : Fin 3 → ℝ) (hν : ∀ who, 0 < ν who) :
    ((exteriorMatrix a b c h₁ h₂ h₃ row).toSquareBlockProp
      (fun who => 0 < exteriorBalancedWeights ν 1 0 who)).det = gap a b c := by
  rw [← det_lcpSelectedMatrix]
  have hselected : lcpSelectedMatrix (exteriorMatrix a b c h₁ h₂ h₃ row)
      (exteriorBalancedWeights ν 1 0) =
      !![1, 0, 0, 0; -h₁, 0, -1, a; -h₂, b, 0, -1; -h₃, -1, c, 0] := by
    funext who coordinate
    fin_cases who <;> fin_cases coordinate <;>
      simp [lcpSelectedMatrix, exteriorBalancedWeights, exteriorMatrix,
        hν 0, hν 1, hν 2]
  rw [hselected, Matrix.det_succ_row_zero]
  norm_num [Matrix.det_fin_three, Fin.sum_univ_succ, Fin.succAbove, gap]
  ring

theorem exterior_fullyActive_active_det {a b c h₁ h₂ h₃ : ℝ}
    (row : Fin 3 → ℝ) (ν : Fin 3 → ℝ) (hν : ∀ who, 0 < ν who)
    (pivot : ℝ) (hpivot : 0 < pivot) :
    ((exteriorMatrix a b c h₁ h₂ h₃ row).toSquareBlockProp
      (fun who => 0 < exteriorBalancedWeights ν 1 pivot who)).det =
      (exteriorMatrix a b c h₁ h₂ h₃ row).det := by
  rw [← det_lcpSelectedMatrix]
  congr 1
  funext who coordinate
  have hpositive : 0 < exteriorBalancedWeights ν 1 pivot who := by
    fin_cases who <;> dsimp [exteriorBalancedWeights]
    · exact hpivot
    · exact mul_pos (by linarith) (hν 0)
    · exact mul_pos (by linarith) (hν 1)
    · exact mul_pos (by linarith) (hν 2)
  exact ite_eq_left hpositive

theorem exterior_r0Degree_eq_zero {a b c h₁ h₂ h₃ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hh₃ : 0 < h₃) (hgap : 0 < gap a b c)
    (row : Fin 3 → ℝ) (hrow : row ⬝ᵥ balanceVector a b c h₁ h₂ h₃ < 0) :
    ∃ hR0 : IsR0Matrix (exteriorMatrix a b c h₁ h₂ h₃ row),
      r0Degree (exteriorMatrix a b c h₁ h₂ h₃ row) hR0 = 0 := by
  classical
  let ν := balanceVector a b c h₁ h₂ h₃
  let charge := row ⬝ᵥ ν
  let pivot := 1 - charge
  let second := -pivot / charge - 1
  let firstRoot := exteriorBalancedWeights ν 1 0
  let secondRoot := exteriorBalancedWeights ν 1 second
  let matrix := exteriorMatrix a b c h₁ h₂ h₃ row
  let offset := exteriorOffset h₁ h₂ h₃ 1 pivot
  have hν : ∀ who, 0 < ν who := balanceVector_pos ha hb hc hh₁ hh₂ hh₃ hgap
  have hcharge : charge < 0 := hrow
  have hpivot : -1 * charge < pivot := by dsimp [pivot]; linarith
  have hsecond : 0 < second := by
    apply sub_pos.mpr
    apply (lt_div_iff_of_neg hcharge).mpr
    dsimp [pivot]
    linarith
  have hsource (root : Fin 4 → ℝ) :
      IsStandardLCPSolution matrix offset root ↔
        root = firstRoot ∨ root = secondRoot :=
    exterior_positiveOffset_solution_iff hh₁ hh₂ hh₃ (by norm_num)
      hgap.ne' hν row hrow hpivot root
  have hsecondPos (who : Fin 4) : 0 < secondRoot who := by
    fin_cases who <;> dsimp [secondRoot, exteriorBalancedWeights]
    · exact hsecond
    · exact mul_pos (by linarith) (hν 0)
    · exact mul_pos (by linarith) (hν 1)
    · exact mul_pos (by linarith) (hν 2)
  have hfirstDet : (matrix.toSquareBlockProp (fun who => 0 < firstRoot who)).det =
      gap a b c := exterior_childOnly_active_det row ν hν
  have hsecondDet : (matrix.toSquareBlockProp (fun who => 0 < secondRoot who)).det =
      gap a b c * charge :=
    (exterior_fullyActive_active_det row ν hν second hsecond).trans
      (exteriorMatrix_det hgap.ne' row)
  have hnegative : gap a b c * charge < 0 := mul_neg_of_pos_of_neg hgap hcharge
  have hstrict : ∀ root, IsStandardLCPSolution matrix offset root →
      ∀ who, root who = 0 → 0 < lcpResidual matrix offset root who := by
    intro root hroot who hzero
    rcases (hsource root).mp hroot with rfl | rfl
    · have hresidual := exteriorBalancedWeights_residual
        (h₁ := h₁) (h₂ := h₂) (h₃ := h₃) hgap.ne' row 1 pivot 0
      fin_cases who
      · change 0 < lcpResidual (exteriorMatrix a b c h₁ h₂ h₃ row)
          (exteriorOffset h₁ h₂ h₃ 1 pivot)
          (exteriorBalancedWeights (balanceVector a b c h₁ h₂ h₃) 1 0) 0
        rw [congrFun hresidual 0]
        change 0 < pivot + (1 + 0) * charge
        dsimp [pivot]
        linarith
      · have hpos : 0 < firstRoot 1 := by simpa [firstRoot, exteriorBalancedWeights] using hν 0
        exact (hpos.ne' hzero).elim
      · have hpos : 0 < firstRoot 2 := by simpa [firstRoot, exteriorBalancedWeights] using hν 1
        exact (hpos.ne' hzero).elim
      · have hpos : 0 < firstRoot 3 := by simpa [firstRoot, exteriorBalancedWeights] using hν 2
        exact (hpos.ne' hzero).elim
    · exact ((hsecondPos who).ne' hzero).elim
  have hnonsingular : ∀ root, IsStandardLCPSolution matrix offset root →
      (matrix.toSquareBlockProp (fun who => 0 < root who)).det ≠ 0 := by
    intro root hroot
    rcases (hsource root).mp hroot with rfl | rfl
    · exact hfirstDet ▸ hgap.ne'
    · exact hsecondDet ▸ hnegative.ne
  have hR0 : IsR0Matrix matrix :=
    exterior_isR0_of_row_balance_ne_zero hh₁ hh₂ hh₃ hgap.ne' row hrow.ne
  obtain ⟨roots, hroots, hsum⟩ :=
    exists_finset_r0Degree_eq_sum_sign_det matrix hR0 offset hstrict hnonsingular
  have hset : roots = {firstRoot, secondRoot} := by
    ext root
    rw [hroots, hsource]
    simp only [Finset.mem_insert, Finset.mem_singleton]
  have hdistinct : firstRoot ≠ secondRoot := by
    intro hequal
    have hcoordinate := congrFun hequal 0
    have hzero : firstRoot 0 = 0 := by simp [firstRoot, exteriorBalancedWeights]
    have hpositive := hsecondPos 0
    rw [← hcoordinate, hzero] at hpositive
    exact (lt_irrefl 0 hpositive)
  refine ⟨hR0, ?_⟩
  rw [hsum, hset, Finset.sum_pair hdistinct, hfirstDet, hsecondDet,
    sign_pos hgap, sign_neg hnegative]
  norm_num

end Math.CyclicChildJointPhase
