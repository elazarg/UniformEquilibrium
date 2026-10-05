import MathUE.CyclicChildJointPhaseAlgebra
import MathUE.LinearProgramming.CopositiveQ

/-! # Cyclic-child complementarity rigidity

Positive child offsets force every child coordinate to be active. The canonical
inverse then identifies every complementarity solution, rather than merely
exhibiting one candidate. Homogeneous zero-coordinate propagation is separate.
These facts do not restrict the exterior row of a larger matrix.
-/

noncomputable section

namespace Math.CyclicChildJointPhase

open Math.LinearProgramming
open scoped Matrix

theorem child_feasible_pos {a b c h₁ h₂ h₃ scale : ℝ}
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hh₃ : 0 < h₃) (hscale : 0 < scale)
    (weights : Fin 3 → ℝ) (hnonneg : ∀ who, 0 ≤ weights who)
    (hfeasible : ∀ who,
      scale * ![h₁, h₂, h₃] who ≤ (childMatrix a b c *ᵥ weights) who) :
    ∀ who, 0 < weights who := by
  have h₀ := hfeasible 0
  have h₁ := hfeasible 1
  have h₂ := hfeasible 2
  simp [childMatrix, Math.LinearProgramming.ThreeCycleInverseFormulas.directedCycleMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h₀ h₁ h₂
  have hw₀ := hnonneg 0
  have hw₁ := hnonneg 1
  have hw₂ := hnonneg 2
  have hp₀ := mul_pos hscale hh₁
  have hp₁ := mul_pos hscale hh₂
  have hp₂ := mul_pos hscale hh₃
  have hz₂ : 0 < weights 2 := by
    by_contra hnot
    have hzero := le_antisymm (le_of_not_gt hnot) hw₂
    rw [hzero, mul_zero] at h₀
    linarith
  have hz₀ : 0 < weights 0 := by
    by_contra hnot
    have hzero := le_antisymm (le_of_not_gt hnot) hw₀
    rw [hzero, mul_zero] at h₁
    linarith
  have hz₁ : 0 < weights 1 := by
    by_contra hnot
    have hzero := le_antisymm (le_of_not_gt hnot) hw₁
    rw [hzero, mul_zero] at h₂
    linarith
  intro who
  fin_cases who <;> assumption

theorem child_homogeneous_zero_or_pos {a b c : ℝ}
    (weights : Fin 3 → ℝ) (hnonneg : ∀ who, 0 ≤ weights who)
    (hfeasible : ∀ who, 0 ≤ (childMatrix a b c *ᵥ weights) who) :
    weights = 0 ∨ ∀ who, 0 < weights who := by
  have h₀ := hfeasible 0
  have h₁ := hfeasible 1
  have h₂ := hfeasible 2
  simp [childMatrix, Math.LinearProgramming.ThreeCycleInverseFormulas.directedCycleMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h₀ h₁ h₂
  have hw₀ := hnonneg 0
  have hw₁ := hnonneg 1
  have hw₂ := hnonneg 2
  by_cases hz₀ : weights 0 = 0
  · have hz₂ : weights 2 = 0 := by
      rw [hz₀, mul_zero] at h₁
      exact le_antisymm h₁ hw₂
    have hz₁ : weights 1 = 0 := by
      rw [hz₂, mul_zero] at h₀
      exact le_antisymm h₀ hw₁
    left
    funext who
    fin_cases who <;> assumption
  by_cases hz₁ : weights 1 = 0
  · have hz₀' : weights 0 = 0 := by
      rw [hz₁, mul_zero] at h₂
      exact le_antisymm h₂ hw₀
    exact (hz₀ hz₀').elim
  by_cases hz₂ : weights 2 = 0
  · have hz₁' : weights 1 = 0 := by
      rw [hz₂, mul_zero] at h₀
      exact le_antisymm h₀ hw₁
    exact (hz₁ hz₁').elim
  right
  intro who
  fin_cases who
  · exact lt_of_le_of_ne hw₀ (Ne.symm hz₀)
  · exact lt_of_le_of_ne hw₁ (Ne.symm hz₁)
  · exact lt_of_le_of_ne hw₂ (Ne.symm hz₂)

theorem child_positiveOffset_solution_eq {a b c h₁ h₂ h₃ scale : ℝ}
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hh₃ : 0 < h₃) (hscale : 0 < scale)
    (hgap : gap a b c ≠ 0) (weights : Fin 3 → ℝ)
    (hsolution : IsStandardLCPSolution (childMatrix a b c)
      (fun who => -scale * ![h₁, h₂, h₃] who) weights) :
    weights = scale • balanceVector a b c h₁ h₂ h₃ := by
  have hresidual (who : Fin 3) :
      lcpResidual (childMatrix a b c) (fun j => -scale * ![h₁, h₂, h₃] j) weights who =
        -scale * ![h₁, h₂, h₃] who + (childMatrix a b c *ᵥ weights) who := by
    simp [lcpResidual, Matrix.mulVec, dotProduct, mul_comm]
  have hpositive := child_feasible_pos hh₁ hh₂ hh₃ hscale weights
    hsolution.weight_nonneg (fun who => by
      have h := hsolution.residual_nonneg who
      rw [hresidual] at h
      linarith)
  have heq : childMatrix a b c *ᵥ weights = scale • ![h₁, h₂, h₃] := by
    funext who
    have hzero := (mul_eq_zero.mp (hsolution.complementary who)).resolve_left
      (hpositive who).ne'
    rw [hresidual] at hzero
    change (childMatrix a b c *ᵥ weights) who = scale * ![h₁, h₂, h₃] who
    linarith
  have hunit : IsUnit (childMatrix a b c).det := by
    rw [childMatrix_det]
    exact isUnit_iff_ne_zero.mpr hgap
  apply (Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr hunit))
  rw [heq, Matrix.mulVec_smul, childMatrix_mulVec_balanceVector a b c h₁ h₂ h₃ hgap]

theorem child_isR0 {a b c : ℝ} (hgap : gap a b c ≠ 0) :
    IsR0Matrix (childMatrix a b c) := by
  intro weights hsolution
  have hresidual (who : Fin 3) :
      lcpResidual (childMatrix a b c) 0 weights who =
        (childMatrix a b c *ᵥ weights) who := by
    simp [lcpResidual, Matrix.mulVec, dotProduct, mul_comm]
  obtain hzero | hpositive := child_homogeneous_zero_or_pos weights
    hsolution.weight_nonneg (fun who => by
      rw [← hresidual]
      exact hsolution.residual_nonneg who)
  · intro who
    rw [hzero]
    rfl
  have heq : childMatrix a b c *ᵥ weights = 0 := by
    funext who
    rw [← hresidual]
    exact (mul_eq_zero.mp (hsolution.complementary who)).resolve_left
      (hpositive who).ne'
  have hunit : IsUnit (childMatrix a b c).det := by
    rw [childMatrix_det]
    exact isUnit_iff_ne_zero.mpr hgap
  have hinjective := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr hunit)
  have hzero : weights = 0 := hinjective (by simpa using heq)
  intro who
  rw [hzero]
  rfl

/-- Exterior row entries are arbitrary; the child convention is receiver-first. -/
def exteriorMatrix (a b c h₁ h₂ h₃ : ℝ) (row : Fin 3 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, row 0, row 1, row 2;
    -h₁, 0, -1, a; -h₂, b, 0, -1; -h₃, -1, c, 0]

def exteriorOffset (h₁ h₂ h₃ scale pivot : ℝ) : Fin 4 → ℝ :=
  ![pivot, -scale * h₁, -scale * h₂, -scale * h₃]

def childWeights (weights : Fin 4 → ℝ) : Fin 3 → ℝ :=
  ![weights 1, weights 2, weights 3]

theorem exterior_child_solution {a b c h₁ h₂ h₃ scale pivot : ℝ}
    (row : Fin 3 → ℝ) (weights : Fin 4 → ℝ)
    (hsolution : IsStandardLCPSolution (exteriorMatrix a b c h₁ h₂ h₃ row)
      (exteriorOffset h₁ h₂ h₃ scale pivot) weights) :
    IsStandardLCPSolution (childMatrix a b c)
      (fun who => -(scale + weights 0) * ![h₁, h₂, h₃] who) (childWeights weights) := by
  have hresidual (who : Fin 3) :
      lcpResidual (childMatrix a b c)
          (fun j => -(scale + weights 0) * ![h₁, h₂, h₃] j) (childWeights weights) who =
        lcpResidual (exteriorMatrix a b c h₁ h₂ h₃ row)
          (exteriorOffset h₁ h₂ h₃ scale pivot) weights who.succ := by
    fin_cases who <;>
      simp [lcpResidual, exteriorMatrix, exteriorOffset, childWeights, childMatrix,
        Math.LinearProgramming.ThreeCycleInverseFormulas.directedCycleMatrix,
        Fin.sum_univ_succ] <;> ring
  refine ⟨?_, ?_, ?_⟩
  · intro who
    fin_cases who <;> exact hsolution.weight_nonneg _
  · intro who
    rw [hresidual]
    exact hsolution.residual_nonneg _
  · intro who
    rw [hresidual]
    have h := hsolution.complementary who.succ
    fin_cases who <;> exact h

theorem exterior_pivot_residual (a b c h₁ h₂ h₃ scale pivot : ℝ)
    (row : Fin 3 → ℝ) (weights : Fin 4 → ℝ) :
    lcpResidual (exteriorMatrix a b c h₁ h₂ h₃ row)
        (exteriorOffset h₁ h₂ h₃ scale pivot) weights 0 =
      pivot + row ⬝ᵥ childWeights weights := by
  simp [lcpResidual, exteriorMatrix, exteriorOffset, childWeights, dotProduct,
    Fin.sum_univ_succ]
  ring

theorem exterior_positiveOffset_child_eq {a b c h₁ h₂ h₃ scale pivot : ℝ}
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hh₃ : 0 < h₃) (hscale : 0 < scale)
    (hgap : gap a b c ≠ 0) (row : Fin 3 → ℝ) (weights : Fin 4 → ℝ)
    (hsolution : IsStandardLCPSolution (exteriorMatrix a b c h₁ h₂ h₃ row)
      (exteriorOffset h₁ h₂ h₃ scale pivot) weights) :
    childWeights weights = (scale + weights 0) • balanceVector a b c h₁ h₂ h₃ := by
  apply child_positiveOffset_solution_eq hh₁ hh₂ hh₃
    (add_pos_of_pos_of_nonneg hscale (hsolution.weight_nonneg 0)) hgap
  exact exterior_child_solution row weights hsolution

theorem exterior_isR0_of_row_balance_ne_zero {a b c h₁ h₂ h₃ : ℝ}
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hh₃ : 0 < h₃)
    (hgap : gap a b c ≠ 0) (row : Fin 3 → ℝ)
    (hrow : row ⬝ᵥ balanceVector a b c h₁ h₂ h₃ ≠ 0) :
    IsR0Matrix (exteriorMatrix a b c h₁ h₂ h₃ row) := by
  intro weights hsolution
  have hsolution' : IsStandardLCPSolution (exteriorMatrix a b c h₁ h₂ h₃ row)
      (exteriorOffset h₁ h₂ h₃ 0 0) weights := by
    have hoffset : exteriorOffset h₁ h₂ h₃ 0 0 = 0 := by
      funext who
      fin_cases who <;> simp [exteriorOffset]
    rw [hoffset]
    exact hsolution
  have hchild := exterior_child_solution row weights hsolution'
  by_cases hzero : weights 0 = 0
  · have hchild' : IsStandardLCPSolution (childMatrix a b c) 0
        (childWeights weights) := by
      change IsStandardLCPSolution (childMatrix a b c) (fun _ => 0) (childWeights weights)
      simpa [hzero] using hchild
    have hzeros := child_isR0 hgap (childWeights weights) hchild'
    intro who
    fin_cases who
    · exact hzero
    · exact hzeros 0
    · exact hzeros 1
    · exact hzeros 2
  have hpositive : 0 < weights 0 := lt_of_le_of_ne (hsolution.weight_nonneg 0)
    (Ne.symm hzero)
  have heq : childWeights weights = weights 0 • balanceVector a b c h₁ h₂ h₃ := by
    apply child_positiveOffset_solution_eq hh₁ hh₂ hh₃ hpositive hgap
    simpa using hchild
  have hpivot := hsolution'.complementary 0
  rw [exterior_pivot_residual, heq] at hpivot
  have hdot : row ⬝ᵥ (weights 0 • balanceVector a b c h₁ h₂ h₃) =
      weights 0 * (row ⬝ᵥ balanceVector a b c h₁ h₂ h₃) := by
    simp [dotProduct, Fin.sum_univ_succ]
    ring
  rw [hdot, zero_add] at hpivot
  have hcontradiction := (mul_eq_zero.mp hpivot).resolve_left hzero
  exact (hrow ((mul_eq_zero.mp hcontradiction).resolve_left hzero)).elim

/-- Every positive-offset solution belongs to one of the two literal families.
Admissibility of the displayed families is proved separately. -/
theorem exterior_positiveOffset_solution_cases {a b c h₁ h₂ h₃ scale pivot : ℝ}
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hh₃ : 0 < h₃) (hscale : 0 < scale)
    (hgap : gap a b c ≠ 0) (row : Fin 3 → ℝ)
    (hrow : row ⬝ᵥ balanceVector a b c h₁ h₂ h₃ ≠ 0) (weights : Fin 4 → ℝ)
    (hsolution : IsStandardLCPSolution (exteriorMatrix a b c h₁ h₂ h₃ row)
      (exteriorOffset h₁ h₂ h₃ scale pivot) weights) :
    let ν := balanceVector a b c h₁ h₂ h₃
    let second := -pivot / (row ⬝ᵥ ν) - scale
    weights = ![0, scale * ν 0, scale * ν 1, scale * ν 2] ∨
      weights = ![second, (scale + second) * ν 0,
        (scale + second) * ν 1, (scale + second) * ν 2] := by
  dsimp only
  have hchild := exterior_positiveOffset_child_eq hh₁ hh₂ hh₃ hscale hgap
    row weights hsolution
  have hcoordinate (who : Fin 3) :
      childWeights weights who =
        (scale + weights 0) * balanceVector a b c h₁ h₂ h₃ who := congrFun hchild who
  by_cases hzero : weights 0 = 0
  · left
    funext who
    fin_cases who
    · exact hzero
    · simpa [childWeights, hzero] using hcoordinate 0
    · simpa [childWeights, hzero] using hcoordinate 1
    · simpa [childWeights, hzero] using hcoordinate 2
  have hpivot := (mul_eq_zero.mp (hsolution.complementary 0)).resolve_left hzero
  rw [exterior_pivot_residual, hchild, dotProduct_smul, smul_eq_mul] at hpivot
  have hfirst : weights 0 =
      -pivot / (row ⬝ᵥ balanceVector a b c h₁ h₂ h₃) - scale := by
    apply (eq_sub_iff_add_eq).mpr
    apply (eq_div_iff hrow).mpr
    linarith
  right
  funext who
  fin_cases who
  · exact hfirst
  · simpa [childWeights, hfirst] using hcoordinate 0
  · simpa [childWeights, hfirst] using hcoordinate 1
  · simpa [childWeights, hfirst] using hcoordinate 2

def exteriorBalancedWeights (balance : Fin 3 → ℝ) (scale pivotWeight : ℝ) : Fin 4 → ℝ :=
  ![pivotWeight, (scale + pivotWeight) * balance 0,
    (scale + pivotWeight) * balance 1, (scale + pivotWeight) * balance 2]

theorem exteriorBalancedWeights_residual {a b c h₁ h₂ h₃ : ℝ}
    (hgap : gap a b c ≠ 0) (row : Fin 3 → ℝ) (scale pivot pivotWeight : ℝ) :
    lcpResidual (exteriorMatrix a b c h₁ h₂ h₃ row)
        (exteriorOffset h₁ h₂ h₃ scale pivot)
        (exteriorBalancedWeights (balanceVector a b c h₁ h₂ h₃) scale pivotWeight) =
      ![pivot + (scale + pivotWeight) * (row ⬝ᵥ balanceVector a b c h₁ h₂ h₃),
        0, 0, 0] := by
  obtain ⟨h₀, h₁, h₂⟩ := balanceVector_balances a b c h₁ h₂ h₃ hgap
  have hscaled₀ := congrArg (fun value => (scale + pivotWeight) * value) h₀
  have hscaled₁ := congrArg (fun value => (scale + pivotWeight) * value) h₁
  have hscaled₂ := congrArg (fun value => (scale + pivotWeight) * value) h₂
  funext who
  fin_cases who <;>
    simp [lcpResidual, exteriorMatrix, exteriorOffset, exteriorBalancedWeights,
      dotProduct, Fin.sum_univ_succ]
  · ring
  · nlinarith only [hscaled₀]
  · nlinarith only [hscaled₁]
  · nlinarith only [hscaled₂]

/-- The negative exterior balance gives exactly two admissible roots at a
regular positive-offset anchor, not merely two exhibited solutions. -/
theorem exterior_positiveOffset_solution_iff {a b c h₁ h₂ h₃ scale pivot : ℝ}
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hh₃ : 0 < h₃) (hscale : 0 < scale)
    (hgap : gap a b c ≠ 0)
    (hbalance : ∀ who, 0 < balanceVector a b c h₁ h₂ h₃ who)
    (row : Fin 3 → ℝ) (hrow : row ⬝ᵥ balanceVector a b c h₁ h₂ h₃ < 0)
    (hpivot : -scale * (row ⬝ᵥ balanceVector a b c h₁ h₂ h₃) < pivot)
    (weights : Fin 4 → ℝ) :
    let ν := balanceVector a b c h₁ h₂ h₃
    let second := -pivot / (row ⬝ᵥ ν) - scale
    IsStandardLCPSolution (exteriorMatrix a b c h₁ h₂ h₃ row)
        (exteriorOffset h₁ h₂ h₃ scale pivot) weights ↔
      weights = exteriorBalancedWeights ν scale 0 ∨
        weights = exteriorBalancedWeights ν scale second := by
  dsimp only
  let ν := balanceVector a b c h₁ h₂ h₃
  let charge := row ⬝ᵥ ν
  let second := -pivot / charge - scale
  have hcharge : charge < 0 := hrow
  have hsecond : 0 < second := by
    change 0 < -pivot / charge - scale
    apply sub_pos.mpr
    apply (lt_div_iff_of_neg hcharge).mpr
    linarith
  have hsecondResidual : pivot + (scale + second) * charge = 0 := by
    dsimp [second]
    field_simp [hcharge.ne]
    ring
  constructor
  · intro hsolution
    have hcases := exterior_positiveOffset_solution_cases hh₁ hh₂ hh₃ hscale hgap
      row hrow.ne weights hsolution
    simpa [exteriorBalancedWeights] using hcases
  · rintro (rfl | rfl)
    · have hresidual := exteriorBalancedWeights_residual
        (h₁ := h₁) (h₂ := h₂) (h₃ := h₃) hgap row scale pivot 0
      refine ⟨?_, ?_, ?_⟩
      · intro who
        fin_cases who <;> dsimp [exteriorBalancedWeights]
        · exact le_rfl
        · simpa only [add_zero] using (mul_pos hscale (hbalance 0)).le
        · simpa only [add_zero] using (mul_pos hscale (hbalance 1)).le
        · simpa only [add_zero] using (mul_pos hscale (hbalance 2)).le
      · intro who
        rw [congrFun hresidual who]
        fin_cases who
        · change 0 ≤ pivot + (scale + 0) * (row ⬝ᵥ ν)
          linarith only [hpivot]
        · exact le_rfl
        · exact le_rfl
        · exact le_rfl
      · intro who
        rw [congrFun hresidual who]
        fin_cases who <;> simp [exteriorBalancedWeights]
    · have hresidual := exteriorBalancedWeights_residual
        (h₁ := h₁) (h₂ := h₂) (h₃ := h₃) hgap row scale pivot second
      have hsum : 0 < scale + second := add_pos hscale hsecond
      refine ⟨?_, ?_, ?_⟩
      · intro who
        fin_cases who <;> dsimp [exteriorBalancedWeights]
        · exact hsecond.le
        · exact (mul_pos hsum (hbalance 0)).le
        · exact (mul_pos hsum (hbalance 1)).le
        · exact (mul_pos hsum (hbalance 2)).le
      · intro who
        rw [congrFun hresidual who]
        fin_cases who
        · change 0 ≤ pivot + (scale + second) * charge
          rw [hsecondResidual]
        · exact le_rfl
        · exact le_rfl
        · exact le_rfl
      · intro who
        rw [congrFun hresidual who]
        fin_cases who
        · change second * (pivot + (scale + second) * charge) = 0
          rw [hsecondResidual, mul_zero]
        · simp
        · simp
        · simp

theorem exteriorMatrix_det {a b c h₁ h₂ h₃ : ℝ}
    (hgap : gap a b c ≠ 0) (row : Fin 3 → ℝ) :
    (exteriorMatrix a b c h₁ h₂ h₃ row).det =
      gap a b c * (row ⬝ᵥ balanceVector a b c h₁ h₂ h₃) := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Matrix.det_fin_three, exteriorMatrix, Fin.sum_univ_succ,
    balanceVector_eq, dotProduct, Fin.succAbove]
  field_simp [hgap]
  ring

theorem exterior_not_isR0_of_row_balance_zero {a b c h₁ h₂ h₃ : ℝ}
    (hgap : gap a b c ≠ 0)
    (hbalance : ∀ who, 0 ≤ balanceVector a b c h₁ h₂ h₃ who)
    (row : Fin 3 → ℝ) (hrow : row ⬝ᵥ balanceVector a b c h₁ h₂ h₃ = 0) :
    ¬IsR0Matrix (exteriorMatrix a b c h₁ h₂ h₃ row) := by
  let weights := exteriorBalancedWeights (balanceVector a b c h₁ h₂ h₃) 0 1
  have hoffset : exteriorOffset h₁ h₂ h₃ 0 0 = 0 := by
    funext who
    fin_cases who <;> simp [exteriorOffset]
  have hresidual : lcpResidual (exteriorMatrix a b c h₁ h₂ h₃ row) 0 weights = 0 := by
    have h := exteriorBalancedWeights_residual
      (h₁ := h₁) (h₂ := h₂) (h₃ := h₃) hgap row 0 0 1
    rw [hoffset] at h
    exact h.trans (by
      funext who
      fin_cases who <;> simp [hrow])
  have hsolution : IsStandardLCPSolution (exteriorMatrix a b c h₁ h₂ h₃ row)
      0 weights := by
    refine ⟨?_, ?_, ?_⟩
    · intro who
      fin_cases who <;> dsimp [weights, exteriorBalancedWeights]
      · exact zero_le_one
      · simpa using hbalance 0
      · simpa using hbalance 1
      · simpa using hbalance 2
    · intro who
      rw [congrFun hresidual who]
      exact le_rfl
    · intro who
      rw [congrFun hresidual who]
      exact mul_zero _
  intro hR0
  have hzero := hR0 weights hsolution 0
  norm_num [weights, exteriorBalancedWeights] at hzero

end Math.CyclicChildJointPhase
