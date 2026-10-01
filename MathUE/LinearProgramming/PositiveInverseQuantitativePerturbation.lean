import MathUE.LinearProgramming.PositiveInverseOpenness
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quantitative matrix inverse perturbation in induced row-sum norm

Invertibility uses the existing normed-ring geometric unit. The resolvent
identity and triangle inequality give the literal error `ε / (1 - ε)` when
the old inverse has norm at most one. Determinant positivity is transported
along the actual invertible straight segment, not supplied as a premise.
-/

noncomputable section

namespace Math.LinearProgramming

open scoped Matrix.Norms.Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The operator norm is bounded by a common upper bound for all absolute row sums. -/
theorem matrix_operator_norm_le_of_rowSum_le
    (matrix : Matrix ι ι ℝ) (bound : ℝ) (hbound : 0 ≤ bound)
    (hrow : ∀ row, ∑ column, ‖matrix row column‖ ≤ bound) : ‖matrix‖ ≤ bound := by
  rw [Matrix.linfty_opNorm_def]
  have hrowNN (row : ι) : (∑ column, ‖matrix row column‖₊) ≤ ⟨bound, hbound⟩ := by
    change ((∑ column, ‖matrix row column‖₊ : NNReal) : ℝ) ≤ bound
    simpa only [NNReal.coe_sum, coe_nnnorm] using hrow row
  exact NNReal.coe_le_coe.mpr (Finset.sup_le (fun row _ => hrowNN row))

/-- Every absolute row sum is bounded by the induced row-sum norm. -/
theorem matrix_rowSum_le_operator_norm (matrix : Matrix ι ι ℝ) (row : ι) :
    (∑ column, ‖matrix row column‖) ≤ ‖matrix‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h := NNReal.coe_le_coe.mpr (Finset.le_sup
    (f := fun who : ι => ∑ col, ‖matrix who col‖₊) (Finset.mem_univ row))
  simpa only [NNReal.coe_sum, coe_nnnorm] using h

/-- Each entry is bounded by the same induced row-sum norm. -/
theorem matrix_entry_norm_le_operator_norm (matrix : Matrix ι ι ℝ) (row column : ι) :
    ‖matrix row column‖ ≤ ‖matrix‖ := by
  have hentry : ‖matrix row column‖ ≤ ∑ who, ‖matrix row who‖ :=
    Finset.single_le_sum (f := fun who => ‖matrix row who‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ column)
  exact hentry.trans (matrix_rowSum_le_operator_norm matrix row)

/-- The existing geometric unit makes every sufficiently small actual perturbation invertible. -/
theorem isUnit_matrix_add_of_inverse_mul_norm_lt_one
    (matrix change : Matrix ι ι ℝ) (hdet : matrix.det ≠ 0)
    (hsmall : ‖matrix⁻¹ * change‖ < 1) : IsUnit (matrix + change) := by
  have hunit : IsUnit matrix.det := isUnit_iff_ne_zero.mpr hdet
  have hfactor : matrix + change = matrix * (1 + matrix⁻¹ * change) := by
    rw [mul_add, mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv matrix hunit, one_mul]
  rw [hfactor]
  apply ((Matrix.isUnit_iff_isUnit_det matrix).mpr hunit).mul
  let factor := Units.oneSub (-(matrix⁻¹ * change)) (by simpa only [norm_neg] using hsmall)
  have hvalue : (factor : Matrix ι ι ℝ) = 1 + matrix⁻¹ * change := by
    change (Units.oneSub (-(matrix⁻¹ * change)) _).val = 1 + matrix⁻¹ * change
    rw [Units.val_oneSub, sub_neg_eq_add]
  have hfactorUnit : IsUnit (factor : Matrix ι ι ℝ) := factor.isUnit
  rw [hvalue] at hfactorUnit
  exact hfactorUnit

private theorem norm_resolvent_sub_le {R : Type*} [NormedRing R]
    (old new change : R) (hbound : ‖old‖ ≤ 1) (error : ℝ) (herror : error < 1)
    (hchange : ‖change‖ ≤ error) (hresolvent : new - old = -(new * change * old)) :
    ‖new - old‖ ≤ error / (1 - error) := by
  have hnonnegative : 0 ≤ error := (norm_nonneg _).trans hchange
  have hnorm : ‖new‖ ≤ ‖new - old‖ + 1 := by
    calc
      _ = ‖(new - old) + old‖ := by rw [sub_add_cancel]
      _ ≤ ‖new - old‖ + ‖old‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl hbound
  have hresolved : ‖new - old‖ ≤ error * (‖new - old‖ + 1) := by
    calc
      _ = ‖new * change * old‖ := by rw [hresolvent, norm_neg]
      _ ≤ ‖new‖ * ‖change‖ * ‖old‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (‖new - old‖ + 1) * error * 1 := by
        apply mul_le_mul
        · exact mul_le_mul hnorm hchange (norm_nonneg _) (by positivity)
        · exact hbound
        · exact norm_nonneg _
        · positivity
      _ = _ := by ring
  apply (le_div_iff₀ (by linarith : 0 < 1 - error)).mpr
  nlinarith

/-- A literal resolvent error, without differentiability or a supplied perturbed inverse. -/
theorem norm_matrix_inverse_add_sub_le
    (matrix change : Matrix ι ι ℝ) (hdet : matrix.det ≠ 0)
    (hbound : ‖matrix⁻¹‖ ≤ 1) (error : ℝ) (herror : error < 1)
    (hchange : ‖change‖ ≤ error) :
    ‖(matrix + change)⁻¹ - matrix⁻¹‖ ≤ error / (1 - error) := by
  have hsmall : ‖matrix⁻¹ * change‖ < 1 := by
    calc
      _ ≤ ‖matrix⁻¹‖ * ‖change‖ := norm_mul_le _ _
      _ ≤ 1 * error := mul_le_mul hbound hchange (norm_nonneg _) (by norm_num)
      _ < 1 := by simpa only [one_mul] using herror
  have hunit := isUnit_matrix_add_of_inverse_mul_norm_lt_one matrix change hdet hsmall
  have hnewDet := (Matrix.isUnit_iff_isUnit_det (matrix + change)).mp hunit
  have hproduct : (matrix + change)⁻¹ * matrix =
      1 - (matrix + change)⁻¹ * change := by
    have h := Matrix.nonsing_inv_mul (matrix + change) hnewDet
    rw [mul_add] at h
    exact eq_sub_of_add_eq h
  have hresolvent : (matrix + change)⁻¹ - matrix⁻¹ =
      -((matrix + change)⁻¹ * change * matrix⁻¹) := by
    calc
      _ = (matrix + change)⁻¹ * (matrix * matrix⁻¹) - matrix⁻¹ := by
        rw [Matrix.mul_nonsing_inv matrix (isUnit_iff_ne_zero.mpr hdet), mul_one]
      _ = ((matrix + change)⁻¹ * matrix) * matrix⁻¹ - matrix⁻¹ := by
        rw [Matrix.mul_assoc]
      _ = (1 - (matrix + change)⁻¹ * change) * matrix⁻¹ - matrix⁻¹ := by
        rw [hproduct]
      _ = _ := by rw [sub_mul, one_mul, sub_sub_cancel_left]
  exact norm_resolvent_sub_le matrix⁻¹ (matrix + change)⁻¹ change
    hbound error herror hchange hresolvent

/-- Positivity of the determinant survives along the same small perturbation segment. -/
theorem det_matrix_add_pos_of_inverse_norm_le_one
    (matrix change : Matrix ι ι ℝ) (hdet : 0 < matrix.det)
    (hbound : ‖matrix⁻¹‖ ≤ 1) (error : ℝ) (herror : error < 1)
    (hchange : ‖change‖ ≤ error) : 0 < (matrix + change).det := by
  have hsegment (time : ℝ) (htime : time ∈ Set.Icc (0 : ℝ) 1) :
      (matrix + time • change).det ≠ 0 := by
    have hscaled : ‖time • change‖ ≤ error := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg htime.1]
      calc
        _ ≤ 1 * ‖change‖ := mul_le_mul_of_nonneg_right htime.2 (norm_nonneg _)
        _ ≤ error := by simpa only [one_mul] using hchange
    have hsmall : ‖matrix⁻¹ * (time • change)‖ < 1 := by
      calc
        _ ≤ ‖matrix⁻¹‖ * ‖time • change‖ := norm_mul_le _ _
        _ ≤ 1 * error := mul_le_mul hbound hscaled (norm_nonneg _) (by norm_num)
        _ < 1 := by simpa only [one_mul] using herror
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      (isUnit_matrix_add_of_inverse_mul_norm_lt_one matrix (time • change) hdet.ne' hsmall))
  have hcontinuous : Continuous (fun time : ℝ => (matrix + time • change).det) :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  by_contra hnot
  have hzero : (0 : ℝ) ∈ Set.Icc
      (matrix + (1 : ℝ) • change).det (matrix + (0 : ℝ) • change).det := by
    simpa only [one_smul, zero_smul, add_zero] using
      (show 0 ∈ Set.Icc (matrix + change).det matrix.det from
        ⟨le_of_not_gt hnot, hdet.le⟩)
  obtain ⟨time, htime, hvalue⟩ :=
    intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcontinuous.continuousOn hzero
  exact hsegment time htime hvalue

end Math.LinearProgramming
