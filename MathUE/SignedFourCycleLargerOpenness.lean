import MathUE.SignedFourCycleStrictOpenness
import Mathlib.Topology.Instances.Matrix

/-! # Polynomial larger-branch matrix tests

The transfer inequality is cleared with the strictly positive successor
denominators. Thus openness uses polynomial entries and the determinant,
without a spectral-root continuity or supplied eigenvector premise.
-/

noncomputable section

namespace Math

local notation "FourMatrix" => Matrix (Fin 4) (Fin 4) ℝ

def signedFourCycleLargerDGap (matrix : FourMatrix) : ℝ :=
  (matrix 0 2 * matrix 1 3 + (-matrix 1 2) * matrix 0 3) * matrix 2 1 -
    (-matrix 0 1) * (-matrix 1 2) * (-matrix 2 3)

def HasSignedFourCycleLargerTests (matrix : FourMatrix) : Prop :=
  (∀ player : Fin 4, matrix player (player + 1) < 0) ∧
  (∀ player : Fin 4, 0 < matrix player (player + 3)) ∧
  matrix 0 2 < 0 ∧ 0 < matrix 1 3 ∧ matrix 2 0 < 0 ∧ 0 < matrix 3 1 ∧
  0 < signedFourCycleLargerDGap matrix ∧ 0 < matrix.det

theorem continuous_signedFourCycleLargerDGap :
    Continuous (fun matrix : FourMatrix => signedFourCycleLargerDGap matrix) := by
  unfold signedFourCycleLargerDGap
  fun_prop

theorem isOpen_hasSignedFourCycleLargerTests :
    IsOpen {matrix : FourMatrix | HasSignedFourCycleLargerTests matrix} := by
  have hsuccessor : IsOpen {matrix : FourMatrix |
      ∀ player : Fin 4, matrix player (player + 1) < 0} := by
    have heq : {matrix : FourMatrix | ∀ player : Fin 4,
        matrix player (player + 1) < 0} =
        ⋂ player : Fin 4, {matrix : FourMatrix | matrix player (player + 1) < 0} := by
      ext matrix
      simp
    rw [heq]
    apply isOpen_iInter_of_finite
    intro player
    have hcoord : Continuous (fun matrix : FourMatrix => matrix player (player + 1)) :=
      continuous_apply_apply player (player + 1)
    exact isOpen_lt hcoord continuous_const
  have hpredecessor : IsOpen {matrix : FourMatrix |
      ∀ player : Fin 4, 0 < matrix player (player + 3)} := by
    have heq : {matrix : FourMatrix | ∀ player : Fin 4,
        0 < matrix player (player + 3)} =
        ⋂ player : Fin 4, {matrix : FourMatrix | 0 < matrix player (player + 3)} := by
      ext matrix
      simp
    rw [heq]
    apply isOpen_iInter_of_finite
    intro player
    have hcoord : Continuous (fun matrix : FourMatrix => matrix player (player + 3)) :=
      continuous_apply_apply player (player + 3)
    exact isOpen_lt continuous_const hcoord
  exact hsuccessor.inter (hpredecessor.inter
    ((isOpen_lt (continuous_apply_apply 0 2) continuous_const).inter
    ((isOpen_lt continuous_const (continuous_apply_apply 1 3)).inter
    ((isOpen_lt (continuous_apply_apply 2 0) continuous_const).inter
    ((isOpen_lt continuous_const (continuous_apply_apply 3 1)).inter
    ((isOpen_lt continuous_const continuous_signedFourCycleLargerDGap).inter
      (isOpen_lt continuous_const continuous_id.matrix_det)))))))

/-- The cleared strict test is exactly the original transfer inequality. -/
theorem lowerRight_gt_one_iff_largerDGap_pos {matrix : FourMatrix}
    (hzero : matrix 0 1 < 0) (hone : matrix 1 2 < 0) (htwo : matrix 2 3 < 0) :
    1 < (signedFourCycleCoefficientsOfMatrix matrix).lowerRight ↔
      0 < signedFourCycleLargerDGap matrix := by
  have hbzero : 0 < -matrix 0 1 := neg_pos.mpr hzero
  have hbone : 0 < -matrix 1 2 := neg_pos.mpr hone
  have hbtwo : 0 < -matrix 2 3 := neg_pos.mpr htwo
  have hdenom : 0 < (-matrix 0 1) * (-matrix 1 2) * (-matrix 2 3) :=
    mul_pos (mul_pos hbzero hbone) hbtwo
  have hformula : (signedFourCycleCoefficientsOfMatrix matrix).lowerRight =
      ((matrix 0 2 * matrix 1 3 + (-matrix 1 2) * matrix 0 3) * matrix 2 1) /
        ((-matrix 0 1) * (-matrix 1 2) * (-matrix 2 3)) := by
    unfold signedFourCycleCoefficientsOfMatrix SignedFourCycleCoefficients.lowerRight
    field_simp [ne_of_lt hzero, ne_of_lt hone, ne_of_lt htwo]
  rw [hformula, lt_div_iff₀ hdenom]
  unfold signedFourCycleLargerDGap
  constructor <;> intro h <;> linarith

end Math
