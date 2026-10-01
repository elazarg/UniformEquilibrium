import MathUE.Polynomial.TensorBernsteinQuadratic
import Mathlib.Tactic.Linarith

/-! # Exact half-survival tensor Bernstein error factors -/

noncomputable section

namespace Math

/-- The nine literal coefficient error factors of a half-survival bilinear difference. -/
def halfSurvivalBernsteinErrorFactor : Fin 3 → Fin 3 → ℝ :=
  ![![1, 3 / 2, 2], ![3 / 2, 7 / 4, 2], ![2, 2, 2]]

/-- With unit corner error for Quit and half error at the all-zero Continue
corner, the coefficient errors are the packet's exact array, not a coarse
amplification of nine samples. This is generic bilinear interpolation algebra. -/
theorem abs_halfSurvivalBernsteinCoefficient_sub_le
    (quit cont otherQuit otherCont : ℝ → ℝ → ℝ) (error : ℝ)
    (hquit : ∀ first second : Fin 2,
      |otherQuit first.val second.val - quit first.val second.val| ≤ error)
    (hcont : ∀ first second : Fin 2,
      |otherCont first.val second.val - cont first.val second.val| ≤
        (if first = 0 ∧ second = 0 then 1 / 2 else 1) * error)
    (first second : Fin 3) :
    |quadraticTensorBernsteinCoefficient (bilinearSurvivalDifference (1 / 2) otherQuit otherCont)
        first second -
      quadraticTensorBernsteinCoefficient (bilinearSurvivalDifference (1 / 2) quit cont)
        first second| ≤ halfSurvivalBernsteinErrorFactor first second * error := by
  have hq00 := abs_le.mp (hquit 0 0)
  have hq01 := abs_le.mp (hquit 0 1)
  have hq10 := abs_le.mp (hquit 1 0)
  have hq11 := abs_le.mp (hquit 1 1)
  have hc00 := abs_le.mp (hcont 0 0)
  have hc01 := abs_le.mp (hcont 0 1)
  have hc10 := abs_le.mp (hcont 1 0)
  have hc11 := abs_le.mp (hcont 1 1)
  simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one,
    Nat.one_ne_zero, and_true, and_false,
    ite_true, ite_false] at hq00 hq01 hq10 hq11 hc00 hc01 hc10 hc11
  norm_num only at hq00 hq01 hq10 hq11 hc00 hc01 hc10 hc11
  fin_cases first
  all_goals fin_cases second
  all_goals dsimp only [quadraticTensorBernsteinCoefficient, quadraticBernsteinCoefficient,
    bilinearSurvivalDifference, halfSurvivalBernsteinErrorFactor]
  all_goals simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Nat.succ_ne_zero,
    Nat.succ.injEq, Nat.zero_ne_one, ite_true, ite_false,
    Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals norm_num only
  all_goals apply abs_le.mpr
  all_goals constructor <;> linarith

theorem halfSurvivalBernsteinErrorFactor_le_two (first second : Fin 3) :
    halfSurvivalBernsteinErrorFactor first second ≤ 2 := by
  fin_cases first
  all_goals fin_cases second
  all_goals dsimp only [halfSurvivalBernsteinErrorFactor]
  all_goals simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals norm_num only

end Math
