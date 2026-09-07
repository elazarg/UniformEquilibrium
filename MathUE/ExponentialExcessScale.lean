import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # A positive exponential scale below a prescribed excess -/

namespace Math

/-- A positive row scale reduced to fit an exponential excess threshold. -/
noncomputable def exponentialExcessScale (rowScale excess baseline : ℝ) : ℝ :=
  min rowScale (Real.log (1 + 2 * excess / baseline) / 2)

theorem exponentialExcessScale_pos {rowScale excess baseline : ℝ}
    (hrow : 0 < rowScale) (hexcess : 0 < excess) (hbaseline : 0 < baseline) :
    0 < exponentialExcessScale rowScale excess baseline := by
  apply lt_min hrow
  exact div_pos (Real.log_pos (lt_add_of_pos_right 1 (by positivity))) (by norm_num)

theorem exponentialExcessScale_le_rowScale (rowScale excess baseline : ℝ) :
    exponentialExcessScale rowScale excess baseline ≤ rowScale :=
  min_le_left _ _

theorem exponentialExcessScale_threshold_le {rowScale excess baseline : ℝ}
    (hexcess : 0 < excess) (hbaseline : 0 < baseline) :
    (Real.exp (exponentialExcessScale rowScale excess baseline) - 1) / 2 *
      baseline ≤ excess := by
  have hratio : 1 < 1 + 2 * excess / baseline := lt_add_of_pos_right 1 (by positivity)
  have hlog := Real.log_pos hratio
  have hscale : exponentialExcessScale rowScale excess baseline ≤
      Real.log (1 + 2 * excess / baseline) := by
    exact (min_le_right _ _).trans (by linarith)
  have hexp : Real.exp (exponentialExcessScale rowScale excess baseline) ≤
      1 + 2 * excess / baseline := by
    calc
      _ ≤ Real.exp (Real.log (1 + 2 * excess / baseline)) :=
        Real.exp_le_exp.mpr hscale
      _ = _ := Real.exp_log (by linarith)
  have hscaled := mul_le_mul_of_nonneg_right hexp hbaseline.le
  have hcancel : (2 * excess / baseline) * baseline = 2 * excess :=
    div_mul_cancel₀ _ hbaseline.ne'
  nlinarith

end Math
