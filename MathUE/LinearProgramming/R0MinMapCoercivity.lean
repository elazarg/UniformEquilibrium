import MathUE.Analysis.PositiveHomogeneousCoercivity
import MathUE.LinearProgramming.LocalAffine

/-! # The global ambient R0 minimum-map margin -/

namespace Math.LinearProgramming

variable {ι : Type*} [Fintype ι]

/-- Packet coercivity holds for the literal minimum map on the entire ambient
space, not just the nonnegative orthant. Empty player types are retained. -/
theorem exists_pos_mul_norm_le_lcpMinMap_zero
    (matrix : Matrix ι ι ℝ) (hR0 : IsR0Matrix matrix) :
    ∃ constant > 0, ∀ point : ι → ℝ,
      constant * ‖point‖ ≤ ‖lcpMinMap matrix 0 point‖ := by
  apply Math.exists_pos_mul_norm_le_of_positiveHomogeneous
    (lcpMinMap matrix 0) (continuous_lcpMinMap matrix 0)
    (fun scalar hscalar point => lcpMinMap_zero_smul matrix scalar hscalar point)
  intro point hzero
  exact funext (hR0 point ((lcpMinMap_eq_zero_iff matrix 0 point).mp hzero))

end Math.LinearProgramming
