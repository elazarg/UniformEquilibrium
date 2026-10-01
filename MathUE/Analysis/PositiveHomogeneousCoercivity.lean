import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Topology.Order.Compact

/-! # Coercivity of positively homogeneous maps with trivial zero fiber

Compactness of the unit sphere supplies the uniform lower bound. The domain
may be zero-dimensional; no linearity, injectivity, or smoothness is assumed.
-/

namespace Math

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous positively homogeneous map with no nonzero zero has a global
positive norm margin, including on signed vectors and in dimension zero. -/
theorem exists_pos_mul_norm_le_of_positiveHomogeneous
    (function : E → F) (hcontinuous : Continuous function)
    (hhomogeneous : ∀ scalar : ℝ, 0 ≤ scalar → ∀ point : E,
      function (scalar • point) = scalar • function point)
    (hzero : ∀ point : E, function point = 0 → point = 0) :
    ∃ constant > 0, ∀ point : E, constant * ‖point‖ ≤ ‖function point‖ := by
  classical
  by_cases hnonempty : (Metric.sphere (0 : E) 1).Nonempty
  · obtain ⟨minimum, hminimum, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
      hnonempty hcontinuous.norm.continuousOn
    have hminimumNorm : ‖minimum‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hminimum
    have hpositive : 0 < ‖function minimum‖ := by
      apply norm_pos_iff.mpr
      intro hequal
      have := hzero minimum hequal
      simp [this] at hminimumNorm
    refine ⟨‖function minimum‖, hpositive, fun point => ?_⟩
    by_cases hpoint : point = 0
    · simp [hpoint]
    have hnorm : 0 < ‖point‖ := norm_pos_iff.mpr hpoint
    have hnormalized : ‖point‖⁻¹ • point ∈ Metric.sphere (0 : E) 1 := by
      simpa [Metric.mem_sphere, RCLike.ofReal_real_eq_id] using
        (norm_smul_inv_norm (𝕜 := ℝ) hpoint)
    have hbound := isMinOn_iff.mp hmin _ hnormalized
    rw [hhomogeneous _ (inv_nonneg.mpr hnorm.le), norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hnorm.le)] at hbound
    have hscaled := mul_le_mul_of_nonneg_right hbound hnorm.le
    calc
      ‖function minimum‖ * ‖point‖ ≤
          (‖point‖⁻¹ * ‖function point‖) * ‖point‖ := hscaled
      _ = ‖function point‖ := by
        rw [mul_assoc, mul_comm ‖function point‖ ‖point‖, ← mul_assoc,
          inv_mul_cancel₀ hnorm.ne', one_mul]
  · refine ⟨1, zero_lt_one, fun point => ?_⟩
    have hpoint : point = 0 := by
      by_contra hpoint
      apply hnonempty
      refine ⟨‖point‖⁻¹ • point, ?_⟩
      simpa [Metric.mem_sphere, RCLike.ofReal_real_eq_id] using
        (norm_smul_inv_norm (𝕜 := ℝ) hpoint)
    simp [hpoint]

end Math
