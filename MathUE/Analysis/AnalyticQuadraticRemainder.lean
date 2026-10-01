import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # The quadratic remainder of an actual analytic map

This is a short adapter of the canonical power-series remainder. It retains
the actual derivative and the full ambient neighborhood, not a one-sided set.
-/

namespace Math

open Filter Asymptotics
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Analyticity upgrades the actual first-order remainder to a quadratic bound. -/
theorem isBigO_quadratic_remainder_of_analyticAt_zero
    {function : E → F} {linear : E →L[ℝ] F}
    (hanalytic : AnalyticAt ℝ function 0) (hderivative : HasFDerivAt function linear 0) :
    (fun point => function point - function 0 - linear point) =O[𝓝 0]
      (fun point : E => ‖point‖ ^ 2) := by
  obtain ⟨series, hseries⟩ := hanalytic
  have hfirst (point : E) : series 1 (fun _ => point) = linear point := by
    simpa only [continuousMultilinearCurryFin1_apply, Fin.snoc_zero] using
      congrArg (fun map : E →L[ℝ] F => map point)
        (hseries.hasFDerivAt.unique hderivative)
  have htendsto : Tendsto (fun point : E => (point, (0 : E)))
      (𝓝 0) (𝓝 (0, 0)) :=
    continuous_id.continuousAt.prodMk continuous_const.continuousAt
  have hbound := hseries.isBigO_image_sub_norm_mul_norm_sub.comp_tendsto htendsto
  change (fun point : E => function point - function 0 -
    series 1 (fun _ => point - 0)) =O[𝓝 0]
      (fun point : E => ‖(point, (0 : E)) - (0, 0)‖ * ‖point - 0‖) at hbound
  have hnorm (point : E) : ‖(point, (0 : E)) - (0, 0)‖ = ‖point‖ := by
    change max ‖point - 0‖ ‖(0 : E) - 0‖ = ‖point‖
    simp only [sub_zero, norm_zero, max_eq_left (norm_nonneg point)]
  simpa only [sub_zero, hfirst, hnorm, pow_two] using hbound

/-- A positive constant and positive radius for the full signed ambient ball. -/
theorem exists_quadratic_remainder_bound_of_analyticAt_zero
    {function : E → F} {linear : E →L[ℝ] F}
    (hanalytic : AnalyticAt ℝ function 0) (hderivative : HasFDerivAt function linear 0) :
    ∃ constant > 0, ∃ radius > 0, ∀ point : E, ‖point‖ < radius →
      ‖function point - function 0 - linear point‖ ≤ constant * ‖point‖ ^ 2 := by
  obtain ⟨constant, hconstant, hbound⟩ :=
    (isBigO_quadratic_remainder_of_analyticAt_zero hanalytic hderivative).exists_pos
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp hbound.bound
  refine ⟨constant, hconstant, radius, hradius, fun point hpoint => ?_⟩
  have hpointwise := hball (by
    simpa only [Metric.mem_ball, dist_zero_right] using hpoint)
  change ‖function point - function 0 - linear point‖ ≤
    constant * ‖‖point‖ ^ 2‖ at hpointwise
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖point‖)] using hpointwise

end Math
