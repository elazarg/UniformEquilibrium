module

public import MathUE.Analysis.NormalizedSphereChartSpeed
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # The canonical sphere containing the complex chart

The ambient real inner-product space is the existing L² product of the complex
plane and the real line. Its unit sphere includes the north pole as an actual
point. The chart is the normalized pinned stereographic chart, not a new
metric or a one-point-compactification axiom.
-/

public section

noncomputable section

namespace Math.ComplexSphere

open Metric
open scoped InnerProductSpace

abbrev Ambient := WithLp 2 (ℂ × ℝ)

@[expose] def pole : Ambient := WithLp.toLp 2 (0, 1)

@[expose] def plane : ℂ →ₗᵢ[ℝ] Ambient where
  toLinearMap := (WithLp.linearEquiv 2 ℝ (ℂ × ℝ)).symm.toLinearMap.comp
    (LinearMap.inl ℝ ℂ ℝ)
  norm_map' z := by
    have h := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (z, (0 : ℝ)))
    change ‖(WithLp.toLp 2 (z, (0 : ℝ)) : Ambient)‖ ^ 2 = ‖z‖ ^ 2 + ‖(0 : ℝ)‖ ^ 2 at h
    simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

theorem norm_pole : ‖pole‖ = 1 := by
  have h := WithLp.prod_norm_sq_eq_of_L2 pole
  change ‖pole‖ ^ 2 = ‖(0 : ℂ)‖ ^ 2 + ‖(1 : ℝ)‖ ^ 2 at h
  norm_num at h
  rcases h with h | h
  · exact h
  · have := norm_nonneg pole
    linarith

theorem pole_orthogonal_plane (z : ℂ) : ⟪pole, plane z⟫_ℝ = 0 := by
  change ⟪(WithLp.toLp 2 ((0 : ℂ), (1 : ℝ)) : Ambient),
    WithLp.toLp 2 (z, (0 : ℝ))⟫_ℝ = 0
  simp [WithLp.prod_inner_apply]

abbrev Sphere := sphere (0 : Ambient) 1

@[expose] def chart (z : ℂ) : Sphere :=
  NormalizedSphereChart.chart pole plane norm_pole pole_orthogonal_plane z

instance : CompleteSpace Sphere := isClosed_sphere.isComplete.completeSpace_coe

end Math.ComplexSphere
