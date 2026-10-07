module

public import MathUE.Complex.HolomorphicRadialLimits
public import MathUE.Complex.HolomorphicInjectiveInverse
public import Mathlib.Topology.Algebra.ConstMulAction

/-! # Actual radial landing on the spherical frontier

For an injective holomorphic disk map, a radial limit cannot be an interior
image point: continuity of the actual inverse would force a unit-circle point
back into the open disk. Combining this with the actual almost-everywhere
landing theorem gives frontier membership, including possible pole endpoints.
This is the frontier step in Milnor §15.3, not boundary extension or separation.
-/

public section

noncomputable section

namespace Math.ComplexSphere

open Metric Set
open scoped InnerProductSpace

theorem isEmbedding_chart : Topology.IsEmbedding chart := by
  let lift : ℂ → (ℝ ∙ pole)ᗮ := fun z => ⟨(2 : ℝ) • plane z, by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    simp only [inner_smul_right, pole_orthogonal_plane, mul_zero]⟩
  have hscaled : Topology.IsEmbedding (fun z : ℂ => (2 : ℝ) • plane z) :=
    (Homeomorph.smulOfNeZero (2 : ℝ) (by norm_num)).isEmbedding.comp
      plane.isometry.isEmbedding
  have hlift : Topology.IsEmbedding lift := hscaled.codRestrict _ _
  exact (isOpenEmbedding_stereographic_symm norm_pole).isEmbedding.comp hlift

@[expose] def north : Sphere := ⟨pole, by simpa using norm_pole⟩

theorem chart_ne_north (z : ℂ) : chart z ≠ north := by
  exact stereoInvFun_ne_north_pole norm_pole _

end Math.ComplexSphere

namespace Math.ComplexAnalysis

open Complex Filter Function MeasureTheory Metric Set
open scoped Topology

private theorem radial_eventually_mem_disk (θ : ℝ) :
    ∀ᶠ r : ℝ in 𝓝[<] 1,
      (r : ℂ) * Complex.exp ((θ : ℂ) * I) ∈ ball 0 1 := by
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r from
      nhdsWithin_le_nhds (eventually_gt_nhds zero_lt_one))] with r hr hpositive
  rw [mem_ball_zero_iff, norm_mul]
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpositive, Complex.norm_exp]
    using hr

theorem sphere_radial_limit_mem_frontier
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1)) (hinj : InjOn g (ball 0 1))
    {θ : ℝ} {endpoint : ComplexSphere.Sphere}
    (hlimit : Tendsto (fun r : ℝ => ComplexSphere.chart
      (g ((r : ℂ) * Complex.exp ((θ : ℂ) * I)))) (𝓝[<] 1) (𝓝 endpoint)) :
    endpoint ∈ frontier (ComplexSphere.chart '' (g '' ball 0 1)) := by
  have hinDisk := radial_eventually_mem_disk θ
  have hclosure : endpoint ∈ closure (ComplexSphere.chart '' (g '' ball 0 1)) :=
    mem_closure_of_tendsto hlimit (hinDisk.mono fun r hr =>
      ⟨_, ⟨_, hr, rfl⟩, rfl⟩)
  have hnotImage : endpoint ∉ ComplexSphere.chart '' (g '' ball 0 1) := by
    rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    have hcomplex : Tendsto
        (fun r : ℝ => g ((r : ℂ) * Complex.exp ((θ : ℂ) * I)))
        (𝓝[<] 1) (𝓝 (g z)) :=
      ComplexSphere.isEmbedding_chart.tendsto_nhds_iff.mpr hlimit
    have hopen : IsOpen (g '' ball 0 1) := by
      simpa only [range_domRestrict] using
        (isOpenMap_domRestrict_of_holomorphic_injOn isOpen_ball hg hinj).isOpen_range
    have hinverse : ContinuousAt (invFunOn g (ball 0 1)) (g z) :=
      (differentiableOn_invFunOn_of_holomorphic_injOn isOpen_ball hg hinj).continuousOn
        |>.continuousAt (hopen.mem_nhds ⟨z, hz, rfl⟩)
    have hinvLimit := hinverse.tendsto.comp hcomplex
    rw [hinj.leftInvOn_invFunOn hz] at hinvLimit
    have hradial : Tendsto (fun r : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * I))
        (𝓝[<] 1) (𝓝 z) := by
      apply hinvLimit.congr'
      filter_upwards [hinDisk] with r hr
      exact hinj.leftInvOn_invFunOn hr
    have hboundary : Tendsto (fun r : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * I))
        (𝓝[<] 1) (𝓝 (Complex.exp ((θ : ℂ) * I))) := by
      have hreal : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝 (1 : ℝ)) (𝓝 (1 : ℂ)) :=
        Complex.continuous_ofReal.tendsto 1
      simpa only [one_mul] using
        (hreal.mul_const
          (Complex.exp ((θ : ℂ) * I))).mono_left nhdsWithin_le_nhds
    have heq : z = Complex.exp ((θ : ℂ) * I) := tendsto_nhds_unique hradial hboundary
    rw [mem_ball_zero_iff, heq] at hz
    simp [Complex.norm_exp] at hz
  exact ⟨hclosure, fun h => hnotImage (interior_subset h)⟩

/-- The actual source theorem: almost every radial direction lands on the
frontier of the actual spherical image. The north pole is not excluded. -/
theorem exists_sphere_radial_frontier_limit_ae
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1)) (hinj : InjOn g (ball 0 1)) :
    ∀ᵐ θ : ℝ, ∃ endpoint ∈ frontier (ComplexSphere.chart '' (g '' ball 0 1)),
      Tendsto (fun r : ℝ => ComplexSphere.chart
        (g ((r : ℂ) * Complex.exp ((θ : ℂ) * I)))) (𝓝[<] 1) (𝓝 endpoint) := by
  filter_upwards [exists_sphere_radial_limit_ae_real hg hinj] with θ hθ
  obtain ⟨endpoint, hlimit⟩ := hθ
  exact ⟨endpoint, sphere_radial_limit_mem_frontier hg hinj hlimit, hlimit⟩

end Math.ComplexAnalysis
