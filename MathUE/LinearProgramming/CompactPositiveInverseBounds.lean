import MathUE.LinearProgramming.PositiveInverseOpenness
import Mathlib.Topology.Order.Compact

/-! # Uniform entry bounds for compact positive-inverse families

Continuity is needed only on the compact parameter set. Neither that set nor
the finite matrix index is required to be nonempty.
-/

noncomputable section

namespace Math.LinearProgramming

open Set

variable {ι Parameter : Type} [Fintype ι] [DecidableEq ι]
  [TopologicalSpace Parameter]

theorem continuousOn_matrix_inverse_of_det_ne_zero
    (family : Parameter → Matrix ι ι ℝ) (parameters : Set Parameter)
    (hcontinuous : ContinuousOn family parameters)
    (hdet : ∀ point ∈ parameters, (family point).det ≠ 0) :
    ContinuousOn (fun point => (family point)⁻¹) parameters := by
  intro point hpoint
  have hscalar : ContinuousAt Ring.inverse (family point).det := by
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ (hdet point hpoint)
  have hinverse : ContinuousAt (fun matrix : Matrix ι ι ℝ => matrix⁻¹) (family point) :=
    continuousAt_matrix_inv (family point) hscalar
  exact hinverse.comp_continuousWithinAt (hcontinuous point hpoint)

theorem exists_uniform_positive_inverse_entry_bounds_on_compact
    (family : Parameter → Matrix ι ι ℝ) (parameters : Set Parameter)
    (hcompact : IsCompact parameters) (hcontinuous : ContinuousOn family parameters)
    (hpositive : ∀ point ∈ parameters, HasStrictlyPositiveInverse (family point)) :
    ∃ lower upper : ℝ, 0 < lower ∧
      ∀ point ∈ parameters, ∀ i j, lower ≤ (family point)⁻¹ i j ∧
        (family point)⁻¹ i j ≤ upper := by
  have hinverse := continuousOn_matrix_inverse_of_det_ne_zero family parameters hcontinuous
    (fun point hpoint => (hpositive point hpoint).1)
  have hentry : ∀ i j, ContinuousOn (fun point => (family point)⁻¹ i j) parameters := by
    intro i j point hpoint
    exact (continuous_apply_apply i j).continuousAt.comp_continuousWithinAt
      (hinverse point hpoint)
  let entries : Set ℝ := ⋃ i : ι, ⋃ j : ι,
    (fun point => (family point)⁻¹ i j) '' parameters
  have hentriesCompact : IsCompact entries :=
    isCompact_iUnion fun i => isCompact_iUnion fun j =>
      hcompact.image_of_continuousOn (hentry i j)
  have hentriesPositive : ∀ value ∈ entries, 0 < value := by
    intro value hvalue
    simp only [entries, mem_iUnion, mem_image] at hvalue
    obtain ⟨i, j, point, hpoint, rfl⟩ := hvalue
    exact (hpositive point hpoint).2 i j
  obtain ⟨lower, hlower, hmin⟩ := hentriesCompact.exists_forall_le'
    continuous_id.continuousOn hentriesPositive
  obtain ⟨upper, hmax⟩ := hentriesCompact.bddAbove
  refine ⟨lower, upper, hlower, ?_⟩
  intro point hpoint i j
  have hmem : (family point)⁻¹ i j ∈ entries :=
    mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, mem_image_of_mem _ hpoint⟩⟩
  exact ⟨hmin _ hmem, hmax hmem⟩

end Math.LinearProgramming
