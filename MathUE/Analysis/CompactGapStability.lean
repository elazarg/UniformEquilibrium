import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.Linarith

/-! # Uniform stability of a strict compact gap

A continuous real function that is strictly below its value at one point on a
compact set retains that strict gap under sufficiently small uniform error on
the compact set together with the point. The compact set may be empty, and the
perturbed function need not be continuous.
-/

namespace Math

/-- A strict compact gap survives uniform perturbation on the set and comparison point. -/
theorem exists_uniform_perturbation_radius_of_lt_on_compact
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {f : X → ℝ} (hf : ContinuousOn f K) (point : X)
    (hstrict : ∀ x ∈ K, f x < f point) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ g : X → ℝ,
      (∀ x ∈ insert point K, |g x - f x| ≤ radius) →
        ∀ x ∈ K, g x < g point := by
  obtain ⟨gap, hgap, hlower⟩ := hK.exists_forall_le'
    (continuousOn_const.sub hf) (fun x hx => sub_pos.mpr (hstrict x hx))
  refine ⟨gap / 3, by linarith, ?_⟩
  intro g hclose x hx
  have hxClose := (abs_le.mp (hclose x (Set.mem_insert_of_mem point hx))).2
  have hpointClose := (abs_le.mp (hclose point (Set.mem_insert point K))).1
  have hbound := hlower x hx
  change gap ≤ f point - f x at hbound
  linarith

end Math
