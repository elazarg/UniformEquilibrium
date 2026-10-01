import MathUE.Topology.AmbientDegreeProperties

/-! # Intrinsic degree normalization for actual rectangle self-maps

This is the source-local adapter to the canonical counted self-map normalization.
The source closure lies strictly inside the chart and retains all its fixed
points. No finite fiber, regularity, or dimension restriction is imposed.
-/

noncomputable section

namespace Math.Topology

open Set

variable {n : ℕ}

/-- Retention of the rectangle's fixed points excludes source-frontier zeros. -/
theorem selfMapField_ne_zero_on_frontier
    (lower upper : Fin n → ℝ) (map : (Fin n → ℝ) → Fin n → ℝ)
    (region : Set (Fin n → ℝ)) (hopen : IsOpen region)
    (hclosure : closure region ⊆
      {point | ∀ who, lower who < point who ∧ point who < upper who})
    (hfixed : ∀ point ∈ Icc lower upper, point = map point → point ∈ region) :
    ∀ point ∈ frontier region, point - map point ≠ 0 := by
  intro point hpoint hzero
  have hbounds := hclosure (frontier_subset_closure hpoint)
  have hmem := hfixed point
    ⟨fun who => (hbounds who).1.le, fun who => (hbounds who).2.le⟩
    (sub_eq_zero.mp hzero)
  have hinterior : point ∈ interior region := by rwa [hopen.interior_eq]
  exact (mem_interior_iff_notMem_frontier hmem).mp hinterior hpoint

/-- The intrinsic ambient degree of identity minus a rectangle self-map is one
on any bounded open source retaining all fixed points in that chart. -/
theorem ambientDegree_of_selfMap_eq_one
    (lower upper : Fin n → ℝ) (hwidth : ∀ who, lower who < upper who)
    (map : (Fin n → ℝ) → Fin n → ℝ) (hmap : Continuous map)
    (hself : MapsTo map (Icc lower upper) (Icc lower upper))
    (region : Set (Fin n → ℝ)) (hopen : IsOpen region)
    (hbounded : Bornology.IsBounded region)
    (hclosure : closure region ⊆
      {point | ∀ who, lower who < point who ∧ point who < upper who})
    (hfixed : ∀ point ∈ Icc lower upper, point = map point → point ∈ region) :
    ambientDegree (fun point => point - map point) region 0 hopen hbounded
      (continuous_id.sub hmap).continuousOn
      (selfMapField_ne_zero_on_frontier lower upper map region hopen hclosure hfixed) = 1 := by
  have hcomputed := ambientDegree_eq_of_extension
    (fun point => point - map point) region 0 hopen hbounded
    (continuous_id.sub hmap).continuousOn
    (selfMapField_ne_zero_on_frontier lower upper map region hopen hclosure hfixed)
    lower upper hwidth hclosure (fun point => point - map point)
    (continuous_id.sub hmap).continuousOn (fun _ _ => rfl)
  have hnormalized := Math.BoxComplementarityProblem.localDegree_of_selfMap_preimage_eq_one
    lower upper hwidth map hmap.continuousOn hself region hopen hfixed
  simp only [sub_zero] at hcomputed
  exact hcomputed.trans hnormalized

end Math.Topology
