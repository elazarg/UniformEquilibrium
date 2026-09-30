import MathUE.Topology.BoxComplementarityDegreeEscape

/-!
# Total degree of a nonzero solution set in a fixed chart

Origin isolation selects the entire nonzero set in the open exterior.
The integer degree is normalized in the supplied cube problem; no ambient
degree or chart independence is asserted.
-/

noncomputable section

namespace Math

open Set

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V]

/-- A continuous chart and closed-ball origin isolation identify the whole
nonzero set selected by the exterior, including its image and total degree.
No finiteness, regularity, or isolation of the nonzero solutions is needed. -/
theorem BoxComplementarityProblem.entireNonzeroSet_degree_compl_origin
    (problem : BoxComplementarityProblem (Fin n))
    (chart : UnitCube (Fin n) → V) (hchart : Continuous chart)
    (fixed : V → Prop) (radius : ℝ) (hradius : 0 < radius)
    (hsolution : ∀ point, problem.IsSolution point ↔ fixed (chart point))
    (hisolation : ∀ source, ‖source‖ ≤ radius → fixed source → source = 0)
    (hcover : ∀ source, source ≠ 0 → fixed source → ∃ point, chart point = source)
    (horigin : problem.IsIsolating (chart ⁻¹' Metric.ball 0 radius)) :
    problem.solutionsIn (closure (chart ⁻¹' Metric.ball 0 radius))ᶜ =
        chart ⁻¹' {source | source ≠ 0 ∧ fixed source} ∧
      chart '' problem.solutionsIn (closure (chart ⁻¹' Metric.ball 0 radius))ᶜ =
        {source | source ≠ 0 ∧ fixed source} ∧
      problem.localDegree (closure (chart ⁻¹' Metric.ball 0 radius))ᶜ
          (problem.isIsolating_compl_closure _ horigin) =
        1 - problem.localDegree (chart ⁻¹' Metric.ball 0 radius) horigin := by
  let region := chart ⁻¹' Metric.ball 0 radius
  have hclosureSmall (point : UnitCube (Fin n)) (hpoint : point ∈ closure region) :
      ‖chart point‖ ≤ radius := by
    have hclosed : IsClosed (chart ⁻¹' Metric.closedBall (0 : V) radius) :=
      Metric.isClosed_closedBall.preimage hchart
    have hsubset : region ⊆ chart ⁻¹' Metric.closedBall (0 : V) radius := by
      intro point hpoint
      exact Metric.ball_subset_closedBall hpoint
    have hmem := closure_minimal hsubset hclosed hpoint
    simpa only [mem_preimage, Metric.mem_closedBall, dist_zero_right] using hmem
  have hselected : problem.solutionsIn (closure region)ᶜ =
      chart ⁻¹' {source | source ≠ 0 ∧ fixed source} := by
    ext point
    change (problem.IsSolution point ∧ point ∉ closure region) ↔
      chart point ≠ 0 ∧ fixed (chart point)
    rw [hsolution]
    constructor
    · rintro ⟨hfixed, hout⟩
      refine ⟨?_, hfixed⟩
      intro hzero
      apply hout
      apply subset_closure
      change dist (chart point) 0 < radius
      simpa only [hzero, dist_self] using hradius
    · rintro ⟨hnonzero, hfixed⟩
      refine ⟨hfixed, ?_⟩
      intro hclosure
      exact hnonzero (hisolation _ (hclosureSmall point hclosure) hfixed)
  refine ⟨hselected, ?_, problem.localDegree_compl_closure _ horigin⟩
  rw [hselected]
  apply Set.Subset.antisymm
  · rintro source ⟨point, hpoint, rfl⟩
    exact hpoint
  · rintro source ⟨hnonzero, hfixed⟩
    obtain ⟨point, hpoint⟩ := hcover source hnonzero hfixed
    refine ⟨point, ?_, hpoint⟩
    change chart point ≠ 0 ∧ fixed (chart point)
    rw [hpoint]
    exact ⟨hnonzero, hfixed⟩

end Math
