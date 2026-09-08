import Research.Topology.BoxComplementaritySpernerSubdivisionPrism

/-!
# Signed finite-grid local counts for box complementarity

The integer weight is the existing endpoint signed weight, transported through
the existing complete-simplex equivalence and extended by zero off complete
tuples. The local sum uses the existing anchor-selected simplex Finset.
Union, excision, and collar coherence delegate to its exact set identities.
No mesh independence or local homotopy invariance is asserted.
-/

noncomputable section

namespace Math

open Classical Set

variable {n : ℕ}

/-- Existing endpoint signed weight, extended by zero to incomplete tuples. -/
def boxComplementarityCompleteSimplexSignedWeight
    (problem : BoxComplementarityProblem (Fin n)) (p : ℕ) (hp : 0 < p)
    (vertices : Fin (n + 1) → (boxComplementaritySpernerCube problem p hp).G) : ℤ :=
  if hcomplete : complete_simplex (boxComplementaritySpernerCube problem p hp) n vertices
  then (completeSimplexEquivKuhnEndpointLabeledSimplex problem p hp
    ⟨vertices, hcomplete⟩).signedWeight else 0

/-- Signed count over the existing local complete-simplex Finset. -/
def boxComplementarityLocalSignedCount
    (problem : BoxComplementarityProblem (Fin n)) (p : ℕ) (hp : 0 < p)
    (region : Set (UnitCube (Fin n))) : ℤ :=
  ∑ vertices ∈ boxComplementarityLocalCompleteSimplices problem p hp region,
    boxComplementarityCompleteSimplexSignedWeight problem p hp vertices

/-- At a complete tuple, the extension is the literal endpoint weight. -/
theorem boxComplementarityCompleteSimplexSignedWeight_eq
    (problem : BoxComplementarityProblem (Fin n)) (p : ℕ) (hp : 0 < p)
    (vertices : Fin (n + 1) → (boxComplementaritySpernerCube problem p hp).G)
    (hcomplete : complete_simplex (boxComplementaritySpernerCube problem p hp) n vertices) :
    boxComplementarityCompleteSimplexSignedWeight problem p hp vertices =
      (completeSimplexEquivKuhnEndpointLabeledSimplex problem p hp
        ⟨vertices, hcomplete⟩).signedWeight := by
  simp only [boxComplementarityCompleteSimplexSignedWeight, dif_pos hcomplete]

/-- Whole-cube local counting is the existing endpoint signed sum. -/
theorem boxComplementarityLocalSignedCount_univ
    (problem : BoxComplementarityProblem (Fin n)) (p : ℕ) (hp : 0 < p) :
    boxComplementarityLocalSignedCount problem p hp Set.univ =
      ∑ vertices : KuhnEndpointLabeledSimplex problem p hp, vertices.signedWeight := by
  classical
  unfold boxComplementarityLocalSignedCount
  rw [Finset.sum_subtype
    (p := fun vertices => complete_simplex
      (boxComplementaritySpernerCube problem p hp) n vertices)
    (boxComplementarityLocalCompleteSimplices problem p hp Set.univ)
    (fun vertices => by
      simpa only [boxComplementarityLocalCompleteSimplices, Finset.mem_filter,
        Finset.mem_univ, true_and] using
        completeSimplexAnchorIn_univ_iff problem p hp vertices)]
  apply Fintype.sum_equiv (completeSimplexEquivKuhnEndpointLabeledSimplex problem p hp)
  intro vertices
  exact boxComplementarityCompleteSimplexSignedWeight_eq problem p hp vertices.1 vertices.2

/-- Disjoint local regions have additive integer counts at the same mesh. -/
theorem boxComplementarityLocalSignedCount_union_of_disjoint
    (problem : BoxComplementarityProblem (Fin n)) (p : ℕ) (hp : 0 < p)
    {first second : Set (UnitCube (Fin n))} (hdisjoint : Disjoint first second) :
    boxComplementarityLocalSignedCount problem p hp (first ∪ second) =
      boxComplementarityLocalSignedCount problem p hp first +
        boxComplementarityLocalSignedCount problem p hp second := by
  unfold boxComplementarityLocalSignedCount
  rw [boxComplementarityLocalCompleteSimplices_union,
    Finset.sum_union (boxComplementarityLocalCompleteSimplices_disjoint
      problem p hp hdisjoint)]

/-- Agreement on the existing selected anchors gives exact count equality. -/
theorem boxComplementarityLocalSignedCount_eq_of_anchor_mem_iff
    (problem : BoxComplementarityProblem (Fin n)) (p : ℕ) (hp : 0 < p)
    (first second : Set (UnitCube (Fin n)))
    (hagrees : ∀ vertices
      (hcomplete : complete_simplex (boxComplementaritySpernerCube problem p hp) n vertices),
      boxComplementarityCompleteSimplexAnchorPoint problem p hp vertices hcomplete ∈ first ↔
        boxComplementarityCompleteSimplexAnchorPoint problem p hp vertices hcomplete ∈ second) :
    boxComplementarityLocalSignedCount problem p hp first =
      boxComplementarityLocalSignedCount problem p hp second := by
  unfold boxComplementarityLocalSignedCount
  rw [boxComplementarityLocalCompleteSimplices_eq_of_anchor_mem_iff
    problem p hp first second hagrees]

/-- A region without vertices of complete simplices has zero signed count. -/
theorem boxComplementarityLocalSignedCount_eq_zero_of_no_vertex
    (problem : BoxComplementarityProblem (Fin n)) (p : ℕ) (hp : 0 < p)
    (region : Set (UnitCube (Fin n)))
    (hno : ¬problem.HasCompleteSimplexVertexIn region p) :
    boxComplementarityLocalSignedCount problem p hp region = 0 := by
  rw [boxComplementarityLocalSignedCount,
    boxComplementarityLocalCompleteSimplices_eq_empty_of_no_vertex problem p hp region hno,
    Finset.sum_empty]

/-- Altering a region only in a cleared set preserves its signed count. -/
theorem boxComplementarityLocalSignedCount_eq_of_difference_subset_cleared
    (problem : BoxComplementarityProblem (Fin n)) (p : ℕ) (hp : 0 < p)
    (first second cleared : Set (UnitCube (Fin n)))
    (hdifference : (first \ second) ∪ (second \ first) ⊆ cleared)
    (hcleared : ¬problem.HasCompleteSimplexVertexIn cleared p) :
    boxComplementarityLocalSignedCount problem p hp first =
      boxComplementarityLocalSignedCount problem p hp second := by
  unfold boxComplementarityLocalSignedCount
  rw [boxComplementarityLocalCompleteSimplices_eq_of_difference_subset_cleared
    problem p hp first second cleared hdifference hcleared]

/-- An isolating frontier has a positive collar with eventually zero signed count. -/
theorem BoxComplementarityProblem.exists_isolatingFrontierCollar_eventually_signedCount_zero
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n))) (hisolating : problem.IsIsolating region) :
    ∃ radius : ℝ, 0 < radius ∧
      ∃ threshold, ∀ p, threshold ≤ p → ∀ hp : 0 < p,
        boxComplementarityLocalSignedCount problem p hp
          (Metric.cthickening radius (frontier region)) = 0 := by
  obtain ⟨radius, hradius, threshold, hcleared⟩ :=
    problem.exists_isolatingFrontierCollar_eventually_cleared region hisolating
  refine ⟨radius, hradius, threshold, ?_⟩
  intro p hpFine hp
  exact boxComplementarityLocalSignedCount_eq_zero_of_no_vertex
    problem p hp _ (hcleared p hpFine)

/-- One isolating collar uniformly permits same-mesh changes of the counting region. -/
theorem BoxComplementarityProblem.exists_isolatingFrontierCollar_eventually_signedCount_coherent
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n))) (hisolating : problem.IsIsolating region) :
    ∃ radius : ℝ, 0 < radius ∧
      ∃ threshold, ∀ p, threshold ≤ p → ∀ hp : 0 < p,
        ∀ first second : Set (UnitCube (Fin n)),
          (first \ second) ∪ (second \ first) ⊆
              Metric.cthickening radius (frontier region) →
            boxComplementarityLocalSignedCount problem p hp first =
              boxComplementarityLocalSignedCount problem p hp second := by
  obtain ⟨radius, hradius, threshold, hcleared⟩ :=
    problem.exists_isolatingFrontierCollar_eventually_cleared region hisolating
  refine ⟨radius, hradius, threshold, ?_⟩
  intro p hpFine hp first second hdifference
  exact boxComplementarityLocalSignedCount_eq_of_difference_subset_cleared
    problem p hp first second _ hdifference (hcleared p hpFine)

end Math
