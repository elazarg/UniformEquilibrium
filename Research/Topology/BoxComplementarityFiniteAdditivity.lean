import Research.Topology.BoxComplementarityLocalDegreeConsequences

/-!
# Finite additivity of the actual local degree

The empty region has degree zero. Repeated binary additivity then computes
the degree on a finite disjoint union of isolating regions as the sum of
their degrees. These statements include the empty family and dimension zero.
-/

noncomputable section

namespace Math

open Set

variable {n : ℕ}

/-- The empty relative region is isolating. -/
theorem BoxComplementarityProblem.isIsolating_empty
    (problem : BoxComplementarityProblem (Fin n)) :
    problem.IsIsolating ∅ := by
  simp [BoxComplementarityProblem.IsIsolating]

/-- The actual local degree on the empty region vanishes. -/
theorem BoxComplementarityProblem.localDegree_empty
    (problem : BoxComplementarityProblem (Fin n)) :
    problem.localDegree ∅ problem.isIsolating_empty = 0 := by
  by_contra hnonzero
  obtain ⟨point, hpoint, _⟩ := problem.exists_solution_mem_of_localDegree_ne_zero
    ∅ problem.isIsolating_empty hnonzero
  exact hpoint

/-- Any finite union of isolating regions is isolating. -/
theorem BoxComplementarityProblem.isIsolating_finsetUnion
    (problem : BoxComplementarityProblem (Fin n))
    {κ : Type*} (regions : κ → Set (UnitCube (Fin n)))
    (hisolating : ∀ index, problem.IsIsolating (regions index))
    (indices : Finset κ) :
    problem.IsIsolating (⋃ index ∈ indices, regions index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa using problem.isIsolating_empty
  | @insert index indices _ hinduction =>
      have hregion : (⋃ next ∈ insert index indices, regions next) =
          regions index ∪ ⋃ next ∈ indices, regions next := by
        ext point
        simp
      rw [hregion]
      exact problem.isIsolating_union _ _ (hisolating index) hinduction

/-- The actual degree is additive on a finite disjoint family of isolating
regions, including the empty family. -/
theorem BoxComplementarityProblem.localDegree_finsetUnion_of_pairwiseDisjoint
    (problem : BoxComplementarityProblem (Fin n))
    {κ : Type*} (regions : κ → Set (UnitCube (Fin n)))
    (hisolating : ∀ index, problem.IsIsolating (regions index))
    (hdisjoint : Pairwise fun first second => Disjoint (regions first) (regions second))
    (indices : Finset κ) :
    problem.localDegree (⋃ index ∈ indices, regions index)
        (problem.isIsolating_finsetUnion regions hisolating indices) =
      ∑ index ∈ indices, problem.localDegree (regions index) (hisolating index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa using problem.localDegree_empty
  | @insert index indices hnotmem hinduction =>
      have hregion : (⋃ next ∈ insert index indices, regions next) =
          regions index ∪ ⋃ next ∈ indices, regions next := by
        ext point
        simp
      have hseparate : Disjoint (regions index) (⋃ next ∈ indices, regions next) := by
        apply Set.disjoint_iUnion₂_right.mpr
        intro next hnext
        exact hdisjoint (fun hequal => hnotmem (hequal.symm ▸ hnext))
      have hadd := problem.localDegree_union_of_disjoint
        (regions index) (⋃ next ∈ indices, regions next) (hisolating index)
        (problem.isIsolating_finsetUnion regions hisolating indices) hseparate
      simpa only [hregion, Finset.sum_insert hnotmem] using
        hadd.trans (congrArg (fun degree =>
          problem.localDegree (regions index) (hisolating index) + degree) hinduction)

/-- An isolating region for a finite family is obtained by taking its union. -/
theorem BoxComplementarityProblem.isIsolating_iUnion
    (problem : BoxComplementarityProblem (Fin n))
    {κ : Type*} [Fintype κ] (regions : κ → Set (UnitCube (Fin n)))
    (hisolating : ∀ index, problem.IsIsolating (regions index)) :
    problem.IsIsolating (⋃ index, regions index) := by
  simpa using problem.isIsolating_finsetUnion regions hisolating Finset.univ

/-- Finite-family form of local-degree additivity, convenient for a finite
type of actual roots and their disjoint isolating neighborhoods. -/
theorem BoxComplementarityProblem.localDegree_iUnion_of_pairwiseDisjoint
    (problem : BoxComplementarityProblem (Fin n))
    {κ : Type*} [Fintype κ] (regions : κ → Set (UnitCube (Fin n)))
    (hisolating : ∀ index, problem.IsIsolating (regions index))
    (hdisjoint : Pairwise fun first second => Disjoint (regions first) (regions second)) :
    problem.localDegree (⋃ index, regions index)
        (problem.isIsolating_iUnion regions hisolating) =
      ∑ index, problem.localDegree (regions index) (hisolating index) := by
  simpa using problem.localDegree_finsetUnion_of_pairwiseDisjoint
    regions hisolating hdisjoint Finset.univ

end Math
