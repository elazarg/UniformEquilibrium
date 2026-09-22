import MathUE.Topology.BoxComplementarityLocalDegreeConsequences

/-!
# Excision from equality of the actual selected solution sets

For two isolating regions of one problem, equality of their actual solutions
makes the closed differences solution-free. Compactness clears these sets of
complete-simplex vertices at sufficiently fine meshes, so the existing
signed-count excision theorem identifies the local degrees. This compares
regions of the same problem, not different ambient charts.
-/

noncomputable section

namespace Math

open Set

variable {n : ℕ}

/-- An isolating region gains no solutions when its closure is taken. -/
theorem BoxComplementarityProblem.solutionsIn_closure_eq_of_isIsolating
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n))) (hisolating : problem.IsIsolating region) :
    problem.solutionsIn (closure region) = problem.solutionsIn region := by
  rw [solutionsIn, closure_eq_self_union_frontier, inter_union_distrib_left,
    hisolating.2, union_empty]
  rfl

/-- Equality of actual selected solutions derives excision, including the finite-grid
clearance needed by the constructed integer degree. -/
theorem BoxComplementarityProblem.localDegree_eq_of_solutionsIn_eq
    (problem : BoxComplementarityProblem (Fin n))
    (first second : Set (UnitCube (Fin n)))
    (hfirst : problem.IsIsolating first) (hsecond : problem.IsIsolating second)
    (hequal : problem.solutionsIn first = problem.solutionsIn second) :
    problem.localDegree first hfirst = problem.localDegree second hsecond := by
  let cleared := (closure first \ second) ∪ (closure second \ first)
  have hcompactFirst : IsCompact (closure first) :=
    isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
  have hcompactSecond : IsCompact (closure second) :=
    isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
  have hcompact : IsCompact cleared :=
    (hcompactFirst.diff hsecond.1).union (hcompactSecond.diff hfirst.1)
  have hdisjoint : Disjoint cleared problem.solutionSet := by
    rw [Set.disjoint_left]
    intro point hpoint hsolution
    rcases hpoint with hpoint | hpoint
    · have hselected : point ∈ problem.solutionsIn first := by
        rw [← problem.solutionsIn_closure_eq_of_isIsolating first hfirst]
        exact ⟨hsolution, hpoint.1⟩
      rw [hequal] at hselected
      exact hpoint.2 hselected.2
    · have hselected : point ∈ problem.solutionsIn second := by
        rw [← problem.solutionsIn_closure_eq_of_isIsolating second hsecond]
        exact ⟨hsolution, hpoint.1⟩
      rw [← hequal] at hselected
      exact hpoint.2 hselected.2
  apply problem.localDegree_eq_of_eventually_cleared_difference
    first second cleared hfirst hsecond
  · intro point hpoint
    rcases hpoint with hpoint | hpoint
    · exact Or.inl ⟨subset_closure hpoint.1, hpoint.2⟩
    · exact Or.inr ⟨subset_closure hpoint.1, hpoint.2⟩
  · exact problem.eventually_no_completeSimplexVertexIn_of_compact cleared hcompact hdisjoint

end Math
