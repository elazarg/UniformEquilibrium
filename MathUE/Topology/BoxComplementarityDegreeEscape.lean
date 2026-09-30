import MathUE.Topology.BoxComplementaritySolutionExcision
import MathUE.Topology.BoxComplementarityMeshOneNormalization

/-!
# Escape from an isolated local degree

The whole cube has integer degree one. If an isolating region has a
different degree, an actual solution lies outside its closure. This is the
topological producer used after a source map's all-Continue zero has been
isolated and its local degree identified.
-/

noncomputable section

namespace Math

open Set

variable {n : ℕ}

/-- Removing the closure of an isolating region leaves an isolating region. -/
theorem BoxComplementarityProblem.isIsolating_compl_closure
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n))) (hisolating : problem.IsIsolating region) :
    problem.IsIsolating (closure region)ᶜ := by
  refine ⟨isClosed_closure.isOpen_compl, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  intro point hpoint
  rcases hpoint with ⟨hsolution, hfrontier⟩
  rw [frontier_compl] at hfrontier
  have hforbidden : point ∈ problem.solutionSet ∩ frontier region :=
    ⟨hsolution, frontier_closure_subset hfrontier⟩
  rw [hisolating.2] at hforbidden
  exact hforbidden

/-- In one fixed cube problem, the degree outside an isolating closure is
the whole-cube degree one minus the removed local degree. No solution
finiteness, regularity, or ambient-chart independence is assumed. -/
theorem BoxComplementarityProblem.localDegree_compl_closure
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n))) (hisolating : problem.IsIsolating region) :
    problem.localDegree (closure region)ᶜ
        (problem.isIsolating_compl_closure region hisolating) =
      1 - problem.localDegree region hisolating := by
  let outside := (closure region)ᶜ
  let houtside := problem.isIsolating_compl_closure region hisolating
  have hdisjoint : Disjoint region outside := by
    rw [Set.disjoint_left]
    intro point hregion hout
    exact hout (subset_closure hregion)
  have hselected : problem.solutionsIn (region ∪ outside) =
      problem.solutionsIn univ := by
    ext point
    constructor
    · exact fun hpoint => ⟨hpoint.1, mem_univ point⟩
    · intro hpoint
      by_cases hclosure : point ∈ closure region
      · have hinside : point ∈ problem.solutionsIn region := by
          rw [← problem.solutionsIn_closure_eq_of_isIsolating region hisolating]
          exact ⟨hpoint.1, hclosure⟩
        exact ⟨hpoint.1, Or.inl hinside.2⟩
      · exact ⟨hpoint.1, Or.inr hclosure⟩
  have hglobal := problem.localDegree_eq_of_solutionsIn_eq
    (region ∪ outside) univ (problem.isIsolating_union region outside hisolating houtside)
    (by simp [BoxComplementarityProblem.IsIsolating]) hselected
  have hadd := problem.localDegree_union_of_disjoint region outside
    hisolating houtside hdisjoint
  have hone : problem.localDegree region hisolating +
      problem.localDegree outside houtside = 1 :=
    hadd.symm.trans (hglobal.trans problem.localDegree_univ_eq_one)
  change problem.localDegree outside houtside = _
  linarith

/-- A local degree different from the whole-cube degree forces an actual
complementarity solution outside the isolating region, even outside its
closure. No finiteness or isolation of that second solution is required. -/
theorem BoxComplementarityProblem.exists_solution_not_mem_closure_of_localDegree_ne_one
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n)))
    (hisolating : problem.IsIsolating region)
    (hdegree : problem.localDegree region hisolating ≠ 1) :
    ∃ point, point ∈ problem.solutionSet ∧ point ∉ closure region := by
  by_contra hno
  have hinside : problem.solutionSet ⊆ closure region := by
    intro point hsolution
    by_contra houtside
    exact hno ⟨point, hsolution, houtside⟩
  have hselected : problem.solutionsIn region = problem.solutionsIn univ := by
    ext point
    constructor
    · exact fun hpoint => ⟨hpoint.1, mem_univ point⟩
    · intro hpoint
      have hclosure : point ∈ problem.solutionsIn (closure region) :=
        ⟨hpoint.1, hinside hpoint.1⟩
      rw [problem.solutionsIn_closure_eq_of_isIsolating region hisolating]
        at hclosure
      exact hclosure
  have hglobal := problem.localDegree_eq_of_solutionsIn_eq
    region univ hisolating (by simp [BoxComplementarityProblem.IsIsolating])
      hselected
  exact hdegree (hglobal.trans problem.localDegree_univ_eq_one)

end Math
