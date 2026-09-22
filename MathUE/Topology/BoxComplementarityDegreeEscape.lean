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
