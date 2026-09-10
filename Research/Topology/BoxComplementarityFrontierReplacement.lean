import Research.Topology.BoxComplementarityStabilizedLocalDegree

/-!
# Frontier replacement for normalized complementarity degree

The explicit straight-line family fixes any common frontier gain field.
This is a consequence of the existing common-isolating homotopy theorem,
not an identification with ambient Brouwer degree.
-/

noncomputable section

namespace Math

open Set

namespace BoxComplementarityProblem

variable {ι : Type*} [Fintype ι]

/-- The literal straight-line interpolation of two continuous gain fields. -/
def straightLine (first second : BoxComplementarityProblem ι)
    (parameter : Set.Icc (0 : ℝ) 1) : BoxComplementarityProblem ι where
  gain point who := (1 - (parameter : ℝ)) * first.gain point who +
    (parameter : ℝ) * second.gain point who
  continuous_gain who :=
    ((first.continuous_gain who).const_mul _).add
      ((second.continuous_gain who).const_mul _)

@[simp] theorem straightLine_zero (first second : BoxComplementarityProblem ι) :
    first.straightLine second 0 = first := by
  cases first
  simp [straightLine]

@[simp] theorem straightLine_one (first second : BoxComplementarityProblem ι) :
    first.straightLine second 1 = second := by
  cases second
  simp [straightLine]

/-- Straight-line interpolation is jointly continuous in its parameter and point. -/
theorem isContinuous_straightLine (first second : BoxComplementarityProblem ι) :
    IsContinuousBoxComplementarityFamily ι (first.straightLine second) := by
  intro who
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    ((first.continuous_gain who).comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).mul
        ((second.continuous_gain who).comp continuous_snd))

/-- Equal frontier gain fields transfer isolation, without an extra endpoint hypothesis. -/
theorem isIsolating_of_gain_eqOn_frontier
    (first second : BoxComplementarityProblem ι) (region : Set (UnitCube ι))
    (hisolating : first.IsIsolating region)
    (hequal : EqOn first.gain second.gain (frontier region)) :
    second.IsIsolating region := by
  refine ⟨hisolating.1, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  rintro point ⟨hsolution, hfrontier⟩
  have hfirst : first.IsSolution point := by
    simpa only [solutionSet, mem_setOf_eq, IsSolution, ← hequal hfrontier] using hsolution
  have hmem : point ∈ first.solutionSet ∩ frontier region := ⟨hfirst, hfrontier⟩
  rw [hisolating.2] at hmem
  exact hmem

/-- Every interpolated problem fixes the frontier gain field. -/
theorem gain_straightLine_eqOn_frontier
    (first second : BoxComplementarityProblem ι) (region : Set (UnitCube ι))
    (hequal : EqOn first.gain second.gain (frontier region))
    (parameter : Set.Icc (0 : ℝ) 1) :
    EqOn first.gain (first.straightLine second parameter).gain (frontier region) := by
  intro point hpoint
  funext who
  simp only [straightLine, ← congrFun (hequal hpoint) who]
  ring

/-- Frontier equality gives a common isolating region for the explicit straight line. -/
theorem isIsolating_straightLine_of_gain_eqOn_frontier
    (first second : BoxComplementarityProblem ι) (region : Set (UnitCube ι))
    (hisolating : first.IsIsolating region)
    (hequal : EqOn first.gain second.gain (frontier region))
    (parameter : Set.Icc (0 : ℝ) 1) :
    (first.straightLine second parameter).IsIsolating region :=
  first.isIsolating_of_gain_eqOn_frontier _ region hisolating
    (first.gain_straightLine_eqOn_frontier second region hequal parameter)

/-- Replacing a gain field away from the isolating frontier preserves normalized degree. -/
theorem localDegree_eq_of_gain_eqOn_frontier
    {n : ℕ} (first second : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n))) (hisolating : first.IsIsolating region)
    (hequal : EqOn first.gain second.gain (frontier region)) :
    first.localDegree region hisolating =
      second.localDegree region
        (first.isIsolating_of_gain_eqOn_frontier second region hisolating hequal) := by
  have hfamily := (first.isContinuous_straightLine second).localDegree_endpoints_eq region
    (first.isIsolating_straightLine_of_gain_eqOn_frontier second region hisolating hequal)
  simpa only [straightLine_zero, straightLine_one] using hfamily

end BoxComplementarityProblem

end Math
