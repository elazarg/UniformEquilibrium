import Research.Topology.BoxComplementaritySpernerLocalCount
import Mathlib.Topology.Maps.Proper.Basic

/-!
# A uniform solution-free collar for a continuous complementarity family

The same relative region is isolating for every parameter in the closed unit
interval. Closedness and compact projection give one spatial collar disjoint
from every actual family solution. This is not yet mesh clearance.
-/

noncomputable section

namespace Math

open Set

variable {n : ℕ}

/-- The actual parameter-solution graph is closed under the existing joint-continuity contract. -/
theorem IsContinuousBoxComplementarityFamily.isClosed_solutionGraph
    {family : Set.Icc (0 : ℝ) 1 → BoxComplementarityProblem (Fin n)}
    (hcontinuous : IsContinuousBoxComplementarityFamily (Fin n) family) :
    IsClosed {pair : Set.Icc (0 : ℝ) 1 × UnitCube (Fin n) |
      (family pair.1).IsSolution pair.2} := by
  have hset : {pair : Set.Icc (0 : ℝ) 1 × UnitCube (Fin n) |
      (family pair.1).IsSolution pair.2} =
      ⋂ who : Fin n,
        {pair | 0 ≤ (pair.2 who : ℝ) * (family pair.1).gain pair.2 who} ∩
        {pair | (1 - (pair.2 who : ℝ)) * (family pair.1).gain pair.2 who ≤ 0} := by
    ext pair
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
    exact (family pair.1).isSolution_iff_mul_gain pair.2
  rw [hset]
  apply isClosed_iInter
  intro who
  have hcoordinate : Continuous
      (fun pair : Set.Icc (0 : ℝ) 1 × UnitCube (Fin n) => (pair.2 who : ℝ)) :=
    continuous_subtype_val.comp ((continuous_apply who).comp continuous_snd)
  exact (isClosed_le continuous_const (hcoordinate.mul (hcontinuous who))).inter
    (isClosed_le ((continuous_const.sub hcoordinate).mul (hcontinuous who)) continuous_const)

/-- Compactness of the parameter interval makes the union of its solution sets closed. -/
theorem IsContinuousBoxComplementarityFamily.isClosed_exists_solution
    {family : Set.Icc (0 : ℝ) 1 → BoxComplementarityProblem (Fin n)}
    (hcontinuous : IsContinuousBoxComplementarityFamily (Fin n) family) :
    IsClosed {point : UnitCube (Fin n) | ∃ parameter, (family parameter).IsSolution point} := by
  have himage : {point : UnitCube (Fin n) | ∃ parameter, (family parameter).IsSolution point} =
      Prod.snd '' {pair : Set.Icc (0 : ℝ) 1 × UnitCube (Fin n) |
        (family pair.1).IsSolution pair.2} := by
    ext point
    simp only [Set.mem_setOf_eq, Set.mem_image, Prod.exists, exists_eq_right]
  rw [himage]
  exact isClosedMap_snd_of_compactSpace _ hcontinuous.isClosed_solutionGraph

/-- One positive spatial collar avoids every member's solutions, with the original region fixed. -/
theorem IsContinuousBoxComplementarityFamily.exists_uniform_isolatingFrontierCollar
    {family : Set.Icc (0 : ℝ) 1 → BoxComplementarityProblem (Fin n)}
    (hcontinuous : IsContinuousBoxComplementarityFamily (Fin n) family)
    (region : Set (UnitCube (Fin n)))
    (hisolating : ∀ parameter, (family parameter).IsIsolating region) :
    ∃ radius : ℝ, 0 < radius ∧
      IsCompact (Metric.cthickening radius (frontier region)) ∧
      ∀ parameter, Disjoint (Metric.cthickening radius (frontier region))
        (family parameter).solutionSet := by
  have hfrontier : IsCompact (frontier region) := isClosed_frontier.isCompact
  have hsubset : frontier region ⊆
      {point : UnitCube (Fin n) | ∃ parameter, (family parameter).IsSolution point}ᶜ := by
    intro point hpoint hsolution
    obtain ⟨parameter, hsolution⟩ := hsolution
    have hbad : point ∈ (family parameter).solutionSet ∩ frontier region :=
      ⟨hsolution, hpoint⟩
    rw [(hisolating parameter).2] at hbad
    exact hbad
  obtain ⟨radius, hradius, hcollar⟩ := hfrontier.exists_cthickening_subset_open
    hcontinuous.isClosed_exists_solution.isOpen_compl hsubset
  refine ⟨radius, hradius, hfrontier.cthickening, ?_⟩
  intro parameter
  rw [Set.disjoint_left]
  intro point hpoint hsolution
  exact hcollar hpoint ⟨parameter, hsolution⟩

end Math
