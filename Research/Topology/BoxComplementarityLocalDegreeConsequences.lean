import Research.Topology.BoxComplementarityStabilizedLocalDegree

/-! # Consequences of the whole-cube-normalized local degree -/

noncomputable section

namespace Math

open Set

variable {n : ℕ}

/-- The union of two isolating regions is isolating. -/
theorem BoxComplementarityProblem.isIsolating_union
    (problem : BoxComplementarityProblem (Fin n))
    (first second : Set (UnitCube (Fin n)))
    (hfirst : problem.IsIsolating first)
    (hsecond : problem.IsIsolating second) :
    problem.IsIsolating (first ∪ second) := by
  refine ⟨hfirst.1.union hsecond.1, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  intro point hpoint
  rcases hpoint with ⟨hsolution, hfrontier⟩
  have hcomponent : point ∈ frontier first ∪ frontier second :=
    (frontier_union_subset first second hfrontier) |> fun hpoint ↦
      Set.union_subset_union inter_subset_left inter_subset_right hpoint
  rcases hcomponent with hfirstFrontier | hsecondFrontier
  · have : point ∈ problem.solutionSet ∩ frontier first :=
      ⟨hsolution, hfirstFrontier⟩
    rw [hfirst.2] at this
    exact this
  · have : point ∈ problem.solutionSet ∩ frontier second :=
      ⟨hsolution, hsecondFrontier⟩
    rw [hsecond.2] at this
    exact this

/-- Stabilized local degree is additive on disjoint isolating regions. -/
theorem BoxComplementarityProblem.localDegree_union_of_disjoint
    (problem : BoxComplementarityProblem (Fin n))
    (first second : Set (UnitCube (Fin n)))
    (hfirst : problem.IsIsolating first)
    (hsecond : problem.IsIsolating second)
    (hdisjoint : Disjoint first second) :
    problem.localDegree (first ∪ second)
        (problem.isIsolating_union first second hfirst hsecond) =
      problem.localDegree first hfirst + problem.localDegree second hsecond := by
  let hunion := problem.isIsolating_union first second hfirst hsecond
  obtain ⟨firstThreshold, hfirstCount⟩ :=
    problem.eventually_normalizedLocalSignedCount_eq_localDegree first hfirst
  obtain ⟨secondThreshold, hsecondCount⟩ :=
    problem.eventually_normalizedLocalSignedCount_eq_localDegree second hsecond
  obtain ⟨unionThreshold, hunionCount⟩ :=
    problem.eventually_normalizedLocalSignedCount_eq_localDegree (first ∪ second) hunion
  let p := max (max firstThreshold secondThreshold) unionThreshold + 1
  have hp : 0 < p := Nat.zero_lt_succ _
  have hpFirst : firstThreshold ≤ p :=
    (le_max_left _ secondThreshold).trans
      ((le_max_left _ unionThreshold).trans (Nat.le_add_right _ 1))
  have hpSecond : secondThreshold ≤ p :=
    (le_max_right firstThreshold _).trans
      ((le_max_left _ unionThreshold).trans (Nat.le_add_right _ 1))
  have hpUnion : unionThreshold ≤ p :=
    (le_max_right (max firstThreshold secondThreshold) _).trans
      (Nat.le_add_right _ 1)
  calc
    problem.localDegree (first ∪ second) hunion =
        (-1 : ℤ) ^ n * boxComplementarityLocalSignedCount problem p hp (first ∪ second) :=
      (hunionCount p hpUnion hp).symm
    _ = (-1 : ℤ) ^ n * boxComplementarityLocalSignedCount problem p hp first +
        (-1 : ℤ) ^ n * boxComplementarityLocalSignedCount problem p hp second :=
      by rw [boxComplementarityLocalSignedCount_union_of_disjoint problem p hp hdisjoint,
        mul_add]
    _ = problem.localDegree first hfirst + problem.localDegree second hsecond := by
      rw [hfirstCount p hpFirst hp, hsecondCount p hpSecond hp]

/-- Eventual finite-grid clearance of the symmetric difference gives exact
excision for the stabilized local degrees of two isolating regions. -/
theorem BoxComplementarityProblem.localDegree_eq_of_eventually_cleared_difference
    (problem : BoxComplementarityProblem (Fin n))
    (first second cleared : Set (UnitCube (Fin n)))
    (hfirst : problem.IsIsolating first)
    (hsecond : problem.IsIsolating second)
    (hdifference : (first \ second) ∪ (second \ first) ⊆ cleared)
    (hcleared : ∃ threshold, ∀ p, threshold ≤ p →
      ¬problem.HasCompleteSimplexVertexIn cleared p) :
    problem.localDegree first hfirst = problem.localDegree second hsecond := by
  obtain ⟨firstThreshold, hfirstCount⟩ :=
    problem.eventually_normalizedLocalSignedCount_eq_localDegree first hfirst
  obtain ⟨secondThreshold, hsecondCount⟩ :=
    problem.eventually_normalizedLocalSignedCount_eq_localDegree second hsecond
  obtain ⟨clearThreshold, hclear⟩ := hcleared
  let p := max (max firstThreshold secondThreshold) clearThreshold + 1
  have hp : 0 < p := Nat.zero_lt_succ _
  have hpFirst : firstThreshold ≤ p :=
    (le_max_left _ secondThreshold).trans
      ((le_max_left _ clearThreshold).trans (Nat.le_add_right _ 1))
  have hpSecond : secondThreshold ≤ p :=
    (le_max_right firstThreshold _).trans
      ((le_max_left _ clearThreshold).trans (Nat.le_add_right _ 1))
  have hpClear : clearThreshold ≤ p :=
    (le_max_right (max firstThreshold secondThreshold) _).trans
      (Nat.le_add_right _ 1)
  calc
    problem.localDegree first hfirst =
        (-1 : ℤ) ^ n * boxComplementarityLocalSignedCount problem p hp first :=
      (hfirstCount p hpFirst hp).symm
    _ = (-1 : ℤ) ^ n * boxComplementarityLocalSignedCount problem p hp second :=
      congrArg (fun value : ℤ => (-1 : ℤ) ^ n * value)
        (boxComplementarityLocalSignedCount_eq_of_difference_subset_cleared
          problem p hp first second cleared hdifference (hclear p hpClear))
    _ = problem.localDegree second hsecond := hsecondCount p hpSecond hp

/-- One isolating frontier collar permits all stabilized region changes whose
symmetric difference lies inside that collar. -/
theorem BoxComplementarityProblem.exists_isolatingFrontierCollar_localDegree_coherent
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n)))
    (hisolating : problem.IsIsolating region) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ first second : Set (UnitCube (Fin n)),
        ∀ (hfirst : problem.IsIsolating first)
          (hsecond : problem.IsIsolating second),
        (first \ second) ∪ (second \ first) ⊆
            Metric.cthickening radius (frontier region) →
          problem.localDegree first hfirst =
            problem.localDegree second hsecond := by
  obtain ⟨radius, hradius, threshold, hcleared⟩ :=
    problem.exists_isolatingFrontierCollar_eventually_cleared region hisolating
  refine ⟨radius, hradius, ?_⟩
  intro first second hfirst hsecond hdifference
  exact problem.localDegree_eq_of_eventually_cleared_difference
    first second _ hfirst hsecond hdifference ⟨threshold, hcleared⟩

/-- Nonzero stabilized degree forces an actual complete-simplex vertex in the
region at every sufficiently fine positive resolution. -/
theorem BoxComplementarityProblem.eventually_hasCompleteSimplexVertexIn_of_localDegree_ne_zero
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n)))
    (hisolating : problem.IsIsolating region)
    (hnonzero : problem.localDegree region hisolating ≠ 0) :
    ∃ threshold, ∀ p, threshold ≤ p → ∀ _hp : 0 < p,
      problem.HasCompleteSimplexVertexIn region p := by
  obtain ⟨threshold, hcount⟩ :=
    problem.eventually_normalizedLocalSignedCount_eq_localDegree region hisolating
  refine ⟨threshold, fun p hpThreshold _hp => ?_⟩
  by_contra hno
  have hzero := boxComplementarityLocalSignedCount_eq_zero_of_no_vertex
    problem p _hp region hno
  apply hnonzero
  rw [← hcount p hpThreshold _hp, hzero, mul_zero]

/-- On any isolating region, nonzero stabilized degree forces an actual
complementarity solution in that region. -/
theorem BoxComplementarityProblem.exists_solution_mem_of_localDegree_ne_zero
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n)))
    (hisolating : problem.IsIsolating region)
    (hnonzero : problem.localDegree region hisolating ≠ 0) :
    ∃ point, point ∈ region ∧ point ∈ problem.solutionSet := by
  by_contra hno
  push Not at hno
  have hdisjoint : Disjoint (closure region) problem.solutionSet := by
    rw [Set.disjoint_left]
    intro point hpoint hsolution
    rw [closure_eq_self_union_frontier] at hpoint
    rcases hpoint with hregion | hfrontier
    · exact hno point hregion hsolution
    · have : point ∈ problem.solutionSet ∩ frontier region :=
        ⟨hsolution, hfrontier⟩
      rw [hisolating.2] at this
      exact this
  have hcompact : IsCompact (closure region) :=
    isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _)
  obtain ⟨clearThreshold, hclear⟩ :=
    problem.eventually_no_completeSimplexVertexIn_of_compact
      (closure region) hcompact hdisjoint
  obtain ⟨degreeThreshold, hdegree⟩ :=
    problem.eventually_hasCompleteSimplexVertexIn_of_localDegree_ne_zero
      region hisolating hnonzero
  let p := max clearThreshold degreeThreshold + 1
  have hp : 0 < p := Nat.zero_lt_succ _
  apply hclear p
    ((le_max_left _ degreeThreshold).trans (Nat.le_add_right _ 1))
  rcases hdegree p
      ((le_max_right clearThreshold _).trans (Nat.le_add_right _ 1)) hp with
    ⟨hp', vertices, hcomplete, index, hselected⟩
  exact ⟨hp', vertices, hcomplete, index, subset_closure hselected⟩

end Math
