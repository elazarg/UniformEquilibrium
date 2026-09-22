import MathUE.LinearProgramming.CopositiveQCorollaries
import Research.Topology.LinearComplementarityLocalIndex
import Research.Topology.BoxComplementarityMeshOneNormalization
import Research.Topology.BoxComplementarityLocalDegreeConsequences

/-!
# Total degree of an R0 minimum-complementarity map

The zero-offset map has one zero. Its degree in a fixed central region
defines the R0 integer. Positive homogeneity compares concentric scalar
charts directly, without arbitrary-chart independence.

The existing R0 solution bound supplies one chart and one central region
for all offsets in a coordinatewise bounded family. Literal offset homotopies
are isolating there, so their total degrees agree with the R0 integer.
Nonzero offsets may have degenerate or nonisolated roots. Cube-boundary
complementarity solutions are not identified with ambient LCP roots.
-/

noncomputable section

namespace Math.LinearProgramming

open Set Math.Topology

variable {n : ℕ}

private theorem source_lcp_of_centralClosure_solution
    (matrix : Matrix (Fin n) (Fin n) ℝ) (offset : Fin n → ℝ)
    (radius : ℝ) (hradius : 0 < radius) (point : UnitCube (Fin n))
    (hpoint : point ∈ closure (diagonalCentralRegion n))
    (hsolution : (lcpMinBoxProblem matrix offset 0 radius hradius).IsSolution point) :
    IsStandardLCPSolution matrix offset
      (rectangularCubePoint (fun _ => -radius) (fun _ => radius) point) := by
  have hbounds := coordinate_bounds_of_mem_closure_diagonalCentralRegion hpoint
  have hinterior (who : Fin n) : 0 < (point who : ℝ) ∧ (point who : ℝ) < 1 := by
    have h := hbounds who
    constructor <;> linarith
  have hzero :=
    (BoxComplementarityProblem.isSolution_iff_gain_eq_zero_of_coordinateInterior
      (lcpMinBoxProblem matrix offset 0 radius hradius) point hinterior).mp hsolution
  apply (lcpMinMap_eq_zero_iff matrix offset _).mp
  simp only [lcpMinBoxProblem, BoxComplementarityProblem.ofAmbientMap,
    Pi.zero_apply, zero_sub, zero_add] at hzero
  change -lcpMinMap matrix offset
    (rectangularCubePoint (fun _ => -radius) (fun _ => radius) point) = 0 at hzero
  exact neg_eq_zero.mp hzero

private theorem isIsolating_central_of_lcp_bound
    (matrix : Matrix (Fin n) (Fin n) ℝ) (offset : Fin n → ℝ)
    (radius : ℝ) (hradius : 0 < radius)
    (hbound : ∀ root, IsStandardLCPSolution matrix offset root →
      ∀ who, root who < radius / 2) :
    (lcpMinBoxProblem matrix offset 0 radius hradius).IsIsolating
      (diagonalCentralRegion n) := by
  refine ⟨isOpen_diagonalCentralRegion, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  rintro point ⟨hsolution, hfrontier⟩
  have hsource := source_lcp_of_centralClosure_solution matrix offset radius hradius
    point (frontier_subset_closure hfrontier) hsolution
  have hcentral : point ∈ diagonalCentralRegion n := by
    intro who
    have hlower := hsource.weight_nonneg who
    have hupper := hbound _ hsource who
    dsimp [rectangularCubePoint, rectangularPoint] at hlower hupper
    have hleft : radius * (1 / 4 : ℝ) < radius * (point who : ℝ) := by
      nlinarith
    have hright : radius * (point who : ℝ) < radius * (3 / 4 : ℝ) := by
      nlinarith
    exact ⟨(mul_lt_mul_iff_right₀ hradius).mp hleft,
      (mul_lt_mul_iff_right₀ hradius).mp hright⟩
  exact hfrontier.2 (by
    simpa only [isOpen_diagonalCentralRegion.interior_eq] using hcentral)

/-- R0 alone isolates the homogeneous minimum map in every positive
zero-centered scalar chart's central region. -/
theorem isIsolating_lcpMinBoxProblem_zero_of_isR0Matrix
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hR0 : IsR0Matrix matrix)
    (radius : ℝ) (hradius : 0 < radius) :
    (lcpMinBoxProblem matrix 0 0 radius hradius).IsIsolating
      (diagonalCentralRegion n) := by
  apply isIsolating_central_of_lcp_bound
  intro root hroot who
  rw [hR0 root hroot who]
  exact half_pos hradius

/-- The R0 integer is the actual normalized degree of the homogeneous
minimum map in the fixed chart `[-2,2]`, selecting its central region. -/
def r0Degree (matrix : Matrix (Fin n) (Fin n) ℝ) (hR0 : IsR0Matrix matrix) : ℤ :=
  (lcpMinBoxProblem matrix 0 0 2 (by norm_num)).localDegree
    (diagonalCentralRegion n)
    (isIsolating_lcpMinBoxProblem_zero_of_isR0Matrix matrix hR0 2 (by norm_num))

/-- In dimension zero the canonical central region is the whole singleton cube,
so its R0 integer is one. -/
theorem r0Degree_fin_zero (matrix : Matrix (Fin 0) (Fin 0) ℝ)
    (hR0 : IsR0Matrix matrix) : r0Degree matrix hR0 = 1 := by
  have hregion : diagonalCentralRegion 0 = Set.univ := by
    ext point
    simp [diagonalCentralRegion]
  simpa only [r0Degree, hregion] using
    (lcpMinBoxProblem matrix 0 0 2 (by norm_num)).localDegree_univ_eq_one

private theorem lcpMinMap_zero_smul
    (matrix : Matrix (Fin n) (Fin n) ℝ) (scalar : ℝ) (hscalar : 0 ≤ scalar)
    (point : Fin n → ℝ) :
    lcpMinMap matrix 0 (scalar • point) = scalar • lcpMinMap matrix 0 point := by
  funext who
  simp only [lcpMinMap, lcpResidual, Pi.zero_apply, zero_add, Pi.smul_apply, smul_eq_mul]
  have hsum : (∑ coordinate, (scalar * point coordinate) * matrix who coordinate) =
      scalar * ∑ coordinate, point coordinate * matrix who coordinate := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro coordinate _
    ring
  rw [hsum]
  exact (mul_min_of_nonneg _ _ hscalar).symm

/-- Changing the radius of the homogeneous scalar chart preserves its
central degree by literal positive scaling of the gain field. -/
theorem localDegree_lcpMinBoxProblem_zero_eq_r0Degree
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hR0 : IsR0Matrix matrix)
    (radius : ℝ) (hradius : 0 < radius) :
    (lcpMinBoxProblem matrix 0 0 radius hradius).localDegree
        (diagonalCentralRegion n)
        (isIsolating_lcpMinBoxProblem_zero_of_isR0Matrix matrix hR0 radius hradius) =
      r0Degree matrix hR0 := by
  have hchart (point : UnitCube (Fin n)) :
      rectangularCubePoint (fun _ => -radius) (fun _ => radius) point =
        (radius / 2) • rectangularCubePoint (fun _ => -2) (fun _ => 2) point := by
    funext who
    dsimp [rectangularCubePoint, rectangularPoint]
    ring
  have hproblem : lcpMinBoxProblem matrix 0 0 radius hradius =
      (lcpMinBoxProblem matrix 0 0 2 (by norm_num)).scaleGain (radius / 2) := by
    apply BoxComplementarityProblem.ext
    funext point who
    dsimp only [lcpMinBoxProblem, BoxComplementarityProblem.ofAmbientMap,
      BoxComplementarityProblem.scaleGain]
    simp only [Pi.zero_apply, zero_sub, zero_add]
    rw [hchart, lcpMinMap_zero_smul matrix _ (half_pos hradius).le]
    simp only [Pi.smul_apply, smul_eq_mul, mul_neg]
  simpa only [hproblem, r0Degree] using
    (lcpMinBoxProblem matrix 0 0 2 (by norm_num)).localDegree_scaleGain
      (half_pos hradius) (diagonalCentralRegion n)
      (isIsolating_lcpMinBoxProblem_zero_of_isR0Matrix matrix hR0 2 (by norm_num))

/-- R0 supplies one actual common scalar chart and isolating central region
for every coordinatewise-bounded offset. Every total degree is the canonical
R0 integer, regardless of degeneracy or infinitude of the selected roots. -/
theorem exists_radius_lcpMinBoxProblem_localDegree_eq_r0Degree
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hR0 : IsR0Matrix matrix) (bound : ℝ) :
    ∃ (radius : ℝ) (hradius : 0 < radius), ∀ offset : Fin n → ℝ,
      (∀ who, |offset who| ≤ bound) →
      ∃ hisolating : (lcpMinBoxProblem matrix offset 0 radius hradius).IsIsolating
          (diagonalCentralRegion n),
        (∀ root, IsStandardLCPSolution matrix offset root →
          ∀ who, root who < radius / 2) ∧
        (lcpMinBoxProblem matrix offset 0 radius hradius).localDegree
          (diagonalCentralRegion n) hisolating = r0Degree matrix hR0 := by
  obtain ⟨totalBound, htotalBound⟩ := exists_bound_sum_of_isR0Matrix matrix hR0 bound
  let radius := 2 * (max 0 totalBound + 1)
  have hradius : 0 < radius := by
    dsimp only [radius]
    have h := le_max_left 0 totalBound
    linarith
  have hbound (offset root : Fin n → ℝ) (hoffset : ∀ who, |offset who| ≤ bound)
      (hroot : IsStandardLCPSolution matrix offset root) (who : Fin n) :
      root who < radius / 2 := by
    have hcoordinate : root who ≤ ∑ next, root next :=
      Finset.single_le_sum (fun next _ => hroot.weight_nonneg next) (Finset.mem_univ who)
    have hsum := htotalBound offset root hoffset hroot
    have hmax := le_max_right 0 totalBound
    dsimp only [radius]
    linarith
  refine ⟨radius, hradius, ?_⟩
  intro offset hoffset
  let family (parameter : Set.Icc (0 : ℝ) 1) :=
    lcpMinBoxProblem matrix ((parameter : ℝ) • offset) 0 radius hradius
  have hfamilyBound (parameter : Set.Icc (0 : ℝ) 1) (who : Fin n) :
      |((parameter : ℝ) • offset) who| ≤ bound := by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg parameter.property.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) parameter.property.2).trans (hoffset who)
  have hisolating (parameter : Set.Icc (0 : ℝ) 1) :
      (family parameter).IsIsolating (diagonalCentralRegion n) :=
    isIsolating_central_of_lcp_bound matrix _ radius hradius
      (fun root hroot who => hbound _ root (hfamilyBound parameter) hroot who)
  have hcontinuous : IsContinuousBoxComplementarityFamily (Fin n) family := by
    let chart := rectangularCubePoint (fun _ : Fin n => -radius) (fun _ => radius)
    have hchart : Continuous chart := continuous_rectangularCubePoint _ _
    intro who
    dsimp only [family, lcpMinBoxProblem, BoxComplementarityProblem.ofAmbientMap,
      lcpMinMap, lcpResidual]
    simp only [Pi.zero_apply, zero_sub, zero_add, Pi.smul_apply, smul_eq_mul]
    change Continuous fun data : Set.Icc (0 : ℝ) 1 × UnitCube (Fin n) =>
      -min (chart data.2 who)
        ((data.1 : ℝ) * offset who +
          ∑ coordinate, chart data.2 coordinate * matrix who coordinate)
    fun_prop
  have hdegree := hcontinuous.localDegree_endpoints_eq (diagonalCentralRegion n) hisolating
  have hactual : (lcpMinBoxProblem matrix offset 0 radius hradius).IsIsolating
      (diagonalCentralRegion n) := by
    simpa only [family, Set.Icc.coe_one, one_smul] using hisolating 1
  refine ⟨hactual, fun root hroot who => hbound offset root hoffset hroot who, ?_⟩
  have hcomparison :
      (lcpMinBoxProblem matrix offset 0 radius hradius).localDegree
          (diagonalCentralRegion n) hactual =
        (lcpMinBoxProblem matrix 0 0 radius hradius).localDegree
          (diagonalCentralRegion n)
          (isIsolating_lcpMinBoxProblem_zero_of_isR0Matrix matrix hR0 radius hradius) := by
    simpa only [family, Set.Icc.coe_zero, Set.Icc.coe_one, zero_smul, one_smul] using
      hdegree.symm
  exact hcomparison.trans
    (localDegree_lcpMinBoxProblem_zero_eq_r0Degree matrix hR0 radius hradius)

/-- Nonzero total R0 degree gives a standard LCP solution for every offset. -/
theorem isStandardQ_of_r0Degree_ne_zero
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hR0 : IsR0Matrix matrix)
    (hdegree : r0Degree matrix hR0 ≠ 0) : IsStandardQ matrix := by
  intro offset
  obtain ⟨radius, hradius, hfamily⟩ :=
    exists_radius_lcpMinBoxProblem_localDegree_eq_r0Degree matrix hR0
      (∑ who, |offset who|)
  obtain ⟨hisolating, _hrootBound, hlocal⟩ := hfamily offset (fun who =>
    Finset.single_le_sum (fun next _ => abs_nonneg (offset next)) (Finset.mem_univ who))
  have hnonzero : (lcpMinBoxProblem matrix offset 0 radius hradius).localDegree
      (diagonalCentralRegion n) hisolating ≠ 0 := by
    rwa [hlocal]
  obtain ⟨point, hpoint, hsolution⟩ :=
    BoxComplementarityProblem.exists_solution_mem_of_localDegree_ne_zero
      (lcpMinBoxProblem matrix offset 0 radius hradius)
      (diagonalCentralRegion n) hisolating hnonzero
  exact ⟨_, source_lcp_of_centralClosure_solution matrix offset radius hradius
    point (subset_closure hpoint) hsolution⟩

end Math.LinearProgramming
