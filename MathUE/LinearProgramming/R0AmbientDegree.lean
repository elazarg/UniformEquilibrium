import MathUE.Topology.AmbientDegree
import MathUE.LinearProgramming.R0Degree

/-!
# Intrinsic ambient comparison for the existing R0 integer

The packet uses the literal coordinatewise minimum map
`lcpMinMap matrix offset`. For R0 matrices its homogeneous field has only
the origin as a zero. The existing R0 integer therefore computes the new
intrinsic operation on every open bounded neighborhood of the origin.

The proof uses the actual enclosing scalar chart, source-owned isolation,
same-problem excision, and the existing positive-homogeneous radius comparison.
It does not redefine R0 degree or infer the full Brouwer-degree properties
from this comparison. No finite or regular root hypothesis is imposed.
-/

noncomputable section

namespace Math.LinearProgramming

open Set Math.Topology

variable {n : ℕ}

/-- R0 identifies the literal homogeneous minimum-map zero fiber. -/
theorem lcpMinMap_zero_eq_zero_iff_of_isR0Matrix
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hR0 : IsR0Matrix matrix) (point : Fin n → ℝ) :
    lcpMinMap matrix 0 point = 0 ↔ point = 0 := by
  constructor
  · intro hzero
    exact funext (hR0 point ((lcpMinMap_eq_zero_iff matrix 0 point).mp hzero))
  · rintro rfl
    exact (lcpMinMap_eq_zero_iff matrix 0 0).mpr
      (isStandardLCPSolution_zero matrix (fun _ => le_rfl))

/-- Openness and origin membership derive the source frontier condition. -/
theorem lcpMinMap_zero_ne_zero_on_frontier_of_isR0Matrix
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hR0 : IsR0Matrix matrix)
    (region : Set (Fin n → ℝ)) (hopen : IsOpen region) (horigin : 0 ∈ region) :
    ∀ point ∈ frontier region, lcpMinMap matrix 0 point ≠ 0 := by
  intro point hfrontier hzero
  have hequal := (lcpMinMap_zero_eq_zero_iff_of_isR0Matrix matrix hR0 point).mp hzero
  subst point
  exact hfrontier.2 (by simpa only [hopen.interior_eq] using horigin)

private theorem central_of_scalarChart_zero
    (radius : ℝ) (hradius : 0 < radius) (point : UnitCube (Fin n))
    (hzero : rectangularCubePoint (fun _ => -radius) (fun _ => radius) point = 0) :
    point ∈ diagonalCentralRegion n := by
  intro who
  have hcoordinate := congrFun hzero who
  dsimp [rectangularCubePoint, rectangularPoint] at hcoordinate
  constructor <;> nlinarith

/-- The existing R0 integer equals the intrinsic operation for the same literal
minimum field on any open bounded neighborhood of its unique zero. -/
theorem ambientDegree_lcpMinMap_zero_eq_r0Degree
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hR0 : IsR0Matrix matrix)
    (region : Set (Fin n → ℝ)) (hopen : IsOpen region)
    (hbounded : Bornology.IsBounded region) (horigin : 0 ∈ region) :
    ambientDegree (lcpMinMap matrix 0) region 0 hopen hbounded
        (continuous_lcpMinMap matrix 0).continuousOn
        (lcpMinMap_zero_ne_zero_on_frontier_of_isR0Matrix matrix hR0 region hopen horigin) =
      r0Degree matrix hR0 := by
  obtain ⟨radius, hradius, hball⟩ := hbounded.closure.subset_ball_lt (0 : ℝ) (0 : Fin n → ℝ)
  have hwidth : ∀ _ : Fin n, -radius < radius := by
    intro _
    linarith
  have hclosure : closure region ⊆
      {point : Fin n → ℝ | ∀ who, -radius < point who ∧ point who < radius} := by
    intro point hpoint who
    have hnorm : ‖point‖ < radius := by
      simpa only [Metric.mem_ball, dist_zero_right] using hball hpoint
    have hcoordinate := (norm_le_pi_norm point who).trans_lt hnorm
    rw [Real.norm_eq_abs] at hcoordinate
    exact abs_lt.mp hcoordinate
  let lower := fun _ : Fin n => -radius
  let upper := fun _ : Fin n => radius
  let chart := rectangularCubePoint lower upper
  let problem := BoxComplementarityProblem.ofAmbientMap lower upper hwidth
    (lcpMinMap matrix 0) (continuous_lcpMinMap matrix 0).continuousOn
  let cubeRegion := chart ⁻¹' region
  have hzeroFree := lcpMinMap_zero_ne_zero_on_frontier_of_isR0Matrix
    matrix hR0 region hopen horigin
  have hisolating : problem.IsIsolating cubeRegion :=
    BoxComplementarityProblem.isIsolating_ofAmbientMap_preimage_of_closure_subset
      lower upper hwidth (lcpMinMap matrix 0) (continuous_lcpMinMap matrix 0).continuousOn
      region hopen hclosure hzeroFree
  have hcomputed := ambientDegree_eq_of_extension (lcpMinMap matrix 0) region 0
    hopen hbounded (continuous_lcpMinMap matrix 0).continuousOn hzeroFree
    lower upper hwidth hclosure (lcpMinMap matrix 0)
    (continuous_lcpMinMap matrix 0).continuousOn (fun _ _ => rfl)
  have hactualDegree :
      ambientDegree (lcpMinMap matrix 0) region 0 hopen hbounded
        (continuous_lcpMinMap matrix 0).continuousOn hzeroFree =
      problem.localDegree cubeRegion hisolating := by
    simpa only [sub_zero] using hcomputed
  have hproblem : problem = lcpMinBoxProblem matrix 0 0 radius hradius := by
    apply BoxComplementarityProblem.ext
    funext point who
    simp only [problem, lower, upper, lcpMinBoxProblem,
      BoxComplementarityProblem.ofAmbientMap, Pi.zero_apply, zero_sub, zero_add]
  have hcentral : problem.IsIsolating (diagonalCentralRegion n) := by
    rw [hproblem]
    exact isIsolating_lcpMinBoxProblem_zero_of_isR0Matrix matrix hR0 radius hradius
  have hselected : problem.solutionsIn cubeRegion =
      problem.solutionsIn (diagonalCentralRegion n) := by
    ext point
    change (problem.IsSolution point ∧ chart point ∈ region) ↔
      (problem.IsSolution point ∧ point ∈ diagonalCentralRegion n)
    constructor
    · intro hpoint
      have hzero := (BoxComplementarityProblem.isSolution_ofAmbientMap_iff_of_imageInterior
        lower upper hwidth (lcpMinMap matrix 0) (continuous_lcpMinMap matrix 0).continuousOn
        point (hclosure (subset_closure hpoint.2))).mp hpoint.1
      have hsource := (lcpMinMap_zero_eq_zero_iff_of_isR0Matrix matrix hR0 (chart point)).mp hzero
      exact ⟨hpoint.1, central_of_scalarChart_zero radius hradius point hsource⟩
    · intro hpoint
      have hinterior (who : Fin n) : 0 < (point who : ℝ) ∧ (point who : ℝ) < 1 := by
        have h := hpoint.2 who
        constructor <;> linarith
      have hzero := (BoxComplementarityProblem.isSolution_ofAmbientMap_iff_of_coordinateInterior
        lower upper hwidth (lcpMinMap matrix 0) (continuous_lcpMinMap matrix 0).continuousOn
        point hinterior).mp hpoint.1
      have hsource := (lcpMinMap_zero_eq_zero_iff_of_isR0Matrix matrix hR0 (chart point)).mp hzero
      exact ⟨hpoint.1, hsource.symm ▸ horigin⟩
  have hexcision := problem.localDegree_eq_of_solutionsIn_eq
    cubeRegion (diagonalCentralRegion n) hisolating hcentral hselected
  have hr0 : problem.localDegree (diagonalCentralRegion n) hcentral = r0Degree matrix hR0 := by
    simpa only [hproblem] using
      localDegree_lcpMinBoxProblem_zero_eq_r0Degree matrix hR0 radius hradius
  exact hactualDegree.trans (hexcision.trans hr0)

/-- The old literal normalized signed count computes the intrinsic homogeneous
minimum-map degree on every sufficiently fine grid of the canonical chart. -/
theorem eventually_normalizedLocalSignedCount_eq_ambientDegree_lcpMinMap_zero
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hR0 : IsR0Matrix matrix)
    (region : Set (Fin n → ℝ)) (hopen : IsOpen region)
    (hbounded : Bornology.IsBounded region) (horigin : 0 ∈ region) :
    ∃ threshold, ∀ p, threshold ≤ p → ∀ hp : 0 < p,
      (-1 : ℤ) ^ n *
        boxComplementarityLocalSignedCount (lcpMinBoxProblem matrix 0 0 2 (by norm_num))
          p hp (diagonalCentralRegion n) =
      ambientDegree (lcpMinMap matrix 0) region 0 hopen hbounded
        (continuous_lcpMinMap matrix 0).continuousOn
        (lcpMinMap_zero_ne_zero_on_frontier_of_isR0Matrix matrix hR0 region hopen horigin) := by
  rw [ambientDegree_lcpMinMap_zero_eq_r0Degree matrix hR0 region hopen hbounded horigin]
  let problem := lcpMinBoxProblem matrix 0 0 2 (by norm_num)
  exact problem.eventually_normalizedLocalSignedCount_eq_localDegree (diagonalCentralRegion n)
      (isIsolating_lcpMinBoxProblem_zero_of_isR0Matrix matrix hR0 2 (by norm_num))

end Math.LinearProgramming
