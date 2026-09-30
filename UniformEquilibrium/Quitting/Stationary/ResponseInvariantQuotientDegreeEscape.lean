import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientLocalDegree
import MathUE.Topology.BoxComplementarityDegreeEscape
import MathUE.Topology.BoxComplementaritySelfMapNormalization

/-!
# Escape from the all-Continue quotient root

The same global centered chart is used for the clipped response and the
homogeneous R0 model. A shrinking source ball permits frontier comparison
without an arbitrary-chart degree transfer.
-/

noncomputable section

namespace GameTheory

open Set _root_.Math _root_.Math.Topology _root_.Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- The fixed signed chart used for the normalized quotient degree. -/
abbrev quittingQuotientGlobalChart (point : UnitCube (Fin k)) : Fin k → ℝ :=
  rectangularCubePoint (fun _ => (-2 : ℝ)) (fun _ => (2 : ℝ)) point

private abbrev quotientChart := @quittingQuotientGlobalChart

/-- The actual quotient self-map field in one global symmetric chart. -/
def quittingQuotientGlobalProblem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι) :
    BoxComplementarityProblem (Fin k) :=
  BoxComplementarityProblem.ofAmbientMap
    (fun _ => (-2 : ℝ)) (fun _ => (2 : ℝ))
    (by intro; norm_num)
    (quittingQuotientFixedPointField reward block representative)
    (by
      apply Continuous.continuousOn
      unfold quittingQuotientFixedPointField
      have hclipped := continuous_quittingQuotientStationaryClippedMap
        reward block representative
      fun_prop)

private theorem quotientChart_norm_of_frontier_ball
    (radius : ℝ) (point : UnitCube (Fin k))
    (hpoint : point ∈ frontier (quotientChart ⁻¹' Metric.ball 0 radius)) :
    ‖quotientChart point‖ = radius := by
  have hsource := (continuous_rectangularCubePoint (fun _ : Fin k => -2)
    (fun _ => 2)).frontier_preimage_subset (Metric.ball 0 radius) hpoint
  simpa only [Metric.mem_sphere, dist_zero_right] using
    Metric.frontier_ball_subset_sphere hsource

private theorem quotientChart_coordinateInterior_of_norm_lt_two
    (point : UnitCube (Fin k)) (hpoint : ‖quotientChart point‖ < 2) :
    ∀ coordinate, 0 < (point coordinate : ℝ) ∧ (point coordinate : ℝ) < 1 := by
  apply (rectangularCubePoint_coordinateInterior_iff
    (show ∀ _ : Fin k, (-2 : ℝ) < 2 by intro _; norm_num) point).mp
  intro coordinate
  have h := (norm_le_pi_norm (quotientChart point) coordinate).trans_lt hpoint
  exact abs_lt.mp h

private theorem exists_pos_quotient_min_sphere_margin
    (matrix : Matrix (Fin k) (Fin k) ℝ) (hR0 : IsR0Matrix matrix) :
    ∃ margin : ℝ, 0 < margin ∧
      ∀ point ∈ Metric.sphere (0 : Fin k → ℝ) 1,
        margin ≤ ‖lcpMinMap matrix 0 point‖ := by
  apply (isCompact_sphere (0 : Fin k → ℝ) 1).exists_forall_le'
    (continuous_lcpMinMap matrix 0).norm.continuousOn
  intro point hpoint
  apply norm_pos_iff.mpr
  intro hzero
  have hroot := (lcpMinMap_eq_zero_iff matrix 0 point).mp hzero
  have hpointZero : point = 0 := by
    funext coordinate
    exact hR0 point hroot coordinate
  have hnorm : ‖point‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hpoint
  simp [hpointZero] at hnorm

private theorem quotientChart_zero_mem_ball
    {radius : ℝ} (hradius : 0 < radius) (point : UnitCube (Fin k))
    (hzero : quotientChart point = 0) :
    point ∈ quotientChart ⁻¹' Metric.ball 0 radius := by
  change dist (quotientChart point) 0 < radius
  simpa only [hzero, dist_self] using hradius

/-- One radius isolates the actual origin on its closed ball and identifies
its canonical R0 local degree in the fixed global self-map chart. -/
theorem exists_globalQuotient_originIsolation_localDegree_eq_r0Degree
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hR0 : IsR0Matrix
      (quittingResponseQuotientMatrix reward block representative)) :
    ∃ radius : ℝ, 0 < radius ∧ radius < 1 ∧
      (∀ source : Fin k → ℝ, ‖source‖ ≤ radius →
        quittingQuotientStationaryClippedMap reward block representative source = source →
          source = 0) ∧
      ∃ hisolating :
        (quittingQuotientGlobalProblem reward block representative).IsIsolating
          (quittingQuotientGlobalChart ⁻¹' Metric.ball 0 radius),
        (quittingQuotientGlobalProblem reward block representative).localDegree
            (quittingQuotientGlobalChart ⁻¹' Metric.ball 0 radius) hisolating =
          r0Degree (quittingResponseQuotientMatrix reward block representative) hR0 := by
  let A := quittingResponseQuotientMatrix reward block representative
  let base := lcpMinBoxProblem A 0 0 2 (by norm_num)
  let actual := quittingQuotientGlobalProblem reward block representative
  have hbase : base.IsIsolating (diagonalCentralRegion k) :=
    isIsolating_lcpMinBoxProblem_zero_of_isR0Matrix A hR0 2 (by norm_num)
  obtain ⟨margin, hmargin, hmarginSphere⟩ :=
    exists_pos_quotient_min_sphere_margin A hR0
  obtain ⟨δ, hδ, happrox⟩ := quittingQuotientMinFieldScaled_uniform_bound
    reward block representative
      (Metric.isBounded_closedBall (x := (0 : Fin k → ℝ)) (r := 1)) hmargin
  obtain ⟨upperRadius, hupperRadius, hupperLocal⟩ := Metric.eventually_nhds_iff.mp
    (eventually_quittingQuotient_upperClip_inactive reward block representative)
  let radius := min (min (δ / 2) (upperRadius / 4)) (1 / 2)
  have hradius : 0 < radius := by dsimp [radius]; positivity
  have hradiusOne : radius < 1 := by
    dsimp [radius]
    have h := min_le_right (min (δ / 2) (upperRadius / 4)) (1 / 2)
    linarith
  have hradiusApprox : radius ≤ δ := by
    dsimp [radius]
    have h := (min_le_left (min (δ / 2) (upperRadius / 4)) (1 / 2)).trans
      (min_le_left (δ / 2) (upperRadius / 4))
    linarith
  have hradiusUpper : radius < upperRadius := by
    dsimp [radius]
    have h := (min_le_left (min (δ / 2) (upperRadius / 4)) (1 / 2)).trans
      (min_le_right (δ / 2) (upperRadius / 4))
    linarith
  let region : Set (UnitCube (Fin k)) := quotientChart ⁻¹' Metric.ball 0 radius
  have hopen : IsOpen region := Metric.isOpen_ball.preimage
    (continuous_rectangularCubePoint (fun _ : Fin k => -2) (fun _ => 2))
  have hinterior (point : UnitCube (Fin k)) (hfrontier : point ∈ frontier region) :
      ∀ coordinate, 0 < (point coordinate : ℝ) ∧ (point coordinate : ℝ) < 1 := by
    have hnorm : ‖quotientChart point‖ = radius :=
      quotientChart_norm_of_frontier_ball radius point hfrontier
    exact quotientChart_coordinateInterior_of_norm_lt_two point (by linarith)
  have herror (source : Fin k → ℝ) (hnonzero : source ≠ 0) (hsmall : ‖source‖ ≤ radius) :
      ‖quittingQuotientFixedPointField reward block representative source -
        lcpMinMap A 0 source‖ < ‖lcpMinMap A 0 source‖ := by
    let scalar := ‖source‖
    let scaled := scalar⁻¹ • source
    have hscalar : 0 < scalar := norm_pos_iff.mpr hnonzero
    have hscalarApprox : scalar ≤ δ := hsmall.trans hradiusApprox
    have hscaledNorm : ‖scaled‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hscalar)]
      change scalar⁻¹ * scalar = 1
      exact inv_mul_cancel₀ hscalar.ne'
    have hscaledSphere : scaled ∈ Metric.sphere (0 : Fin k → ℝ) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hscaledNorm
    have hscaledBall : scaled ∈ Metric.closedBall (0 : Fin k → ℝ) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, hscaledNorm]
    have hfieldApprox := happrox scalar hscalar hscalarApprox scaled hscaledBall
    have hsourceScaled : scalar • scaled = source := by
      dsimp only [scaled]
      exact smul_inv_smul₀ hscalar.ne' source
    have hupper : ∀ coordinate,
        source coordinate + quittingQuotientResponse reward block representative
          source coordinate ≤ 1 := by
      intro coordinate
      exact (hupperLocal (by rw [dist_zero_right]; exact hsmall.trans_lt hradiusUpper)
        coordinate).le
    have hfield : quittingQuotientFixedPointField reward block representative source =
        quittingQuotientMinField reward block representative source :=
      quittingQuotientFixedPointField_eq_minField
        reward block representative hrepresentative source hupper
    have hmodel : lcpMinMap A 0 source = scalar • lcpMinMap A 0 scaled := by
      rw [← hsourceScaled]
      exact lcpMinMap_zero_smul A scalar hscalar.le scaled
    rw [hfield, hmodel]
    have hscaledField : quittingQuotientMinFieldScaled reward block representative
        scalar scaled = scalar⁻¹ •
          quittingQuotientMinField reward block representative source := by
      simp only [quittingQuotientMinFieldScaled, hsourceScaled]
    rw [hscaledField] at hfieldApprox
    have hstrict := hfieldApprox.trans_le (hmarginSphere scaled hscaledSphere)
    have hequal :
        quittingQuotientMinField reward block representative source -
          scalar • lcpMinMap A 0 scaled =
        scalar • (scalar⁻¹ •
          quittingQuotientMinField reward block representative source -
            lcpMinMap A 0 scaled) := by
      rw [smul_sub, smul_inv_smul₀ hscalar.ne']
    rw [hequal, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hscalar]
    exact mul_lt_mul_of_pos_left hstrict hscalar
  have hisolation (source : Fin k → ℝ) (hsmall : ‖source‖ ≤ radius)
      (hfixed : quittingQuotientStationaryClippedMap reward block representative source =
        source) : source = 0 := by
    by_contra hnonzero
    have hstrict := herror source hnonzero hsmall
    have hfieldZero : quittingQuotientFixedPointField reward block representative source =
        0 := by
      simp only [quittingQuotientFixedPointField, hfixed, sub_self]
    rw [hfieldZero, zero_sub, norm_neg] at hstrict
    exact (lt_irrefl _) hstrict
  have hclose (point : UnitCube (Fin k)) (hfrontier : point ∈ frontier region) :
      ‖actual.gain point - base.gain point‖ < ‖base.gain point‖ := by
    let source := quotientChart point
    have hnorm : ‖source‖ = radius :=
      quotientChart_norm_of_frontier_ball radius point hfrontier
    have hnonzero : source ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hnorm
      exact hradius.ne' hnorm.symm
    have hstrict := herror source hnonzero hnorm.le
    simp only [actual, base, quittingQuotientGlobalProblem,
      lcpMinBoxProblem, BoxComplementarityProblem.ofAmbientMap,
      Pi.zero_apply, zero_sub, zero_add]
    change ‖-quittingQuotientFixedPointField reward block representative source -
      -lcpMinMap A 0 source‖ < ‖-lcpMinMap A 0 source‖
    calc
      ‖-quittingQuotientFixedPointField reward block representative source -
          -lcpMinMap A 0 source‖ =
          ‖-(quittingQuotientFixedPointField reward block representative source -
            lcpMinMap A 0 source)‖ := by congr 1; abel
      _ = ‖quittingQuotientFixedPointField reward block representative source -
          lcpMinMap A 0 source‖ := norm_neg _
      _ < ‖lcpMinMap A 0 source‖ := hstrict
      _ = ‖-lcpMinMap A 0 source‖ := (norm_neg _).symm
  obtain ⟨hbaseRegion, hactualRegion, heqDegree⟩ :=
    base.localDegree_eq_of_norm_sub_lt_norm actual region hopen hinterior hclose
  have hsubset : region ⊆ diagonalCentralRegion k := by
    intro point hpoint coordinate
    have hnorm : ‖quotientChart point‖ < radius := by
      simpa only [region, mem_preimage, Metric.mem_ball, dist_zero_right] using hpoint
    have hcoord := (norm_le_pi_norm (quotientChart point) coordinate).trans_lt hnorm
    rw [Real.norm_eq_abs, abs_lt] at hcoord
    dsimp [quotientChart, quittingQuotientGlobalChart,
      rectangularCubePoint, rectangularPoint] at hcoord
    constructor <;> nlinarith [hcoord.1, hcoord.2, hradiusOne]
  have hsolutions : base.solutionsIn region =
      base.solutionsIn (diagonalCentralRegion k) := by
    ext point
    constructor
    · intro hpoint
      exact ⟨hpoint.1, hsubset hpoint.2⟩
    · intro hpoint
      have hinteriorPoint (coordinate : Fin k) :
          0 < (point coordinate : ℝ) ∧ (point coordinate : ℝ) < 1 := by
        have h := hpoint.2 coordinate
        constructor <;> linarith
      have hzero := (BoxComplementarityProblem.isSolution_iff_gain_eq_zero_of_coordinateInterior
        base point hinteriorPoint).mp hpoint.1
      have hroot : IsStandardLCPSolution A 0 (quotientChart point) := by
        apply (lcpMinMap_eq_zero_iff A 0 (quotientChart point)).mp
        simp only [base, lcpMinBoxProblem, BoxComplementarityProblem.ofAmbientMap,
          Pi.zero_apply, zero_sub, zero_add] at hzero
        change -lcpMinMap A 0 (quotientChart point) = 0 at hzero
        exact neg_eq_zero.mp hzero
      have hchartZero : quotientChart point = 0 := by
        funext coordinate
        exact hR0 (quotientChart point) hroot coordinate
      exact ⟨hpoint.1, quotientChart_zero_mem_ball hradius point hchartZero⟩
  have hbaseDegree := base.localDegree_eq_of_solutionsIn_eq region
    (diagonalCentralRegion k) hbaseRegion hbase hsolutions
  refine ⟨radius, hradius, hradiusOne, hisolation, hactualRegion, ?_⟩
  exact heqDegree.symm.trans
    (hbaseDegree.trans (localDegree_lcpMinBoxProblem_zero_eq_r0Degree A hR0 2
      (by norm_num)))

/-- The actual quotient clipped map has canonical R0 local degree on a
derived small ball in the fixed global self-map chart. -/
theorem exists_globalQuotient_localDegree_eq_r0Degree
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hR0 : IsR0Matrix
      (quittingResponseQuotientMatrix reward block representative)) :
    ∃ radius : ℝ, 0 < radius ∧ radius < 1 ∧
      ∃ hisolating :
        (quittingQuotientGlobalProblem reward block representative).IsIsolating
          (quittingQuotientGlobalChart ⁻¹' Metric.ball 0 radius),
        (quittingQuotientGlobalProblem reward block representative).localDegree
            (quittingQuotientGlobalChart ⁻¹' Metric.ball 0 radius) hisolating =
          r0Degree (quittingResponseQuotientMatrix reward block representative) hR0 := by
  obtain ⟨radius, hradius, hsmall, -, hisolating, hdegree⟩ :=
    exists_globalQuotient_originIsolation_localDegree_eq_r0Degree
      reward block representative hrepresentative hR0
  exact ⟨radius, hradius, hsmall, hisolating, hdegree⟩

/-- A quotient degree different from one forces a nonzero fixed point of
the literal block-coordinate stationary clipped map. -/
theorem exists_nonzero_quittingQuotientStationaryClippedMap_fixedPoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hR0 : IsR0Matrix
      (quittingResponseQuotientMatrix reward block representative))
    (hdegree : r0Degree (quittingResponseQuotientMatrix reward block representative)
      hR0 ≠ 1) :
    ∃ point : Fin k → ℝ, point ≠ 0 ∧
      quittingQuotientStationaryClippedMap reward block representative point = point := by
  obtain ⟨radius, hradius, _hradiusOne, hisolating, hlocalDegree⟩ :=
    exists_globalQuotient_localDegree_eq_r0Degree reward block representative
      hrepresentative hR0
  let actual := quittingQuotientGlobalProblem reward block representative
  have hlocalNe : actual.localDegree (quotientChart ⁻¹' Metric.ball 0 radius)
      hisolating ≠ 1 := by
    rw [hlocalDegree]
    exact hdegree
  obtain ⟨cubePoint, hsolution, houtside⟩ :=
    actual.exists_solution_not_mem_closure_of_localDegree_ne_one
      (quotientChart ⁻¹' Metric.ball 0 radius) hisolating hlocalNe
  let map := quittingQuotientStationaryClippedMap reward block representative
  have hmap : ContinuousOn map (Icc (fun _ : Fin k => -2) (fun _ => 2)) :=
    (continuous_quittingQuotientStationaryClippedMap reward block representative).continuousOn
  have hself : MapsTo map (Icc (fun _ : Fin k => -2) (fun _ => 2))
      (Icc (fun _ => -2) (fun _ => 2)) := by
    intro source _
    have hcube := quittingQuotientStationaryClippedMap_mem_unitCube
      reward block representative source
    constructor <;> intro coordinate
    · have h := hcube.1 coordinate
      change 0 ≤ map source coordinate at h
      linarith
    · have h := hcube.2 coordinate
      change map source coordinate ≤ 1 at h
      linarith
  have hfixed : quotientChart cubePoint = map (quotientChart cubePoint) := by
    apply (BoxComplementarityProblem.isSolution_of_selfMap_iff
      (fun _ : Fin k => -2) (fun _ => 2) (by intro; norm_num)
      map hmap hself cubePoint).mp
    exact hsolution
  have hnonzero : quotientChart cubePoint ≠ 0 := by
    intro hzero
    apply houtside
    exact subset_closure (quotientChart_zero_mem_ball hradius cubePoint hzero)
  exact ⟨quotientChart cubePoint, hnonzero, hfixed.symm⟩

end GameTheory
