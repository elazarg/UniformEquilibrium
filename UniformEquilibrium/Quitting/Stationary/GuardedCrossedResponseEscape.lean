import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseDegree

/-! # Global degree escape for the literal crossed auxiliary map -/

noncomputable section

namespace GameTheory

open Set _root_.Math _root_.Math.Topology _root_.Math.LinearProgramming

variable {n : ℕ}

private abbrev crossedGlobalChart (point : UnitCube (Fin n)) : Fin n → ℝ :=
  rectangularCubePoint (fun _ => (-2 : ℝ)) (fun _ => (2 : ℝ)) point

/-- The genuine crossed clipped field in a global chart containing the whole
auxiliary strategy box strictly in its interior. -/
def quittingCrossedGlobalProblem
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ) : BoxComplementarityProblem (Fin n) :=
  BoxComplementarityProblem.ofAmbientMap
    (fun _ => (-2 : ℝ)) (fun _ => (2 : ℝ)) (by intro; norm_num)
    (quittingCrossedFixedPointField reward first second height)
    (by
      apply Continuous.continuousOn
      unfold quittingCrossedFixedPointField
      have hclipped := continuous_quittingCrossedClippedMap reward first second height
      fun_prop)

private theorem crossedGlobalChart_norm_of_frontier_ball
    (radius : ℝ) (point : UnitCube (Fin n))
    (hpoint : point ∈ frontier (crossedGlobalChart ⁻¹' Metric.ball 0 radius)) :
    ‖crossedGlobalChart point‖ = radius := by
  have hsource := (continuous_rectangularCubePoint (fun _ : Fin n => -2)
    (fun _ => 2)).frontier_preimage_subset (Metric.ball 0 radius) hpoint
  simpa only [Metric.mem_sphere, dist_zero_right] using
    Metric.frontier_ball_subset_sphere hsource

private theorem crossedGlobalChart_coordinateInterior_of_norm_lt_two
    (point : UnitCube (Fin n)) (hpoint : ‖crossedGlobalChart point‖ < 2) :
    ∀ coordinate, 0 < (point coordinate : ℝ) ∧ (point coordinate : ℝ) < 1 := by
  apply (rectangularCubePoint_coordinateInterior_iff
    (show ∀ _ : Fin n, (-2 : ℝ) < 2 by intro _; norm_num) point).mp
  intro coordinate
  have h := (norm_le_pi_norm (crossedGlobalChart point) coordinate).trans_lt hpoint
  exact abs_lt.mp h

private theorem exists_pos_crossed_min_sphere_margin
    (matrix : Matrix (Fin n) (Fin n) ℝ) (hR0 : IsR0Matrix matrix) :
    ∃ margin : ℝ, 0 < margin ∧
      ∀ point ∈ Metric.sphere (0 : Fin n → ℝ) 1,
        margin ≤ ‖lcpMinMap matrix 0 point‖ := by
  apply (isCompact_sphere (0 : Fin n → ℝ) 1).exists_forall_le'
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

private theorem crossedGlobalChart_zero_mem_ball
    {radius : ℝ} (hradius : 0 < radius) (point : UnitCube (Fin n))
    (hzero : crossedGlobalChart point = 0) :
    point ∈ crossedGlobalChart ⁻¹' Metric.ball 0 radius := by
  change dist (crossedGlobalChart point) 0 < radius
  simpa only [hzero, dist_self] using hradius

/-- The literal height-capped crossed map has local degree `κ(PΓ)` at zero
in the same ambient chart as its global degree-one self-map argument. -/
theorem exists_globalCrossed_localDegree_eq_r0Degree
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ) (hheight : 0 < height)
    (hR0 : IsR0Matrix (quittingCrossedSingletonMatrix reward first second)) :
    ∃ radius : ℝ, 0 < radius ∧ radius < 1 ∧
      ∃ hisolating :
        (quittingCrossedGlobalProblem reward first second height).IsIsolating
          (crossedGlobalChart ⁻¹' Metric.ball 0 radius),
        (quittingCrossedGlobalProblem reward first second height).localDegree
            (crossedGlobalChart ⁻¹' Metric.ball 0 radius) hisolating =
          r0Degree (quittingCrossedSingletonMatrix reward first second) hR0 := by
  let A := quittingCrossedSingletonMatrix reward first second
  let base := lcpMinBoxProblem A 0 0 2 (by norm_num)
  let actual := quittingCrossedGlobalProblem reward first second height
  have hbase : base.IsIsolating (diagonalCentralRegion n) :=
    isIsolating_lcpMinBoxProblem_zero_of_isR0Matrix A hR0 2 (by norm_num)
  obtain ⟨margin, hmargin, hmarginSphere⟩ :=
    exists_pos_crossed_min_sphere_margin A hR0
  obtain ⟨δ, hδ, happrox⟩ := quittingCrossedMinFieldScaled_uniform_bound
    reward first second
      (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 1)) hmargin
  obtain ⟨upperRadius, hupperRadius, hupperLocal⟩ := Metric.eventually_nhds_iff.mp
    (eventually_quittingCrossed_upperClip_inactive reward first second height hheight)
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
  let region : Set (UnitCube (Fin n)) := crossedGlobalChart ⁻¹' Metric.ball 0 radius
  have hopen : IsOpen region := Metric.isOpen_ball.preimage
    (continuous_rectangularCubePoint (fun _ : Fin n => -2) (fun _ => 2))
  have hinterior (point : UnitCube (Fin n)) (hfrontier : point ∈ frontier region) :
      ∀ coordinate, 0 < (point coordinate : ℝ) ∧ (point coordinate : ℝ) < 1 := by
    have hnorm : ‖crossedGlobalChart point‖ = radius :=
      crossedGlobalChart_norm_of_frontier_ball radius point hfrontier
    exact crossedGlobalChart_coordinateInterior_of_norm_lt_two point (by linarith)
  have hclose (point : UnitCube (Fin n)) (hfrontier : point ∈ frontier region) :
      ‖actual.gain point - base.gain point‖ < ‖base.gain point‖ := by
    let source := crossedGlobalChart point
    let scaled := radius⁻¹ • source
    have hnorm : ‖source‖ = radius :=
      crossedGlobalChart_norm_of_frontier_ball radius point hfrontier
    have hscaledNorm : ‖scaled‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hradius), hnorm]
      field_simp [hradius.ne']
    have hscaledSphere : scaled ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hscaledNorm
    have hscaledBall : scaled ∈ Metric.closedBall (0 : Fin n → ℝ) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, hscaledNorm]
    have hfieldApprox := happrox radius hradius hradiusApprox scaled hscaledBall
    have hsourceScaled : radius • scaled = source := by
      dsimp only [scaled]
      exact smul_inv_smul₀ hradius.ne' source
    have hupper : ∀ coordinate,
        source coordinate + quittingCrossedResponse reward first second source coordinate ≤
          quittingCrossedCeiling first second height coordinate := by
      intro coordinate
      exact (hupperLocal (by rw [dist_zero_right, hnorm]; exact hradiusUpper)
        coordinate).le
    have hfield : quittingCrossedFixedPointField reward first second height source =
        quittingCrossedMinField reward first second source :=
      quittingCrossedFixedPointField_eq_minField
        reward first second height hheight source hupper
    have hmodel : lcpMinMap A 0 source = radius • lcpMinMap A 0 scaled := by
      rw [← hsourceScaled]
      exact lcpMinMap_zero_smul A radius hradius.le scaled
    have herror :
        ‖quittingCrossedFixedPointField reward first second height source -
          lcpMinMap A 0 source‖ < ‖lcpMinMap A 0 source‖ := by
      rw [hfield, hmodel]
      have hscaledField : quittingCrossedMinFieldScaled reward first second
          radius scaled = radius⁻¹ •
            quittingCrossedMinField reward first second source := by
        simp only [quittingCrossedMinFieldScaled, hsourceScaled]
      rw [hscaledField] at hfieldApprox
      have hmarginBound := hmarginSphere scaled hscaledSphere
      have hstrict := hfieldApprox.trans_le hmarginBound
      have hequal :
          quittingCrossedMinField reward first second source -
            radius • lcpMinMap A 0 scaled =
          radius • (radius⁻¹ • quittingCrossedMinField reward first second source -
            lcpMinMap A 0 scaled) := by
        rw [smul_sub, smul_inv_smul₀ hradius.ne']
      rw [hequal, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hradius]
      exact mul_lt_mul_of_pos_left hstrict hradius
    simp only [actual, base, quittingCrossedGlobalProblem,
      lcpMinBoxProblem, BoxComplementarityProblem.ofAmbientMap,
      Pi.zero_apply, zero_sub, zero_add]
    change ‖-quittingCrossedFixedPointField reward first second height source -
      -lcpMinMap A 0 source‖ < ‖-lcpMinMap A 0 source‖
    calc
      ‖-quittingCrossedFixedPointField reward first second height source -
          -lcpMinMap A 0 source‖ =
          ‖-(quittingCrossedFixedPointField reward first second height source -
            lcpMinMap A 0 source)‖ := by congr 1; abel
      _ = ‖quittingCrossedFixedPointField reward first second height source -
          lcpMinMap A 0 source‖ := norm_neg _
      _ < ‖lcpMinMap A 0 source‖ := herror
      _ = ‖-lcpMinMap A 0 source‖ := (norm_neg _).symm
  obtain ⟨hbaseRegion, hactualRegion, heqDegree⟩ :=
    base.localDegree_eq_of_norm_sub_lt_norm actual region hopen hinterior hclose
  have hsubset : region ⊆ diagonalCentralRegion n := by
    intro point hpoint coordinate
    have hnorm : ‖crossedGlobalChart point‖ < radius := by
      simpa only [region, mem_preimage, Metric.mem_ball, dist_zero_right] using hpoint
    have hcoord := (norm_le_pi_norm (crossedGlobalChart point) coordinate).trans_lt hnorm
    rw [Real.norm_eq_abs, abs_lt] at hcoord
    dsimp [crossedGlobalChart, rectangularCubePoint, rectangularPoint] at hcoord
    constructor <;> nlinarith [hcoord.1, hcoord.2, hradiusOne]
  have hsolutions : base.solutionsIn region =
      base.solutionsIn (diagonalCentralRegion n) := by
    ext point
    constructor
    · intro hpoint
      exact ⟨hpoint.1, hsubset hpoint.2⟩
    · intro hpoint
      have hinteriorPoint (coordinate : Fin n) :
          0 < (point coordinate : ℝ) ∧ (point coordinate : ℝ) < 1 := by
        have h := hpoint.2 coordinate
        constructor <;> linarith
      have hzero := (BoxComplementarityProblem.isSolution_iff_gain_eq_zero_of_coordinateInterior
        base point hinteriorPoint).mp hpoint.1
      have hroot : IsStandardLCPSolution A 0 (crossedGlobalChart point) := by
        apply (lcpMinMap_eq_zero_iff A 0 (crossedGlobalChart point)).mp
        simp only [base, lcpMinBoxProblem, BoxComplementarityProblem.ofAmbientMap,
          Pi.zero_apply, zero_sub, zero_add] at hzero
        change -lcpMinMap A 0 (crossedGlobalChart point) = 0 at hzero
        exact neg_eq_zero.mp hzero
      have hchartZero : crossedGlobalChart point = 0 := by
        funext coordinate
        exact hR0 (crossedGlobalChart point) hroot coordinate
      exact ⟨hpoint.1, crossedGlobalChart_zero_mem_ball hradius point hchartZero⟩
  have hbaseDegree := base.localDegree_eq_of_solutionsIn_eq region
    (diagonalCentralRegion n) hbaseRegion hbase hsolutions
  refine ⟨radius, hradius, hradiusOne, hactualRegion, ?_⟩
  exact heqDegree.symm.trans
    (hbaseDegree.trans (localDegree_lcpMinBoxProblem_zero_eq_r0Degree A hR0 2
      (by norm_num)))

/-- A nonunit local index forces an actual nonzero fixed point of the
crossed auxiliary response map. No root is supplied as a hypothesis. -/
theorem exists_nonzero_quittingCrossedClippedMap_fixedPoint
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ)
    (hheight : 0 < height) (hheightOne : height ≤ 1)
    (hR0 : IsR0Matrix (quittingCrossedSingletonMatrix reward first second))
    (hdegree : r0Degree (quittingCrossedSingletonMatrix reward first second) hR0 ≠ 1) :
    ∃ point : Fin n → ℝ, point ≠ 0 ∧
      quittingCrossedClippedMap reward first second height point = point := by
  obtain ⟨radius, hradius, _hradiusOne, hisolating, hlocalDegree⟩ :=
    exists_globalCrossed_localDegree_eq_r0Degree reward first second height
      hheight hR0
  let actual := quittingCrossedGlobalProblem reward first second height
  have hlocalNe : actual.localDegree
      (crossedGlobalChart ⁻¹' Metric.ball 0 radius) hisolating ≠ 1 := by
    rw [hlocalDegree]
    exact hdegree
  obtain ⟨cubePoint, hsolution, houtside⟩ :=
    actual.exists_solution_not_mem_closure_of_localDegree_ne_one
      (crossedGlobalChart ⁻¹' Metric.ball 0 radius) hisolating hlocalNe
  let map := quittingCrossedClippedMap reward first second height
  have hmap : ContinuousOn map (Icc (fun _ : Fin n => -2) (fun _ => 2)) :=
    (continuous_quittingCrossedClippedMap reward first second height).continuousOn
  have hself : MapsTo map (Icc (fun _ : Fin n => -2) (fun _ => 2))
      (Icc (fun _ => -2) (fun _ => 2)) := by
    intro source _
    constructor <;> intro coordinate
    · have hzero : 0 ≤ map source coordinate := by
        change 0 ≤ min (quittingCrossedCeiling first second height coordinate)
          (max 0 (source coordinate +
            quittingCrossedResponse reward first second source coordinate))
        apply le_min
        · unfold quittingCrossedCeiling
          split_ifs <;> linarith
        · exact le_max_left _ _
      linarith
    · have hceiling : map source coordinate ≤
          quittingCrossedCeiling first second height coordinate := by
        exact min_le_left _ _
      have hupper : quittingCrossedCeiling first second height coordinate ≤ 1 := by
        unfold quittingCrossedCeiling
        split_ifs <;> linarith
      linarith
  have hfixed : crossedGlobalChart cubePoint = map (crossedGlobalChart cubePoint) := by
    apply (BoxComplementarityProblem.isSolution_of_selfMap_iff
      (fun _ : Fin n => -2) (fun _ => 2) (by intro; norm_num)
      map hmap hself cubePoint).mp
    exact hsolution
  have hnonzero : crossedGlobalChart cubePoint ≠ 0 := by
    intro hzero
    apply houtside
    exact subset_closure (crossedGlobalChart_zero_mem_ball hradius cubePoint hzero)
  exact ⟨crossedGlobalChart cubePoint, hnonzero, hfixed.symm⟩

end GameTheory
