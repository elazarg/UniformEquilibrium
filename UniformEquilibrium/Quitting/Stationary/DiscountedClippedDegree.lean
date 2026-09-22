import UniformEquilibrium.Quitting.Stationary.DiscountedClippedScaling
import MathUE.LinearProgramming.R0Degree
import MathUE.Topology.BoxComplementaritySelfMapNormalization
import MathUE.Topology.BoxComplementarityFrontierPerturbation

/-!
# Total R0 degree from localization of the actual discounted clipped map

The comparison uses one fixed rectangular chart and shrinking sup-norm balls.
Uniform localization of every literal discounted clipped fixed point normalizes
its degree to one. The source-derived scaling estimate compares it with the
actual minimum LCP map, and equality of the selected solution sets excises back
to the common R0 region. No arbitrary-chart invariance, root finiteness, or
regular-root hypothesis is used. Signed rewards and dimension zero are retained.
-/

noncomputable section

namespace GameTheory

open Set _root_.Math _root_.Math.Topology _root_.Math.LinearProgramming
  QuittingLCPClassification

variable {n : ℕ}

private abbrev degreeChart (radius : ℝ) : UnitCube (Fin n) → (Fin n → ℝ) :=
  rectangularCubePoint (fun _ => -radius) (fun _ => radius)

private theorem centralRegion_eq_degreeChart_preimage_ball
    (radius : ℝ) (hradius : 0 < radius) :
    diagonalCentralRegion n = degreeChart radius ⁻¹' Metric.ball 0 (radius / 2) := by
  ext point
  change (∀ who, 1 / 4 < (point who : ℝ) ∧ (point who : ℝ) < 3 / 4) ↔
    dist (degreeChart radius point) 0 < radius / 2
  rw [dist_zero_right, pi_norm_lt_iff (half_pos hradius)]
  constructor
  · intro hpoint who
    rw [Real.norm_eq_abs, abs_lt]
    have h := hpoint who
    dsimp [degreeChart, rectangularCubePoint, rectangularPoint]
    constructor <;> nlinarith
  · intro hpoint who
    have h := hpoint who
    rw [Real.norm_eq_abs, abs_lt] at h
    dsimp [degreeChart, rectangularCubePoint, rectangularPoint] at h
    constructor <;> nlinarith

private theorem norm_degreeChart_of_mem_frontier_preimage_ball
    (radius innerRadius : ℝ) (point : UnitCube (Fin n))
    (hpoint : point ∈ frontier (degreeChart radius ⁻¹' Metric.ball 0 innerRadius)) :
    ‖degreeChart radius point‖ = innerRadius := by
  have hsource := (continuous_rectangularCubePoint (fun _ : Fin n => -radius)
    (fun _ => radius)).frontier_preimage_subset (Metric.ball 0 innerRadius) hpoint
  simpa only [Metric.mem_sphere, dist_zero_right] using
    Metric.frontier_ball_subset_sphere hsource

private theorem coordinateInterior_of_norm_degreeChart_lt
    (radius : ℝ) (hradius : 0 < radius) (point : UnitCube (Fin n))
    (hpoint : ‖degreeChart radius point‖ < radius) :
    ∀ who, 0 < (point who : ℝ) ∧ (point who : ℝ) < 1 := by
  apply (rectangularCubePoint_coordinateInterior_iff
    (show ∀ _ : Fin n, -radius < radius by intro _; linarith) point).mp
  intro who
  have h := (norm_le_pi_norm (degreeChart radius point) who).trans_lt hpoint
  exact abs_lt.mp h

private theorem lcpMinBoxProblem_gain_degreeChart
    (matrix : Matrix (Fin n) (Fin n) ℝ) (offset : Fin n → ℝ)
    (radius : ℝ) (hradius : 0 < radius) (point : UnitCube (Fin n)) :
    (lcpMinBoxProblem matrix offset 0 radius hradius).gain point =
      -lcpMinMap matrix offset (degreeChart radius point) := by
  funext who
  simp only [lcpMinBoxProblem, BoxComplementarityProblem.ofAmbientMap,
    Pi.zero_apply, zero_sub, zero_add]
  rfl

private theorem norm_lcp_root_lt_of_coordinate_bound
    (matrix : Matrix (Fin n) (Fin n) ℝ) (offset root : Fin n → ℝ)
    (radius : ℝ) (hradius : 0 < radius)
    (hroot : IsStandardLCPSolution matrix offset root)
    (hbound : ∀ who, root who < radius) : ‖root‖ < radius := by
  apply (pi_norm_lt_iff hradius).mpr
  intro who
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hroot.weight_nonneg who)] using hbound who

private theorem exists_pos_minMap_sphere_margin
    (matrix : Matrix (Fin n) (Fin n) ℝ) (offset : Fin n → ℝ)
    (radius : ℝ) (hradius : 0 < radius)
    (hbound : ∀ root, IsStandardLCPSolution matrix offset root →
      ∀ who, root who < radius) :
    ∃ margin : ℝ, 0 < margin ∧
      ∀ point ∈ Metric.sphere (0 : Fin n → ℝ) radius,
        margin ≤ ‖lcpMinMap matrix offset point‖ := by
  apply (isCompact_sphere (0 : Fin n → ℝ) radius).exists_forall_le'
    (continuous_lcpMinMap matrix offset).norm.continuousOn
  intro point hpoint
  apply norm_pos_iff.mpr
  intro hzero
  have hroot := (lcpMinMap_eq_zero_iff matrix offset point).mp hzero
  have hnorm := norm_lcp_root_lt_of_coordinate_bound matrix offset point radius hradius
    hroot (hbound point hroot)
  have hequal : ‖point‖ = radius := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hpoint
  exact (ne_of_lt hnorm) hequal

private theorem quittingDiscountedClippedMap_mem_unitBox
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (discount : ℝ) (hazard : Fin n → ℝ) :
    quittingDiscountedClippedMap reward discount hazard ∈
      Icc (0 : Fin n → ℝ) 1 := by
  constructor <;> intro who
  · exact le_min (by norm_num) (le_max_left _ _)
  · exact min_le_left _ _

private theorem solutionsIn_shrinking_ball_eq_central
    (matrix : Matrix (Fin n) (Fin n) ℝ) (offset : Fin n → ℝ)
    (radius : ℝ) (hradius : 0 < radius)
    (scalar : ℝ) (hscalar : 0 < scalar) (hscalarOne : scalar ≤ 1)
    (hbound : ∀ root, IsStandardLCPSolution matrix offset root →
      ∀ who, root who < radius / 2) :
    (lcpMinBoxProblem matrix (scalar • offset) 0 radius hradius).solutionsIn
        (degreeChart radius ⁻¹' Metric.ball 0 (scalar * (radius / 2))) =
      (lcpMinBoxProblem matrix (scalar • offset) 0 radius hradius).solutionsIn
        (diagonalCentralRegion n) := by
  ext point
  constructor
  · intro hpoint
    refine ⟨hpoint.1, ?_⟩
    rw [centralRegion_eq_degreeChart_preimage_ball radius hradius]
    have hnorm : ‖degreeChart radius point‖ < scalar * (radius / 2) := by
      simpa only [mem_preimage, Metric.mem_ball, dist_zero_right] using hpoint.2
    change dist (degreeChart radius point) 0 < radius / 2
    rw [dist_zero_right]
    exact hnorm.trans_le (mul_le_of_le_one_left (half_pos hradius).le hscalarOne)
  · intro hpoint
    have hinterior : ∀ who, 0 < (point who : ℝ) ∧ (point who : ℝ) < 1 := by
      intro who
      have h := hpoint.2 who
      constructor <;> linarith
    have hzero := (BoxComplementarityProblem.isSolution_iff_gain_eq_zero_of_coordinateInterior
      (lcpMinBoxProblem matrix (scalar • offset) 0 radius hradius) point hinterior).mp hpoint.1
    rw [lcpMinBoxProblem_gain_degreeChart] at hzero
    have hsource := (lcpMinMap_eq_zero_iff matrix (scalar • offset)
      (degreeChart radius point)).mp (neg_eq_zero.mp hzero)
    have hscaled : IsStandardLCPSolution matrix offset
        (scalar⁻¹ • degreeChart radius point) := by
      apply (isStandardLCPSolution_smul_iff matrix scalar hscalar offset
        (scalar⁻¹ • degreeChart radius point)).mp
      simpa only [smul_inv_smul₀ hscalar.ne'] using hsource
    have hnorm := norm_lcp_root_lt_of_coordinate_bound matrix offset
      (scalar⁻¹ • degreeChart radius point) (radius / 2) (half_pos hradius)
      hscaled (hbound _ hscaled)
    refine ⟨hpoint.1, ?_⟩
    change dist (degreeChart radius point) 0 < scalar * (radius / 2)
    rw [dist_zero_right]
    calc
      ‖degreeChart radius point‖ =
          ‖scalar • (scalar⁻¹ • degreeChart radius point)‖ := by
            rw [smul_inv_smul₀ hscalar.ne']
      _ = scalar * ‖scalar⁻¹ • degreeChart radius point‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hscalar]
      _ < scalar * (radius / 2) := mul_lt_mul_of_pos_left hnorm hscalar

private theorem norm_scaled_degreeChart_of_mem_frontier
    (radius scalar : ℝ) (hscalar : 0 < scalar) (point : UnitCube (Fin n))
    (hpoint : point ∈ frontier
      (degreeChart radius ⁻¹' Metric.ball 0 (scalar * (radius / 2)))) :
    ‖scalar⁻¹ • degreeChart radius point‖ = radius / 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hscalar),
    norm_degreeChart_of_mem_frontier_preimage_ball radius _ point hpoint]
  field_simp [hscalar.ne']

private theorem norm_field_sub_lcpMinMap_scaled_lt
    (matrix : Matrix (Fin n) (Fin n) ℝ) (offset : Fin n → ℝ)
    (scalar : ℝ) (hscalar : 0 < scalar) (point field : Fin n → ℝ) (margin : ℝ)
    (herror : ‖scalar⁻¹ • field - lcpMinMap matrix offset (scalar⁻¹ • point)‖ < margin)
    (hlower : margin ≤ ‖lcpMinMap matrix offset (scalar⁻¹ • point)‖) :
    ‖field - lcpMinMap matrix (scalar • offset) point‖ <
      ‖lcpMinMap matrix (scalar • offset) point‖ := by
  have hmin : lcpMinMap matrix (scalar • offset) point =
      scalar • lcpMinMap matrix offset (scalar⁻¹ • point) := by
    simpa only [smul_inv_smul₀ hscalar.ne'] using
      lcpMinMap_smul matrix scalar hscalar.le offset (scalar⁻¹ • point)
  have hequal : field - lcpMinMap matrix (scalar • offset) point =
      scalar • (scalar⁻¹ • field - lcpMinMap matrix offset (scalar⁻¹ • point)) := by
    rw [smul_sub, smul_inv_smul₀ hscalar.ne', hmin]
  rw [hequal, hmin, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hscalar]
  exact mul_lt_mul_of_pos_left (herror.trans_le hlower) hscalar

/-- Full R0 and uniform scaled localization of every literal clipped fixed point
force the canonical total R0 degree to be one. The localization premise concerns
the actual source map, not a selected branch or a supplied degree identity. -/
theorem r0Degree_quittingSingletonMatrix_eq_one_of_discounted_fixedPoint_localization
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (hR0 : IsR0Matrix (quittingSingletonMatrix reward))
    (hlocalization : ∃ localRadius : ℝ, 0 < localRadius ∧
      ∃ threshold : ℝ, 0 < threshold ∧
        ∀ discount : ℝ, 0 < discount → discount ≤ threshold →
          ∀ hazard : Fin n → ℝ,
            quittingDiscountedClippedMap reward discount hazard = hazard →
              ∀ who, hazard who / discount < localRadius) :
    r0Degree (quittingSingletonMatrix reward) hR0 = 1 := by
  obtain ⟨localRadius, hlocalRadius, threshold, hthreshold, hlocal⟩ := hlocalization
  let matrix : Matrix (Fin n) (Fin n) ℝ := quittingSingletonMatrix reward
  let offset : Fin n → ℝ :=
    fun who => -reward ⟨{who}, Finset.singleton_nonempty who⟩ who
  let bound := ∑ who, |offset who|
  have hoffset : ∀ who, |offset who| ≤ bound := fun who =>
    Finset.single_le_sum (fun next _ => abs_nonneg (offset next)) (Finset.mem_univ who)
  obtain ⟨radius, hradius, hfloor, hfamily⟩ :=
    exists_radius_above_lcpMinBoxProblem_localDegree_eq_r0Degree matrix hR0 bound
      (2 + 2 * localRadius)
  have hradiusOne : 1 < radius := by linarith
  have hlocalInner : localRadius < radius / 2 := by linarith
  obtain ⟨_hbaseIsolating, hbaseBound, _hbaseDegree⟩ := hfamily offset hoffset
  obtain ⟨margin, hmargin, hmarginBound⟩ :=
    exists_pos_minMap_sphere_margin matrix offset (radius / 2) (half_pos hradius) hbaseBound
  obtain ⟨δ, hδ, happrox⟩ := quittingDiscountedClippedMap_scaled_uniform_bound reward
    (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := radius / 2)) hmargin
  let discount := min (min threshold δ) 1
  have hdiscount : 0 < discount := lt_min (lt_min hthreshold hδ) zero_lt_one
  have hdiscountThreshold : discount ≤ threshold :=
    (min_le_left (min threshold δ) 1).trans (min_le_left threshold δ)
  have hdiscountApprox : discount ≤ δ :=
    (min_le_left (min threshold δ) 1).trans (min_le_right threshold δ)
  have hdiscountOne : discount ≤ 1 := min_le_right _ _
  have hinner : 0 < discount * (radius / 2) := mul_pos hdiscount (half_pos hradius)
  let map := quittingDiscountedClippedMap reward discount
  have hmap : Continuous map :=
    (continuous_quittingDiscountedClippedMap reward).comp
      (continuous_const.prodMk continuous_id)
  have hwidth : ∀ _ : Fin n, -radius < radius := by intro _; linarith
  have hself : MapsTo map (Icc (fun _ => -radius) (fun _ => radius))
      (Icc (fun _ => -radius) (fun _ => radius)) := by
    intro hazard _hhazard
    have hcube := quittingDiscountedClippedMap_mem_unitBox reward discount hazard
    constructor <;> intro who
    · have h := hcube.1 who
      change 0 ≤ map hazard who at h
      change -radius ≤ map hazard who
      linarith
    · have h := hcube.2 who
      change map hazard who ≤ 1 at h
      change map hazard who ≤ radius
      linarith
  let region : Set (UnitCube (Fin n)) :=
    degreeChart radius ⁻¹' Metric.ball 0 (discount * (radius / 2))
  have hopen : IsOpen region := Metric.isOpen_ball.preimage
    (continuous_rectangularCubePoint (fun _ : Fin n => -radius) (fun _ => radius))
  let actual := BoxComplementarityProblem.ofAmbientMap
    (fun _ => -radius) (fun _ => radius) hwidth (fun point => point - map point)
    (continuousOn_id.sub hmap.continuousOn)
  have hfixed : ∀ hazard ∈ Icc (fun _ => -radius) (fun _ => radius),
      hazard = map hazard → hazard ∈ Metric.ball 0 (discount * (radius / 2)) := by
    intro hazard _hhazard hfixed
    have hcube : hazard ∈ Icc (0 : Fin n → ℝ) 1 := by
      rw [hfixed]
      exact quittingDiscountedClippedMap_mem_unitBox reward discount hazard
    have hbound := hlocal discount hdiscount hdiscountThreshold hazard hfixed.symm
    rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hinner]
    intro who
    rw [Real.norm_eq_abs, abs_of_nonneg (hcube.1 who)]
    have hwho := (div_lt_iff₀ hdiscount).mp (hbound who)
    have hscale := mul_lt_mul_of_pos_right hlocalInner hdiscount
    nlinarith
  have hactualIsolating : actual.IsIsolating region :=
    BoxComplementarityProblem.isIsolating_of_selfMap_preimage
      (fun _ => -radius) (fun _ => radius) hwidth map hmap.continuousOn hself
      (Metric.ball 0 (discount * (radius / 2))) Metric.isOpen_ball hfixed
  have hactualDegree : actual.localDegree region hactualIsolating = 1 :=
    BoxComplementarityProblem.localDegree_of_selfMap_preimage_eq_one
      (fun _ => -radius) (fun _ => radius) hwidth map hmap.continuousOn hself
      (Metric.ball 0 (discount * (radius / 2))) Metric.isOpen_ball hfixed
  let reference := lcpMinBoxProblem matrix (discount • offset) 0 radius hradius
  have hscaledOffset : ∀ who, |(discount • offset) who| ≤ bound := by
    intro who
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hdiscount]
    exact (mul_le_of_le_one_left (abs_nonneg _) hdiscountOne).trans (hoffset who)
  obtain ⟨hreferenceCentral, _hscaledRootBound, hreferenceDegree⟩ :=
    hfamily (discount • offset) hscaledOffset
  have hinterior : ∀ point ∈ frontier region,
      ∀ who, 0 < (point who : ℝ) ∧ (point who : ℝ) < 1 := by
    intro point hpoint
    apply coordinateInterior_of_norm_degreeChart_lt radius hradius point
    rw [norm_degreeChart_of_mem_frontier_preimage_ball radius _ point hpoint]
    exact (mul_le_of_le_one_left (half_pos hradius).le hdiscountOne).trans_lt (by linarith)
  have hclose : ∀ point ∈ frontier region,
      ‖actual.gain point - reference.gain point‖ < ‖reference.gain point‖ := by
    intro point hpoint
    let source := degreeChart radius point
    have hsourceNorm : ‖discount⁻¹ • source‖ = radius / 2 :=
      norm_scaled_degreeChart_of_mem_frontier radius discount hdiscount point hpoint
    have hsourceSphere : discount⁻¹ • source ∈ Metric.sphere (0 : Fin n → ℝ) (radius / 2) := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hsourceNorm
    have hsourceClosed : discount⁻¹ • source ∈
        Metric.closedBall (0 : Fin n → ℝ) (radius / 2) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hsourceNorm.le
    have herror := (happrox discount hdiscount hdiscountApprox
      (discount⁻¹ • source) hsourceClosed).2
    simp only [smul_inv_smul₀ hdiscount.ne'] at herror
    have herror' : ‖discount⁻¹ • (source - map source) -
        lcpMinMap matrix offset (discount⁻¹ • source)‖ < margin := by
      change ‖(fun who => discount⁻¹ * (source who - map source who)) -
        lcpMinMap matrix offset (discount⁻¹ • source)‖ < margin
      simpa only [div_eq_mul_inv, mul_comm] using herror
    have hcomparison := norm_field_sub_lcpMinMap_scaled_lt matrix offset discount hdiscount
      source (source - map source) margin herror' (hmarginBound _ hsourceSphere)
    have hreferenceGain : reference.gain point =
        -lcpMinMap matrix (discount • offset) source :=
      lcpMinBoxProblem_gain_degreeChart matrix (discount • offset) radius hradius point
    have hactualGain : actual.gain point = -(source - map source) := rfl
    rw [hactualGain, hreferenceGain, neg_sub_neg, norm_sub_rev, norm_neg]
    exact hcomparison
  obtain ⟨hreferenceIsolating, _hactualIsolating, hdegrees⟩ :=
    reference.localDegree_eq_of_norm_sub_lt_norm actual region hopen hinterior hclose
  have hsolutions : reference.solutionsIn region =
      reference.solutionsIn (diagonalCentralRegion n) :=
    solutionsIn_shrinking_ball_eq_central matrix offset radius hradius
      discount hdiscount hdiscountOne hbaseBound
  have hexcision := reference.localDegree_eq_of_solutionsIn_eq region
    (diagonalCentralRegion n) hreferenceIsolating hreferenceCentral hsolutions
  exact hreferenceDegree.symm.trans (hexcision.symm.trans (hdegrees.trans hactualDegree))

end GameTheory
