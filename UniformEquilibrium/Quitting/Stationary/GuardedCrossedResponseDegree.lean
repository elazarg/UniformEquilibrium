import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseLocal
import MathUE.Topology.BoxComplementarityFrontierPerturbation
import MathUE.Topology.BoxComplementaritySelfMapNormalization
import MathUE.Topology.BoxComplementarityDegreeEscape

/-! # Local and global degree of the literal crossed clipped response -/

noncomputable section

namespace GameTheory

open Set _root_.Math _root_.Math.Topology _root_.Math.LinearProgramming

variable {n : ℕ}

private abbrev crossedChart (point : UnitCube (Fin n)) : Fin n → ℝ :=
  rectangularCubePoint (fun _ => (-2 : ℝ)) (fun _ => (2 : ℝ)) point

/-- The crossed minimum field in a positive original-hazard chart. -/
def quittingCrossedScaledMinProblem
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (scalar : ℝ) : BoxComplementarityProblem (Fin n) :=
  BoxComplementarityProblem.ofAmbientMap
    (fun _ => (-2 : ℝ)) (fun _ => (2 : ℝ)) (by intro; norm_num)
    (quittingCrossedMinFieldScaled reward first second scalar)
    (by
      apply Continuous.continuousOn
      unfold quittingCrossedMinFieldScaled quittingCrossedMinField
      have hresponse := continuous_quittingCrossedResponse reward first second
      fun_prop)

/-- The actual crossed fixed-point field in the same positive chart. -/
def quittingCrossedScaledFixedPointProblem
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height scalar : ℝ) :
    BoxComplementarityProblem (Fin n) :=
  BoxComplementarityProblem.ofAmbientMap
    (fun _ => (-2 : ℝ)) (fun _ => (2 : ℝ)) (by intro; norm_num)
    (fun point => scalar⁻¹ • quittingCrossedFixedPointField reward first second height
      (scalar • point))
    (by
      apply Continuous.continuousOn
      unfold quittingCrossedFixedPointField
      have hclipped := continuous_quittingCrossedClippedMap reward first second height
      fun_prop)

private theorem crossedChart_mem_closedBall_two (point : UnitCube (Fin n)) :
    crossedChart point ∈ Metric.closedBall 0 2 := by
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
  intro coordinate
  rw [Real.norm_eq_abs]
  have h := (point coordinate).property
  dsimp [crossedChart, rectangularCubePoint, rectangularPoint]
  rw [abs_le]
  constructor <;> nlinarith [h.1, h.2]

/-- The crossed nonlinear minimum has the canonical R0 local degree at zero;
the height-dependent upper clip is also inactive on the derived small chart. -/
theorem exists_scaledCrossed_localDegree_eq_r0Degree
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ) (hheight : 0 < height)
    (hR0 : IsR0Matrix (quittingCrossedSingletonMatrix reward first second)) :
    ∃ scalar : ℝ, 0 < scalar ∧
      (∀ point ∈ Metric.closedBall (0 : Fin n → ℝ) 2,
        ∀ coordinate,
          (scalar • point) coordinate +
            quittingCrossedResponse reward first second (scalar • point) coordinate <
            quittingCrossedCeiling first second height coordinate) ∧
      ∃ hisolating :
        (quittingCrossedScaledMinProblem reward first second scalar).IsIsolating
          (diagonalCentralRegion n),
        (quittingCrossedScaledMinProblem reward first second scalar).localDegree
            (diagonalCentralRegion n) hisolating =
          r0Degree (quittingCrossedSingletonMatrix reward first second) hR0 := by
  let A := quittingCrossedSingletonMatrix reward first second
  let base := lcpMinBoxProblem A 0 0 2 (by norm_num)
  have hbase : base.IsIsolating (diagonalCentralRegion n) :=
    isIsolating_lcpMinBoxProblem_zero_of_isR0Matrix A hR0 2 (by norm_num)
  obtain ⟨tolerance, htolerance, hstable⟩ :=
    base.exists_pos_localDegree_eq_of_norm_sub_lt (diagonalCentralRegion n) hbase
  obtain ⟨δ, hδ, happrox⟩ := quittingCrossedMinFieldScaled_uniform_bound
    reward first second
      (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 2)) htolerance
  obtain ⟨upperRadius, hupperRadius, hupperLocal⟩ := Metric.eventually_nhds_iff.mp
    (eventually_quittingCrossed_upperClip_inactive reward first second height hheight)
  let scalar := min (δ / 2) (upperRadius / 4)
  have hscalar : 0 < scalar := by dsimp [scalar]; positivity
  have hsmall : scalar ≤ δ := by
    dsimp [scalar]
    have h := min_le_left (δ / 2) (upperRadius / 4)
    linarith
  have hupper (point : Fin n → ℝ)
      (hpoint : point ∈ Metric.closedBall (0 : Fin n → ℝ) 2) (coordinate : Fin n) :
      (scalar • point) coordinate +
        quittingCrossedResponse reward first second (scalar • point) coordinate <
        quittingCrossedCeiling first second height coordinate := by
    have hnorm : ‖point‖ ≤ 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hpoint
    have hnormScaled : ‖scalar • point‖ ≤ scalar * 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hscalar]
      exact mul_le_mul_of_nonneg_left hnorm hscalar.le
    have hscalarRadius : scalar ≤ upperRadius / 4 := min_le_right _ _
    have hnear : dist (scalar • point) 0 < upperRadius := by
      rw [dist_zero_right]
      nlinarith
    exact hupperLocal hnear coordinate
  let actual := quittingCrossedScaledMinProblem reward first second scalar
  have hclose (point : UnitCube (Fin n)) (_hfrontier :
      point ∈ frontier (diagonalCentralRegion n)) :
      ‖actual.gain point - base.gain point‖ < tolerance := by
    let source := crossedChart point
    have hsource : source ∈ Metric.closedBall (0 : Fin n → ℝ) 2 :=
      crossedChart_mem_closedBall_two point
    have hbound := happrox scalar hscalar hsmall source hsource
    simp only [actual, base, quittingCrossedScaledMinProblem,
      lcpMinBoxProblem, BoxComplementarityProblem.ofAmbientMap,
      Pi.zero_apply, zero_sub, zero_add]
    change ‖-quittingCrossedMinFieldScaled reward first second scalar source -
      -lcpMinMap A 0 source‖ < tolerance
    calc
      ‖-quittingCrossedMinFieldScaled reward first second scalar source -
          -lcpMinMap A 0 source‖ =
          ‖-(quittingCrossedMinFieldScaled reward first second scalar source -
            lcpMinMap A 0 source)‖ := by congr 1; abel
      _ = ‖quittingCrossedMinFieldScaled reward first second scalar source -
          lcpMinMap A 0 source‖ := norm_neg _
      _ < tolerance := hbound
  obtain ⟨hactual, heq⟩ := hstable actual hclose
  exact ⟨scalar, hscalar, hupper, hactual,
    heq.symm.trans (localDegree_lcpMinBoxProblem_zero_eq_r0Degree A hR0 2
      (by norm_num))⟩

/-- The actual crossed clipped map, with selected ceiling `height`, has
local degree of its literal row-swapped singleton matrix at all-Continue. -/
theorem exists_actualCrossed_localDegree_eq_r0Degree
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ) (hheight : 0 < height)
    (hR0 : IsR0Matrix (quittingCrossedSingletonMatrix reward first second)) :
    ∃ scalar : ℝ, 0 < scalar ∧
      ∃ hisolating :
        (quittingCrossedScaledFixedPointProblem reward first second height scalar).IsIsolating
          (diagonalCentralRegion n),
        (quittingCrossedScaledFixedPointProblem reward first second height scalar).localDegree
          (diagonalCentralRegion n) hisolating =
          r0Degree (quittingCrossedSingletonMatrix reward first second) hR0 := by
  obtain ⟨scalar, hscalar, hupper, hminIsolating, hminDegree⟩ :=
    exists_scaledCrossed_localDegree_eq_r0Degree reward first second height hheight hR0
  have hequal : quittingCrossedScaledFixedPointProblem reward first second height scalar =
      quittingCrossedScaledMinProblem reward first second scalar := by
    apply BoxComplementarityProblem.ext
    funext point coordinate
    let source := crossedChart point
    have hsource : source ∈ Metric.closedBall (0 : Fin n → ℝ) 2 :=
      crossedChart_mem_closedBall_two point
    have hfield := quittingCrossedFixedPointField_eq_minField reward first second
      height hheight (scalar • source)
        (fun who => (hupper source hsource who).le)
    change -(scalar⁻¹ • quittingCrossedFixedPointField reward first second height
      (scalar • source)) coordinate =
        -(quittingCrossedMinFieldScaled reward first second scalar source) coordinate
    rw [hfield]
    rfl
  have hisolating :
      (quittingCrossedScaledFixedPointProblem reward first second height scalar).IsIsolating
        (diagonalCentralRegion n) := by
    rw [hequal]
    exact hminIsolating
  refine ⟨scalar, hscalar, hisolating, ?_⟩
  simpa only [hequal] using hminDegree

end GameTheory
