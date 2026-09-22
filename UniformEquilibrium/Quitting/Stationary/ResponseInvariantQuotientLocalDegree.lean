import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientScaling
import MathUE.Topology.BoxComplementarityFrontierPerturbation

/-!
# Fixed-chart local degree of the actual quotient response

The centered chart rescales the original nonlinear minimum field. The raw
R0 matrix isolates the homogeneous model. Uniform signed scaling and the
existing frontier perturbation theorem identify the nonlinear local degree.
-/

noncomputable section

namespace GameTheory

open Set _root_.Math _root_.Math.Topology _root_.Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- A small original-hazard chart represented on the fixed reference cube.
Its ambient field is the positively rescaled literal quotient minimum. -/
def quittingQuotientScaledMinProblem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (scalar : ℝ) : BoxComplementarityProblem (Fin k) :=
  BoxComplementarityProblem.ofAmbientMap
    (fun _ => (-2 : ℝ)) (fun _ => (2 : ℝ))
    (by intro; norm_num)
    (quittingQuotientMinFieldScaled reward block representative scalar)
    (by
      apply Continuous.continuousOn
      unfold quittingQuotientMinFieldScaled quittingQuotientMinField
      have hresponse := continuous_quittingQuotientResponse reward block representative
      fun_prop)

/-- The actual quotient fixed-point field, rescaled into the same chart. -/
def quittingQuotientScaledFixedPointProblem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (scalar : ℝ) : BoxComplementarityProblem (Fin k) :=
  BoxComplementarityProblem.ofAmbientMap
    (fun _ => (-2 : ℝ)) (fun _ => (2 : ℝ))
    (by intro; norm_num)
    (fun point => scalar⁻¹ • quittingQuotientFixedPointField reward block representative
      (scalar • point))
    (by
      apply Continuous.continuousOn
      unfold quittingQuotientFixedPointField
      have hclipped := continuous_quittingQuotientStationaryClippedMap
        reward block representative
      fun_prop)

private theorem chart_mem_closedBall_two (point : UnitCube (Fin k)) :
    rectangularCubePoint (fun _ => (-2 : ℝ)) (fun _ => (2 : ℝ)) point ∈
      Metric.closedBall 0 2 := by
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
  intro coordinate
  rw [Real.norm_eq_abs]
  have h := (point coordinate).property
  dsimp [rectangularCubePoint, rectangularPoint]
  rw [abs_le]
  constructor <;> nlinarith [h.1, h.2]

/-- R0 and the literal response polynomial produce an isolating central
region in a positive original-hazard chart, with canonical R0 degree.
No local-degree identity or isolating chart is supplied as a hypothesis. -/
theorem exists_scaledQuotient_localDegree_eq_r0Degree
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (hR0 : IsR0Matrix
      (quittingResponseQuotientMatrix reward block representative)) :
    ∃ scalar : ℝ, 0 < scalar ∧
      (∀ point ∈ Metric.closedBall (0 : Fin k → ℝ) 2,
        ∀ coordinate,
          (scalar • point) coordinate +
            quittingQuotientResponse reward block representative
              (scalar • point) coordinate < 1) ∧
      ∃ hisolating :
        (quittingQuotientScaledMinProblem reward block representative scalar).IsIsolating
          (diagonalCentralRegion k),
        (quittingQuotientScaledMinProblem reward block representative scalar).localDegree
            (diagonalCentralRegion k) hisolating =
          r0Degree (quittingResponseQuotientMatrix reward block representative) hR0 := by
  let A := quittingResponseQuotientMatrix reward block representative
  let base := lcpMinBoxProblem A 0 0 2 (by norm_num)
  have hbase : base.IsIsolating (diagonalCentralRegion k) :=
    isIsolating_lcpMinBoxProblem_zero_of_isR0Matrix A hR0 2 (by norm_num)
  obtain ⟨tolerance, htolerance, hstable⟩ :=
    base.exists_pos_localDegree_eq_of_norm_sub_lt (diagonalCentralRegion k) hbase
  obtain ⟨δ, hδ, happrox⟩ := quittingQuotientMinFieldScaled_uniform_bound
    reward block representative
      (Metric.isBounded_closedBall (x := (0 : Fin k → ℝ)) (r := 2)) htolerance
  obtain ⟨upperRadius, hupperRadius, hupperLocal⟩ := Metric.eventually_nhds_iff.mp
    (eventually_quittingQuotient_upperClip_inactive reward block representative)
  let scalar := min (δ / 2) (upperRadius / 4)
  have hscalar : 0 < scalar := by dsimp [scalar]; positivity
  have hsmall : scalar ≤ δ := by
    dsimp [scalar]
    have h := min_le_left (δ / 2) (upperRadius / 4)
    linarith
  have hupper (point : Fin k → ℝ)
      (hpoint : point ∈ Metric.closedBall (0 : Fin k → ℝ) 2) (coordinate : Fin k) :
      (scalar • point) coordinate +
        quittingQuotientResponse reward block representative
          (scalar • point) coordinate < 1 := by
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
  let actual := quittingQuotientScaledMinProblem reward block representative scalar
  have hclose (point : UnitCube (Fin k)) (_hfrontier :
      point ∈ frontier (diagonalCentralRegion k)) :
      ‖actual.gain point - base.gain point‖ < tolerance := by
    let source := rectangularCubePoint (fun _ => (-2 : ℝ)) (fun _ => (2 : ℝ)) point
    have hsource : source ∈ Metric.closedBall (0 : Fin k → ℝ) 2 :=
      chart_mem_closedBall_two point
    have hbound := happrox scalar hscalar hsmall source hsource
    simp only [actual, base, quittingQuotientScaledMinProblem,
      lcpMinBoxProblem, BoxComplementarityProblem.ofAmbientMap,
      Pi.zero_apply, zero_sub, zero_add]
    change ‖-quittingQuotientMinFieldScaled reward block representative scalar source -
      -lcpMinMap A 0 source‖ < tolerance
    calc
      ‖-quittingQuotientMinFieldScaled reward block representative scalar source -
          -lcpMinMap A 0 source‖ =
          ‖-(quittingQuotientMinFieldScaled reward block representative scalar source -
            lcpMinMap A 0 source)‖ := by congr 1; abel
      _ = ‖quittingQuotientMinFieldScaled reward block representative scalar source -
          lcpMinMap A 0 source‖ := norm_neg _
      _ < tolerance := hbound
  obtain ⟨hactual, heq⟩ := hstable actual hclose
  exact ⟨scalar, hscalar, hupper, hactual,
    heq.symm.trans (localDegree_lcpMinBoxProblem_zero_eq_r0Degree A hR0 2
      (by norm_num))⟩

/-- The same derived chart isolates the actual clipped quotient map at
all-Continue and gives it the canonical R0 local degree. -/
theorem exists_actualQuotient_localDegree_eq_r0Degree
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hR0 : IsR0Matrix
      (quittingResponseQuotientMatrix reward block representative)) :
    ∃ scalar : ℝ, 0 < scalar ∧
      ∃ hisolating :
        (quittingQuotientScaledFixedPointProblem reward block representative scalar).IsIsolating
          (diagonalCentralRegion k),
        (quittingQuotientScaledFixedPointProblem reward block representative scalar).localDegree
            (diagonalCentralRegion k) hisolating =
          r0Degree (quittingResponseQuotientMatrix reward block representative) hR0 := by
  obtain ⟨scalar, hscalar, hupper, hminIsolating, hminDegree⟩ :=
    exists_scaledQuotient_localDegree_eq_r0Degree reward block representative hR0
  have hequal : quittingQuotientScaledFixedPointProblem reward block representative scalar =
      quittingQuotientScaledMinProblem reward block representative scalar := by
    apply BoxComplementarityProblem.ext
    funext point coordinate
    let source := rectangularCubePoint (fun _ => (-2 : ℝ)) (fun _ => (2 : ℝ)) point
    have hsource : source ∈ Metric.closedBall (0 : Fin k → ℝ) 2 :=
      chart_mem_closedBall_two point
    have hfield := quittingQuotientFixedPointField_eq_minField
      reward block representative hrepresentative (scalar • source)
        (fun who => (hupper source hsource who).le)
    change -(scalar⁻¹ • quittingQuotientFixedPointField reward block representative
      (scalar • source)) coordinate =
        -(quittingQuotientMinFieldScaled reward block representative scalar source)
          coordinate
    rw [hfield]
    rfl
  have hisolating :
      (quittingQuotientScaledFixedPointProblem reward block representative scalar).IsIsolating
        (diagonalCentralRegion k) := by
    rw [hequal]
    exact hminIsolating
  refine ⟨scalar, hscalar, hisolating, ?_⟩
  simpa only [hequal] using hminDegree

end GameTheory
