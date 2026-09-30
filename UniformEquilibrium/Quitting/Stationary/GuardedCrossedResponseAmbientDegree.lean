import MathUE.Topology.AmbientDegree
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseTotalDegree

/-!
# Intrinsic degree of the entire nonzero crossed fixed-point set

The actual ambient source is the bounded open annulus
`ball 0 (3/2) \ closedBall 0 radius`. Its zero fiber is exactly the entire
nonzero fixed-point set of the literal crossed clipped map. Confinement and
origin isolation derive the zero-free source frontier. Closure containment
inside the existing positive `[-2,2]` chart is proved, not assumed.

Actual-solutions excision compares this annulus with the existing cube
exterior, and the intrinsic operation computes its degree as `1 - r0Degree`.
No finite or regular nonzero root inventory is needed.
-/

noncomputable section

namespace GameTheory

open Set _root_.Math _root_.Math.Topology _root_.Math.LinearProgramming

variable {n : ℕ}

/-- A bounded open ambient source selecting the complete nonzero crossed fiber. -/
def quittingCrossedAmbientAnnulus (radius : ℝ) : Set (Fin n → ℝ) :=
  Metric.ball 0 (3 / 2) \ Metric.closedBall 0 radius

theorem isOpen_quittingCrossedAmbientAnnulus (radius : ℝ) :
    IsOpen (quittingCrossedAmbientAnnulus (n := n) radius) :=
  Metric.isOpen_ball.inter Metric.isClosed_closedBall.isOpen_compl

theorem isBounded_quittingCrossedAmbientAnnulus (radius : ℝ) :
    Bornology.IsBounded (quittingCrossedAmbientAnnulus (n := n) radius) :=
  Metric.isBounded_ball.subset sdiff_subset

theorem continuous_quittingCrossedFixedPointField
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ) :
    Continuous (quittingCrossedFixedPointField reward first second height) :=
  continuous_id.sub (continuous_quittingCrossedClippedMap reward first second height)

private theorem crossed_fixed_norm_le_one
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ) (hheight : 0 ≤ height) (hheightOne : height ≤ 1)
    (source : Fin n → ℝ)
    (hfixed : quittingCrossedClippedMap reward first second height source = source) :
    ‖source‖ ≤ 1 := by
  have hbox := quittingCrossedClippedMap_fixed_mem_box
    reward first second height hheight source hfixed
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro who
  rw [Real.norm_eq_abs, abs_le]
  have hceiling : quittingCrossedCeiling first second height who ≤ 1 := by
    unfold quittingCrossedCeiling
    split_ifs <;> linarith
  exact ⟨by linarith [(hbox who).1], (hbox who).2.trans hceiling⟩

private theorem crossed_field_zero_iff_fixed
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ) (source : Fin n → ℝ) :
    quittingCrossedFixedPointField reward first second height source = 0 ↔
      quittingCrossedClippedMap reward first second height source = source := by
  change source - quittingCrossedClippedMap reward first second height source = 0 ↔ _
  rw [sub_eq_zero]
  exact eq_comm

private theorem closure_annulus_subset_closedBall (radius : ℝ) :
    closure (quittingCrossedAmbientAnnulus (n := n) radius) ⊆
      Metric.closedBall 0 (3 / 2) :=
  closure_minimal (fun _ h => Metric.ball_subset_closedBall h.1) Metric.isClosed_closedBall

private theorem closure_annulus_subset_compl_ball (radius : ℝ) :
    closure (quittingCrossedAmbientAnnulus (n := n) radius) ⊆
      (Metric.ball 0 radius)ᶜ :=
  closure_minimal (fun _ h hball => h.2 (Metric.ball_subset_closedBall hball))
    Metric.isOpen_ball.isClosed_compl

private theorem closure_annulus_coordinateInterior (radius : ℝ) :
    closure (quittingCrossedAmbientAnnulus (n := n) radius) ⊆
      {source | ∀ who, (-2 : ℝ) < source who ∧ source who < 2} := by
  intro source hsource who
  have hnorm : ‖source‖ ≤ 3 / 2 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      closure_annulus_subset_closedBall radius hsource
  have hcoordinate := (norm_le_pi_norm source who).trans hnorm
  rw [Real.norm_eq_abs, abs_le] at hcoordinate
  constructor <;> linarith

/-- The actual bounded annulus selects the entire nonzero crossed zero fiber
and its intrinsic integer equals one minus the existing R0 integer. The
radius and all source conditions are constructed from the literal map. -/
theorem exists_quittingCrossedAmbientAnnulus_degree_eq_one_sub_r0Degree
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ) (hheight : 0 < height) (hheightOne : height ≤ 1)
    (hR0 : IsR0Matrix (quittingCrossedSingletonMatrix reward first second)) :
    ∃ radius : ℝ, 0 < radius ∧ radius < 1 ∧
      (∀ source : Fin n → ℝ, ‖source‖ ≤ radius →
        quittingCrossedClippedMap reward first second height source = source → source = 0) ∧
      ∃ hfrontier : ∀ source ∈ frontier (quittingCrossedAmbientAnnulus (n := n) radius),
        quittingCrossedFixedPointField reward first second height source ≠ 0,
        ({source | quittingCrossedFixedPointField reward first second height source = 0} ∩
          quittingCrossedAmbientAnnulus radius) =
            quittingCrossedNonzeroFixedPointSet reward first second height ∧
        ambientDegree (quittingCrossedFixedPointField reward first second height)
          (quittingCrossedAmbientAnnulus radius) 0
          (isOpen_quittingCrossedAmbientAnnulus radius)
          (isBounded_quittingCrossedAmbientAnnulus radius)
          (continuous_quittingCrossedFixedPointField reward first second height).continuousOn
          hfrontier = 1 - r0Degree (quittingCrossedSingletonMatrix reward first second) hR0 := by
  obtain ⟨radius, hradius, hsmall, hisolation, horigin, houtside,
      hlocal, hselected, himage, hdegree⟩ :=
    exists_globalCrossed_entireNonzeroSet_degree_eq_one_sub_r0Degree
      reward first second height hheight hheightOne hR0
  let field := quittingCrossedFixedPointField reward first second height
  let annulus := quittingCrossedAmbientAnnulus (n := n) radius
  have hopenAnnulus : IsOpen annulus := isOpen_quittingCrossedAmbientAnnulus radius
  have hnorm (source : Fin n → ℝ)
      (hfixed : quittingCrossedClippedMap reward first second height source = source) :
      ‖source‖ ≤ 1 :=
    crossed_fixed_norm_le_one reward first second height hheight.le hheightOne source hfixed
  have hnonzero_mem (source : Fin n → ℝ) (hnonzero : source ≠ 0)
      (hfixed : quittingCrossedClippedMap reward first second height source = source) :
      source ∈ annulus := by
    constructor
    · rw [Metric.mem_ball, dist_zero_right]
      linarith [hnorm source hfixed]
    · intro hclosed
      have hnormSmall : ‖source‖ ≤ radius := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hclosed
      exact hnonzero (hisolation source hnormSmall hfixed)
  have hzeroSet : {source | field source = 0} ∩ annulus =
      quittingCrossedNonzeroFixedPointSet reward first second height := by
    ext source
    change (field source = 0 ∧ source ∈ annulus) ↔
      (source ≠ 0 ∧ quittingCrossedClippedMap reward first second height source = source)
    rw [crossed_field_zero_iff_fixed]
    constructor
    · rintro ⟨hfixed, hsource⟩
      refine ⟨?_, hfixed⟩
      rintro rfl
      exact hsource.2 (by simpa only [Metric.mem_closedBall, dist_self] using hradius.le)
    · exact fun h => ⟨h.2, hnonzero_mem source h.1 h.2⟩
  have hfrontier : ∀ source ∈ frontier annulus, field source ≠ 0 := by
    intro source hsource hzero
    have hfixed := (crossed_field_zero_iff_fixed reward first second height source).mp hzero
    by_cases hnormSmall : ‖source‖ ≤ radius
    · have hzero := hisolation source hnormSmall hfixed
      have hout := closure_annulus_subset_compl_ball radius (frontier_subset_closure hsource)
      apply hout
      simpa only [hzero, Metric.mem_ball, dist_self] using hradius
    · have hmem : source ∈ annulus := by
        constructor
        · rw [Metric.mem_ball, dist_zero_right]
          linarith [hnorm source hfixed]
        · simpa only [Metric.mem_closedBall, dist_zero_right] using hnormSmall
      exact hsource.2 (by
        rw [hopenAnnulus.interior_eq]
        exact hmem)
  let actual := quittingCrossedGlobalProblem reward first second height
  let cubeAnnulus := quittingCrossedGlobalChart ⁻¹' annulus
  have hisolating : actual.IsIsolating cubeAnnulus := by
    have hfield : ContinuousOn field (Icc (fun _ => -2) (fun _ => 2)) :=
      (continuous_quittingCrossedFixedPointField reward first second height).continuousOn
    change (BoxComplementarityProblem.ofAmbientMap (fun _ => -2) (fun _ => 2)
      (by intro _; norm_num) field hfield).IsIsolating
      (rectangularCubePoint (fun _ => -2) (fun _ => 2) ⁻¹' annulus)
    exact BoxComplementarityProblem.isIsolating_ofAmbientMap_preimage_of_closure_subset
      (fun _ => -2) (fun _ => 2) (by intro _; norm_num) field hfield
      annulus hopenAnnulus (closure_annulus_coordinateInterior radius) hfrontier
  have hsame : actual.solutionsIn cubeAnnulus =
      actual.solutionsIn (closure (quittingCrossedGlobalOriginRegion radius))ᶜ := by
    rw [hselected]
    ext point
    change (actual.IsSolution point ∧ quittingCrossedGlobalChart point ∈ annulus) ↔
      (quittingCrossedGlobalChart point ≠ 0 ∧
        quittingCrossedClippedMap reward first second height (quittingCrossedGlobalChart point) =
          quittingCrossedGlobalChart point)
    rw [quittingCrossedGlobalProblem_isSolution_iff_fixedPoint
      reward first second height hheight.le hheightOne point]
    have hsource := Set.ext_iff.mp hzeroSet (quittingCrossedGlobalChart point)
    simpa only [mem_inter_iff, mem_ofPred_eq, field, quittingCrossedNonzeroFixedPointSet,
      crossed_field_zero_iff_fixed] using hsource
  have hexterior := actual.localDegree_eq_of_solutionsIn_eq cubeAnnulus
    (closure (quittingCrossedGlobalOriginRegion radius))ᶜ hisolating houtside hsame
  have hcomputed := ambientDegree_eq_of_extension field annulus 0
    (isOpen_quittingCrossedAmbientAnnulus radius) (isBounded_quittingCrossedAmbientAnnulus radius)
    (continuous_quittingCrossedFixedPointField reward first second height).continuousOn
    hfrontier (fun _ => -2) (fun _ => 2) (by intro _; norm_num)
    (closure_annulus_coordinateInterior radius) field
    (continuous_quittingCrossedFixedPointField reward first second height).continuousOn
    (fun _ _ => rfl)
  have hintrinsic : ambientDegree field annulus 0
      (isOpen_quittingCrossedAmbientAnnulus radius) (isBounded_quittingCrossedAmbientAnnulus radius)
      (continuous_quittingCrossedFixedPointField reward first second height).continuousOn
      hfrontier = actual.localDegree cubeAnnulus hisolating := by
    simpa only [sub_zero, actual, cubeAnnulus, quittingCrossedGlobalProblem,
      quittingCrossedGlobalChart, field] using hcomputed
  exact ⟨radius, hradius, hsmall, hisolation, hfrontier, hzeroSet,
    hintrinsic.trans (hexterior.trans hdegree)⟩

end GameTheory
