import MathUE.Topology.AmbientDegreeSelfMapNormalization
import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientTotalDegree

/-! # Literal ambient degrees of the stationary response quotient

The total source is (-1,2)^k. Its closure is enclosed by [-3,3], not by the
old [-2,2] chart. The sup-norm origin ball is exactly the printed open box.
Excision and additivity retain the entire nonzero fiber, without regularity.
-/

noncomputable section

namespace GameTheory

open Set _root_.Math _root_.Math.Topology _root_.Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- The expanded source includes every strategy-boundary fixed point. -/
def quittingQuotientOmega : Set (Fin k → ℝ) :=
  {point | ∀ coordinate, (-1 : ℝ) < point coordinate ∧ point coordinate < 2}

/-- In the finite product sup norm, this is exactly (-radius,radius)^k. -/
def quittingQuotientOriginBox (radius : ℝ) : Set (Fin k → ℝ) :=
  Metric.ball 0 radius

/-- The literal source with the closed origin box removed. -/
def quittingQuotientOmegaAnnulus (radius : ℝ) : Set (Fin k → ℝ) :=
  quittingQuotientOmega \ Metric.closedBall 0 radius

theorem mem_quittingQuotientOriginBox_iff (radius : ℝ) (hradius : 0 < radius)
    (point : Fin k → ℝ) :
    point ∈ quittingQuotientOriginBox radius ↔
      ∀ coordinate, -radius < point coordinate ∧ point coordinate < radius := by
  simp only [quittingQuotientOriginBox, Metric.mem_ball, dist_zero_right,
    pi_norm_lt_iff hradius, Real.norm_eq_abs, abs_lt]

theorem mem_quittingQuotientClosedOriginBox_iff (radius : ℝ) (hradius : 0 < radius)
    (point : Fin k → ℝ) :
    point ∈ Metric.closedBall 0 radius ↔
      ∀ coordinate, -radius ≤ point coordinate ∧ point coordinate ≤ radius := by
  simp only [Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg hradius.le, Real.norm_eq_abs, abs_le]

theorem isOpen_quittingQuotientOmega : IsOpen (quittingQuotientOmega (k := k)) := by
  have hopen (coordinate : Fin k) : IsOpen {point : Fin k → ℝ |
      (-1 : ℝ) < point coordinate ∧ point coordinate < 2} :=
    (isOpen_lt continuous_const (continuous_apply coordinate)).inter
      (isOpen_lt (continuous_apply coordinate) continuous_const)
  simpa only [quittingQuotientOmega, ofPred_forall] using isOpen_iInter_of_finite hopen

theorem isBounded_quittingQuotientOmega :
    Bornology.IsBounded (quittingQuotientOmega (k := k)) := by
  have hbox : Bornology.IsBounded
      (Set.pi Set.univ (fun _ : Fin k => Icc (-1 : ℝ) 2)) :=
    Bornology.IsBounded.pi (fun _ => Metric.isBounded_Icc _ _)
  apply hbox.subset
  intro point hpoint coordinate _
  exact ⟨(hpoint coordinate).1.le, (hpoint coordinate).2.le⟩

theorem isOpen_quittingQuotientOmegaAnnulus (radius : ℝ) :
    IsOpen (quittingQuotientOmegaAnnulus (k := k) radius) :=
  isOpen_quittingQuotientOmega.inter Metric.isClosed_closedBall.isOpen_compl

theorem isBounded_quittingQuotientOmegaAnnulus (radius : ℝ) :
    Bornology.IsBounded (quittingQuotientOmegaAnnulus (k := k) radius) :=
  isBounded_quittingQuotientOmega.subset sdiff_subset

theorem continuous_quittingQuotientFixedPointField
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι) :
    Continuous (quittingQuotientFixedPointField reward block representative) :=
  continuous_id.sub (continuous_quittingQuotientStationaryClippedMap
    reward block representative)

theorem quittingQuotientFixedPointField_eq_zero_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι) (point : Fin k → ℝ) :
    quittingQuotientFixedPointField reward block representative point = 0 ↔
      quittingQuotientStationaryClippedMap reward block representative point = point := by
  change point - quittingQuotientStationaryClippedMap reward block representative point = 0 ↔ _
  rw [sub_eq_zero]
  exact eq_comm

theorem quittingQuotientFixedPointField_zero_mem_omega
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι) (point : Fin k → ℝ)
    (hzero : quittingQuotientFixedPointField reward block representative point = 0) :
    point ∈ quittingQuotientOmega := by
  have hfixed := (quittingQuotientFixedPointField_eq_zero_iff
    reward block representative point).mp hzero
  have hcube := quittingQuotientStationaryClippedMap_mem_unitCube
    reward block representative point
  rw [hfixed] at hcube
  intro coordinate
  have hzero : (0 : ℝ) ≤ point coordinate := hcube.1 coordinate
  have hone : point coordinate ≤ (1 : ℝ) := hcube.2 coordinate
  constructor <;> linarith

theorem quittingQuotientFixedPointField_ne_zero_on_frontier_omega
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι) :
    ∀ point ∈ frontier (quittingQuotientOmega (k := k)),
      quittingQuotientFixedPointField reward block representative point ≠ 0 := by
  intro point hpoint hzero
  have hmem := quittingQuotientFixedPointField_zero_mem_omega
    reward block representative point hzero
  have hinterior : point ∈ interior (quittingQuotientOmega (k := k)) := by
    rwa [isOpen_quittingQuotientOmega.interior_eq]
  exact (mem_interior_iff_notMem_frontier hmem).mp hinterior hpoint

private theorem closure_quotientOmega_coordinateInterior :
    closure (quittingQuotientOmega (k := k)) ⊆
      {point | ∀ coordinate, (-3 : ℝ) < point coordinate ∧ point coordinate < 3} := by
  have hclosed : closure (quittingQuotientOmega (k := k)) ⊆
      Icc (fun _ => (-1 : ℝ)) (fun _ => 2) :=
    closure_minimal
      (fun _ h => ⟨fun coordinate => (h coordinate).1.le,
        fun coordinate => (h coordinate).2.le⟩) isClosed_Icc
  intro point hpoint coordinate
  constructor <;> linarith [(hclosed hpoint).1 coordinate, (hclosed hpoint).2 coordinate]

/-- The actual signed ambient field has degree +1 on the literal total box. -/
theorem quittingQuotientFixedPointField_ambientDegree_omega_eq_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι) :
    ambientDegree (quittingQuotientFixedPointField reward block representative)
      quittingQuotientOmega 0 isOpen_quittingQuotientOmega isBounded_quittingQuotientOmega
      (continuous_quittingQuotientFixedPointField reward block representative).continuousOn
      (quittingQuotientFixedPointField_ne_zero_on_frontier_omega
        reward block representative) = 1 := by
  let map := quittingQuotientStationaryClippedMap reward block representative
  have hself : MapsTo map (Icc (fun _ => (-3 : ℝ)) (fun _ => 3))
      (Icc (fun _ => (-3 : ℝ)) (fun _ => 3)) := by
    intro point _
    have hcube := quittingQuotientStationaryClippedMap_mem_unitCube
      reward block representative point
    constructor
    · intro coordinate
      change (-3 : ℝ) ≤ map point coordinate
      have hzero : (0 : ℝ) ≤ map point coordinate := hcube.1 coordinate
      linarith
    · intro coordinate
      change map point coordinate ≤ (3 : ℝ)
      have hone : map point coordinate ≤ (1 : ℝ) := hcube.2 coordinate
      linarith
  have hfixed : ∀ point ∈ Icc (fun _ => (-3 : ℝ)) (fun _ => 3),
      point = map point → point ∈ quittingQuotientOmega := by
    intro point _ hpoint
    apply quittingQuotientFixedPointField_zero_mem_omega reward block representative point
    exact sub_eq_zero.mpr hpoint
  exact ambientDegree_of_selfMap_eq_one
    (fun _ => -3) (fun _ => 3) (by intro; norm_num) map
    (continuous_quittingQuotientStationaryClippedMap reward block representative) hself
    quittingQuotientOmega isOpen_quittingQuotientOmega isBounded_quittingQuotientOmega
    closure_quotientOmega_coordinateInterior hfixed

/-- Shrink the checked origin comparison to a literal box of radius below 1/2.
No individual nonzero root is assumed isolated. -/
theorem exists_quittingQuotientOriginBox_ambientDegree_eq_r0Degree
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hR0 : IsR0Matrix (quittingResponseQuotientMatrix reward block representative)) :
    ∃ radius : ℝ, 0 < radius ∧ radius < 1 / 2 ∧
      (∀ point : Fin k → ℝ, ‖point‖ ≤ radius →
        quittingQuotientStationaryClippedMap reward block representative point = point →
          point = 0) ∧
      ∃ hfrontier : ∀ point ∈ frontier (quittingQuotientOriginBox (k := k) radius),
          quittingQuotientFixedPointField reward block representative point ≠ 0,
        ambientDegree (quittingQuotientFixedPointField reward block representative)
          (quittingQuotientOriginBox radius) 0 Metric.isOpen_ball Metric.isBounded_ball
          (continuous_quittingQuotientFixedPointField reward block representative).continuousOn
          hfrontier = r0Degree
            (quittingResponseQuotientMatrix reward block representative) hR0 := by
  obtain ⟨largeRadius, hlargePositive, hlargeSmall, hisolation, hlargeIso, hlargeDegree⟩ :=
    exists_globalQuotient_originIsolation_localDegree_eq_r0Degree
      reward block representative hrepresentative hR0
  let radius := largeRadius / 2
  have hradius : 0 < radius := by dsimp only [radius]; positivity
  have hsmall : radius < 1 / 2 := by dsimp only [radius]; linarith
  have hle : radius ≤ largeRadius := by dsimp only [radius]; linarith
  have hisolationSmall : ∀ point : Fin k → ℝ, ‖point‖ ≤ radius →
      quittingQuotientStationaryClippedMap reward block representative point = point →
        point = 0 := fun point hpoint => hisolation point (hpoint.trans hle)
  have hclosure : closure (quittingQuotientOriginBox (k := k) radius) ⊆
      {point | ∀ coordinate, (-2 : ℝ) < point coordinate ∧ point coordinate < 2} := by
    intro point hpoint coordinate
    have hclosed : point ∈ Metric.closedBall (0 : Fin k → ℝ) radius :=
      (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall) hpoint
    have hnorm : ‖point‖ ≤ radius := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hclosed
    have hcoordinate := (norm_le_pi_norm point coordinate).trans hnorm
    rw [Real.norm_eq_abs, abs_le] at hcoordinate
    constructor <;> linarith
  have hfrontier : ∀ point ∈ frontier (quittingQuotientOriginBox (k := k) radius),
      quittingQuotientFixedPointField reward block representative point ≠ 0 := by
    intro point hpoint hzero
    have hnorm : ‖point‖ ≤ radius := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall)
          (frontier_subset_closure hpoint)
    have hpointZero := hisolationSmall point hnorm
      ((quittingQuotientFixedPointField_eq_zero_iff reward block representative point).mp hzero)
    have hmem : point ∈ quittingQuotientOriginBox (k := k) radius := by
      simpa only [quittingQuotientOriginBox, hpointZero, Metric.mem_ball, dist_self] using hradius
    have hinterior : point ∈ interior (quittingQuotientOriginBox (k := k) radius) := by
      change point ∈ interior (Metric.ball (0 : Fin k → ℝ) radius)
      rw [Metric.isOpen_ball.interior_eq]
      exact hmem
    exact (mem_interior_iff_notMem_frontier hmem).mp hinterior hpoint
  let actual := quittingQuotientGlobalProblem reward block representative
  let smallRegion := quittingQuotientGlobalChart ⁻¹' quittingQuotientOriginBox (k := k) radius
  let largeRegion : Set (UnitCube (Fin k)) :=
    quittingQuotientGlobalChart ⁻¹' Metric.ball (0 : Fin k → ℝ) largeRadius
  have hsmallIso : actual.IsIsolating smallRegion := by
    exact BoxComplementarityProblem.isIsolating_ofAmbientMap_preimage_of_closure_subset
      (fun _ => -2) (fun _ => 2) (by intro; norm_num)
      (quittingQuotientFixedPointField reward block representative)
      (continuous_quittingQuotientFixedPointField reward block representative).continuousOn
      (quittingQuotientOriginBox radius) Metric.isOpen_ball hclosure hfrontier
  have hsame : actual.solutionsIn smallRegion = actual.solutionsIn largeRegion := by
    ext point
    constructor
    · rintro ⟨hsolution, hpoint⟩
      refine ⟨hsolution, ?_⟩
      change dist (quittingQuotientGlobalChart point) 0 < largeRadius
      exact (show dist (quittingQuotientGlobalChart point) 0 < radius from hpoint).trans_le hle
    · rintro ⟨hsolution, hpoint⟩
      have hfixed := (quittingQuotientGlobalProblem_isSolution_iff_fixedPoint
        reward block representative point).mp hsolution
      have hnorm : ‖quittingQuotientGlobalChart point‖ ≤ largeRadius := by
        exact (show ‖quittingQuotientGlobalChart point‖ < largeRadius from
          (by simpa only [largeRegion, mem_preimage, Metric.mem_ball, dist_zero_right]
            using hpoint)).le
      have hzero := hisolation _ hnorm hfixed
      refine ⟨hsolution, ?_⟩
      simpa only [smallRegion, mem_preimage, quittingQuotientOriginBox,
        Metric.mem_ball, hzero, dist_self] using hradius
  have hlocal := actual.localDegree_eq_of_solutionsIn_eq
    smallRegion largeRegion hsmallIso hlargeIso hsame
  have hcomputed := ambientDegree_eq_of_extension
    (quittingQuotientFixedPointField reward block representative)
    (quittingQuotientOriginBox radius) 0 Metric.isOpen_ball Metric.isBounded_ball
    (continuous_quittingQuotientFixedPointField reward block representative).continuousOn
    hfrontier (fun _ => -2) (fun _ => 2) (by intro; norm_num) hclosure
    (quittingQuotientFixedPointField reward block representative)
    (continuous_quittingQuotientFixedPointField reward block representative).continuousOn
    (fun _ _ => rfl)
  have hintrinsic : ambientDegree
      (quittingQuotientFixedPointField reward block representative)
      (quittingQuotientOriginBox radius) 0 Metric.isOpen_ball Metric.isBounded_ball
      (continuous_quittingQuotientFixedPointField reward block representative).continuousOn
      hfrontier = actual.localDegree smallRegion hsmallIso := by
    simpa only [sub_zero, actual, smallRegion, quittingQuotientGlobalProblem,
      quittingQuotientGlobalChart] using hcomputed
  exact ⟨radius, hradius, hsmall, hisolationSmall, hfrontier,
    hintrinsic.trans (hlocal.trans hlargeDegree)⟩

/-- The literal annulus has exactly the entire nonzero fixed fiber and degree
1 minus the R0 integer. Upper-face and nonisolated roots remain included. -/
theorem exists_quittingQuotientOmegaAnnulus_ambientDegree_eq_one_sub_r0Degree
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hR0 : IsR0Matrix (quittingResponseQuotientMatrix reward block representative)) :
    ∃ radius : ℝ, 0 < radius ∧ radius < 1 / 2 ∧
      (∀ point : Fin k → ℝ, ‖point‖ ≤ radius →
        quittingQuotientStationaryClippedMap reward block representative point = point →
          point = 0) ∧
      ∃ hfrontier : ∀ point ∈ frontier (quittingQuotientOmegaAnnulus (k := k) radius),
          quittingQuotientFixedPointField reward block representative point ≠ 0,
        ({point | quittingQuotientFixedPointField reward block representative point = 0} ∩
          quittingQuotientOmegaAnnulus radius) =
            quittingQuotientNonzeroFixedPointSet reward block representative ∧
        ambientDegree (quittingQuotientFixedPointField reward block representative)
          (quittingQuotientOmegaAnnulus radius) 0
          (isOpen_quittingQuotientOmegaAnnulus radius)
          (isBounded_quittingQuotientOmegaAnnulus radius)
          (continuous_quittingQuotientFixedPointField reward block representative).continuousOn
          hfrontier = 1 - r0Degree
            (quittingResponseQuotientMatrix reward block representative) hR0 := by
  obtain ⟨radius, hradius, hsmall, hisolation, horiginFrontier, horiginDegree⟩ :=
    exists_quittingQuotientOriginBox_ambientDegree_eq_r0Degree
      reward block representative hrepresentative hR0
  let field := quittingQuotientFixedPointField reward block representative
  let origin := quittingQuotientOriginBox (k := k) radius
  let annulus := quittingQuotientOmegaAnnulus (k := k) radius
  have hopenOrigin : IsOpen origin := Metric.isOpen_ball
  have hopenAnnulus : IsOpen annulus := isOpen_quittingQuotientOmegaAnnulus radius
  have horiginSubset : origin ⊆ quittingQuotientOmega := by
    intro point hpoint coordinate
    have hnorm : ‖point‖ < radius := by
      simpa only [origin, quittingQuotientOriginBox, Metric.mem_ball, dist_zero_right]
        using hpoint
    have hcoordinate := (norm_le_pi_norm point coordinate).trans_lt hnorm
    rw [Real.norm_eq_abs, abs_lt] at hcoordinate
    constructor <;> linarith
  have hannulusSubset : annulus ⊆ quittingQuotientOmega := sdiff_subset
  have hdisjoint : Disjoint origin annulus := by
    apply Set.disjoint_left.mpr
    intro point hpoint hannulus
    exact hannulus.2 (Metric.ball_subset_closedBall hpoint)
  have hretain : ∀ point ∈ quittingQuotientOmega (k := k), field point = 0 →
      point ∈ origin ∪ annulus := by
    intro point hpoint hzero
    by_cases hnorm : ‖point‖ ≤ radius
    · have hpointZero := hisolation point hnorm
        ((quittingQuotientFixedPointField_eq_zero_iff
          reward block representative point).mp hzero)
      left
      simpa only [origin, quittingQuotientOriginBox, Metric.mem_ball, hpointZero, dist_self]
        using hradius
    · right
      refine ⟨hpoint, ?_⟩
      simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm
  have homegaFrontier := quittingQuotientFixedPointField_ne_zero_on_frontier_omega
    reward block representative
  have hfrontier : ∀ point ∈ frontier annulus, field point ≠ 0 :=
    frontier_avoids_of_disjoint_rootCover field quittingQuotientOmega annulus origin 0
      hopenAnnulus hopenOrigin hannulusSubset hdisjoint.symm homegaFrontier
      (fun point hpoint hzero => (hretain point hpoint hzero).symm)
  have hzeroSet : {point | field point = 0} ∩ annulus =
      quittingQuotientNonzeroFixedPointSet reward block representative := by
    ext point
    change (field point = 0 ∧ point ∈ annulus) ↔
      (point ≠ 0 ∧ quittingQuotientStationaryClippedMap
        reward block representative point = point)
    constructor
    · rintro ⟨hzero, hpoint⟩
      refine ⟨?_, (quittingQuotientFixedPointField_eq_zero_iff
        reward block representative point).mp hzero⟩
      rintro rfl
      exact hpoint.2 (by
        simpa only [Metric.mem_closedBall, dist_self] using hradius.le)
    · rintro ⟨hnonzero, hfixed⟩
      have hzero := (quittingQuotientFixedPointField_eq_zero_iff
        reward block representative point).mpr hfixed
      refine ⟨hzero, quittingQuotientFixedPointField_zero_mem_omega
        reward block representative point hzero, ?_⟩
      intro hclosed
      have hnorm : ‖point‖ ≤ radius := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hclosed
      exact hnonzero (hisolation point hnorm hfixed)
  have hsum := ambientDegree_additive field quittingQuotientOmega origin annulus 0
    isOpen_quittingQuotientOmega isBounded_quittingQuotientOmega
    (continuous_quittingQuotientFixedPointField reward block representative).continuousOn
    homegaFrontier hopenOrigin hopenAnnulus horiginSubset hannulusSubset hdisjoint hretain
  have htotal := quittingQuotientFixedPointField_ambientDegree_omega_eq_one
    reward block representative
  let totalDegree : ℤ := ambientDegree field quittingQuotientOmega 0
    isOpen_quittingQuotientOmega isBounded_quittingQuotientOmega
    (continuous_quittingQuotientFixedPointField reward block representative).continuousOn
    homegaFrontier
  let originDegree : ℤ := ambientDegree field origin 0
    Metric.isOpen_ball Metric.isBounded_ball
    (continuous_quittingQuotientFixedPointField reward block representative).continuousOn
    horiginFrontier
  let annulusDegree : ℤ := ambientDegree field annulus 0
    (isOpen_quittingQuotientOmegaAnnulus radius)
    (isBounded_quittingQuotientOmegaAnnulus radius)
    (continuous_quittingQuotientFixedPointField reward block representative).continuousOn
    hfrontier
  have hsplit : totalDegree = originDegree + annulusDegree := hsum
  have htotalEq : totalDegree = 1 := htotal
  have horiginEq : originDegree =
      r0Degree (quittingResponseQuotientMatrix reward block representative) hR0 := horiginDegree
  have hannulusEq : annulusDegree =
      1 - r0Degree (quittingResponseQuotientMatrix reward block representative) hR0 := by
    omega
  refine ⟨radius, hradius, hsmall, hisolation, hfrontier, hzeroSet, ?_⟩
  exact hannulusEq

end GameTheory
