import MathUE.Topology.AmbientDegreeSelfMapNormalization
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseOmegaDegree

/-!
# Literal total-box and origin-ball ambient degrees

The total box uses the larger chart `[-3,3]`: its closure is not strictly
inside the older `[-2,2]` chart. The origin ball uses the existing local
comparison in that older chart. Both conclusions concern the actual source
field and intrinsic ambient degree, with no regular-root assumption.
-/

noncomputable section

namespace GameTheory

open Set _root_.Math.Topology _root_.Math.LinearProgramming

variable {n : ℕ}

private theorem closure_quittingCrossedOmega_coordinateInterior :
    closure (quittingCrossedOmega (n := n)) ⊆
      {source | ∀ who, (-3 : ℝ) < source who ∧ source who < 3} := by
  have hclosed : closure (quittingCrossedOmega (n := n)) ⊆
      Icc (fun _ => (-1 : ℝ)) (fun _ => 2) :=
    closure_minimal
      (fun _ h => ⟨fun who => (h who).1.le, fun who => (h who).2.le⟩) isClosed_Icc
  intro source hsource who
  have hbounds := hclosed hsource
  constructor <;> linarith [hbounds.1 who, hbounds.2 who]

/-- The literal field misses zero on the frontier of the packet's entire box. -/
theorem quittingCrossedFixedPointField_ne_zero_on_frontier_omega
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ) (hheight : 0 ≤ height) (hheightOne : height ≤ 1) :
    ∀ source ∈ frontier (quittingCrossedOmega (n := n)),
      quittingCrossedFixedPointField reward first second height source ≠ 0 := by
  intro source hsource hzero
  have hmem := quittingCrossedFixedPointField_zero_mem_omega
    reward first second height hheight hheightOne source hzero
  have hinterior : source ∈ interior (quittingCrossedOmega (n := n)) := by
    rwa [isOpen_quittingCrossedOmega.interior_eq]
  exact (mem_interior_iff_notMem_frontier hmem).mp hinterior hsource

/-- Packet (4.3): the actual total ambient degree on Ω is positive one.
Neither source guards nor R0 are needed for this global normalization. -/
theorem quittingCrossedFixedPointField_ambientDegree_omega_eq_one
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ) (hheight : 0 ≤ height) (hheightOne : height ≤ 1) :
    ambientDegree (quittingCrossedFixedPointField reward first second height)
      quittingCrossedOmega 0 isOpen_quittingCrossedOmega isBounded_quittingCrossedOmega
      (continuous_quittingCrossedFixedPointField reward first second height).continuousOn
      (quittingCrossedFixedPointField_ne_zero_on_frontier_omega
        reward first second height hheight hheightOne) = 1 := by
  let map := quittingCrossedClippedMap reward first second height
  have hself : MapsTo map (Icc (fun _ => (-3 : ℝ)) (fun _ => 3))
      (Icc (fun _ => (-3 : ℝ)) (fun _ => 3)) := by
    intro source _
    have hbounds (who : Fin n) : 0 ≤ map source who ∧ map source who ≤ 1 := by
      have hceiling : 0 ≤ quittingCrossedCeiling first second height who ∧
          quittingCrossedCeiling first second height who ≤ 1 := by
        unfold quittingCrossedCeiling
        split_ifs <;> constructor <;> linarith
      constructor
      · exact le_min hceiling.1 (le_max_left _ _)
      · exact (min_le_left _ _).trans hceiling.2
    exact ⟨fun who => by linarith [(hbounds who).1],
      fun who => by linarith [(hbounds who).2]⟩
  have hfixed : ∀ source ∈ Icc (fun _ => (-3 : ℝ)) (fun _ => 3),
      source = map source → source ∈ quittingCrossedOmega := by
    intro source _ hsource
    apply quittingCrossedFixedPointField_zero_mem_omega
      reward first second height hheight hheightOne source
    exact sub_eq_zero.mpr hsource
  exact ambientDegree_of_selfMap_eq_one
    (fun _ => -3) (fun _ => 3) (by intro; norm_num) map
    (continuous_quittingCrossedClippedMap reward first second height) hself
    quittingCrossedOmega isOpen_quittingCrossedOmega isBounded_quittingCrossedOmega
    closure_quittingCrossedOmega_coordinateInterior hfixed

/-- The existing isolated origin comparison is literally the ambient degree
on a real open ball, with its frontier avoidance and radius derived. -/
theorem exists_quittingCrossedFixedPointField_ambientDegree_ball_eq_r0Degree
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ) (hheight : 0 < height)
    (hR0 : IsR0Matrix (quittingCrossedSingletonMatrix reward first second)) :
    ∃ radius : ℝ, 0 < radius ∧ radius < 1 ∧
      (∀ source : Fin n → ℝ, ‖source‖ ≤ radius →
        quittingCrossedClippedMap reward first second height source = source → source = 0) ∧
      ∃ hfrontier : ∀ source ∈ frontier (Metric.ball (0 : Fin n → ℝ) radius),
        quittingCrossedFixedPointField reward first second height source ≠ 0,
        ambientDegree (quittingCrossedFixedPointField reward first second height)
          (Metric.ball 0 radius) 0 Metric.isOpen_ball Metric.isBounded_ball
          (continuous_quittingCrossedFixedPointField reward first second height).continuousOn
          hfrontier = r0Degree (quittingCrossedSingletonMatrix reward first second) hR0 := by
  obtain ⟨radius, hradius, hsmall, hisolation, horigin, hlocal⟩ :=
    exists_globalCrossed_originIsolation_localDegree_eq_r0Degree
      reward first second height hheight hR0
  have hclosure : closure (Metric.ball (0 : Fin n → ℝ) radius) ⊆
      {source | ∀ who, (-2 : ℝ) < source who ∧ source who < 2} := by
    intro source hsource who
    have hclosed : source ∈ Metric.closedBall (0 : Fin n → ℝ) radius :=
      (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall) hsource
    have hnorm : ‖source‖ ≤ radius := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hclosed
    have hcoordinate := (norm_le_pi_norm source who).trans hnorm
    rw [Real.norm_eq_abs, abs_le] at hcoordinate
    constructor <;> linarith
  have hfrontier : ∀ source ∈ frontier (Metric.ball (0 : Fin n → ℝ) radius),
      quittingCrossedFixedPointField reward first second height source ≠ 0 := by
    intro source hsource hzero
    have hclosed : source ∈ Metric.closedBall (0 : Fin n → ℝ) radius :=
      (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall)
        (frontier_subset_closure hsource)
    have hnorm : ‖source‖ ≤ radius := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hclosed
    have hsourceZero := hisolation source hnorm (sub_eq_zero.mp hzero).symm
    have hmem : source ∈ Metric.ball (0 : Fin n → ℝ) radius := by
      simpa only [hsourceZero, Metric.mem_ball, dist_self] using hradius
    have hinterior : source ∈ interior (Metric.ball (0 : Fin n → ℝ) radius) := by
      rwa [Metric.isOpen_ball.interior_eq]
    exact (mem_interior_iff_notMem_frontier hmem).mp hinterior hsource
  have hcomputed := ambientDegree_eq_of_extension
    (quittingCrossedFixedPointField reward first second height) (Metric.ball 0 radius) 0
    Metric.isOpen_ball Metric.isBounded_ball
    (continuous_quittingCrossedFixedPointField reward first second height).continuousOn
    hfrontier (fun _ => -2) (fun _ => 2) (by intro; norm_num) hclosure
    (quittingCrossedFixedPointField reward first second height)
    (continuous_quittingCrossedFixedPointField reward first second height).continuousOn
    (fun _ _ => rfl)
  have hintrinsic : ambientDegree (quittingCrossedFixedPointField reward first second height)
      (Metric.ball 0 radius) 0 Metric.isOpen_ball Metric.isBounded_ball
      (continuous_quittingCrossedFixedPointField reward first second height).continuousOn
      hfrontier = (quittingCrossedGlobalProblem reward first second height).localDegree
        (quittingCrossedGlobalChart ⁻¹' Metric.ball 0 radius) horigin := by
    simpa only [sub_zero, quittingCrossedGlobalProblem, quittingCrossedGlobalChart]
      using hcomputed
  exact ⟨radius, hradius, hsmall, hisolation, hfrontier, hintrinsic.trans hlocal⟩

end GameTheory
