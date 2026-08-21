/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Topology.PathConcatenation
import MathUE.Viability.LipschitzCompactness
import Mathlib.Analysis.Convex.PathConnected
import UniformEquilibrium.Quitting.AbsorptionPath.PrincipalQClockReachability

/-!
# Cumulative-control paths for principal-Q clock reachability

A clock path records the cumulative simplex control on a normalized unit
interval.  Coordinate monotonicity and the exact total-mass clock make its
Lipschitz bound automatic.  The matrix image of cumulative mass is required
to remain on the scaled nonnegative boundary and to reach the prescribed
clock node.  This is the compact path carrier used to compile well-founded
clock reachability into a continuous absorption path.
-/

noncomputable section

namespace GameTheory.QuittingLCPClassification

open Filter Finset Math Math.LinearProgramming Set unitInterval
open scoped unitInterval

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The matrix image of an arbitrary cumulative player-mass vector. -/
def principalQMassImage (M : ι → ι → ℝ) (mass : ι → ℝ) : ι → ℝ :=
  fun who => ∑ owner, mass owner * M who owner

omit [DecidableEq ι] in
@[simp] theorem principalQMassImage_zero (M : ι → ι → ℝ) :
    principalQMassImage M 0 = 0 := by
  funext who
  simp [principalQMassImage]

omit [DecidableEq ι] in
/-- Matrix images are additive in cumulative mass. -/
theorem principalQMassImage_add (M : ι → ι → ℝ)
    (first second : ι → ℝ) :
    principalQMassImage M (first + second) =
      principalQMassImage M first + principalQMassImage M second := by
  funext who
  simp only [principalQMassImage, Pi.add_apply, add_mul, Finset.sum_add_distrib]

omit [DecidableEq ι] in
/-- Matrix images commute with scalar multiplication. -/
theorem principalQMassImage_smul (M : ι → ι → ℝ)
    (scale : ℝ) (mass : ι → ℝ) :
    principalQMassImage M (scale • mass) =
      scale • principalQMassImage M mass := by
  funext who
  simp only [principalQMassImage, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro owner _
  ring

omit [DecidableEq ι] in
/-- A scalar multiple of a simplex control maps to the corresponding scalar
multiple of its singleton-LCP residual. -/
theorem principalQMassImage_smul_simplex (M : ι → ι → ℝ)
    (scale : ℝ) (weight : stdSimplex ℝ ι) :
    principalQMassImage M (scale • (weight : ι → ℝ)) =
      scale • fun who => singletonLCPResidual M weight who := by
  funext who
  simp only [principalQMassImage, Pi.smul_apply, smul_eq_mul,
    singletonLCPResidual, wsum, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro owner _
  ring

/-- The elapsed clock duration between two nodes. -/
def principalQClockDuration
    (initial node : PrincipalQClockNode ι) : ℝ :=
  node.time - initial.time

/-- The normalized clock time corresponding to a unit-interval parameter. -/
def principalQNormalizedClock
    (initial node : PrincipalQClockNode ι) (parameter : unitInterval) : ℝ :=
  initial.time + (parameter : ℝ) * principalQClockDuration initial node

/-- Cumulative simplex control from `initial` to `node`, normalized to the
unit interval.  Its total mass is exactly elapsed clock time. -/
structure PrincipalQClockMassPath
    (M : ι → ι → ℝ) (initial node : PrincipalQClockNode ι) where
  mass : BoundedContinuousFunction unitInterval (ι → ℝ)
  mass_zero : mass 0 = 0
  coordinate_monotone : ∀ who,
    Monotone fun parameter => mass parameter who
  total_mass : ∀ parameter,
    ∑ who, mass parameter who =
      (parameter : ℝ) * principalQClockDuration initial node
  scaledState_mem : ∀ parameter,
    principalQClockScaledState initial +
        principalQMassImage M (mass parameter) ∈
      nonnegativeBoundary
  scaledState_one :
    principalQClockScaledState initial +
        principalQMassImage M (mass 1) =
      principalQClockScaledState node

omit [DecidableEq ι] in
/-- Robust mesh support: whenever a player's cumulative control increases
on an interval, some clock point in that same interval has that player's
scaled state within the local mesh error of zero. -/
def PrincipalQClockMassPath.IsMeshSupported
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node) (stepBound : ℝ) : Prop :=
  ∀ who first second, first ≤ second →
    path.mass first who < path.mass second who →
    ∃ witness ∈ Set.Icc first second,
      (principalQClockScaledState initial +
          principalQMassImage M (path.mass witness)) who ≤
        principalQMatrixSpeedBound M *
          principalQNormalizedClock initial node witness * stepBound

omit [DecidableEq ι] in
/-- Every coordinate of cumulative mass is nonnegative. -/
theorem PrincipalQClockMassPath.mass_nonneg
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (parameter : unitInterval) (who : ι) :
    0 ≤ path.mass parameter who := by
  have hzero := path.coordinate_monotone who
    (show (0 : unitInterval) ≤ parameter from parameter.property.1)
  simpa [path.mass_zero] using hzero

omit [DecidableEq ι] in
/-- The duration of any clock mass path is nonnegative. -/
theorem PrincipalQClockMassPath.duration_nonneg
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node) :
    0 ≤ principalQClockDuration initial node := by
  have htotal := path.total_mass 1
  have hsum : 0 ≤ ∑ who, path.mass 1 who :=
    Finset.sum_nonneg fun who _ => path.mass_nonneg 1 who
  rw [htotal] at hsum
  simpa [principalQClockDuration] using hsum

/-- The duration as a nonnegative real Lipschitz constant. -/
def PrincipalQClockMassPath.durationNNReal
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node) : NNReal :=
  ⟨principalQClockDuration initial node, path.duration_nonneg⟩

omit [DecidableEq ι] in
/-- Coordinate monotonicity and exact total mass force the normalized mass
path to be Lipschitz with constant equal to elapsed clock time. -/
theorem PrincipalQClockMassPath.lipschitzWith_mass
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node) :
    LipschitzWith path.durationNNReal path.mass := by
  rw [lipschitzWith_iff_dist_le_mul]
  have hordered : ∀ first second : unitInterval, first ≤ second →
      dist (path.mass first) (path.mass second) ≤
        ↑path.durationNNReal * dist first second := by
    intro first second hle
    have hreal : (first : ℝ) ≤ (second : ℝ) := hle
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg
      (mul_nonneg path.duration_nonneg (dist_nonneg : 0 ≤ dist first second))).2
    intro who
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    rw [abs_of_nonpos
      (sub_nonpos.mpr (path.coordinate_monotone who hle))]
    calc
      -(path.mass first who - path.mass second who) =
          path.mass second who - path.mass first who := by ring
      _ ≤
          ∑ owner, (path.mass second owner - path.mass first owner) := by
        exact Finset.single_le_sum
          (fun owner _ => sub_nonneg.mpr (path.coordinate_monotone owner hle))
          (Finset.mem_univ who)
      _ = principalQClockDuration initial node *
          ((second : ℝ) - (first : ℝ)) := by
        rw [Finset.sum_sub_distrib, path.total_mass, path.total_mass]
        ring
      _ = ↑path.durationNNReal * dist first second := by
        change principalQClockDuration initial node *
            ((second : ℝ) - (first : ℝ)) =
          principalQClockDuration initial node *
            |(first : ℝ) - (second : ℝ)|
        rw [abs_of_nonpos (sub_nonpos.mpr hreal)]
        ring
  intro first second
  rcases le_total first second with hle | hle
  · exact hordered first second hle
  · rw [dist_comm]
    simpa only [dist_comm first second] using hordered second first hle

/-- The zero cumulative path witnesses reachability at the initial node. -/
def initialPrincipalQClockMassPath
    (M : ι → ι → ℝ) (initial : PrincipalQClockNode ι) :
    PrincipalQClockMassPath M initial initial where
  mass := BoundedContinuousFunction.mkOfCompact
    (ContinuousMap.const unitInterval (0 : ι → ℝ))
  mass_zero := rfl
  coordinate_monotone := fun _ _ _ _ => le_rfl
  total_mass := by
    intro parameter
    simp [principalQClockDuration]
  scaledState_mem := by
    intro parameter
    simpa using principalQClockScaledState_mem initial
  scaledState_one := by
    simp

omit [DecidableEq ι] in
/-- The zero initial path satisfies every mesh-support bound vacuously. -/
theorem initialPrincipalQClockMassPath_isMeshSupported
    (M : ι → ι → ℝ) (initial : PrincipalQClockNode ι)
    (stepBound : ℝ) :
    (initialPrincipalQClockMassPath M initial).IsMeshSupported stepBound := by
  intro who first second hle hincrease
  simp [initialPrincipalQClockMassPath] at hincrease

/-! ## Appending one local clock arc -/

/-- A cumulative mass path as an ordinary endpoint-indexed topological path. -/
def PrincipalQClockMassPath.toPath
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node) :
    Path (0 : ι → ℝ) (path.mass 1) where
  toContinuousMap := path.mass.toContinuousMap
  source' := path.mass_zero
  target' := rfl

omit [DecidableEq ι] in
@[simp] theorem PrincipalQClockMassPath.toPath_apply
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node) (parameter : unitInterval) :
    path.toPath parameter = path.mass parameter :=
  rfl

/-- Cumulative player mass contributed by one local clock arc. -/
def principalQClockStepMass
    {M : ι → ι → ℝ} {stepBound : ℝ} {node : PrincipalQClockNode ι}
    (step : PrincipalQClockStep M stepBound node.time node.state) : ι → ℝ :=
  (step.endTime - node.time) • (step.direction.weight : ι → ℝ)

omit [DecidableEq ι] in
/-- A local step contributes nonnegative mass in every coordinate. -/
theorem principalQClockStepMass_nonneg
    {M : ι → ι → ℝ} {stepBound : ℝ} {node : PrincipalQClockNode ι}
    (step : PrincipalQClockStep M stepBound node.time node.state) (who : ι) :
    0 ≤ principalQClockStepMass step who := by
  exact mul_nonneg (sub_nonneg.mpr step.start_lt_endTime.le)
    (step.direction.weight.property.1 who)

omit [DecidableEq ι] in
/-- The total mass of a local step equals its elapsed clock time. -/
theorem sum_principalQClockStepMass
    {M : ι → ι → ℝ} {stepBound : ℝ} {node : PrincipalQClockNode ι}
    (step : PrincipalQClockStep M stepBound node.time node.state) :
    ∑ who, principalQClockStepMass step who =
      step.endTime - node.time := by
  simp [principalQClockStepMass, ← Finset.mul_sum]

omit [DecidableEq ι] in
/-- Zero elapsed duration forces every coordinate of cumulative mass to be
zero. -/
theorem PrincipalQClockMassPath.mass_one_eq_zero_of_duration_eq_zero
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (hduration : principalQClockDuration initial node = 0) :
    path.mass 1 = 0 := by
  funext who
  apply le_antisymm
  · have hsingle : path.mass 1 who ≤ ∑ owner, path.mass 1 owner :=
      Finset.single_le_sum
        (fun owner _ => path.mass_nonneg 1 owner) (Finset.mem_univ who)
    rw [path.total_mass, hduration, mul_zero] at hsingle
    exact hsingle
  · exact path.mass_nonneg 1 who

/-- The affine mass segment contributed by a local clock step. -/
def PrincipalQClockMassPath.stepSegment
    {M : ι → ι → ℝ} {stepBound : ℝ}
    {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (step : PrincipalQClockStep M stepBound node.time node.state) :
    Path (path.mass 1) (path.mass 1 + principalQClockStepMass step) :=
  Path.segment (path.mass 1)
    (path.mass 1 + principalQClockStepMass step)

omit [DecidableEq ι] in
/-- Total mass along the appended affine segment is the old duration plus
the corresponding fraction of the new step duration. -/
theorem PrincipalQClockMassPath.sum_stepSegment
    {M : ι → ι → ℝ} {stepBound : ℝ}
    {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (step : PrincipalQClockStep M stepBound node.time node.state)
    (parameter : unitInterval) :
    ∑ who, path.stepSegment step parameter who =
      principalQClockDuration initial node +
        (parameter : ℝ) * (step.endTime - node.time) := by
  simp only [PrincipalQClockMassPath.stepSegment, Path.segment_apply,
    AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, path.total_mass,
    sum_principalQClockStepMass]
  norm_num
  ring

omit [DecidableEq ι] in
/-- Total mass along a zero-based local segment is its parameter times the
step duration. -/
theorem sum_principalQClockStepMass_segment
    {M : ι → ι → ℝ} {stepBound : ℝ} {node : PrincipalQClockNode ι}
    (step : PrincipalQClockStep M stepBound node.time node.state)
    (parameter : unitInterval) :
    ∑ who, Path.segment (0 : ι → ℝ) (principalQClockStepMass step)
        parameter who =
      (parameter : ℝ) * (step.endTime - node.time) := by
  simp only [Path.segment_apply, AffineMap.lineMap_apply_module, Pi.zero_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_zero, zero_add,
    ← Finset.mul_sum, sum_principalQClockStepMass]

omit [DecidableEq ι] in
/-- The scaled state along the appended affine mass segment is exactly the
local principal-Q arc state at the corresponding clock time. -/
theorem PrincipalQClockMassPath.scaledState_stepSegment
    {M : ι → ι → ℝ} {stepBound : ℝ}
    {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (step : PrincipalQClockStep M stepBound node.time node.state)
    (parameter : unitInterval) :
    principalQClockScaledState initial +
        principalQMassImage M (path.stepSegment step parameter) =
      (node.time + (parameter : ℝ) * (step.endTime - node.time)) •
        principalQLocalArcState M node.time node.state step.direction
          (node.time + (parameter : ℝ) * (step.endTime - node.time)) := by
  have htime : node.time ≤
      node.time + (parameter : ℝ) * (step.endTime - node.time) := by
    exact le_add_of_nonneg_right (mul_nonneg parameter.property.1
      (sub_nonneg.mpr step.start_lt_endTime.le))
  have hsegment : path.stepSegment step parameter =
      path.mass 1 + (parameter : ℝ) • principalQClockStepMass step := by
    funext who
    simp only [PrincipalQClockMassPath.stepSegment, Path.segment_apply,
      AffineMap.lineMap_apply_module', Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  have hstepImage : principalQMassImage M (principalQClockStepMass step) =
      (step.endTime - node.time) • fun who =>
        singletonLCPResidual M step.direction.weight who := by
    exact principalQMassImage_smul_simplex M
      (step.endTime - node.time) step.direction.weight
  rw [hsegment, principalQMassImage_add, principalQMassImage_smul,
    ← add_assoc, path.scaledState_one]
  rw [principalQLocalArcState_scaled_balance M node.time_pos htime]
  rw [hstepImage]
  funext who
  simp only [principalQClockScaledState, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

omit [DecidableEq ι] in
/-- The scaled state along an appended affine segment remains on the
nonnegative boundary. -/
theorem PrincipalQClockMassPath.scaledState_stepSegment_mem
    {M : ι → ι → ℝ} {stepBound : ℝ}
    {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (step : PrincipalQClockStep M stepBound node.time node.state)
    (parameter : unitInterval) :
    principalQClockScaledState initial +
        principalQMassImage M (path.stepSegment step parameter) ∈
      nonnegativeBoundary := by
  let time := node.time + (parameter : ℝ) * (step.endTime - node.time)
  have htimeLower : node.time ≤ time := by
    exact le_add_of_nonneg_right (mul_nonneg parameter.property.1
      (sub_nonneg.mpr step.start_lt_endTime.le))
  have htimeUpper : time ≤ step.endTime := by
    dsimp only [time]
    nlinarith [parameter.property.2, step.start_lt_endTime.le]
  have hstate := step.state_mem time ⟨htimeLower, htimeUpper⟩
  rw [path.scaledState_stepSegment]
  constructor
  · intro who
    exact mul_nonneg (node.time_pos.trans_le htimeLower).le (hstate.1 who)
  · obtain ⟨who, hwho⟩ := hstate.2
    refine ⟨who, ?_⟩
    change time *
      principalQLocalArcState M node.time node.state step.direction time who = 0
    rw [hwho, mul_zero]

omit [DecidableEq ι] in
/-- On a mesh arc, every coordinate receiving positive mass has scaled state
at most `speed · clock · mesh`. This robust support estimate is designed
to survive a vanishing-mesh compact limit. -/
theorem PrincipalQClockMassPath.scaledState_stepSegment_le_mesh
    {M : ι → ι → ℝ} {stepBound : ℝ}
    {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (step : PrincipalQClockStep M stepBound node.time node.state)
    (parameter : unitInterval) (who : ι)
    (hweight : step.direction.weight who ≠ 0) :
    (principalQClockScaledState initial +
        principalQMassImage M (path.stepSegment step parameter)) who ≤
      principalQMatrixSpeedBound M *
        (node.time + (parameter : ℝ) * (step.endTime - node.time)) *
          stepBound := by
  let clock := node.time +
    (parameter : ℝ) * (step.endTime - node.time)
  have hclockLower : node.time ≤ clock := by
    exact le_add_of_nonneg_right (mul_nonneg parameter.property.1
      (sub_nonneg.mpr step.start_lt_endTime.le))
  have hclockUpper : clock ≤ step.endTime := by
    dsimp only [clock]
    nlinarith [parameter.property.2, step.start_lt_endTime.le]
  have hclockPos : 0 < clock := node.time_pos.trans_le hclockLower
  have halphaDenom : 0 < 1 - step.alpha := sub_pos.mpr step.alpha_lt_one
  have hscaledClock : clock * (1 - step.alpha) ≤ node.time := by
    apply (le_div_iff₀ halphaDenom).mp
    simpa [PrincipalQClockStep.endTime, mul_comm] using hclockUpper
  have hdeltaAlpha : clock - node.time ≤ clock * step.alpha := by
    linarith
  have hdeltaNonneg : 0 ≤ clock - node.time := sub_nonneg.mpr hclockLower
  have hsupport : node.state who = 0 :=
    step.direction.supported_on_zero who hweight
  have hbalance := congrFun
    (principalQLocalArcState_scaled_balance M node.time_pos hclockLower
      node.state step.direction) who
  have hstateEq :
      (clock • principalQLocalArcState M node.time node.state
        step.direction clock) who =
        (clock - node.time) *
          singletonLCPResidual M step.direction.weight who := by
    simpa [hsupport] using hbalance
  rw [path.scaledState_stepSegment]
  change (clock • principalQLocalArcState M node.time node.state
    step.direction clock) who ≤ _
  rw [hstateEq]
  have hresidual : singletonLCPResidual M step.direction.weight who ≤
      principalQMatrixSpeedBound M := by
    calc
      singletonLCPResidual M step.direction.weight who ≤
          |singletonLCPResidual M step.direction.weight who| := le_abs_self _
      _ = ‖singletonLCPResidual M step.direction.weight who‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ‖fun i => singletonLCPResidual M step.direction.weight i‖ :=
        norm_le_pi_norm _ who
      _ ≤ principalQMatrixSpeedBound M :=
        norm_singletonLCPResidual_le_speedBound M step.direction.weight
  calc
    (clock - node.time) *
        singletonLCPResidual M step.direction.weight who ≤
      (clock - node.time) * principalQMatrixSpeedBound M :=
        mul_le_mul_of_nonneg_left hresidual hdeltaNonneg
    _ = principalQMatrixSpeedBound M * (clock - node.time) := mul_comm _ _
    _ ≤ principalQMatrixSpeedBound M * (clock * step.alpha) :=
      mul_le_mul_of_nonneg_left hdeltaAlpha
        (principalQMatrixSpeedBound_nonneg M)
    _ ≤ principalQMatrixSpeedBound M * (clock * stepBound) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left step.alpha_lt_stepBound.le hclockPos.le)
        (principalQMatrixSpeedBound_nonneg M)
    _ = principalQMatrixSpeedBound M * clock * stepBound := by ring

omit [DecidableEq ι] in
/-- Every strict coordinate increase inside one local segment has an
in-interval witness satisfying the robust mesh-support estimate. -/
theorem PrincipalQClockMassPath.exists_stepSegment_meshSupport_witness
    {M : ι → ι → ℝ} {stepBound : ℝ}
    {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (step : PrincipalQClockStep M stepBound node.time node.state)
    (who : ι) (first second : unitInterval) (hle : first ≤ second)
    (hincrease : path.stepSegment step first who <
      path.stepSegment step second who) :
    ∃ witness ∈ Set.Icc first second,
      (principalQClockScaledState initial +
          principalQMassImage M (path.stepSegment step witness)) who ≤
        principalQMatrixSpeedBound M *
          (node.time + (witness : ℝ) * (step.endTime - node.time)) *
            stepBound := by
  have hweight : step.direction.weight who ≠ 0 := by
    intro hzero
    have hstepMass : principalQClockStepMass step who = 0 := by
      simp [principalQClockStepMass, hzero]
    have hconstant (parameter : unitInterval) :
        path.stepSegment step parameter who = path.mass 1 who := by
      simp [PrincipalQClockMassPath.stepSegment,
        AffineMap.lineMap_apply_module', hstepMass]
    rw [hconstant first, hconstant second] at hincrease
    exact (lt_irrefl _ hincrease).elim
  exact ⟨second, ⟨hle, le_rfl⟩,
    path.scaledState_stepSegment_le_mesh step second who hweight⟩

/-- The cumulative mass function obtained by appending one local clock arc.
The nontrivial-duration branch concatenates at the exact ratio of elapsed
clock durations; a zero-duration prefix is discarded. -/
def PrincipalQClockMassPath.appendMass
    {M : ι → ι → ℝ} {stepBound : ℝ}
    {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (step : PrincipalQClockStep M stepBound node.time node.state) :
    BoundedContinuousFunction unitInterval (ι → ℝ) := by
  let oldDuration := principalQClockDuration initial node
  let stepDuration := step.endTime - node.time
  if hold : 0 < oldDuration then
    have hstep : 0 < stepDuration := sub_pos.mpr step.start_lt_endTime
    have htotal : 0 < oldDuration + stepDuration := add_pos hold hstep
    let split := oldDuration / (oldDuration + stepDuration)
    have hsplitPos : 0 < split := div_pos hold htotal
    have hsplitOne : split < 1 :=
      (div_lt_one htotal).2 (lt_add_of_pos_right _ hstep)
    exact BoundedContinuousFunction.mkOfCompact
      ((path.toPath.transAt (path.stepSegment step) split hsplitPos hsplitOne).toContinuousMap)
  else
    exact BoundedContinuousFunction.mkOfCompact
      (Path.segment (0 : ι → ℝ) (principalQClockStepMass step)).toContinuousMap

omit [DecidableEq ι] in
/-- Appending a local arc preserves coordinatewise monotonicity of cumulative
mass. -/
theorem PrincipalQClockMassPath.monotone_appendMass
    {M : ι → ι → ℝ} {stepBound : ℝ}
    {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (step : PrincipalQClockStep M stepBound node.time node.state) (who : ι) :
    Monotone fun parameter => path.appendMass step parameter who := by
  classical
  let oldDuration := principalQClockDuration initial node
  let stepDuration := step.endTime - node.time
  by_cases hold : 0 < oldDuration
  · have hstep : 0 < stepDuration := sub_pos.mpr step.start_lt_endTime
    have htotal : 0 < oldDuration + stepDuration := add_pos hold hstep
    let split := oldDuration / (oldDuration + stepDuration)
    have hsplitPos : 0 < split := div_pos hold htotal
    have hsplitOne : split < 1 :=
      (div_lt_one htotal).2 (lt_add_of_pos_right _ hstep)
    unfold appendMass
    dsimp only
    rw [dif_pos hold]
    change Monotone fun parameter =>
      (path.toPath.transAt (path.stepSegment step) split hsplitPos hsplitOne)
        parameter who
    have hfirst : Monotone path.toPath := by
      intro first second hle owner
      exact path.coordinate_monotone owner hle
    have hsecond : Monotone (path.stepSegment step) := by
      intro first second hle owner
      have hleReal : (first : ℝ) ≤ (second : ℝ) := hle
      simp only [PrincipalQClockMassPath.stepSegment, Path.segment_apply,
        AffineMap.lineMap_apply_module', Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      have hincrement := principalQClockStepMass_nonneg step owner
      nlinarith
    exact fun first second hle =>
      Path.monotone_transAt path.toPath (path.stepSegment step) hsplitPos hsplitOne
        hfirst hsecond hle who
  · unfold appendMass
    dsimp only
    rw [dif_neg hold]
    change Monotone fun parameter =>
      Path.segment (0 : ι → ℝ) (principalQClockStepMass step) parameter who
    intro first second hle
    have hleReal : (first : ℝ) ≤ (second : ℝ) := hle
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module', Pi.zero_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_zero, add_zero]
    have hincrement := principalQClockStepMass_nonneg step who
    nlinarith

omit [DecidableEq ι] in
/-- Appending a local arc preserves the exact total-mass clock. -/
theorem PrincipalQClockMassPath.sum_appendMass
    {M : ι → ι → ℝ} {stepBound : ℝ}
    {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (step : PrincipalQClockStep M stepBound node.time node.state)
    (parameter : unitInterval) :
    ∑ who, path.appendMass step parameter who =
      (parameter : ℝ) * principalQClockDuration initial step.endNode := by
  classical
  let oldDuration := principalQClockDuration initial node
  let stepDuration := step.endTime - node.time
  have hduration : principalQClockDuration initial step.endNode =
      oldDuration + stepDuration := by
    simp only [principalQClockDuration, PrincipalQClockStep.endNode_time]
    dsimp only [oldDuration, stepDuration, principalQClockDuration]
    ring
  by_cases hold : 0 < oldDuration
  · have hstep : 0 < stepDuration := sub_pos.mpr step.start_lt_endTime
    have htotal : 0 < oldDuration + stepDuration := add_pos hold hstep
    let split := oldDuration / (oldDuration + stepDuration)
    have hsplitPos : 0 < split := div_pos hold htotal
    have hsplitOne : split < 1 :=
      (div_lt_one htotal).2 (lt_add_of_pos_right _ hstep)
    unfold appendMass
    dsimp only
    rw [dif_pos hold]
    change (∑ who,
      (path.toPath.transAt (path.stepSegment step) split hsplitPos hsplitOne
        parameter) who) = _
    by_cases hparameter : (parameter : ℝ) ≤ split
    · rw [Path.transAt_apply_leftParameter path.toPath (path.stepSegment step)
        hsplitPos hsplitOne parameter hparameter]
      simp only [path.toPath_apply, path.total_mass, hduration]
      dsimp only [Path.transAtLeftParameter, split]
      field_simp [ne_of_gt hold, ne_of_gt htotal]
      ring
    · have hparameter' : split < (parameter : ℝ) := lt_of_not_ge hparameter
      rw [Path.transAt_apply_rightParameter path.toPath (path.stepSegment step)
        hsplitPos hsplitOne parameter hparameter']
      rw [path.sum_stepSegment, hduration]
      dsimp only [Path.transAtRightParameter, split]
      field_simp [ne_of_gt hold, ne_of_gt hstep, ne_of_gt htotal]
      ring
  · have hzero : oldDuration = 0 :=
      le_antisymm (le_of_not_gt hold) path.duration_nonneg
    unfold appendMass
    dsimp only
    rw [dif_neg hold]
    change (∑ who,
      Path.segment (0 : ι → ℝ) (principalQClockStepMass step) parameter who) = _
    rw [sum_principalQClockStepMass_segment, hduration, hzero, zero_add]

omit [DecidableEq ι] in
@[simp] theorem PrincipalQClockMassPath.appendMass_zero
    {M : ι → ι → ℝ} {stepBound : ℝ}
    {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (step : PrincipalQClockStep M stepBound node.time node.state) :
    path.appendMass step 0 = 0 := by
  classical
  let oldDuration := principalQClockDuration initial node
  let stepDuration := step.endTime - node.time
  by_cases hold : 0 < oldDuration
  · have hstep : 0 < stepDuration := sub_pos.mpr step.start_lt_endTime
    have htotal : 0 < oldDuration + stepDuration := add_pos hold hstep
    let split := oldDuration / (oldDuration + stepDuration)
    have hsplitPos : 0 < split := div_pos hold htotal
    have hsplitOne : split < 1 :=
      (div_lt_one htotal).2 (lt_add_of_pos_right _ hstep)
    unfold appendMass
    dsimp only
    rw [dif_pos hold]
    change path.toPath.transAt (path.stepSegment step) split hsplitPos hsplitOne 0 = 0
    rw [Path.transAt_apply_leftParameter path.toPath (path.stepSegment step)
      hsplitPos hsplitOne 0 (by simpa using hsplitPos.le)]
    have hparameter : Path.transAtLeftParameter hsplitPos 0
        (by simpa using hsplitPos.le) = 0 := by
      apply Subtype.ext
      simp [Path.transAtLeftParameter]
    rw [hparameter, path.toPath_apply, path.mass_zero]
  · unfold appendMass
    dsimp only
    rw [dif_neg hold]
    exact (Path.segment (0 : ι → ℝ) (principalQClockStepMass step)).source

omit [DecidableEq ι] in
@[simp] theorem PrincipalQClockMassPath.appendMass_one
    {M : ι → ι → ℝ} {stepBound : ℝ}
    {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (step : PrincipalQClockStep M stepBound node.time node.state) :
    path.appendMass step 1 = path.mass 1 + principalQClockStepMass step := by
  classical
  let oldDuration := principalQClockDuration initial node
  let stepDuration := step.endTime - node.time
  by_cases hold : 0 < oldDuration
  · have hstep : 0 < stepDuration := sub_pos.mpr step.start_lt_endTime
    have htotal : 0 < oldDuration + stepDuration := add_pos hold hstep
    let split := oldDuration / (oldDuration + stepDuration)
    have hsplitPos : 0 < split := div_pos hold htotal
    have hsplitOne : split < 1 :=
      (div_lt_one htotal).2 (lt_add_of_pos_right _ hstep)
    unfold appendMass
    dsimp only
    rw [dif_pos hold]
    change path.toPath.transAt (path.stepSegment step) split hsplitPos hsplitOne 1 = _
    rw [Path.transAt_apply_rightParameter path.toPath (path.stepSegment step)
      hsplitPos hsplitOne 1 (by simpa using hsplitOne)]
    have hparameter : Path.transAtRightParameter hsplitOne 1
        (by simpa using hsplitOne.le) = 1 := by
      apply Subtype.ext
      dsimp only [Path.transAtRightParameter]
      change (1 - split) / (1 - split) = 1
      rw [div_self (sub_ne_zero.mpr (ne_of_gt hsplitOne))]
    rw [hparameter, (path.stepSegment step).target]
  · have hzero : oldDuration = 0 :=
      le_antisymm (le_of_not_gt hold) path.duration_nonneg
    have hmassZero := path.mass_one_eq_zero_of_duration_eq_zero hzero
    unfold appendMass
    dsimp only
    rw [dif_neg hold]
    change Path.segment (0 : ι → ℝ) (principalQClockStepMass step) 1 = _
    rw [(Path.segment (0 : ι → ℝ) (principalQClockStepMass step)).target,
      hmassZero, zero_add]

omit [DecidableEq ι] in
/-- Appending a local arc preserves scaled nonnegative-boundary membership
at every normalized time. -/
theorem PrincipalQClockMassPath.scaledState_appendMass_mem
    {M : ι → ι → ℝ} {stepBound : ℝ}
    {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (step : PrincipalQClockStep M stepBound node.time node.state)
    (parameter : unitInterval) :
    principalQClockScaledState initial +
        principalQMassImage M (path.appendMass step parameter) ∈
      nonnegativeBoundary := by
  classical
  let oldDuration := principalQClockDuration initial node
  let stepDuration := step.endTime - node.time
  by_cases hold : 0 < oldDuration
  · have hstep : 0 < stepDuration := sub_pos.mpr step.start_lt_endTime
    have htotal : 0 < oldDuration + stepDuration := add_pos hold hstep
    let split := oldDuration / (oldDuration + stepDuration)
    have hsplitPos : 0 < split := div_pos hold htotal
    have hsplitOne : split < 1 :=
      (div_lt_one htotal).2 (lt_add_of_pos_right _ hstep)
    unfold appendMass
    dsimp only
    rw [dif_pos hold]
    change principalQClockScaledState initial +
        principalQMassImage M
          (path.toPath.transAt (path.stepSegment step) split hsplitPos
            hsplitOne parameter) ∈ nonnegativeBoundary
    by_cases hparameter : (parameter : ℝ) ≤ split
    · rw [Path.transAt_apply_leftParameter path.toPath (path.stepSegment step)
        hsplitPos hsplitOne parameter hparameter, path.toPath_apply]
      exact path.scaledState_mem _
    · have hparameter' : split < (parameter : ℝ) := lt_of_not_ge hparameter
      rw [Path.transAt_apply_rightParameter path.toPath (path.stepSegment step)
        hsplitPos hsplitOne parameter hparameter']
      exact path.scaledState_stepSegment_mem step _
  · have hzero : oldDuration = 0 :=
      le_antisymm (le_of_not_gt hold) path.duration_nonneg
    have hmassZero := path.mass_one_eq_zero_of_duration_eq_zero hzero
    unfold appendMass
    dsimp only
    rw [dif_neg hold]
    have hsegment :
        Path.segment (0 : ι → ℝ) (principalQClockStepMass step) parameter =
          path.stepSegment step parameter := by
      simp [PrincipalQClockMassPath.stepSegment, hmassZero]
    change principalQClockScaledState initial +
        principalQMassImage M
          (Path.segment (0 : ι → ℝ) (principalQClockStepMass step) parameter) ∈
      nonnegativeBoundary
    rw [hsegment]
    exact path.scaledState_stepSegment_mem step parameter

omit [DecidableEq ι] in
/-- The endpoint of the appended cumulative mass is the scaled endpoint of
the local clock step. -/
theorem PrincipalQClockMassPath.scaledState_appendMass_one
    {M : ι → ι → ℝ} {stepBound : ℝ}
    {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (step : PrincipalQClockStep M stepBound node.time node.state) :
    principalQClockScaledState initial +
        principalQMassImage M (path.appendMass step 1) =
      principalQClockScaledState step.endNode := by
  rw [path.appendMass_one, principalQMassImage_add, ← add_assoc,
    path.scaledState_one]
  have hstepImage : principalQMassImage M (principalQClockStepMass step) =
      (step.endTime - node.time) • fun who =>
        singletonLCPResidual M step.direction.weight who := by
    exact principalQMassImage_smul_simplex M
      (step.endTime - node.time) step.direction.weight
  rw [hstepImage]
  change node.time • node.state +
      (step.endTime - node.time) • (fun who =>
        singletonLCPResidual M step.direction.weight who) =
    step.endTime • step.endState
  exact (principalQLocalArcState_scaled_balance M node.time_pos
    step.start_lt_endTime.le node.state step.direction).symm

/-- Append one exact local principal-Q arc to a cumulative clock mass path. -/
def PrincipalQClockMassPath.append
    {M : ι → ι → ℝ} {stepBound : ℝ}
    {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (step : PrincipalQClockStep M stepBound node.time node.state) :
    PrincipalQClockMassPath M initial step.endNode where
  mass := path.appendMass step
  mass_zero := path.appendMass_zero step
  coordinate_monotone := path.monotone_appendMass step
  total_mass := path.sum_appendMass step
  scaledState_mem := path.scaledState_appendMass_mem step
  scaledState_one := path.scaledState_appendMass_one step

/-! ## Exact clock truncation -/

omit [DecidableEq ι] in
/-- The node visited by a cumulative-mass path at a normalized parameter. -/
def PrincipalQClockMassPath.nodeAt
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (cut : unitInterval) : PrincipalQClockNode ι :=
  principalQClockNodeOfScaledState
    (principalQNormalizedClock initial node cut)
    (add_pos_of_pos_of_nonneg initial.time_pos
      (mul_nonneg cut.property.1 path.duration_nonneg))
    (principalQClockScaledState initial + principalQMassImage M (path.mass cut))
    (path.scaledState_mem cut)

omit [DecidableEq ι] in
@[simp] theorem PrincipalQClockMassPath.nodeAt_time
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (cut : unitInterval) :
    (path.nodeAt cut).time = principalQNormalizedClock initial node cut :=
  rfl

omit [DecidableEq ι] in
@[simp] theorem PrincipalQClockMassPath.scaledState_nodeAt
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (cut : unitInterval) :
    principalQClockScaledState (path.nodeAt cut) =
      principalQClockScaledState initial +
        principalQMassImage M (path.mass cut) := by
  exact principalQClockNodeOfScaledState_scaledState _ _ _ _

/-- The cumulative mass up to `cut`, reparameterized over the unit interval. -/
def PrincipalQClockMassPath.initialSegmentMass
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (cut : unitInterval) : BoundedContinuousFunction unitInterval (ι → ℝ) :=
  BoundedContinuousFunction.mkOfCompact
    (path.toPath.initialSegment cut).toContinuousMap

omit [DecidableEq ι] in
@[simp] theorem PrincipalQClockMassPath.initialSegmentMass_apply
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (cut parameter : unitInterval) :
    path.initialSegmentMass cut parameter =
      path.mass ⟨(parameter : ℝ) * (cut : ℝ), by
        constructor
        · exact mul_nonneg parameter.property.1 cut.property.1
        · nlinarith [parameter.property.1, parameter.property.2,
            cut.property.1, cut.property.2]⟩ :=
  rfl

omit [DecidableEq ι] in
/-- Restrict a cumulative-mass path to an exact intermediate clock. -/
def PrincipalQClockMassPath.initialSegment
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (cut : unitInterval) : PrincipalQClockMassPath M initial (path.nodeAt cut) where
  mass := path.initialSegmentMass cut
  mass_zero := by simp [path.mass_zero]
  coordinate_monotone := by
    intro who first second hle
    exact path.coordinate_monotone who
      (mul_le_mul_of_nonneg_right
        (show (first : ℝ) ≤ (second : ℝ) from hle) cut.property.1)
  total_mass := by
    intro parameter
    rw [path.initialSegmentMass_apply, path.total_mass]
    simp only [principalQClockDuration, path.nodeAt_time,
      principalQNormalizedClock]
    ring
  scaledState_mem := by
    intro parameter
    rw [path.initialSegmentMass_apply]
    exact path.scaledState_mem _
  scaledState_one := by
    rw [path.initialSegmentMass_apply, path.scaledState_nodeAt]
    congr 3
    ext
    simp

/-! ## Compact limits of normalized clock mass paths -/

omit [DecidableEq ι] in
/-- Convergence of endpoint clocks gives a uniformly convergent subsequence
of normalized cumulative-mass paths.  Exact clock mass makes both the common
Lipschitz constant and the common compact range automatic. -/
theorem exists_tendsto_subsequence_principalQClockMass
    {M : ι → ι → ℝ} {initial : PrincipalQClockNode ι}
    (node : ℕ → PrincipalQClockNode ι)
    (timeLimit : ℝ)
    (htime : Tendsto (fun n => (node n).time) atTop (nhds timeLimit))
    (path : ∀ n, PrincipalQClockMassPath M initial (node n)) :
    ∃ limit : BoundedContinuousFunction unitInterval (ι → ℝ),
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
        Tendsto (fun n => (path (subsequence n)).mass) atTop (nhds limit) := by
  let duration : ℕ → ℝ := fun n => principalQClockDuration initial (node n)
  have hduration : Tendsto duration atTop
      (nhds (timeLimit - initial.time)) := by
    exact htime.sub tendsto_const_nhds
  obtain ⟨bound, hbound⟩ :=
    Metric.isBounded_range_iff.mp
      (Metric.isBounded_range_of_tendsto duration hduration)
  let boundReal := max (duration 0 + bound) 0
  have hdurationLe (n : ℕ) : duration n ≤ boundReal := by
    have hdist := hbound n 0
    have hdiff : duration n - duration 0 ≤ bound := by
      exact (le_abs_self (duration n - duration 0)).trans (by
        simpa [Real.dist_eq] using hdist)
    exact (by linarith : duration n ≤ duration 0 + bound) |>.trans
      (le_max_left _ _)
  let boundNNReal : NNReal := ⟨boundReal, le_max_right _ _⟩
  let rangeSet : Set (ι → ℝ) := Metric.closedBall 0 boundReal
  have hpath (n : ℕ) : (path n).mass ∈
      Viability.compactRangeLipschitzFamily boundNNReal rangeSet := by
    constructor
    · apply (path n).lipschitzWith_mass.weaken
      exact hdurationLe n
    · intro parameter
      rw [Metric.mem_closedBall]
      calc
        dist ((path n).mass parameter) 0 =
            dist ((path n).mass parameter) ((path n).mass 0) := by
          rw [(path n).mass_zero]
        _ ≤ duration n * dist parameter 0 :=
          (path n).lipschitzWith_mass.dist_le_mul parameter 0
        _ ≤ duration n := by
          apply mul_le_of_le_one_right (path n).duration_nonneg
          change dist (parameter : ℝ) 0 ≤ 1
          rw [Real.dist_eq, sub_zero, abs_of_nonneg parameter.property.1]
          exact parameter.property.2
        _ ≤ boundReal := hdurationLe n
  obtain ⟨limit, _hlimit, subsequence, hsubsequence, htendsto⟩ :=
    Viability.exists_tendsto_subsequence_compactRangeLipschitzFamily
      boundNNReal (isCompact_closedBall (0 : ι → ℝ) boundReal)
      (fun n => (path n).mass) hpath
  exact ⟨limit, subsequence, hsubsequence, htendsto⟩

omit [DecidableEq ι] in
/-- Uniform compactness turns a convergent sequence of endpoint nodes and
their cumulative-mass paths into a cumulative-mass path to the limit node. -/
theorem exists_principalQClockMassPath_limit
    {M : ι → ι → ℝ} {initial : PrincipalQClockNode ι}
    (node : ℕ → PrincipalQClockNode ι)
    (path : ∀ n, PrincipalQClockMassPath M initial (node n))
    (timeLimit : ℝ) (htimeLimit : 0 < timeLimit)
    (scaledStateLimit : ι → ℝ)
    (hscaledStateLimit : scaledStateLimit ∈ nonnegativeBoundary)
    (htime : Tendsto (fun n => (node n).time) atTop (nhds timeLimit))
    (hscaledState : Tendsto (fun n => principalQClockScaledState (node n))
      atTop (nhds scaledStateLimit)) :
    Nonempty (PrincipalQClockMassPath M initial
      (principalQClockNodeOfScaledState timeLimit htimeLimit
        scaledStateLimit hscaledStateLimit)) := by
  obtain ⟨limit, subsequence, hsubsequence, hmass⟩ :=
    exists_tendsto_subsequence_principalQClockMass
      node timeLimit htime path
  have hmassAt (parameter : unitInterval) : Tendsto
      (fun n => (path (subsequence n)).mass parameter) atTop
      (nhds (limit parameter)) := by
    exact ((BoundedContinuousFunction.lipschitz_eval_const parameter).continuous
      |>.tendsto limit).comp hmass
  have htimeSubsequence : Tendsto (fun n => (node (subsequence n)).time)
      atTop (nhds timeLimit) :=
    htime.comp hsubsequence.tendsto_atTop
  have hscaledSubsequence : Tendsto
      (fun n => principalQClockScaledState (node (subsequence n)))
      atTop (nhds scaledStateLimit) :=
    hscaledState.comp hsubsequence.tendsto_atTop
  refine ⟨{
    mass := limit
    mass_zero := ?_
    coordinate_monotone := ?_
    total_mass := ?_
    scaledState_mem := ?_
    scaledState_one := ?_ }⟩
  · apply tendsto_nhds_unique (hmassAt 0)
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ι → ℝ))
      atTop (nhds 0)) |>.congr' (Eventually.of_forall fun n =>
        (path (subsequence n)).mass_zero.symm)
  · intro who first second hle
    have hfirst : Tendsto
        (fun n => (path (subsequence n)).mass first who) atTop
        (nhds (limit first who)) :=
      ((continuous_apply who).tendsto _).comp (hmassAt first)
    have hsecond : Tendsto
        (fun n => (path (subsequence n)).mass second who) atTop
        (nhds (limit second who)) :=
      ((continuous_apply who).tendsto _).comp (hmassAt second)
    exact le_of_tendsto_of_tendsto' hfirst hsecond
      (fun n => (path (subsequence n)).coordinate_monotone who hle)
  · intro parameter
    have hsum : Tendsto
        (fun n => ∑ who, (path (subsequence n)).mass parameter who)
        atTop (nhds (∑ who, limit parameter who)) := by
      apply tendsto_finsetSum
      intro who _
      exact ((continuous_apply who).tendsto _).comp (hmassAt parameter)
    have hright : Tendsto
        (fun n => (parameter : ℝ) *
          principalQClockDuration initial (node (subsequence n))) atTop
        (nhds ((parameter : ℝ) *
          principalQClockDuration initial
            (principalQClockNodeOfScaledState timeLimit htimeLimit
              scaledStateLimit hscaledStateLimit))) := by
      simpa only [principalQClockDuration,
        principalQClockNodeOfScaledState_time] using
        tendsto_const_nhds.mul
          (htimeSubsequence.sub tendsto_const_nhds)
    apply tendsto_nhds_unique hsum
    exact hright.congr' (Eventually.of_forall fun n =>
      (path (subsequence n)).total_mass parameter |>.symm)
  · intro parameter
    have hstate : Tendsto
        (fun n => principalQClockScaledState initial +
          principalQMassImage M ((path (subsequence n)).mass parameter))
        atTop (nhds (principalQClockScaledState initial +
          principalQMassImage M (limit parameter))) := by
      have hcontinuous : Continuous (fun mass : ι → ℝ =>
          principalQClockScaledState initial + principalQMassImage M mass) := by
        unfold principalQMassImage
        fun_prop
      exact (hcontinuous.tendsto _).comp (hmassAt parameter)
    exact isClosed_nonnegativeBoundary.mem_of_tendsto hstate
      (Eventually.of_forall fun n =>
        (path (subsequence n)).scaledState_mem parameter)
  · have hleft : Tendsto
        (fun n => principalQClockScaledState initial +
          principalQMassImage M ((path (subsequence n)).mass 1))
        atTop (nhds (principalQClockScaledState initial +
          principalQMassImage M (limit 1))) := by
      have hcontinuous : Continuous (fun mass : ι → ℝ =>
          principalQClockScaledState initial + principalQMassImage M mass) := by
        unfold principalQMassImage
        fun_prop
      exact (hcontinuous.tendsto _).comp (hmassAt 1)
    have hright : Tendsto
        (fun n => principalQClockScaledState initial +
          principalQMassImage M ((path (subsequence n)).mass 1))
        atTop (nhds scaledStateLimit) :=
      hscaledSubsequence.congr' (Eventually.of_forall fun n =>
        (path (subsequence n)).scaledState_one.symm)
    have heq := tendsto_nhds_unique hleft hright
    simpa only [principalQClockNodeOfScaledState_scaledState] using heq

omit [DecidableEq ι] in
/-- Every node in the well-founded clock-reachability closure is realized by
an exact cumulative-mass path. -/
theorem PrincipalQClockReachable.exists_massPath
    {M : ι → ι → ℝ} {stepBound : ℝ}
    {initial node : PrincipalQClockNode ι}
    (hnode : PrincipalQClockReachable M stepBound initial node) :
    Nonempty (PrincipalQClockMassPath M initial node) := by
  induction hnode with
  | initial => exact ⟨initialPrincipalQClockMassPath M initial⟩
  | step hnode arc ih =>
      obtain ⟨path⟩ := ih
      exact ⟨path.append arc⟩
  | limit node hnode timeLimit htimeLimit scaledStateLimit
      hscaledStateLimit htime hscaledState ih =>
      exact exists_principalQClockMassPath_limit node
        (fun n => Classical.choice (ih n)) timeLimit htimeLimit
        scaledStateLimit hscaledStateLimit htime hscaledState

omit [DecidableEq ι] in
/-- From any positive boundary clock, the principal-Q construction supplies
an exact cumulative-mass path to every prescribed later finite clock. -/
theorem exists_principalQClockMassPath_at_time
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (initial : PrincipalQClockNode ι)
    (target : ℝ) (hinitialTarget : initial.time ≤ target) :
    ∃ node : PrincipalQClockNode ι, node.time = target ∧
      Nonempty (PrincipalQClockMassPath M initial node) := by
  classical
  rcases eq_or_lt_of_le hinitialTarget with htarget | htarget
  · subst target
    exact ⟨initial, rfl, ⟨initialPrincipalQClockMassPath M initial⟩⟩
  · obtain ⟨later, hlaterReachable, htargetLater⟩ :=
      exists_principalQClockReachable_time_ge M hdiag hQ hstepBound
        initial target
    obtain ⟨path⟩ := hlaterReachable.exists_massPath
    have hlaterDuration : 0 < principalQClockDuration initial later := by
      exact sub_pos.mpr (htarget.trans_le htargetLater)
    let cut : unitInterval :=
      ⟨(target - initial.time) / principalQClockDuration initial later,
        div_nonneg (sub_nonneg.mpr htarget.le) hlaterDuration.le,
        (div_le_one hlaterDuration).2 (by
          simpa only [principalQClockDuration] using
            sub_le_sub_right htargetLater initial.time)⟩
    have hnodeTime : (path.nodeAt cut).time = target := by
      rw [path.nodeAt_time]
      change initial.time +
          ((target - initial.time) /
            principalQClockDuration initial later) *
              principalQClockDuration initial later = target
      rw [div_mul_cancel₀ _ hlaterDuration.ne']
      ring
    exact ⟨path.nodeAt cut, hnodeTime, ⟨path.initialSegment cut⟩⟩

end GameTheory.QuittingLCPClassification
