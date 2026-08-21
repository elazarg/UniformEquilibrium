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

open Finset Math Math.LinearProgramming Set unitInterval
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

end GameTheory.QuittingLCPClassification
