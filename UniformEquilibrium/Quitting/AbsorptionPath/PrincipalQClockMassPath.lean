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

end GameTheory.QuittingLCPClassification
