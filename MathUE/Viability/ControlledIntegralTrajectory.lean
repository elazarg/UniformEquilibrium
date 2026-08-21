/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Controlled integral trajectories

A controlled differential inclusion is most honestly represented by its
integral equation: a state remains in a constraint set, an admissible control
is selected almost everywhere, and the accumulated dynamics reproduce the
state.  This formulation accommodates the measurable controls supplied by
classical viability theorems; it does not incorrectly demand a pointwise
derivative or a continuous selector.
-/

noncomputable section

namespace Math
namespace Viability

open MeasureTheory Set
open scoped Interval

variable {State Control : Type*}
  [NormedAddCommGroup State] [NormedSpace ℝ State] [CompleteSpace State]

/-- A controlled trajectory on the unoriented interval between `start` and
`finish`.  Its state solves the integral equation, stays in `constraint`, and
uses an admissible control almost everywhere. -/
structure ControlledIntegralTrajectory
    (constraint : Set State) (admissible : ℝ → State → Set Control)
    (dynamics : ℝ → State → Control → State)
    (start finish : ℝ) (initial : State) where
  state : ℝ → State
  control : ℝ → Control
  dynamics_intervalIntegrable : IntervalIntegrable
    (fun time => dynamics time (state time) (control time)) volume start finish
  state_eq : ∀ time ∈ uIcc start finish,
    state time = initial +
      ∫ s in start..time, dynamics s (state s) (control s)
  state_mem : ∀ time ∈ uIcc start finish, state time ∈ constraint
  control_mem : ∀ᵐ time ∂volume.restrict (uIcc start finish),
    control time ∈ admissible time (state time)

omit [CompleteSpace State] in
/-- The integral equation pins the state at the initial time. -/
@[simp] theorem ControlledIntegralTrajectory.state_start
    {constraint : Set State} {admissible : ℝ → State → Set Control}
    {dynamics : ℝ → State → Control → State}
    {start finish : ℝ} {initial : State}
    (trajectory : ControlledIntegralTrajectory constraint admissible dynamics
      start finish initial) :
    trajectory.state start = initial := by
  rw [trajectory.state_eq start left_mem_uIcc]
  simp

omit [CompleteSpace State] in
/-- Every controlled integral trajectory has a continuous state path on its
time interval. -/
theorem ControlledIntegralTrajectory.continuousOn_state
    {constraint : Set State} {admissible : ℝ → State → Set Control}
    {dynamics : ℝ → State → Control → State}
    {start finish : ℝ} {initial : State}
    (trajectory : ControlledIntegralTrajectory constraint admissible dynamics
      start finish initial) :
    ContinuousOn trajectory.state (uIcc start finish) := by
  let velocity : ℝ → State := fun time =>
    dynamics time (trajectory.state time) (trajectory.control time)
  have hintegral : ContinuousOn (fun time => ∫ s in start..time, velocity s)
      (uIcc start finish) :=
    intervalIntegral.continuousOn_primitive_interval'
      trajectory.dynamics_intervalIntegrable left_mem_uIcc
  have hformula : EqOn trajectory.state
      (fun time => initial + ∫ s in start..time, velocity s)
      (uIcc start finish) := by
    intro time htime
    exact trajectory.state_eq time htime
  have hcontinuous : ContinuousOn
      (fun time => initial + ∫ s in start..time, velocity s)
      (uIcc start finish) :=
    continuousOn_const.add hintegral
  exact hcontinuous.congr hformula

end Viability
end Math
