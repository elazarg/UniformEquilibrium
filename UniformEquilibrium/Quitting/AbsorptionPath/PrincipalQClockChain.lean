/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.PrincipalQLocalArc

/-!
# Finite clocked principal-Q chains

This module concatenates the local paper-clock arcs as finite data. Each step
advances time strictly, stays on the nonnegative boundary throughout, and has
the exact scaled-state balance. No divergence of an infinite clock is asserted.
-/

noncomputable section

namespace GameTheory.QuittingLCPClassification

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One nontrivial local arc, retaining precisely the data needed to append
the next arc at its right endpoint. -/
structure PrincipalQClockStep (M : ι → ι → ℝ) (stepBound start : ℝ)
    (q : ι → ℝ) where
  direction : NonnegativeBoundaryDirection M q
  alpha : ℝ
  alpha_pos : 0 < alpha
  alpha_lt_stepBound : alpha < stepBound
  alpha_lt_one : alpha < 1
  start_pos : 0 < start
  state_mem : ∀ time ∈ Icc start (start / (1 - alpha)),
    IsNonnegativeBoundary
      (principalQLocalArcState M start q direction time)

/-- The right clock endpoint of a local principal-Q step. -/
def PrincipalQClockStep.endTime
    {M : ι → ι → ℝ} {stepBound start : ℝ} {q : ι → ℝ}
    (step : PrincipalQClockStep M stepBound start q) : ℝ :=
  start / (1 - step.alpha)

/-- The state at the right endpoint of a local principal-Q step. -/
def PrincipalQClockStep.endState
    {M : ι → ι → ℝ} {stepBound start : ℝ} {q : ι → ℝ}
    (step : PrincipalQClockStep M stepBound start q) : ι → ℝ :=
  principalQLocalArcState M start q step.direction step.endTime

omit [DecidableEq ι] in
/-- Every local clock step advances time strictly. -/
theorem PrincipalQClockStep.start_lt_endTime
    {M : ι → ι → ℝ} {stepBound start : ℝ} {q : ι → ℝ}
    (step : PrincipalQClockStep M stepBound start q) :
    start < step.endTime := by
  exact principalQArc_start_lt_end step.start_pos step.alpha_pos step.alpha_lt_one

omit [DecidableEq ι] in
/-- The end time of a local clock step is positive. -/
theorem PrincipalQClockStep.endTime_pos
    {M : ι → ι → ℝ} {stepBound start : ℝ} {q : ι → ℝ}
    (step : PrincipalQClockStep M stepBound start q) :
    0 < step.endTime :=
  step.start_pos.trans step.start_lt_endTime

omit [DecidableEq ι] in
/-- The right endpoint remains on the nonnegative boundary. -/
theorem PrincipalQClockStep.endState_mem
    {M : ι → ι → ℝ} {stepBound start : ℝ} {q : ι → ℝ}
    (step : PrincipalQClockStep M stepBound start q) :
    IsNonnegativeBoundary step.endState := by
  apply step.state_mem step.endTime
  exact ⟨step.start_lt_endTime.le, le_rfl⟩

/-- Complete projective-Q face control supplies one clock step below every
positive affine mesh. -/
theorem exists_principalQClockStep
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound start : ℝ}
    (hstepBound : 0 < stepBound) (hstart : 0 < start)
    (q : ι → ℝ) (hq : IsNonnegativeBoundary q) :
    Nonempty (PrincipalQClockStep M stepBound start q) := by
  obtain ⟨direction, alpha, halpha, halphaBound, halphaOne, _hend, hstate⟩ :=
    exists_principalQLocalArc M hdiag hQ hstart hstepBound q hq
  exact ⟨⟨direction, alpha, halpha, halphaBound, halphaOne, hstart, hstate⟩⟩

/-- A finite sequence of composable clocked local arcs. -/
inductive PrincipalQClockChain (M : ι → ι → ℝ) (stepBound : ℝ) :
    (length : ℕ) → (start : ℝ) → (q : ι → ℝ) → Type
  | nil {start : ℝ} {q : ι → ℝ}
      (hstart : 0 < start) (hq : IsNonnegativeBoundary q) :
      PrincipalQClockChain M stepBound 0 start q
  | cons {length : ℕ} {start : ℝ} {q : ι → ℝ}
      (step : PrincipalQClockStep M stepBound start q)
      (tail : PrincipalQClockChain M stepBound length
        step.endTime step.endState) :
      PrincipalQClockChain M stepBound (length + 1) start q

/-- Projective-Q face control supplies a clocked chain of every finite length. -/
theorem nonempty_principalQClockChain
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound start : ℝ}
    (hstepBound : 0 < stepBound) (hstart : 0 < start)
    (q : ι → ℝ) (hq : IsNonnegativeBoundary q) (length : ℕ) :
    Nonempty (PrincipalQClockChain M stepBound length start q) := by
  induction length generalizing start q with
  | zero => exact ⟨.nil hstart hq⟩
  | succ length ih =>
      obtain ⟨step⟩ :=
        exists_principalQClockStep M hdiag hQ hstepBound hstart q hq
      obtain ⟨tail⟩ := ih step.endTime_pos step.endState step.endState_mem
      exact ⟨.cons step tail⟩

end GameTheory.QuittingLCPClassification
