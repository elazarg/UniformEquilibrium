/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import Mathlib.Tactic
import UniformEquilibrium.Quitting.PayoffProcess.FiniteStageCompiler
import UniformEquilibrium.Quitting.PayoffProcess.TailSplice

/-!
# Finite-prefix backward induction for a quitting payoff process

Starting from an integrable continuation payoff at a deterministic cutoff,
this module recursively constructs the measurable finite-game roots for all
earlier stages.  The recursion is indexed by distance from the cutoff, so its
defining equation exposes exactly which conditional next-stage value is fed
to each selector.
-/

noncomputable section

namespace GameTheory

open MeasureTheory StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Backward values indexed by their distance from `cutoff`.  Distance zero
is the supplied tail payoff; a successor performs one measurable
finite-stage selection. -/
def QuittingPayoffProcess.finiteBackwardValue
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (tailValue : process.Ω → Payoff ι) :
    ℕ → process.Ω → Payoff ι
  | 0 => tailValue
  | depth + 1 =>
      process.finiteStageValue (cutoff - (depth + 1)) hδ
        (process.finiteBackwardValue cutoff hδ tailValue depth)

@[simp]
theorem QuittingPayoffProcess.finiteBackwardValue_zero
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (tailValue : process.Ω → Payoff ι) :
    process.finiteBackwardValue cutoff hδ tailValue 0 = tailValue :=
  rfl

@[simp]
theorem QuittingPayoffProcess.finiteBackwardValue_succ
    (process : QuittingPayoffProcess ι) (cutoff depth : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (tailValue : process.Ω → Payoff ι) :
    process.finiteBackwardValue cutoff hδ tailValue (depth + 1) =
      process.finiteStageValue (cutoff - (depth + 1)) hδ
        (process.finiteBackwardValue cutoff hδ tailValue depth) :=
  rfl

/-- Integrability of the cutoff continuation propagates through every
finite backward-induction stage. -/
theorem QuittingPayoffProcess.finiteBackwardValue_integrable
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (tailValue : process.Ω → Payoff ι)
    (htail : ∀ player,
      Integrable (fun ω ↦ tailValue ω player) process.μ) :
    ∀ depth player,
      Integrable (fun ω ↦
        process.finiteBackwardValue cutoff hδ tailValue depth ω player)
        process.μ := by
  intro depth
  induction depth with
  | zero => exact htail
  | succ depth ih =>
      intro player
      exact process.finiteStageValue_integrable
        (cutoff - (depth + 1)) hδ
        (process.finiteBackwardValue cutoff hδ tailValue depth)
        ih player

/-- At an actual stage before the cutoff, the backward value is definitionally
the selected finite-stage payoff with the next backward value as its
conditional continuation. -/
theorem QuittingPayoffProcess.finiteBackwardValue_eq_stage
    (process : QuittingPayoffProcess ι) (cutoff time : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (tailValue : process.Ω → Payoff ι)
    (htime : time < cutoff) :
    process.finiteBackwardValue cutoff hδ tailValue (cutoff - time) =
      process.finiteStageValue time hδ
        (process.finiteBackwardValue cutoff hδ tailValue
          (cutoff - (time + 1))) := by
  have hdepth : cutoff - time = cutoff - (time + 1) + 1 := by omega
  rw [hdepth, process.finiteBackwardValue_succ]
  congr 1
  omega

/-- The finite-prefix root at a stage before `cutoff`; values after the cutoff
are irrelevant and are filled with sure Continue. -/
def QuittingPayoffProcess.finiteBackwardPrefix
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (tailValue : process.Ω → Payoff ι) :
    QuittingProcessProfile process :=
  fun time who ω =>
    if _htime : time < cutoff then
      process.finiteStageRoot time hδ
        (process.finiteBackwardValue cutoff hδ tailValue
          (cutoff - (time + 1))) ω who
    else PMF.pure false

/-- Before the cutoff, the finite prefix is exactly the root selected from
the current payoff table and the conditional next backward value. -/
theorem QuittingPayoffProcess.finiteBackwardPrefix_eq
    (process : QuittingPayoffProcess ι) (cutoff time : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (tailValue : process.Ω → Payoff ι)
    (htime : time < cutoff) :
    process.finiteBackwardPrefix cutoff hδ tailValue time =
      fun who ω ↦
        process.finiteStageRoot time hδ
          (process.finiteBackwardValue cutoff hδ tailValue
            (cutoff - (time + 1))) ω who := by
  funext who ω
  simp [QuittingPayoffProcess.finiteBackwardPrefix, htime]

/-- Every root in the selected finite prefix is measurable in the actual
natural filtration at that stage. -/
theorem QuittingPayoffProcess.finiteBackwardPrefix_measurable
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (tailValue : process.Ω → Payoff ι) :
    ∀ time, time < cutoff → ∀ (who : ι) (action : Bool),
      @Measurable process.Ω ℝ (process.filtration time)
        Real.measurableSpace
        (fun ω ↦
          (process.finiteBackwardPrefix cutoff hδ tailValue
            time who ω action).toReal) := by
  intro time htime who action
  rw [process.finiteBackwardPrefix_eq cutoff time hδ tailValue htime]
  exact process.finiteStageRoot_measurable_filtration time hδ
    (process.finiteBackwardValue cutoff hδ tailValue
      (cutoff - (time + 1))) who action

/-- The finite-prefix coordinates are also measurable in the ambient process
space, including the irrelevant sure-Continue filler after the cutoff. -/
theorem QuittingPayoffProcess.finiteBackwardPrefix_measurable_ambient
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (tailValue : process.Ω → Payoff ι)
    (time : ℕ) (who : ι) (action : Bool) :
    @Measurable process.Ω ℝ process.measurableSpace Real.measurableSpace
      (fun ω ↦
        (process.finiteBackwardPrefix cutoff hδ tailValue
          time who ω action).toReal) := by
  by_cases htime : time < cutoff
  · exact (process.finiteBackwardPrefix_measurable cutoff hδ tailValue
      time htime who action).mono (process.filtration_le time) le_rfl
  · simp [QuittingPayoffProcess.finiteBackwardPrefix, htime]

/-- Splicing the backward-selected finite prefix to the public-signal tail
produces an adapted process profile. -/
theorem QuittingPayoffProcess.splice_finiteBackwardPrefix_adapted
    [Nonempty ι] (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (tailValue : process.Ω → Payoff ι) :
    process.Adapted
      (process.spliceProfile cutoff
        (process.finiteBackwardPrefix cutoff hδ tailValue)
        (process.soloExitTailProfile cutoff η hη)) :=
  process.splice_soloExitTailProfile_adapted cutoff
    (process.finiteBackwardPrefix cutoff hδ tailValue) η hη
    (process.finiteBackwardPrefix_measurable cutoff hδ tailValue)

end GameTheory
