/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import UniformEquilibrium.Quitting.PayoffProcess.Basic

/-!
# Uniform tail approximation outside an integrably small event

Almost-sure convergence of a finite payoff table is eventually uniform over
its coordinates.  An integrable envelope upgrades the exceptional-event
probability statement to the weighted estimate actually needed in the
equilibrium proof: the envelope integral on the bad tail tends to zero.
-/

noncomputable section

namespace GameTheory

open Filter MeasureTheory Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- From `cutoff` onward, every payoff table is uniformly within `ε` of the
limit table. -/
def QuittingPayoffProcess.TailClose
    (process : QuittingPayoffProcess ι) (cutoff : ℕ) (ε : ℝ) :
    Set process.Ω :=
  {ω | ∀ time, cutoff ≤ time →
    dist (process.payoff time ω) (process.limit ω) < ε}

/-- Tail closeness is monotone in the cutoff. -/
theorem QuittingPayoffProcess.tailClose_mono_cutoff
    (process : QuittingPayoffProcess ι) {first second : ℕ}
    (hcutoff : first ≤ second) {ε : ℝ} :
    process.TailClose first ε ⊆ process.TailClose second ε := by
  intro ω hω time htime
  exact hω time (hcutoff.trans htime)

/-- The uniform tail-close event is measurable. -/
theorem QuittingPayoffProcess.measurableSet_tailClose
    (process : QuittingPayoffProcess ι) (cutoff : ℕ) (ε : ℝ) :
    MeasurableSet[process.measurableSpace] (process.TailClose cutoff ε) := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  have hdistance (time : ℕ) : Measurable fun ω =>
      dist (process.payoff time ω) (process.limit ω) :=
    (process.payoffTable_measurable time).dist process.limitTable_measurable
  have hstage (time : ℕ) : MeasurableSet
      {ω | cutoff ≤ time →
        dist (process.payoff time ω) (process.limit ω) < ε} := by
    by_cases htime : cutoff ≤ time
    · simpa only [htime, true_implies] using
        measurableSet_lt (hdistance time) measurable_const
    · simp only [htime, false_implies, setOf_true, MeasurableSet.univ]
  have hintersection : MeasurableSet (⋂ time, {ω | cutoff ≤ time →
      dist (process.payoff time ω) (process.limit ω) < ε}) :=
    MeasurableSet.iInter hstage
  have heq : process.TailClose cutoff ε =
      ⋂ time, {ω | cutoff ≤ time →
        dist (process.payoff time ω) (process.limit ω) < ε} := by
    ext ω
    simp only [QuittingPayoffProcess.TailClose, mem_setOf_eq, mem_iInter]
  rw [heq]
  exact hintersection

/-- Almost every sample path is uniformly close to its limit after some
cutoff. -/
theorem QuittingPayoffProcess.ae_exists_tailClose
    (process : QuittingPayoffProcess ι) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂process.μ, ∃ cutoff, ω ∈ process.TailClose cutoff ε := by
  filter_upwards [process.ae_tendsto_payoffTable] with ω hω
  exact (Metric.tendsto_atTop.mp hω ε hε)

/-- The envelope restricted to the bad tail event. -/
def QuittingPayoffProcess.badTailEnvelope
    (process : QuittingPayoffProcess ι) (bound : process.Ω → ℝ)
    (cutoff : ℕ) (ε : ℝ) : process.Ω → ℝ :=
  (process.TailClose cutoff ε)ᶜ.indicator fun ω => |bound ω|

/-- The bad-tail envelope integral tends to zero. -/
theorem QuittingPayoffProcess.tendsto_integral_badTailEnvelope
    (process : QuittingPayoffProcess ι) (bound : process.Ω → ℝ)
    (hbound : Integrable bound process.μ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun cutoff =>
      ∫ ω, process.badTailEnvelope bound cutoff ε ω ∂process.μ)
      atTop (nhds 0) := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  let bad : ℕ → process.Ω → ℝ := fun cutoff =>
    process.badTailEnvelope bound cutoff ε
  have hmeasurable (cutoff : ℕ) : AEStronglyMeasurable (bad cutoff) process.μ := by
    exact hbound.abs.aestronglyMeasurable.indicator
      (process.measurableSet_tailClose cutoff ε).compl
  have hdominated (cutoff : ℕ) : ∀ᵐ ω ∂process.μ,
      ‖bad cutoff ω‖ ≤ |bound ω| := by
    filter_upwards with ω
    by_cases hω : ω ∈ process.TailClose cutoff ε
    · simp [bad, QuittingPayoffProcess.badTailEnvelope, hω]
    · simp [bad, QuittingPayoffProcess.badTailEnvelope, hω]
  have hpointwise : ∀ᵐ ω ∂process.μ,
      Tendsto (fun cutoff => bad cutoff ω) atTop (nhds 0) := by
    filter_upwards [process.ae_exists_tailClose hε] with ω hω
    obtain ⟨cutoff, hcutoff⟩ := hω
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop cutoff] with later hlater
    have hlaterClose := process.tailClose_mono_cutoff hlater hcutoff
    simp [bad, QuittingPayoffProcess.badTailEnvelope, hlaterClose]
  simpa only [bad, integral_zero] using
    tendsto_integral_of_dominated_convergence (fun ω => |bound ω|)
      hmeasurable hbound.abs hdominated hpointwise

/-- For every positive budget, some deterministic cutoff makes the envelope
integral on the bad tail smaller than that budget. -/
theorem QuittingPayoffProcess.exists_integral_badTailEnvelope_lt
    (process : QuittingPayoffProcess ι) (bound : process.Ω → ℝ)
    (hbound : Integrable bound process.μ)
    {tableError budget : ℝ} (htableError : 0 < tableError)
    (hbudget : 0 < budget) :
    ∃ cutoff,
      ∫ ω, process.badTailEnvelope bound cutoff tableError ω ∂process.μ <
        budget := by
  have htendsto := process.tendsto_integral_badTailEnvelope
    bound hbound htableError
  rw [Metric.tendsto_atTop] at htendsto
  obtain ⟨cutoff, hcutoff⟩ := htendsto budget hbudget
  refine ⟨cutoff, ?_⟩
  have := hcutoff cutoff le_rfl
  rw [Real.dist_eq, sub_zero] at this
  exact lt_of_le_of_lt (le_abs_self _) this

end GameTheory
