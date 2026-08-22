/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import UniformEquilibrium.Quitting.PayoffProcess.Basic
import UniformEquilibrium.Quitting.PayoffProcess.FiniteStageSelector

/-!
# One backward-induction stage for a quitting payoff process

Given an integrable next-stage value, conditional expectation projects that
value into the current natural filtration.  The measurable finite-game
selector is then applied to the current quitting table with precisely that
conditional continuation payoff.  Thus the selected root is adapted to the
actual public filtration, rather than merely measurable in an ambient sample
space.
-/

noncomputable section

namespace GameTheory

open MeasureTheory StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Conditional expected next-stage payoff, projected onto the natural
filtration available at `time`. -/
def QuittingPayoffProcess.conditionalContinuation
    (process : QuittingPayoffProcess ι) (time : ℕ)
    (nextValue : process.Ω → Payoff ι) : process.Ω → Payoff ι := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  exact fun ω who ↦
    process.μ[fun sample ↦ nextValue sample who |
      process.filtration time] ω

/-- Conditional continuation coordinates are measurable in the actual
natural filtration at the current stage. -/
theorem QuittingPayoffProcess.conditionalContinuation_measurable_filtration
    (process : QuittingPayoffProcess ι) (time : ℕ)
    (nextValue : process.Ω → Payoff ι) (who : ι) :
    @Measurable process.Ω ℝ (process.filtration time)
      Real.measurableSpace
      (fun ω ↦ process.conditionalContinuation time nextValue ω who) := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  exact stronglyMeasurable_condExp.measurable

/-- Conditional continuation remains integrable whenever its input
coordinate is integrable. -/
theorem QuittingPayoffProcess.conditionalContinuation_integrable
    (process : QuittingPayoffProcess ι) (time : ℕ)
    (nextValue : process.Ω → Payoff ι) (who : ι) :
    Integrable
      (fun ω ↦ process.conditionalContinuation time nextValue ω who)
      process.μ := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  exact integrable_condExp

/-- The random finite-game utility table used at one backward-induction
stage.  Its all-Continue payoff is the conditional expected next value. -/
def QuittingPayoffProcess.finiteStageUtility
    (process : QuittingPayoffProcess ι) (time : ℕ)
    (nextValue : process.Ω → Payoff ι) (ω : process.Ω) :
    (ι → Bool) → ι → ℝ :=
  quittingStageUtility (process.payoff time ω)
    (process.conditionalContinuation time nextValue ω)

/-- The finite game presented to the selector is measurable in the current
natural filtration, including its conditional continuation branch. -/
theorem QuittingPayoffProcess.finiteStageUtility_measurable_filtration
    (process : QuittingPayoffProcess ι) (time : ℕ)
    (nextValue : process.Ω → Payoff ι) :
    @Measurable process.Ω ((ι → Bool) → ι → ℝ)
      (process.filtration time) inferInstance
      (process.finiteStageUtility time nextValue) := by
  exact measurable_quittingStageUtility (process.payoff time)
    (process.conditionalContinuation time nextValue)
    (process.payoff_measurable_filtration time)
    (process.conditionalContinuation_measurable_filtration time nextValue)

/-- The root selected at one finite backward-induction stage. -/
def QuittingPayoffProcess.finiteStageRoot
    (process : QuittingPayoffProcess ι) (time : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (nextValue : process.Ω → Payoff ι)
    (ω : process.Ω) : ι → PMF Bool :=
  quittingStageRootSelector hδ (process.finiteStageUtility time nextValue ω)

/-- The selected root is measurable in the actual natural filtration at its
stage. -/
theorem QuittingPayoffProcess.finiteStageRoot_measurable_filtration
    (process : QuittingPayoffProcess ι) (time : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (nextValue : process.Ω → Payoff ι)
    (who : ι) (action : Bool) :
    @Measurable process.Ω ℝ (process.filtration time)
      Real.measurableSpace
      (fun ω ↦
        (process.finiteStageRoot time hδ nextValue ω who action).toReal) :=
  measurable_quittingStageRootSelector_comp hδ
    (process.finiteStageUtility time nextValue)
    (process.finiteStageUtility_measurable_filtration time nextValue)
    who action

/-- Bellman value of the selected finite-stage root. -/
def QuittingPayoffProcess.finiteStageValue
    (process : QuittingPayoffProcess ι) (time : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (nextValue : process.Ω → Payoff ι)
    (ω : process.Ω) : Payoff ι :=
  fun who ↦ quittingRootExpectedPayoff (process.payoff time ω)
    (process.conditionalContinuation time nextValue ω)
    (process.finiteStageRoot time hδ nextValue ω) who

/-- The selected Bellman value is measurable in the current natural
filtration. -/
theorem QuittingPayoffProcess.finiteStageValue_measurable_filtration
    (process : QuittingPayoffProcess ι) (time : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (nextValue : process.Ω → Payoff ι)
    (who : ι) :
    @Measurable process.Ω ℝ (process.filtration time)
      Real.measurableSpace
      (fun ω ↦ process.finiteStageValue time hδ nextValue ω who) := by
  letI : MeasurableSpace process.Ω := process.filtration time
  exact measurable_quittingRootExpectedPayoff
    (process.payoff time)
    (process.conditionalContinuation time nextValue)
    (process.finiteStageRoot time hδ nextValue)
    (process.payoff_measurable_filtration time)
    (process.conditionalContinuation_measurable_filtration time nextValue)
    (process.finiteStageRoot_measurable_filtration time hδ nextValue)
    who

/-- The abstract expected utility evaluated by the finite-game selector is
exactly the quitting-process Bellman payoff with conditional continuation. -/
theorem QuittingPayoffProcess.expectedUtility_finiteStage_eq_value
    (process : QuittingPayoffProcess ι) (time : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (nextValue : process.Ω → Payoff ι)
    (ω : process.Ω) (who : ι) :
    expectedUtility (process.finiteStageUtility time nextValue ω) who
        ((quittingBinaryForm ι).mixed.play
          (fun player ↦
            _root_.Math.Probability.finDistOfPMF
              (process.finiteStageRoot time hδ nextValue ω player))) =
      process.finiteStageValue time hδ nextValue ω who := by
  rw [expectedUtility_quittingBinaryForm_eq]
  simp only [_root_.Math.Probability.toPMF_finDistOfPMF]
  rfl

/-- Pointwise one-stage incentive bound for an arbitrary randomized action
replacement, stated in the process continuation semantics. -/
theorem QuittingPayoffProcess.finiteStage_deviation_le
    (process : QuittingPayoffProcess ι) (time : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (nextValue : process.Ω → Payoff ι)
    (ω : process.Ω) (who : ι) (replacement : PMF Bool) :
    quittingRootExpectedPayoff (process.payoff time ω)
        (process.conditionalContinuation time nextValue ω)
        (Function.update
          (process.finiteStageRoot time hδ nextValue ω) who replacement)
        who ≤
      process.finiteStageValue time hδ nextValue ω who + δ := by
  exact quittingStageRootSelector_deviation_le hδ
    (process.payoff time ω)
    (process.conditionalContinuation time nextValue ω) who replacement

/-- Integrability propagates one step backward through conditional
expectation and the finite-game selector. -/
theorem QuittingPayoffProcess.finiteStageValue_integrable
    (process : QuittingPayoffProcess ι) (time : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (nextValue : process.Ω → Payoff ι)
    (_hnext : ∀ player, Integrable (fun ω ↦ nextValue ω player) process.μ)
    (who : ι) :
    Integrable
      (fun ω ↦ process.finiteStageValue time hδ nextValue ω who)
      process.μ := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  obtain ⟨bound, hbound, hreward⟩ := process.integrableEnvelope
  let envelope : process.Ω → ℝ := fun ω ↦
    bound ω + ∑ player,
      |process.conditionalContinuation time nextValue ω player|
  have henvelope : Integrable envelope process.μ := by
    exact hbound.add (integrable_finsetSum Finset.univ fun player _ ↦
      (process.conditionalContinuation_integrable time nextValue player).abs)
  apply Integrable.mono' henvelope
  · exact (process.finiteStageValue_measurable_filtration
      time hδ nextValue who).mono (process.filtration_le time) le_rfl
      |>.aestronglyMeasurable
  · filter_upwards with ω
    exact (abs_quittingRootExpectedPayoff_le_envelopeSum
      (process.payoff time ω)
      (process.conditionalContinuation time nextValue ω)
      (process.finiteStageRoot time hδ nextValue ω) who (bound ω)
      (fun terminal player ↦ hreward time ω terminal player))

end GameTheory
