/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.PayoffProcess.PathPayoffMeasurable
import UniformEquilibrium.Quitting.PayoffProcess.TailEquilibrium

/-!
# Expected equilibrium bound for the selected tail

The pointwise `9η` comparison holds on the uniform tail-close event.  On its
complement, both prescribed and deviating path payoffs are bounded by the
integrable payoff envelope.  Integration therefore adds exactly twice the
bad-event envelope integral.
-/

noncomputable section

namespace GameTheory

open MeasureTheory StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Each selected live-spine root probability is measurable in the ambient
payoff-process space. -/
theorem QuittingPayoffProcess.measurable_soloExitTailRoots_toReal
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    (η : ℝ) (hη : 0 < η) (time : ℕ) (who : ι) (action : Bool) :
    @Measurable process.Ω ℝ process.measurableSpace Real.measurableSpace
      (fun ω =>
        (process.soloExitTailRoots cutoff η hη ω time who action).toReal) := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  unfold QuittingPayoffProcess.soloExitTailRoots quittingProfileLiveRoot
  exact (measurable_soloExitTailStepProfile_apply
    (ι := ι) η hη who time
      (quittingLiveHist (soloExitRewardCenter (ι := ι) 0) time) action).comp
        (process.payoffTable_measurable cutoff) |>.ennreal_toReal

/-- A unilateral update of the selected tail roots is measurable whenever
the deviating hazard is adapted at the corresponding global stages. -/
theorem QuittingPayoffProcess.measurable_updatedSoloExitTailRoots_toReal
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    (η : ℝ) (hη : 0 < η) (deviator : ι)
    (deviation : ℕ → process.Ω → PMF Bool)
    (hadapted : ∀ time action,
      @Measurable process.Ω ℝ (process.filtration (cutoff + time))
        Real.measurableSpace
        (fun ω => (deviation time ω action).toReal)) :
    ∀ time player action,
      @Measurable process.Ω ℝ process.measurableSpace Real.measurableSpace
        (fun ω =>
          ((quittingRootSequenceUpdate
            (process.soloExitTailRoots cutoff η hη ω) deviator
              (fun stage => deviation stage ω)) time player action).toReal) := by
  intro time player action
  by_cases hplayer : player = deviator
  · subst player
    simpa only [quittingRootSequenceUpdate, Function.update_self] using
      (hadapted time action).mono
        (process.filtration_le (cutoff + time)) le_rfl
  · simpa only [quittingRootSequenceUpdate,
      Function.update_of_ne hplayer] using
      process.measurable_soloExitTailRoots_toReal cutoff η hη
        time player action

/-- Actual varying-table payoff of the selected tail, as a random payoff
vector observed at the splice cutoff. -/
def QuittingPayoffProcess.soloExitTailValue
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    (η : ℝ) (hη : 0 < η) : process.Ω → Payoff ι :=
  fun ω who ↦ quittingVariableTailValue (process.shiftedPayoff cutoff ω)
    (process.soloExitTailRoots cutoff η hη ω) who 0

/-- The selected tail payoff is measurable in the ambient payoff-process
space. -/
theorem QuittingPayoffProcess.soloExitTailValue_measurable
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    (η : ℝ) (hη : 0 < η) (who : ι) :
    @Measurable process.Ω ℝ process.measurableSpace Real.measurableSpace
      (fun ω ↦ process.soloExitTailValue cutoff η hη ω who) := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  exact measurable_quittingVariableTailValue
    (fun time ω ↦ process.payoff (cutoff + time) ω)
    (fun time ω ↦ process.soloExitTailRoots cutoff η hη ω time)
    (fun time terminal player ↦ process.payoff_measurable
      (cutoff + time) terminal player)
    (process.measurable_soloExitTailRoots_toReal cutoff η hη) who 0

/-- The process envelope makes every coordinate of the selected tail payoff
integrable. -/
theorem QuittingPayoffProcess.soloExitTailValue_integrable
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    (η : ℝ) (hη : 0 < η) (bound : process.Ω → ℝ)
    (hbound : Integrable bound process.μ)
    (hrewardBound : ∀ time ω terminal player,
      |process.payoff time ω terminal player| ≤ bound ω)
    (who : ι) :
    Integrable (fun ω ↦ process.soloExitTailValue cutoff η hη ω who)
      process.μ := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  exact integrable_quittingVariableTailValue process.μ
    (fun time ω ↦ process.payoff (cutoff + time) ω)
    (fun time ω ↦ process.soloExitTailRoots cutoff η hη ω time)
    (fun time terminal player ↦ process.payoff_measurable
      (cutoff + time) terminal player)
    (process.measurable_soloExitTailRoots_toReal cutoff η hη)
    bound hbound (fun time ω terminal player ↦
      (hrewardBound (cutoff + time) ω terminal player).trans
        (le_abs_self (bound ω))) who 0

/-- Tail payoff after one player's adapted live-spine deviation. -/
def QuittingPayoffProcess.deviatedSoloExitTailValue
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    (η : ℝ) (hη : 0 < η) (who : ι)
    (deviation : ℕ → process.Ω → PMF Bool) : process.Ω → Payoff ι :=
  fun ω recipient ↦ quittingVariableTailValue
    (process.shiftedPayoff cutoff ω)
    (quittingRootSequenceUpdate
      (process.soloExitTailRoots cutoff η hη ω) who
      (fun time ↦ deviation time ω)) recipient 0

/-- The deviated tail payoff is measurable when the shifted deviation is
adapted at the corresponding global stages. -/
theorem QuittingPayoffProcess.deviatedSoloExitTailValue_measurable
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    (η : ℝ) (hη : 0 < η) (who : ι)
    (deviation : ℕ → process.Ω → PMF Bool)
    (hadapted : ∀ time action,
      @Measurable process.Ω ℝ (process.filtration (cutoff + time))
        Real.measurableSpace
        (fun ω ↦ (deviation time ω action).toReal)) (recipient : ι) :
    @Measurable process.Ω ℝ process.measurableSpace Real.measurableSpace
      (fun ω ↦ process.deviatedSoloExitTailValue cutoff η hη who
        deviation ω recipient) := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  exact measurable_quittingVariableTailValue
    (fun time ω ↦ process.payoff (cutoff + time) ω)
    (fun time ω ↦ quittingRootSequenceUpdate
      (process.soloExitTailRoots cutoff η hη ω) who
      (fun stage ↦ deviation stage ω) time)
    (fun time terminal player ↦ process.payoff_measurable
      (cutoff + time) terminal player)
    (process.measurable_updatedSoloExitTailRoots_toReal
      cutoff η hη who deviation hadapted) recipient 0

/-- The process envelope also integrates every coordinate of an adapted
deviated tail payoff. -/
theorem QuittingPayoffProcess.deviatedSoloExitTailValue_integrable
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    (η : ℝ) (hη : 0 < η) (bound : process.Ω → ℝ)
    (hbound : Integrable bound process.μ)
    (hrewardBound : ∀ time ω terminal player,
      |process.payoff time ω terminal player| ≤ bound ω)
    (who : ι) (deviation : ℕ → process.Ω → PMF Bool)
    (hadapted : ∀ time action,
      @Measurable process.Ω ℝ (process.filtration (cutoff + time))
        Real.measurableSpace
        (fun ω ↦ (deviation time ω action).toReal)) (recipient : ι) :
    Integrable (fun ω ↦ process.deviatedSoloExitTailValue cutoff η hη
      who deviation ω recipient) process.μ := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  exact integrable_quittingVariableTailValue process.μ
    (fun time ω ↦ process.payoff (cutoff + time) ω)
    (fun time ω ↦ quittingRootSequenceUpdate
      (process.soloExitTailRoots cutoff η hη ω) who
      (fun stage ↦ deviation stage ω) time)
    (fun time terminal player ↦ process.payoff_measurable
      (cutoff + time) terminal player)
    (process.measurable_updatedSoloExitTailRoots_toReal
      cutoff η hη who deviation hadapted)
    bound hbound (fun time ω terminal player ↦
      (hrewardBound (cutoff + time) ω terminal player).trans
        (le_abs_self (bound ω))) recipient 0

/-- Pathwise deviation bound for the selected tail.  The visible `9η` is the
`5η` selector stability plus two `2η` table-transport errors.  On the bad
tail-close event, twice the integrable envelope bounds the two path payoffs. -/
theorem QuittingPayoffProcess.ae_soloExitTail_deviation_le
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {η : ℝ} (hη : 0 < η)
    (hassumptions : process.SoloExitAssumptions)
    (bound : process.Ω → ℝ)
    (hrewardBound : ∀ time ω terminal player,
      |process.payoff time ω terminal player| ≤ bound ω)
    (who : ι) (deviation : ℕ → process.Ω → PMF Bool) :
    (∀ᵐ ω ∂process.μ,
      quittingVariableTailValue (process.shiftedPayoff cutoff ω)
          (quittingRootSequenceUpdate
            (process.soloExitTailRoots cutoff η hη ω) who
            (fun time ↦ deviation time ω)) who 0 ≤
        quittingVariableTailValue (process.shiftedPayoff cutoff ω)
          (process.soloExitTailRoots cutoff η hη ω) who 0 + 9 * η +
        2 * process.badTailEnvelope bound cutoff η ω) := by
  filter_upwards [hassumptions] with ω hlimit
  by_cases hclose : ω ∈ process.TailClose cutoff η
  · have hnash := process.soloExitTailPath_isNash_on_good
      cutoff hη ω hlimit hclose who (fun time ↦ deviation time ω)
    have hbadZero : process.badTailEnvelope bound cutoff η ω = 0 := by
      simp [QuittingPayoffProcess.badTailEnvelope, hclose]
    rw [hbadZero]
    linarith
  · have hboundNonneg : 0 ≤ bound ω := by
      let player : ι := Classical.choice inferInstance
      have hcoordinate :=
        hrewardBound 0 ω (quittingSingletonTerminal player) player
      exact (abs_nonneg _).trans hcoordinate
    have hprescribedAbs :
        |quittingVariableTailValue (process.shiftedPayoff cutoff ω)
          (process.soloExitTailRoots cutoff η hη ω) who 0| ≤ bound ω :=
      abs_quittingVariableTailValue_le
        (process.shiftedPayoff cutoff ω)
        (process.soloExitTailRoots cutoff η hη ω) who 0 hboundNonneg
        (fun offset ↦ by
          simpa only [Nat.zero_add,
            QuittingPayoffProcess.shiftedPayoff] using
            hrewardBound (cutoff + offset) ω)
    have hdeviatedAbs :
        |quittingVariableTailValue (process.shiftedPayoff cutoff ω)
          (quittingRootSequenceUpdate
            (process.soloExitTailRoots cutoff η hη ω) who
            (fun time ↦ deviation time ω)) who 0| ≤ bound ω :=
      abs_quittingVariableTailValue_le
        (process.shiftedPayoff cutoff ω)
        (quittingRootSequenceUpdate
          (process.soloExitTailRoots cutoff η hη ω) who
          (fun time ↦ deviation time ω)) who 0 hboundNonneg
        (fun offset ↦ by
          simpa only [Nat.zero_add,
            QuittingPayoffProcess.shiftedPayoff] using
            hrewardBound (cutoff + offset) ω)
    have hbadValue : process.badTailEnvelope bound cutoff η ω = |bound ω| := by
      simp [QuittingPayoffProcess.badTailEnvelope, hclose]
    rw [hbadValue, abs_of_nonneg hboundNonneg]
    have hη0 : 0 ≤ η := hη.le
    have hprescribedLower :
        -bound ω ≤ quittingVariableTailValue
          (process.shiftedPayoff cutoff ω)
          (process.soloExitTailRoots cutoff η hη ω) who 0 :=
      neg_le_of_abs_le hprescribedAbs
    have hdeviatedUpper :
        quittingVariableTailValue (process.shiftedPayoff cutoff ω)
          (quittingRootSequenceUpdate
            (process.soloExitTailRoots cutoff η hη ω) who
            (fun time ↦ deviation time ω)) who 0 ≤ bound ω :=
      (le_abs_self _).trans hdeviatedAbs
    linarith

/-- Expected deviation gain in the selected tail is at most `9η` plus twice
the bad-event envelope integral. -/
theorem QuittingPayoffProcess.integral_soloExitTail_deviation_le
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {η : ℝ} (hη : 0 < η)
    (hassumptions : process.SoloExitAssumptions)
    (bound : process.Ω → ℝ) (hbound : Integrable bound process.μ)
    (hrewardBound : ∀ time ω terminal player,
      |process.payoff time ω terminal player| ≤ bound ω)
    (who : ι) (deviation : ℕ → process.Ω → PMF Bool)
    (hadapted : ∀ time action,
      @Measurable process.Ω ℝ (process.filtration (cutoff + time))
        Real.measurableSpace
        (fun ω => (deviation time ω action).toReal)) :
    (∫ ω, quittingVariableTailValue (process.shiftedPayoff cutoff ω)
          (process.soloExitTailRoots cutoff η hη ω) who 0 ∂process.μ) +
        9 * η +
        2 * (∫ ω, process.badTailEnvelope bound cutoff η ω ∂process.μ) ≥
      ∫ ω, quittingVariableTailValue (process.shiftedPayoff cutoff ω)
        (quittingRootSequenceUpdate
          (process.soloExitTailRoots cutoff η hη ω) who
          (fun time => deviation time ω)) who 0 ∂process.μ := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  letI : IsProbabilityMeasure process.μ := process.probability
  let prescribed : process.Ω → ℝ := fun ω =>
    quittingVariableTailValue (process.shiftedPayoff cutoff ω)
      (process.soloExitTailRoots cutoff η hη ω) who 0
  let deviated : process.Ω → ℝ := fun ω =>
    quittingVariableTailValue (process.shiftedPayoff cutoff ω)
      (quittingRootSequenceUpdate
        (process.soloExitTailRoots cutoff η hη ω) who
        (fun time => deviation time ω)) who 0
  let bad : process.Ω → ℝ := process.badTailEnvelope bound cutoff η
  have hrewardAbs : ∀ time ω terminal player,
      |process.payoff time ω terminal player| ≤ |bound ω| := by
    intro time ω terminal player
    exact (hrewardBound time ω terminal player).trans (le_abs_self _)
  have hprescribed : Integrable prescribed process.μ :=
    integrable_quittingVariableTailValue process.μ
      (fun time ω => process.payoff (cutoff + time) ω)
      (fun time ω => process.soloExitTailRoots cutoff η hη ω time)
      (fun time terminal player => process.payoff_measurable
        (cutoff + time) terminal player)
      (process.measurable_soloExitTailRoots_toReal cutoff η hη)
      bound hbound (fun time ω terminal player =>
        hrewardAbs (cutoff + time) ω terminal player) who 0
  have hdeviated : Integrable deviated process.μ :=
    integrable_quittingVariableTailValue process.μ
      (fun time ω => process.payoff (cutoff + time) ω)
      (fun time ω => quittingRootSequenceUpdate
        (process.soloExitTailRoots cutoff η hη ω) who
        (fun stage => deviation stage ω) time)
      (fun time terminal player => process.payoff_measurable
        (cutoff + time) terminal player)
      (process.measurable_updatedSoloExitTailRoots_toReal
        cutoff η hη who deviation hadapted)
      bound hbound (fun time ω terminal player =>
        hrewardAbs (cutoff + time) ω terminal player) who 0
  have hbad : Integrable bad process.μ := by
    exact hbound.abs.indicator
      (process.measurableSet_tailClose cutoff η).compl
  let upper : process.Ω → ℝ := fun ω => prescribed ω + 9 * η + 2 * bad ω
  have hupper : Integrable upper process.μ := by
    have hconstant : Integrable (fun _ : process.Ω => 9 * η) process.μ :=
      integrable_const _
    have hscaled : Integrable (fun ω => 2 * bad ω) process.μ :=
      hbad.const_mul 2
    exact (hprescribed.add hconstant).add hscaled
  have hpointwise : deviated ≤ᵐ[process.μ] upper := by
    filter_upwards [process.ae_soloExitTail_deviation_le cutoff hη
      hassumptions bound hrewardBound who deviation] with ω hω
    exact hω
  have hintegral := integral_mono_ae hdeviated hupper hpointwise
  have hconstant : Integrable (fun _ : process.Ω => 9 * η) process.μ :=
    integrable_const _
  have hscaled : Integrable (fun ω => 2 * bad ω) process.μ :=
    hbad.const_mul 2
  have hupperIntegral : (∫ ω, upper ω ∂process.μ) =
      (∫ ω, prescribed ω ∂process.μ) + 9 * η +
        2 * (∫ ω, bad ω ∂process.μ) := by
    calc
      (∫ ω, upper ω ∂process.μ) =
          (∫ ω, prescribed ω + 9 * η ∂process.μ) +
            ∫ ω, 2 * bad ω ∂process.μ := by
        dsimp only [upper]
        simpa only [Pi.add_apply] using
          integral_add (hprescribed.add hconstant) hscaled
      _ = ((∫ ω, prescribed ω ∂process.μ) +
            ∫ _ : process.Ω, 9 * η ∂process.μ) +
            ∫ ω, 2 * bad ω ∂process.μ := by
        rw [show (∫ ω, prescribed ω + 9 * η ∂process.μ) =
          (∫ ω, prescribed ω ∂process.μ) +
            ∫ _ : process.Ω, 9 * η ∂process.μ by
          simpa only [Pi.add_apply] using integral_add hprescribed hconstant]
      _ = _ := by
        rw [integral_const, integral_const_mul]
        simp
  rw [hupperIntegral] at hintegral
  exact hintegral

end GameTheory
