/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.PayoffProcess.ExpectedTailEquilibrium
import UniformEquilibrium.Quitting.PayoffProcess.FinitePrefixAccounting

/-!
# Deviation accounting through the finite prefix

A pathwise tail error is first conditioned on the cutoff history.  Backward
induction then conditions the accumulated error at every earlier stage and
adds the one-stage selector slack.  Its expectation is therefore exactly the
tail-error expectation plus one selector slack per finite-prefix stage.
-/

noncomputable section

namespace GameTheory

open MeasureTheory StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Scalar conditional expectation in the payoff process's natural
filtration. -/
def QuittingPayoffProcess.conditionalError
    (process : QuittingPayoffProcess ι) (time : ℕ)
    (error : process.Ω → ℝ) : process.Ω → ℝ := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  exact process.μ[error | process.filtration time]

/-- Backward error budget: condition at the relevant stage and add one
finite-game selector slack. -/
def QuittingPayoffProcess.finiteBackwardError
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    (δ : ℝ) (tailError : process.Ω → ℝ) : ℕ → process.Ω → ℝ
  | 0 => process.conditionalError cutoff tailError
  | depth + 1 => fun ω ↦
      process.conditionalError (cutoff - (depth + 1))
        (process.finiteBackwardError cutoff δ tailError depth) ω + δ

@[simp]
theorem QuittingPayoffProcess.finiteBackwardError_zero
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    (δ : ℝ) (tailError : process.Ω → ℝ) :
    process.finiteBackwardError cutoff δ tailError 0 =
      process.conditionalError cutoff tailError :=
  rfl

@[simp]
theorem QuittingPayoffProcess.finiteBackwardError_succ
    (process : QuittingPayoffProcess ι) (cutoff depth : ℕ)
    (δ : ℝ) (tailError : process.Ω → ℝ) :
    process.finiteBackwardError cutoff δ tailError (depth + 1) =
      fun ω ↦ process.conditionalError (cutoff - (depth + 1))
        (process.finiteBackwardError cutoff δ tailError depth) ω + δ :=
  rfl

/-- Conditional errors are measurable in the filtration on which they are
conditioned. -/
theorem QuittingPayoffProcess.conditionalError_measurable
    (process : QuittingPayoffProcess ι) (time : ℕ)
    (error : process.Ω → ℝ) :
    @Measurable process.Ω ℝ (process.filtration time) Real.measurableSpace
      (process.conditionalError time error) := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  exact stronglyMeasurable_condExp.measurable

/-- Conditional errors are integrable. -/
theorem QuittingPayoffProcess.conditionalError_integrable
    (process : QuittingPayoffProcess ι) (time : ℕ)
    (error : process.Ω → ℝ) :
    Integrable (process.conditionalError time error) process.μ := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  exact integrable_condExp

/-- Every finite backward error is integrable. -/
theorem QuittingPayoffProcess.finiteBackwardError_integrable
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    (δ : ℝ) (tailError : process.Ω → ℝ) :
    ∀ depth,
      Integrable (process.finiteBackwardError cutoff δ tailError depth)
        process.μ := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  letI : IsProbabilityMeasure process.μ := process.probability
  intro depth
  induction depth with
  | zero => exact process.conditionalError_integrable cutoff tailError
  | succ depth _ =>
      exact (process.conditionalError_integrable
        (cutoff - (depth + 1))
        (process.finiteBackwardError cutoff δ tailError depth)).add
          (integrable_const δ)

/-- A nonnegative tail error remains nonnegative through the backward error
recursion when the selector slack is nonnegative. -/
theorem QuittingPayoffProcess.finiteBackwardError_nonneg
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) (tailError : process.Ω → ℝ)
    (htail : 0 ≤ᵐ[process.μ] tailError) :
    ∀ depth, 0 ≤ᵐ[process.μ]
      process.finiteBackwardError cutoff δ tailError depth := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  intro depth
  induction depth with
  | zero => exact condExp_nonneg htail
  | succ depth ih =>
      filter_upwards [condExp_nonneg ih] with ω hω
      exact add_nonneg hω hδ

/-- Expected backward error is the expected tail error plus `depth * δ`. -/
theorem QuittingPayoffProcess.integral_finiteBackwardError
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    (δ : ℝ) (tailError : process.Ω → ℝ) :
    ∀ depth,
      (∫ ω, process.finiteBackwardError cutoff δ tailError depth ω
          ∂process.μ) =
        (∫ ω, tailError ω ∂process.μ) + depth * δ := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  letI : IsProbabilityMeasure process.μ := process.probability
  intro depth
  induction depth with
  | zero =>
      change (∫ ω, process.μ[tailError | process.filtration cutoff] ω
        ∂process.μ) = _
      simpa using integral_condExp (process.filtration_le cutoff)
  | succ depth ih =>
      rw [process.finiteBackwardError_succ]
      have hconditional := process.conditionalError_integrable
        (cutoff - (depth + 1))
        (process.finiteBackwardError cutoff δ tailError depth)
      rw [show (∫ ω, process.conditionalError (cutoff - (depth + 1))
          (process.finiteBackwardError cutoff δ tailError depth) ω + δ
          ∂process.μ) =
          (∫ ω, process.conditionalError (cutoff - (depth + 1))
            (process.finiteBackwardError cutoff δ tailError depth) ω
            ∂process.μ) + ∫ _ : process.Ω, δ ∂process.μ by
        simpa only [Pi.add_apply] using
          integral_add hconditional (integrable_const δ)]
      have hconditionalIntegral :
          (∫ ω, process.conditionalError (cutoff - (depth + 1))
            (process.finiteBackwardError cutoff δ tailError depth) ω
            ∂process.μ) =
          ∫ ω, process.finiteBackwardError cutoff δ tailError depth ω
            ∂process.μ := by
        change (∫ ω, process.μ[
          process.finiteBackwardError cutoff δ tailError depth |
            process.filtration (cutoff - (depth + 1))] ω ∂process.μ) = _
        exact integral_condExp
          (process.filtration_le (cutoff - (depth + 1)))
      rw [hconditionalIntegral, integral_const, ih]
      simp only [probReal_univ]
      push_cast
      ring

/-- Root sequence obtained by replacing one player's finite-prefix action law
at every stage. -/
def QuittingPayoffProcess.finiteBackwardDeviationRoots
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (tailValue : process.Ω → Payoff ι)
    (who : ι) (deviation : ℕ → process.Ω → PMF Bool) :
    ℕ → process.Ω → ι → PMF Bool :=
  fun time ω ↦ Function.update
    (process.finiteBackwardRoots cutoff hδ tailValue time ω)
    who (deviation time ω)

/-- The unilateral finite-prefix update is measurable in the actual stage
filtration when the deviating action law is adapted. -/
theorem QuittingPayoffProcess.finiteBackwardDeviationRoots_measurable
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (tailValue : process.Ω → Payoff ι)
    (who : ι) (deviation : ℕ → process.Ω → PMF Bool)
    (hdeviation : ∀ time action,
      @Measurable process.Ω ℝ (process.filtration time)
        Real.measurableSpace
        (fun ω ↦ (deviation time ω action).toReal)) :
    ∀ time player action,
      @Measurable process.Ω ℝ (process.filtration time)
        Real.measurableSpace
        (fun ω ↦ (process.finiteBackwardDeviationRoots cutoff hδ
          tailValue who deviation time ω player action).toReal) := by
  intro time player action
  by_cases hplayer : player = who
  · subst player
    simpa [QuittingPayoffProcess.finiteBackwardDeviationRoots] using
      hdeviation time action
  · by_cases htime : time < cutoff
    · simp only [QuittingPayoffProcess.finiteBackwardDeviationRoots,
          Function.update_of_ne hplayer]
      change @Measurable process.Ω ℝ (process.filtration time)
          Real.measurableSpace (fun ω ↦
            (process.finiteBackwardPrefix cutoff hδ
              (process.cutoffConditionalValue cutoff tailValue)
              time player ω action).toReal)
      exact process.finiteBackwardPrefix_measurable cutoff hδ
        (process.cutoffConditionalValue cutoff tailValue)
        time htime player action
    · simp [QuittingPayoffProcess.finiteBackwardDeviationRoots,
        QuittingPayoffProcess.finiteBackwardRoots,
        QuittingPayoffProcess.finiteBackwardPrefix,
        Function.update_of_ne hplayer, htime]

/-- A pathwise tail-deviation bound propagates through the measurable finite
prefix.  At distance `depth` from the cutoff, the conditional deviating value
is bounded by the prescribed backward value plus the conditioned accumulated
error. -/
theorem QuittingPayoffProcess.condExp_finiteContinuationValue_deviation_le
    [Nonempty ι] (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (tailValue : process.Ω → Payoff ι)
    (htail : ∀ player,
      Integrable (fun ω ↦ tailValue ω player) process.μ)
    (who : ι) (deviation : ℕ → process.Ω → PMF Bool)
    (hdeviation : ∀ time action,
      @Measurable process.Ω ℝ (process.filtration time)
        Real.measurableSpace
        (fun ω ↦ (deviation time ω action).toReal))
    (deviatedTail : process.Ω → Payoff ι)
    (hdeviatedTailMeasurable : ∀ player,
      @Measurable process.Ω ℝ process.measurableSpace Real.measurableSpace
        (fun ω ↦ deviatedTail ω player))
    (hdeviatedTail : ∀ player,
      Integrable (fun ω ↦ deviatedTail ω player) process.μ)
    (tailError : process.Ω → ℝ) (htailError : Integrable tailError process.μ)
    (htailErrorNonneg : 0 ≤ᵐ[process.μ] tailError)
    (htailDeviation : (∀ᵐ ω ∂process.μ,
      deviatedTail ω who ≤ tailValue ω who + tailError ω)) :
    ∀ start depth, start + depth = cutoff →
      process.μ[fun ω ↦ process.finiteContinuationValue
        (process.finiteBackwardDeviationRoots cutoff hδ tailValue
          who deviation) deviatedTail start depth ω who |
        process.filtration start] ≤ᵐ[process.μ]
      fun ω ↦ process.finiteBackwardValue cutoff hδ
          (process.cutoffConditionalValue cutoff tailValue) depth ω who +
        process.finiteBackwardError cutoff δ tailError depth ω := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  letI : IsProbabilityMeasure process.μ := process.probability
  intro start depth
  induction depth generalizing start with
  | zero =>
      intro hstart
      have hstartEq : start = cutoff := by omega
      subst start
      have hsum : Integrable (fun ω ↦ tailValue ω who + tailError ω)
          process.μ := (htail who).add htailError
      have hmono := condExp_mono (m := process.filtration cutoff)
        (hdeviatedTail who) hsum htailDeviation
      have hadd := condExp_add (htail who) htailError
        (process.filtration cutoff)
      filter_upwards [hmono, hadd] with ω hmonoω haddω
      change process.μ[fun sample ↦ tailValue sample who + tailError sample |
          process.filtration cutoff] ω = _ at haddω
      change process.μ[fun sample ↦ deviatedTail sample who |
          process.filtration cutoff] ω ≤ _
      rw [haddω] at hmonoω
      exact hmonoω
  | succ depth ih =>
      intro hstart
      have hstartLt : start < cutoff := by omega
      have hnextSum : start + 1 + depth = cutoff := by omega
      let terminal : process.Ω → Payoff ι :=
        process.cutoffConditionalValue cutoff tailValue
      let prescribedRoots : ℕ → process.Ω → ι → PMF Bool :=
        process.finiteBackwardRoots cutoff hδ tailValue
      let deviatedRoots : ℕ → process.Ω → ι → PMF Bool :=
        process.finiteBackwardDeviationRoots cutoff hδ tailValue
          who deviation
      let actualNext : process.Ω → Payoff ι := fun ω ↦
        process.finiteContinuationValue deviatedRoots deviatedTail
          (start + 1) depth ω
      let backwardNext : process.Ω → Payoff ι :=
        process.finiteBackwardValue cutoff hδ terminal depth
      let errorNext : process.Ω → ℝ :=
        process.finiteBackwardError cutoff δ tailError depth
      have hdeviatedRootsFiltration :=
        process.finiteBackwardDeviationRoots_measurable cutoff hδ
          tailValue who deviation hdeviation
      have hdeviatedRootsAmbient : ∀ time player action,
          @Measurable process.Ω ℝ process.measurableSpace
            Real.measurableSpace
            (fun ω ↦ (deviatedRoots time ω player action).toReal) := by
        intro time player action
        exact (hdeviatedRootsFiltration time player action).mono
          (process.filtration_le time) le_rfl
      have hactualNext : ∀ player,
          Integrable (fun ω ↦ actualNext ω player) process.μ := by
        intro player
        exact process.finiteContinuationValue_integrable deviatedRoots
          hdeviatedRootsAmbient deviatedTail hdeviatedTailMeasurable
          hdeviatedTail (start + 1) depth player
      have hbackwardNext : ∀ player,
          Integrable (fun ω ↦ backwardNext ω player) process.μ := by
        intro player
        exact process.finiteBackwardValue_integrable cutoff hδ terminal
          (fun recipient ↦
            process.conditionalContinuation_integrable cutoff
              tailValue recipient) depth player
      have herrorNext : Integrable errorNext process.μ :=
        process.finiteBackwardError_integrable cutoff δ tailError depth
      have herrorNextNonneg : 0 ≤ᵐ[process.μ] errorNext :=
        process.finiteBackwardError_nonneg cutoff hδ.le tailError
          htailErrorNonneg depth
      have ihNext := ih (start + 1) hnextSum
      have hmono := condExp_mono (m := process.filtration start)
        integrable_condExp
        ((hbackwardNext who).add herrorNext) ihNext
      have htower :
          process.μ[process.μ[fun ω ↦ actualNext ω who |
              process.filtration (start + 1)] |
              process.filtration start] =ᵐ[process.μ]
            process.μ[fun ω ↦ actualNext ω who |
              process.filtration start] :=
        condExp_condExp_of_le
          (process.filtration_mono (Nat.le_succ start))
          (process.filtration_le (start + 1))
      have hadd := condExp_add (hbackwardNext who) herrorNext
        (process.filtration start)
      have hcontinuation :
          process.μ[fun ω ↦ actualNext ω who |
              process.filtration start] ≤ᵐ[process.μ]
            fun ω ↦ process.conditionalContinuation start
                backwardNext ω who +
              process.conditionalError start errorNext ω := by
        filter_upwards [hmono, htower, hadd] with ω hmonoω htowerω haddω
        rw [← htowerω]
        rw [haddω] at hmonoω
        exact hmonoω
      have herrorConditionalNonneg :
          0 ≤ᵐ[process.μ] process.conditionalError start errorNext :=
        condExp_nonneg herrorNextNonneg
      have hstep := process.condExp_rootExpected_eq start
        (deviatedRoots start)
        (hdeviatedRootsFiltration start) actualNext hactualNext who
      have hremaining : cutoff - (start + 1) = depth := by omega
      have hprescribedRoot : prescribedRoots start =
          process.finiteStageRoot start hδ backwardNext := by
        funext ω player
        change process.finiteBackwardPrefix cutoff hδ terminal
            start player ω = _
        rw [process.finiteBackwardPrefix_eq cutoff start hδ terminal
          hstartLt]
        change process.finiteStageRoot start hδ
            (process.finiteBackwardValue cutoff hδ terminal
              (cutoff - (start + 1))) ω player = _
        rw [hremaining]
      filter_upwards [hstep, hcontinuation, herrorConditionalNonneg] with
          ω hstepω hcontinuationω herrorNonnegω
      change process.μ[fun sample ↦ quittingRootExpectedPayoff
          (process.payoff start sample) (actualNext sample)
          (deviatedRoots start sample) who | process.filtration start] ω ≤ _
      rw [hstepω]
      have htransport := quittingRootExpectedPayoff_continuation_le_add
        (process.payoff start ω)
        (process.conditionalContinuation start actualNext ω)
        (process.conditionalContinuation start backwardNext ω)
        (deviatedRoots start ω) who herrorNonnegω hcontinuationω
      have hrootUpdate : deviatedRoots start ω = Function.update
          (process.finiteStageRoot start hδ backwardNext ω) who
          (deviation start ω) := by
        rw [show deviatedRoots start ω = Function.update
          (prescribedRoots start ω) who (deviation start ω) from rfl,
          hprescribedRoot]
      rw [hrootUpdate] at htransport
      rw [hrootUpdate]
      have hselector := process.finiteStage_deviation_le start hδ
        backwardNext ω who (deviation start ω)
      have hstageIndex : cutoff - (depth + 1) = start := by omega
      rw [process.finiteBackwardError_succ]
      simp only [process.finiteBackwardValue_succ]
      rw [hstageIndex]
      linarith

/-- Integrated finite-prefix deviation bound.  The tail error is paid once,
and the measurable finite-game selector contributes exactly `cutoff * δ`. -/
theorem QuittingPayoffProcess.integral_finiteContinuationValue_deviation_le
    [Nonempty ι] (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (tailValue : process.Ω → Payoff ι)
    (htail : ∀ player,
      Integrable (fun ω ↦ tailValue ω player) process.μ)
    (who : ι) (deviation : ℕ → process.Ω → PMF Bool)
    (hdeviation : ∀ time action,
      @Measurable process.Ω ℝ (process.filtration time)
        Real.measurableSpace
        (fun ω ↦ (deviation time ω action).toReal))
    (deviatedTail : process.Ω → Payoff ι)
    (hdeviatedTailMeasurable : ∀ player,
      @Measurable process.Ω ℝ process.measurableSpace Real.measurableSpace
        (fun ω ↦ deviatedTail ω player))
    (hdeviatedTail : ∀ player,
      Integrable (fun ω ↦ deviatedTail ω player) process.μ)
    (tailError : process.Ω → ℝ) (htailError : Integrable tailError process.μ)
    (htailErrorNonneg : 0 ≤ᵐ[process.μ] tailError)
    (htailDeviation : (∀ᵐ ω ∂process.μ,
      deviatedTail ω who ≤ tailValue ω who + tailError ω)) :
    (∫ ω, process.finiteContinuationValue
        (process.finiteBackwardDeviationRoots cutoff hδ tailValue
          who deviation) deviatedTail 0 cutoff ω who ∂process.μ) ≤
      (∫ ω, process.finiteBackwardValue cutoff hδ
        (process.cutoffConditionalValue cutoff tailValue) cutoff ω who
        ∂process.μ) +
      (∫ ω, tailError ω ∂process.μ) + cutoff * δ := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  letI : IsProbabilityMeasure process.μ := process.probability
  have hconditional :=
    process.condExp_finiteContinuationValue_deviation_le cutoff hδ
      tailValue htail who deviation hdeviation deviatedTail
      hdeviatedTailMeasurable hdeviatedTail tailError htailError
      htailErrorNonneg htailDeviation 0 cutoff (by omega)
  have hbackward : Integrable (fun ω ↦
      process.finiteBackwardValue cutoff hδ
        (process.cutoffConditionalValue cutoff tailValue) cutoff ω who)
      process.μ :=
    process.finiteBackwardValue_integrable cutoff hδ
      (process.cutoffConditionalValue cutoff tailValue)
      (fun player ↦ process.conditionalContinuation_integrable cutoff
        tailValue player) cutoff who
  have herror := process.finiteBackwardError_integrable
    cutoff δ tailError cutoff
  have hintegral := integral_mono_ae integrable_condExp
    (hbackward.add herror) hconditional
  have hleft : (∫ ω, process.μ[fun sample ↦
        process.finiteContinuationValue
          (process.finiteBackwardDeviationRoots cutoff hδ tailValue
            who deviation) deviatedTail 0 cutoff sample who |
          process.filtration 0] ω ∂process.μ) =
      ∫ ω, process.finiteContinuationValue
        (process.finiteBackwardDeviationRoots cutoff hδ tailValue
          who deviation) deviatedTail 0 cutoff ω who ∂process.μ :=
    integral_condExp (process.filtration_le 0)
  have hright : (∫ ω,
      process.finiteBackwardValue cutoff hδ
          (process.cutoffConditionalValue cutoff tailValue) cutoff ω who +
        process.finiteBackwardError cutoff δ tailError cutoff ω
        ∂process.μ) =
      (∫ ω, process.finiteBackwardValue cutoff hδ
        (process.cutoffConditionalValue cutoff tailValue) cutoff ω who
        ∂process.μ) +
      (∫ ω, tailError ω ∂process.μ) + cutoff * δ := by
    rw [show (∫ ω,
        process.finiteBackwardValue cutoff hδ
            (process.cutoffConditionalValue cutoff tailValue) cutoff ω who +
          process.finiteBackwardError cutoff δ tailError cutoff ω
          ∂process.μ) =
        (∫ ω, process.finiteBackwardValue cutoff hδ
          (process.cutoffConditionalValue cutoff tailValue) cutoff ω who
          ∂process.μ) +
        ∫ ω, process.finiteBackwardError cutoff δ tailError cutoff ω
          ∂process.μ by
      simpa only [Pi.add_apply] using integral_add hbackward herror]
    rw [process.integral_finiteBackwardError cutoff δ tailError cutoff]
    ring
  rw [hleft] at hintegral
  change (∫ ω, process.finiteContinuationValue
      (process.finiteBackwardDeviationRoots cutoff hδ tailValue
        who deviation) deviatedTail 0 cutoff ω who ∂process.μ) ≤
    ∫ ω, process.finiteBackwardValue cutoff hδ
        (process.cutoffConditionalValue cutoff tailValue) cutoff ω who +
      process.finiteBackwardError cutoff δ tailError cutoff ω
      ∂process.μ at hintegral
  rw [hright] at hintegral
  exact hintegral

end GameTheory
