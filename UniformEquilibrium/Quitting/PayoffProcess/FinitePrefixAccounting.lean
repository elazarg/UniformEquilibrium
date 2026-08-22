/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import UniformEquilibrium.Quitting.PayoffProcess.FinitePrefixBackwardInduction
import UniformEquilibrium.Quitting.PayoffProcess.PathPayoffMeasurable

/-!
# Accounting for a finite quitting prefix

The all-Continue coefficient of a root selected at stage `n` is measurable in
the natural filtration at `n`.  Conditional expectation can therefore be
pulled through that coefficient.  This is the bridge between the random
finite normal-form game used in backward induction and the actual continuation
payoff of the process.
-/

noncomputable section

namespace GameTheory

open MeasureTheory StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Conditional expectation has the same integral after multiplication by a
current-stage all-Continue probability. -/
theorem QuittingPayoffProcess.integral_continueMass_conditionalContinuation_eq
    (process : QuittingPayoffProcess ι) (time : ℕ)
    (root : process.Ω → ι → PMF Bool)
    (hroot : ∀ player,
      @Measurable process.Ω ℝ (process.filtration time)
        Real.measurableSpace
        (fun ω ↦ (root ω player false).toReal))
    (nextValue : process.Ω → Payoff ι)
    (hnext : ∀ player,
      Integrable (fun ω ↦ nextValue ω player) process.μ)
    (who : ι) :
    (∫ ω, quittingStationaryContinueMass (root ω) *
        process.conditionalContinuation time nextValue ω who ∂process.μ) =
      ∫ ω, quittingStationaryContinueMass (root ω) *
        nextValue ω who ∂process.μ := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  letI : IsProbabilityMeasure process.μ := process.probability
  let coefficient : process.Ω → ℝ := fun ω ↦
    quittingStationaryContinueMass (root ω)
  let continuation : process.Ω → ℝ := fun ω ↦ nextValue ω who
  have hcoefficient : StronglyMeasurable[process.filtration time] coefficient := by
    have hmeasurable : @Measurable process.Ω ℝ
        (process.filtration time) Real.measurableSpace coefficient := by
      letI : MeasurableSpace process.Ω := process.filtration time
      exact measurable_quittingStationaryContinueMass root hroot
    exact hmeasurable.stronglyMeasurable
  have hcoefficientAmbient : AEStronglyMeasurable coefficient process.μ :=
    (hcoefficient.mono (process.filtration_le time)).aestronglyMeasurable
  have hcoefficientBound : ∀ᵐ ω ∂process.μ, ‖coefficient ω‖ ≤ 1 := by
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg
      (quittingStationaryContinueMass_nonneg (root ω))]
    exact quittingStationaryContinueMass_le_one (root ω)
  have hproduct : Integrable (fun ω ↦ coefficient ω * continuation ω)
      process.μ :=
    (hnext who).bdd_mul hcoefficientAmbient hcoefficientBound
  have hpull :
      process.μ[fun ω ↦ coefficient ω * continuation ω |
          process.filtration time] =ᵐ[process.μ]
        fun ω ↦ coefficient ω *
          process.μ[continuation | process.filtration time] ω :=
    condExp_mul_of_stronglyMeasurable_left hcoefficient hproduct
      (hnext who)
  calc
    (∫ ω, quittingStationaryContinueMass (root ω) *
        process.conditionalContinuation time nextValue ω who ∂process.μ) =
        ∫ ω, coefficient ω *
          process.μ[continuation | process.filtration time] ω
          ∂process.μ := by rfl
    _ = ∫ ω,
        process.μ[fun sample ↦ coefficient sample * continuation sample |
          process.filtration time] ω ∂process.μ :=
      integral_congr_ae hpull.symm
    _ = ∫ ω, coefficient ω * continuation ω ∂process.μ :=
      integral_condExp (process.filtration_le time)
    _ = ∫ ω, quittingStationaryContinueMass (root ω) *
        nextValue ω who ∂process.μ := by rfl

/-- Integrating the one-stage payoff with conditional continuation gives the
same value as integrating the one-stage payoff with the actual random next
value.  This is the exact semantic bridge used by backward induction. -/
theorem QuittingPayoffProcess.integral_rootExpected_conditionalContinuation_eq
    [Nonempty ι] (process : QuittingPayoffProcess ι) (time : ℕ)
    (root : process.Ω → ι → PMF Bool)
    (hroot : ∀ player action,
      @Measurable process.Ω ℝ (process.filtration time)
        Real.measurableSpace
        (fun ω ↦ (root ω player action).toReal))
    (nextValue : process.Ω → Payoff ι)
    (hnext : ∀ player,
      Integrable (fun ω ↦ nextValue ω player) process.μ)
    (who : ι) :
    (∫ ω, quittingRootExpectedPayoff (process.payoff time ω)
        (process.conditionalContinuation time nextValue ω) (root ω) who
        ∂process.μ) =
      ∫ ω, quittingRootExpectedPayoff (process.payoff time ω)
        (nextValue ω) (root ω) who ∂process.μ := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  letI : IsProbabilityMeasure process.μ := process.probability
  let absorbing : process.Ω → ℝ := fun ω ↦
    quittingRootAbsorbingContribution (process.payoff time ω) (root ω) who
  let coefficient : process.Ω → ℝ := fun ω ↦
    quittingStationaryContinueMass (root ω)
  let continuation : process.Ω → ℝ := fun ω ↦ nextValue ω who
  have hrootAmbient : ∀ player action,
      @Measurable process.Ω ℝ process.measurableSpace Real.measurableSpace
        (fun ω ↦ (root ω player action).toReal) :=
    fun player action ↦
      (hroot player action).mono (process.filtration_le time) le_rfl
  have habsorbing : Integrable absorbing process.μ := by
    obtain ⟨bound, hbound, hreward⟩ := process.integrableEnvelope
    apply Integrable.mono' hbound
    · exact (measurable_quittingRootAbsorbingContribution
        (process.payoff time) root (process.payoff_measurable time)
        hrootAmbient who).aestronglyMeasurable
    · filter_upwards with ω
      have hle := abs_quittingRootExpectedPayoff_le_envelopeSum
        (process.payoff time ω) (0 : Payoff ι) (root ω) who (bound ω)
        (fun terminal player ↦ hreward time ω terminal player)
      have hle' :
          |quittingRootAbsorbingContribution
            (process.payoff time ω) (root ω) who| ≤ bound ω := by
        simpa only [quittingRootAbsorbingContribution,
          Pi.zero_apply, abs_zero, Finset.sum_const_zero, add_zero] using hle
      simpa only [absorbing, Real.norm_eq_abs] using hle'
  have hcoefficient : StronglyMeasurable[process.filtration time] coefficient := by
    have hmeasurable : @Measurable process.Ω ℝ
        (process.filtration time) Real.measurableSpace coefficient := by
      letI : MeasurableSpace process.Ω := process.filtration time
      exact measurable_quittingStationaryContinueMass root
        (fun player ↦ hroot player false)
    exact hmeasurable.stronglyMeasurable
  have hcoefficientAmbient : AEStronglyMeasurable coefficient process.μ :=
    (hcoefficient.mono (process.filtration_le time)).aestronglyMeasurable
  have hcoefficientBound : ∀ᵐ ω ∂process.μ, ‖coefficient ω‖ ≤ 1 := by
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg
      (quittingStationaryContinueMass_nonneg (root ω))]
    exact quittingStationaryContinueMass_le_one (root ω)
  have hactual : Integrable (fun ω ↦ coefficient ω * continuation ω)
      process.μ :=
    (hnext who).bdd_mul hcoefficientAmbient hcoefficientBound
  have hconditional : Integrable (fun ω ↦ coefficient ω *
      process.conditionalContinuation time nextValue ω who) process.μ :=
    (process.conditionalContinuation_integrable time nextValue who).bdd_mul
      hcoefficientAmbient hcoefficientBound
  have hcontinue := process.integral_continueMass_conditionalContinuation_eq
    time root (fun player ↦ hroot player false) nextValue hnext who
  simp_rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
  rw [integral_add habsorbing hconditional, integral_add habsorbing hactual]
  exact congrArg (fun value ↦ (∫ ω, absorbing ω ∂process.μ) + value)
    hcontinue

/-- Conditional expectation of the actual one-stage payoff is the Bellman
payoff whose continuation is the conditional expected next value. -/
theorem QuittingPayoffProcess.condExp_rootExpected_eq
    [Nonempty ι] (process : QuittingPayoffProcess ι) (time : ℕ)
    (root : process.Ω → ι → PMF Bool)
    (hroot : ∀ player action,
      @Measurable process.Ω ℝ (process.filtration time)
        Real.measurableSpace
        (fun ω ↦ (root ω player action).toReal))
    (nextValue : process.Ω → Payoff ι)
    (hnext : ∀ player,
      Integrable (fun ω ↦ nextValue ω player) process.μ)
    (who : ι) :
    process.μ[fun ω ↦ quittingRootExpectedPayoff
        (process.payoff time ω) (nextValue ω) (root ω) who |
        process.filtration time] =ᵐ[process.μ]
      fun ω ↦ quittingRootExpectedPayoff (process.payoff time ω)
        (process.conditionalContinuation time nextValue ω) (root ω) who := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  letI : IsProbabilityMeasure process.μ := process.probability
  let absorbing : process.Ω → ℝ := fun ω ↦
    quittingRootAbsorbingContribution (process.payoff time ω) (root ω) who
  let coefficient : process.Ω → ℝ := fun ω ↦
    quittingStationaryContinueMass (root ω)
  let continuation : process.Ω → ℝ := fun ω ↦ nextValue ω who
  have hrootAmbient : ∀ player action,
      @Measurable process.Ω ℝ process.measurableSpace Real.measurableSpace
        (fun ω ↦ (root ω player action).toReal) :=
    fun player action ↦
      (hroot player action).mono (process.filtration_le time) le_rfl
  have habsorbingMeasurable :
      @Measurable process.Ω ℝ (process.filtration time)
        Real.measurableSpace absorbing := by
    letI : MeasurableSpace process.Ω := process.filtration time
    exact measurable_quittingRootAbsorbingContribution
      (process.payoff time) root
      (process.payoff_measurable_filtration time) hroot who
  have habsorbingStrong :
      StronglyMeasurable[process.filtration time] absorbing :=
    habsorbingMeasurable.stronglyMeasurable
  have habsorbing : Integrable absorbing process.μ := by
    obtain ⟨bound, hbound, hreward⟩ := process.integrableEnvelope
    apply Integrable.mono' hbound
    · exact (habsorbingMeasurable.mono
        (process.filtration_le time) le_rfl).aestronglyMeasurable
    · filter_upwards with ω
      have hle := abs_quittingRootExpectedPayoff_le_envelopeSum
        (process.payoff time ω) (0 : Payoff ι) (root ω) who (bound ω)
        (fun terminal player ↦ hreward time ω terminal player)
      have hle' :
          |quittingRootAbsorbingContribution
            (process.payoff time ω) (root ω) who| ≤ bound ω := by
        simpa only [quittingRootAbsorbingContribution, Pi.zero_apply,
          abs_zero, Finset.sum_const_zero, add_zero] using hle
      simpa only [absorbing, Real.norm_eq_abs] using hle'
  have hcoefficient : StronglyMeasurable[process.filtration time] coefficient := by
    have hmeasurable : @Measurable process.Ω ℝ
        (process.filtration time) Real.measurableSpace coefficient := by
      letI : MeasurableSpace process.Ω := process.filtration time
      exact measurable_quittingStationaryContinueMass root
        (fun player ↦ hroot player false)
    exact hmeasurable.stronglyMeasurable
  have hcoefficientAmbient : AEStronglyMeasurable coefficient process.μ :=
    (hcoefficient.mono (process.filtration_le time)).aestronglyMeasurable
  have hcoefficientBound : ∀ᵐ ω ∂process.μ, ‖coefficient ω‖ ≤ 1 := by
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg
      (quittingStationaryContinueMass_nonneg (root ω))]
    exact quittingStationaryContinueMass_le_one (root ω)
  have hproduct : Integrable (fun ω ↦ coefficient ω * continuation ω)
      process.μ :=
    (hnext who).bdd_mul hcoefficientAmbient hcoefficientBound
  have hpull :
      process.μ[fun ω ↦ coefficient ω * continuation ω |
          process.filtration time] =ᵐ[process.μ]
        fun ω ↦ coefficient ω *
          process.μ[continuation | process.filtration time] ω :=
    condExp_mul_of_stronglyMeasurable_left hcoefficient hproduct
      (hnext who)
  have habsorbingFixed :
      process.μ[absorbing | process.filtration time] = absorbing :=
    condExp_of_stronglyMeasurable (process.filtration_le time)
      habsorbingStrong habsorbing
  have hadd := condExp_add habsorbing hproduct (process.filtration time)
  calc
    process.μ[fun ω ↦ quittingRootExpectedPayoff
        (process.payoff time ω) (nextValue ω) (root ω) who |
        process.filtration time] =ᵐ[process.μ]
        process.μ[fun ω ↦ absorbing ω +
          coefficient ω * continuation ω | process.filtration time] := by
      apply condExp_congr_ae
      filter_upwards with ω
      exact quittingRootExpectedPayoff_eq_absorbingContribution_add
        (process.payoff time ω) (nextValue ω) (root ω) who
    _ =ᵐ[process.μ] fun ω ↦ process.μ[absorbing |
          process.filtration time] ω +
        process.μ[fun sample ↦ coefficient sample * continuation sample |
          process.filtration time] ω := hadd
    _ =ᵐ[process.μ] fun ω ↦ absorbing ω + coefficient ω *
        process.μ[continuation | process.filtration time] ω := by
      filter_upwards [hpull] with ω hpullω
      rw [habsorbingFixed, hpullω]
    _ =ᵐ[process.μ] fun ω ↦ quittingRootExpectedPayoff
        (process.payoff time ω)
        (process.conditionalContinuation time nextValue ω) (root ω) who := by
      filter_upwards with ω
      exact (quittingRootExpectedPayoff_eq_absorbingContribution_add
        (process.payoff time ω)
        (process.conditionalContinuation time nextValue ω) (root ω) who).symm

/-- Actual finite-horizon payoff obtained by playing `roots` from `start` for
`fuel` stages and then receiving `terminalValue` after all Continue. -/
def QuittingPayoffProcess.finiteContinuationValue
    (process : QuittingPayoffProcess ι)
    (roots : ℕ → process.Ω → ι → PMF Bool)
    (terminalValue : process.Ω → Payoff ι) :
    ℕ → ℕ → process.Ω → Payoff ι
  | _, 0 => terminalValue
  | start, fuel + 1 => fun ω who ↦
      quittingRootExpectedPayoff (process.payoff start ω)
        (process.finiteContinuationValue roots terminalValue
          (start + 1) fuel ω)
        (roots start ω) who

@[simp]
theorem QuittingPayoffProcess.finiteContinuationValue_zero
    (process : QuittingPayoffProcess ι)
    (roots : ℕ → process.Ω → ι → PMF Bool)
    (terminalValue : process.Ω → Payoff ι) (start : ℕ) :
    process.finiteContinuationValue roots terminalValue start 0 =
      terminalValue :=
  rfl

@[simp]
theorem QuittingPayoffProcess.finiteContinuationValue_succ
    (process : QuittingPayoffProcess ι)
    (roots : ℕ → process.Ω → ι → PMF Bool)
    (terminalValue : process.Ω → Payoff ι) (start fuel : ℕ) :
    process.finiteContinuationValue roots terminalValue start (fuel + 1) =
      fun ω who ↦ quittingRootExpectedPayoff (process.payoff start ω)
        (process.finiteContinuationValue roots terminalValue
          (start + 1) fuel ω)
        (roots start ω) who :=
  rfl

/-- Measurability of a finite continuation value follows from measurable
root coordinates and a measurable terminal value. -/
theorem QuittingPayoffProcess.finiteContinuationValue_measurable
    (process : QuittingPayoffProcess ι)
    (roots : ℕ → process.Ω → ι → PMF Bool)
    (hroots : ∀ time player action,
      @Measurable process.Ω ℝ process.measurableSpace Real.measurableSpace
        (fun ω ↦ (roots time ω player action).toReal))
    (terminalValue : process.Ω → Payoff ι)
    (hterminal : ∀ player,
      @Measurable process.Ω ℝ process.measurableSpace Real.measurableSpace
        (fun ω ↦ terminalValue ω player)) :
    ∀ start fuel player,
      @Measurable process.Ω ℝ process.measurableSpace Real.measurableSpace
        (fun ω ↦
          process.finiteContinuationValue roots terminalValue
            start fuel ω player) := by
  intro start fuel
  induction fuel generalizing start with
  | zero => exact hterminal
  | succ fuel ih =>
      intro player
      letI : MeasurableSpace process.Ω := process.measurableSpace
      exact measurable_quittingRootExpectedPayoff
        (process.payoff start)
        (process.finiteContinuationValue roots terminalValue
          (start + 1) fuel)
        (roots start) (process.payoff_measurable start) (ih (start + 1))
        (hroots start) player

/-- Integrability of a finite continuation value follows from the process
envelope and integrability of the terminal payoff. -/
theorem QuittingPayoffProcess.finiteContinuationValue_integrable
    (process : QuittingPayoffProcess ι)
    (roots : ℕ → process.Ω → ι → PMF Bool)
    (hroots : ∀ time player action,
      @Measurable process.Ω ℝ process.measurableSpace Real.measurableSpace
        (fun ω ↦ (roots time ω player action).toReal))
    (terminalValue : process.Ω → Payoff ι)
    (hterminalMeasurable : ∀ player,
      @Measurable process.Ω ℝ process.measurableSpace Real.measurableSpace
        (fun ω ↦ terminalValue ω player))
    (hterminal : ∀ player,
      Integrable (fun ω ↦ terminalValue ω player) process.μ) :
    ∀ start fuel player,
      Integrable (fun ω ↦
        process.finiteContinuationValue roots terminalValue
          start fuel ω player) process.μ := by
  intro start fuel
  induction fuel generalizing start with
  | zero => exact hterminal
  | succ fuel ih =>
      intro player
      letI : MeasurableSpace process.Ω := process.measurableSpace
      obtain ⟨bound, hbound, hreward⟩ := process.integrableEnvelope
      let envelope : process.Ω → ℝ := fun ω ↦
        bound ω + ∑ nextPlayer,
          |process.finiteContinuationValue roots terminalValue
            (start + 1) fuel ω nextPlayer|
      have henvelope : Integrable envelope process.μ := by
        exact hbound.add (integrable_finsetSum Finset.univ
          fun nextPlayer _ ↦ (ih (start + 1) nextPlayer).abs)
      apply Integrable.mono' henvelope
      · exact (process.finiteContinuationValue_measurable roots hroots
          terminalValue hterminalMeasurable start (fuel + 1) player)
          |>.aestronglyMeasurable
      · filter_upwards with ω
        exact abs_quittingRootExpectedPayoff_le_envelopeSum
          (process.payoff start ω)
          (process.finiteContinuationValue roots terminalValue
            (start + 1) fuel ω)
          (roots start ω) player (bound ω)
          (fun terminal recipient ↦ hreward start ω terminal recipient)

/-- The cutoff value used by finite backward induction is the conditional
expectation, given the cutoff history, of the actual selected tail payoff. -/
def QuittingPayoffProcess.cutoffConditionalValue
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    (tailValue : process.Ω → Payoff ι) : process.Ω → Payoff ι :=
  process.conditionalContinuation cutoff tailValue

/-- Root sequence underlying the finite backward prefix, with arguments in
the time/sample/player order used by finite-path accounting. -/
def QuittingPayoffProcess.finiteBackwardRoots
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (tailValue : process.Ω → Payoff ι) :
    ℕ → process.Ω → ι → PMF Bool :=
  fun time ω player ↦
    process.finiteBackwardPrefix cutoff hδ
      (process.cutoffConditionalValue cutoff tailValue) time player ω

/-- Backward values are the conditional expectations, in the actual natural
filtration, of the finite-prefix payoff followed by the random tail payoff. -/
theorem QuittingPayoffProcess.condExp_finiteContinuationValue_eq_backward
    [Nonempty ι] (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (tailValue : process.Ω → Payoff ι)
    (htailMeasurable : ∀ player,
      @Measurable process.Ω ℝ process.measurableSpace Real.measurableSpace
        (fun ω ↦ tailValue ω player))
    (htail : ∀ player,
      Integrable (fun ω ↦ tailValue ω player) process.μ) :
    ∀ start depth, start + depth = cutoff → ∀ player,
      process.μ[fun ω ↦
        process.finiteContinuationValue
          (process.finiteBackwardRoots cutoff hδ tailValue) tailValue
          start depth ω player | process.filtration start] =ᵐ[process.μ]
        fun ω ↦ process.finiteBackwardValue cutoff hδ
          (process.cutoffConditionalValue cutoff tailValue) depth ω player := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  letI : IsProbabilityMeasure process.μ := process.probability
  intro start depth
  induction depth generalizing start with
  | zero =>
      intro hstart player
      have hstartEq : start = cutoff := by omega
      subst start
      filter_upwards with ω
      rfl
  | succ depth ih =>
      intro hstart player
      have hstartLt : start < cutoff := by omega
      have hnextSum : start + 1 + depth = cutoff := by omega
      let terminal : process.Ω → Payoff ι :=
        process.cutoffConditionalValue cutoff tailValue
      let roots : ℕ → process.Ω → ι → PMF Bool :=
        process.finiteBackwardRoots cutoff hδ tailValue
      let actualNext : process.Ω → Payoff ι := fun ω ↦
        process.finiteContinuationValue roots tailValue
          (start + 1) depth ω
      let backwardNext : process.Ω → Payoff ι :=
        process.finiteBackwardValue cutoff hδ terminal depth
      have hrootsAmbient : ∀ time who action,
          @Measurable process.Ω ℝ process.measurableSpace
            Real.measurableSpace
            (fun ω ↦ (roots time ω who action).toReal) := by
        intro time who action
        exact process.finiteBackwardPrefix_measurable_ambient cutoff hδ
          terminal time who action
      have hactualNext : ∀ who,
          Integrable (fun ω ↦ actualNext ω who) process.μ := by
        intro who
        exact process.finiteContinuationValue_integrable roots hrootsAmbient
          tailValue htailMeasurable htail (start + 1) depth who
      have hrootFiltration : ∀ who action,
          @Measurable process.Ω ℝ (process.filtration start)
            Real.measurableSpace
            (fun ω ↦ (roots start ω who action).toReal) := by
        intro who action
        exact process.finiteBackwardPrefix_measurable cutoff hδ terminal
          start hstartLt who action
      have hstep := process.condExp_rootExpected_eq start (roots start)
        hrootFiltration actualNext hactualNext player
      have ihNext (who : ι) := ih (start + 1) hnextSum who
      have htower (who : ι) :
          process.μ[process.μ[fun ω ↦ actualNext ω who |
              process.filtration (start + 1)] |
              process.filtration start] =ᵐ[process.μ]
            process.μ[fun ω ↦ actualNext ω who |
              process.filtration start] :=
        condExp_condExp_of_le
          (process.filtration_mono (Nat.le_succ start))
          (process.filtration_le (start + 1))
      have hcontinuation (who : ι) :
          process.μ[fun ω ↦ actualNext ω who |
              process.filtration start] =ᵐ[process.μ]
            process.μ[fun ω ↦ backwardNext ω who |
              process.filtration start] := by
        exact (htower who).symm.trans (condExp_congr_ae (ihNext who))
      have hstage :
          process.μ[fun ω ↦
            process.finiteContinuationValue roots tailValue
              start (depth + 1) ω player | process.filtration start] =ᵐ[process.μ]
            fun ω ↦ process.finiteStageValue start hδ
              backwardNext ω player := by
        filter_upwards [hstep, hcontinuation player] with ω hstepω hcontinuationω
        change process.μ[fun sample ↦ quittingRootExpectedPayoff
            (process.payoff start sample) (actualNext sample)
            (roots start sample) player | process.filtration start] ω = _
        rw [hstepω]
        have hremaining : cutoff - (start + 1) = depth := by omega
        have hrootEq : roots start ω =
            process.finiteStageRoot start hδ backwardNext ω := by
          funext selected
          change process.finiteBackwardPrefix cutoff hδ terminal
              start selected ω = _
          rw [process.finiteBackwardPrefix_eq cutoff start hδ terminal
            hstartLt]
          change process.finiteStageRoot start hδ
              (process.finiteBackwardValue cutoff hδ terminal
                (cutoff - (start + 1))) ω selected = _
          rw [hremaining]
        rw [QuittingPayoffProcess.finiteStageValue, ← hrootEq]
        exact quittingRootExpectedPayoff_continuation_congr
          (process.payoff start ω)
          (process.conditionalContinuation start actualNext ω)
          (process.conditionalContinuation start backwardNext ω)
          (roots start ω) player hcontinuationω
      filter_upwards [hstage] with ω hstageω
      rw [hstageω]
      have hstageIndex : cutoff - (depth + 1) = start := by omega
      simp only [QuittingPayoffProcess.finiteBackwardValue_succ,
        terminal, backwardNext]
      rw [hstageIndex]

/-- Integrating the selected finite prefix followed by its actual random tail
equals the initial backward-induction value. -/
theorem QuittingPayoffProcess.integral_finiteContinuationValue_eq_backward
    [Nonempty ι] (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (tailValue : process.Ω → Payoff ι)
    (htailMeasurable : ∀ player,
      @Measurable process.Ω ℝ process.measurableSpace Real.measurableSpace
        (fun ω ↦ tailValue ω player))
    (htail : ∀ player,
      Integrable (fun ω ↦ tailValue ω player) process.μ)
    (player : ι) :
    (∫ ω, process.finiteContinuationValue
        (process.finiteBackwardRoots cutoff hδ tailValue) tailValue
        0 cutoff ω player ∂process.μ) =
      ∫ ω, process.finiteBackwardValue cutoff hδ
        (process.cutoffConditionalValue cutoff tailValue) cutoff ω player
        ∂process.μ := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  letI : IsProbabilityMeasure process.μ := process.probability
  have hconditional :=
    process.condExp_finiteContinuationValue_eq_backward cutoff hδ
      tailValue htailMeasurable htail 0 cutoff (by omega) player
  calc
    (∫ ω, process.finiteContinuationValue
        (process.finiteBackwardRoots cutoff hδ tailValue) tailValue
        0 cutoff ω player ∂process.μ) =
        ∫ ω, process.μ[fun sample ↦
          process.finiteContinuationValue
            (process.finiteBackwardRoots cutoff hδ tailValue) tailValue
            0 cutoff sample player | process.filtration 0] ω
          ∂process.μ :=
      (integral_condExp (process.filtration_le 0)).symm
    _ = ∫ ω, process.finiteBackwardValue cutoff hδ
        (process.cutoffConditionalValue cutoff tailValue) cutoff ω player
        ∂process.μ := integral_congr_ae hconditional

/-- Infinite continuation payoff of a root process from a deterministic
cutoff, written with the original global stage indices. -/
def QuittingPayoffProcess.rootTailValue
    (process : QuittingPayoffProcess ι)
    (roots : ℕ → process.Ω → ι → PMF Bool) (cutoff : ℕ) :
    process.Ω → Payoff ι :=
  fun ω who ↦ quittingVariableTailValue
    (fun time ↦ process.payoff time ω) (fun time ↦ roots time ω)
    who cutoff

/-- Finite continuation recursion followed by the matching infinite tail is
exactly the whole root-path payoff. -/
theorem QuittingPayoffProcess.finiteContinuationValue_rootTailValue_eq
    [Nonempty ι] (process : QuittingPayoffProcess ι)
    (roots : ℕ → process.Ω → ι → PMF Bool) :
    ∀ start fuel, ∀ ω player,
      process.finiteContinuationValue roots
          (process.rootTailValue roots (start + fuel))
          start fuel ω player =
        quittingVariableTailValue (fun time ↦ process.payoff time ω)
          (fun time ↦ roots time ω) player start := by
  obtain ⟨bound, _, hreward⟩ := process.integrableEnvelope
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro ω player
      rfl
  | succ fuel ih =>
      intro ω player
      have hboundNonneg : 0 ≤ bound ω := by
        let witness : ι := Classical.choice inferInstance
        exact (abs_nonneg
          (process.payoff 0 ω (quittingSingletonTerminal witness) witness)).trans
            (hreward 0 ω (quittingSingletonTerminal witness) witness)
      have htailRecursion := quittingVariableTailValue_eq
        (fun time ↦ process.payoff time ω) (fun time ↦ roots time ω)
        player start hboundNonneg
        (fun offset terminal recipient ↦
          hreward (start + offset) ω terminal recipient)
      change quittingRootExpectedPayoff (process.payoff start ω)
        (process.finiteContinuationValue roots
          (process.rootTailValue roots (start + (fuel + 1)))
          (start + 1) fuel ω) (roots start ω) player = _
      have hcutoff : start + (fuel + 1) = start + 1 + fuel := by omega
      rw [hcutoff]
      have hnext : process.finiteContinuationValue roots
          (process.rootTailValue roots (start + 1 + fuel))
          (start + 1) fuel ω =
          fun recipient ↦ quittingVariableTailValue
            (fun time ↦ process.payoff time ω) (fun time ↦ roots time ω)
            recipient (start + 1) := by
        funext recipient
        exact ih (start + 1) ω recipient
      rw [hnext]
      rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
      exact htailRecursion.symm

end GameTheory
