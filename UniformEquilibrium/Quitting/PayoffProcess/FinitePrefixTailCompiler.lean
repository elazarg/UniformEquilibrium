/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.PayoffProcess.ExpectedTailEquilibrium
import UniformEquilibrium.Quitting.PayoffProcess.FinitePrefixDeviation

/-!
# Compiling finite backward induction with a selected payoff-process tail

The finite prefix is selected by measurable approximate Nash backward
induction.  At the deterministic cutoff it is spliced to the countably
selected solo-exit tail.  This file identifies the actual global path payoff
with the finite recursion used in the incentive accounting.
-/

noncomputable section

namespace GameTheory

open MeasureTheory StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The global adapted profile obtained by finite backward induction followed
by the selected solo-exit tail. -/
def QuittingPayoffProcess.finitePrefixSoloExitProfile
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    QuittingProcessProfile process :=
  let tailValue := process.soloExitTailValue cutoff η hη
  process.spliceProfile cutoff
    (process.finiteBackwardPrefix cutoff hδ
      (process.cutoffConditionalValue cutoff tailValue))
    (process.soloExitTailProfile cutoff η hη)

/-- The compiled profile is adapted to the actual payoff filtration. -/
theorem QuittingPayoffProcess.finitePrefixSoloExitProfile_adapted
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    process.Adapted
      (process.finitePrefixSoloExitProfile cutoff hδ hη) := by
  exact process.splice_finiteBackwardPrefix_adapted cutoff hδ hη
    (process.cutoffConditionalValue cutoff
      (process.soloExitTailValue cutoff η hη))

/-- Time/sample/player ordering of the roots prescribed by the compiled
profile. -/
def QuittingPayoffProcess.finitePrefixSoloExitRoots
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ℕ → process.Ω → ι → PMF Bool :=
  fun time ω player ↦
    process.finitePrefixSoloExitProfile cutoff hδ hη time player ω

/-- Before the splice, the compiled roots are exactly the roots used in the
finite backward accounting. -/
theorem QuittingPayoffProcess.finitePrefixSoloExitRoots_eq_prefix
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    {time : ℕ} (htime : time < cutoff) (ω : process.Ω) :
    process.finitePrefixSoloExitRoots cutoff hδ hη time ω =
      process.finiteBackwardRoots cutoff hδ
        (process.soloExitTailValue cutoff η hη) time ω := by
  funext player
  simp [QuittingPayoffProcess.finitePrefixSoloExitRoots,
    QuittingPayoffProcess.finitePrefixSoloExitProfile,
    QuittingPayoffProcess.spliceProfile,
    QuittingPayoffProcess.finiteBackwardRoots, htime]

/-- At and after the splice, the compiled roots are the selected tail roots
with the global clock shifted by the cutoff. -/
theorem QuittingPayoffProcess.finitePrefixSoloExitRoots_eq_tail
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (offset : ℕ) (ω : process.Ω) :
    process.finitePrefixSoloExitRoots cutoff hδ hη (cutoff + offset) ω =
      process.soloExitTailRoots cutoff η hη ω offset := by
  funext player
  simp [QuittingPayoffProcess.finitePrefixSoloExitRoots,
    QuittingPayoffProcess.finitePrefixSoloExitProfile,
    QuittingPayoffProcess.spliceProfile,
    QuittingPayoffProcess.soloExitTailProfile,
    QuittingPayoffProcess.soloExitTailRoots, quittingProfileLiveRoot,
    quittingLiveHist]
  have htime : cutoff + offset - cutoff = offset := by omega
  rw [htime]
  rfl

/-- The global tail of the compiled roots is exactly the random payoff vector
fed to the finite backward induction. -/
theorem QuittingPayoffProcess.rootTailValue_finitePrefixSoloExitRoots_eq
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    process.rootTailValue
        (process.finitePrefixSoloExitRoots cutoff hδ hη) cutoff =
      process.soloExitTailValue cutoff η hη := by
  funext ω who
  rw [QuittingPayoffProcess.rootTailValue,
    quittingVariableTailValue_eq_shift]
  apply congrArg (fun roots ↦ quittingVariableTailValue
    (process.shiftedPayoff cutoff ω) roots who 0)
  funext offset
  exact process.finitePrefixSoloExitRoots_eq_tail
    cutoff hδ hη offset ω

omit [Nonempty ι] in
/-- A finite recursion is unchanged when its roots agree throughout the
finite window and its terminal payoff agrees. -/
theorem QuittingPayoffProcess.finiteContinuationValue_congr
    (process : QuittingPayoffProcess ι)
    (firstRoots secondRoots : ℕ → process.Ω → ι → PMF Bool)
    (firstTerminal secondTerminal : process.Ω → Payoff ι)
    (hterminal : firstTerminal = secondTerminal) :
    ∀ start fuel,
      (∀ offset, offset < fuel →
        firstRoots (start + offset) = secondRoots (start + offset)) →
      process.finiteContinuationValue firstRoots firstTerminal start fuel =
        process.finiteContinuationValue secondRoots secondTerminal start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro _hroots
      exact hterminal
  | succ fuel ih =>
      intro hroots
      rw [process.finiteContinuationValue_succ,
        process.finiteContinuationValue_succ]
      have hcurrent := hroots 0 (Nat.zero_lt_succ fuel)
      simp only [Nat.add_zero] at hcurrent
      rw [hcurrent]
      have hnext : process.finiteContinuationValue firstRoots firstTerminal
          (start + 1) fuel =
          process.finiteContinuationValue secondRoots secondTerminal
            (start + 1) fuel := by
        apply ih (start + 1)
        intro offset hoffset
        have hagree := hroots (offset + 1) (Nat.succ_lt_succ hoffset)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using hagree
      rw [hnext]

/-- The actual prescribed global path payoff equals the finite backward
prefix followed by the selected tail payoff. -/
theorem QuittingPayoffProcess.finitePrefixSoloExitPathValue_eq
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (ω : process.Ω) (who : ι) :
    quittingVariableTailValue (fun time ↦ process.payoff time ω)
        (fun time ↦ process.finitePrefixSoloExitRoots cutoff hδ hη time ω)
        who 0 =
      process.finiteContinuationValue
        (process.finiteBackwardRoots cutoff hδ
          (process.soloExitTailValue cutoff η hη))
        (process.soloExitTailValue cutoff η hη) 0 cutoff ω who := by
  let compiledRoots := process.finitePrefixSoloExitRoots cutoff hδ hη
  have hwhole := process.finiteContinuationValue_rootTailValue_eq
    compiledRoots 0 cutoff ω who
  have hterminal := process.rootTailValue_finitePrefixSoloExitRoots_eq
    cutoff hδ hη
  have hfinite : process.finiteContinuationValue compiledRoots
        (process.rootTailValue compiledRoots cutoff) 0 cutoff =
      process.finiteContinuationValue
        (process.finiteBackwardRoots cutoff hδ
          (process.soloExitTailValue cutoff η hη))
        (process.soloExitTailValue cutoff η hη) 0 cutoff := by
    apply process.finiteContinuationValue_congr
    · exact hterminal
    · intro offset hoffset
      funext sample
      simpa only [Nat.zero_add] using
        process.finitePrefixSoloExitRoots_eq_prefix
          cutoff hδ hη hoffset sample
  have hwhole' : process.finiteContinuationValue compiledRoots
        (process.rootTailValue compiledRoots cutoff) 0 cutoff ω who =
      quittingVariableTailValue (fun time ↦ process.payoff time ω)
        (fun time ↦ compiledRoots time ω) who 0 := by
    simpa only [Nat.zero_add] using hwhole
  exact hwhole'.symm.trans (congrFun (congrFun hfinite ω) who)

/-- Roots of the global compiled profile after a unilateral adapted
deviation. -/
def QuittingPayoffProcess.finitePrefixSoloExitDeviationRoots
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (who : ι)
    (deviation : ℕ → process.Ω → PMF Bool) :
    ℕ → process.Ω → ι → PMF Bool :=
  fun time ω ↦ Function.update
    (process.finitePrefixSoloExitRoots cutoff hδ hη time ω) who
    (deviation time ω)

/-- Before the splice, the deviated compiled roots are exactly the roots used
in finite-prefix deviation accounting. -/
theorem QuittingPayoffProcess.finitePrefixSoloExitDeviationRoots_eq_prefix
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (who : ι)
    (deviation : ℕ → process.Ω → PMF Bool)
    {time : ℕ} (htime : time < cutoff) (ω : process.Ω) :
    process.finitePrefixSoloExitDeviationRoots cutoff hδ hη who deviation
        time ω =
      process.finiteBackwardDeviationRoots cutoff hδ
        (process.soloExitTailValue cutoff η hη) who deviation time ω := by
  unfold QuittingPayoffProcess.finitePrefixSoloExitDeviationRoots
    QuittingPayoffProcess.finiteBackwardDeviationRoots
  rw [process.finitePrefixSoloExitRoots_eq_prefix cutoff hδ hη htime ω]

/-- At and after the splice, a global deviation becomes the shifted tail
deviation used by the selected-tail estimate. -/
theorem QuittingPayoffProcess.finitePrefixSoloExitDeviationRoots_eq_tail
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (who : ι)
    (deviation : ℕ → process.Ω → PMF Bool)
    (offset : ℕ) (ω : process.Ω) :
    process.finitePrefixSoloExitDeviationRoots cutoff hδ hη who deviation
        (cutoff + offset) ω =
      quittingRootSequenceUpdate
        (process.soloExitTailRoots cutoff η hη ω) who
        (fun time ↦ deviation (cutoff + time) ω) offset := by
  unfold QuittingPayoffProcess.finitePrefixSoloExitDeviationRoots
    quittingRootSequenceUpdate
  rw [process.finitePrefixSoloExitRoots_eq_tail cutoff hδ hη offset ω]

/-- The global deviated tail is the shifted selected-tail deviation payoff
used in the pointwise and integrated tail bounds. -/
theorem QuittingPayoffProcess.rootTailValue_finitePrefixSoloExitDeviationRoots_eq
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (who : ι)
    (deviation : ℕ → process.Ω → PMF Bool) :
    process.rootTailValue
        (process.finitePrefixSoloExitDeviationRoots cutoff hδ hη
          who deviation) cutoff =
      process.deviatedSoloExitTailValue cutoff η hη who
        (fun time ω ↦ deviation (cutoff + time) ω) := by
  funext ω recipient
  rw [QuittingPayoffProcess.rootTailValue,
    quittingVariableTailValue_eq_shift]
  apply congrArg (fun roots ↦ quittingVariableTailValue
    (process.shiftedPayoff cutoff ω) roots recipient 0)
  funext offset
  exact process.finitePrefixSoloExitDeviationRoots_eq_tail
    cutoff hδ hη who deviation offset ω

/-- The actual deviated global path payoff equals the finite deviated prefix
followed by the corresponding selected-tail deviation payoff. -/
theorem QuittingPayoffProcess.finitePrefixSoloExitDeviationPathValue_eq
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (who : ι)
    (deviation : ℕ → process.Ω → PMF Bool) (ω : process.Ω) :
    quittingVariableTailValue (fun time ↦ process.payoff time ω)
        (fun time ↦ process.finitePrefixSoloExitDeviationRoots cutoff hδ hη
          who deviation time ω) who 0 =
      process.finiteContinuationValue
        (process.finiteBackwardDeviationRoots cutoff hδ
          (process.soloExitTailValue cutoff η hη) who deviation)
        (process.deviatedSoloExitTailValue cutoff η hη who
          (fun time ω ↦ deviation (cutoff + time) ω))
        0 cutoff ω who := by
  let compiledRoots := process.finitePrefixSoloExitDeviationRoots cutoff hδ hη
    who deviation
  have hwhole := process.finiteContinuationValue_rootTailValue_eq
    compiledRoots 0 cutoff ω who
  have hterminal :=
    process.rootTailValue_finitePrefixSoloExitDeviationRoots_eq
      cutoff hδ hη who deviation
  have hfinite : process.finiteContinuationValue compiledRoots
        (process.rootTailValue compiledRoots cutoff) 0 cutoff =
      process.finiteContinuationValue
        (process.finiteBackwardDeviationRoots cutoff hδ
          (process.soloExitTailValue cutoff η hη) who deviation)
        (process.deviatedSoloExitTailValue cutoff η hη who
          (fun time ω ↦ deviation (cutoff + time) ω))
        0 cutoff := by
    apply process.finiteContinuationValue_congr
    · exact hterminal
    · intro offset hoffset
      funext sample
      simpa only [Nat.zero_add] using
        process.finitePrefixSoloExitDeviationRoots_eq_prefix
          cutoff hδ hη who deviation hoffset sample
  have hwhole' : process.finiteContinuationValue compiledRoots
        (process.rootTailValue compiledRoots cutoff) 0 cutoff ω who =
      quittingVariableTailValue (fun time ↦ process.payoff time ω)
        (fun time ↦ compiledRoots time ω) who 0 := by
    simpa only [Nat.zero_add] using hwhole
  exact hwhole'.symm.trans (congrFun (congrFun hfinite ω) who)

omit [Nonempty ι] in
/-- The semantic expected payoff is the integral of the corresponding global
root path value. -/
theorem QuittingPayoffProcess.expectedPayoff_eq_integral_pathValue
    (process : QuittingPayoffProcess ι)
    (profile : QuittingProcessProfile process) (who : ι) :
    process.expectedPayoff profile who =
      ∫ ω, quittingVariableTailValue (fun time ↦ process.payoff time ω)
        (fun time ↦ fun player ↦ profile time player ω) who 0 ∂process.μ :=
  by
    unfold QuittingPayoffProcess.expectedPayoff quittingVariableTailValue
    congr 1
    funext ω
    apply congrArg tsum
    funext time
    simp only [Nat.zero_add]

/-- Quantitative incentive bound for the compiled finite-prefix/tail profile.
The three errors are, respectively, the visible `9η` tail selector error,
twice the bad-event envelope integral, and `cutoff * δ` from finite backward
induction. -/
theorem QuittingPayoffProcess.finitePrefixSoloExitProfile_isεEquilibrium
    (process : QuittingPayoffProcess ι)
    (hassumptions : process.SoloExitAssumptions)
    (bound : process.Ω → ℝ) (hbound : Integrable bound process.μ)
    (hrewardBound : ∀ time ω terminal player,
      |process.payoff time ω terminal player| ≤ bound ω)
    (cutoff : ℕ) {δ η ε : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (herror : 9 * η +
        2 * (∫ ω, process.badTailEnvelope bound cutoff η ω ∂process.μ) +
        cutoff * δ ≤ ε) :
    process.IsεEquilibrium
      (process.finitePrefixSoloExitProfile cutoff hδ hη) ε := by
  letI : MeasurableSpace process.Ω := process.measurableSpace
  letI : IsProbabilityMeasure process.μ := process.probability
  intro who deviation hadapted
  let profile := process.finitePrefixSoloExitProfile cutoff hδ hη
  let tailValue := process.soloExitTailValue cutoff η hη
  let tailDeviation : ℕ → process.Ω → PMF Bool :=
    fun time ω ↦ deviation (cutoff + time) ω
  let deviatedTail := process.deviatedSoloExitTailValue cutoff η hη who
    tailDeviation
  let tailError : process.Ω → ℝ := fun ω ↦
    9 * η + 2 * process.badTailEnvelope bound cutoff η ω
  have hdeviation : ∀ time action,
      @Measurable process.Ω ℝ (process.filtration time)
        Real.measurableSpace
        (fun ω ↦ (deviation time ω action).toReal) := by
    intro time action
    have hcoordinate := hadapted time who action
    simpa only [Function.update_self] using hcoordinate
  have htailDeviation : ∀ time action,
      @Measurable process.Ω ℝ (process.filtration (cutoff + time))
        Real.measurableSpace
        (fun ω ↦ (tailDeviation time ω action).toReal) := by
    intro time action
    exact hdeviation (cutoff + time) action
  have htailMeasurable : ∀ player,
      @Measurable process.Ω ℝ process.measurableSpace Real.measurableSpace
        (fun ω ↦ tailValue ω player) := by
    exact process.soloExitTailValue_measurable cutoff η hη
  have htail : ∀ player,
      Integrable (fun ω ↦ tailValue ω player) process.μ := by
    exact process.soloExitTailValue_integrable cutoff η hη
      bound hbound hrewardBound
  have hdeviatedTailMeasurable : ∀ player,
      @Measurable process.Ω ℝ process.measurableSpace Real.measurableSpace
        (fun ω ↦ deviatedTail ω player) := by
    exact process.deviatedSoloExitTailValue_measurable cutoff η hη who
      tailDeviation htailDeviation
  have hdeviatedTail : ∀ player,
      Integrable (fun ω ↦ deviatedTail ω player) process.μ := by
    exact process.deviatedSoloExitTailValue_integrable cutoff η hη
      bound hbound hrewardBound who tailDeviation htailDeviation
  have hbad : Integrable
      (process.badTailEnvelope bound cutoff η) process.μ :=
    hbound.abs.indicator (process.measurableSet_tailClose cutoff η).compl
  have htailError : Integrable tailError process.μ := by
    exact (integrable_const (9 * η)).add (hbad.const_mul 2)
  have htailErrorNonneg : 0 ≤ᵐ[process.μ] tailError := by
    filter_upwards with ω
    have hbadNonneg : 0 ≤ process.badTailEnvelope bound cutoff η ω := by
      unfold QuittingPayoffProcess.badTailEnvelope
      exact Set.indicator_nonneg (fun sample _ ↦ abs_nonneg (bound sample)) ω
    dsimp only [tailError]
    positivity
  have htailPointwise : ∀ᵐ ω ∂process.μ,
      deviatedTail ω who ≤ tailValue ω who + tailError ω := by
    simpa only [deviatedTail, tailValue, tailDeviation, tailError,
      QuittingPayoffProcess.deviatedSoloExitTailValue,
      QuittingPayoffProcess.soloExitTailValue, add_assoc] using
      process.ae_soloExitTail_deviation_le cutoff hη hassumptions
        bound hrewardBound who tailDeviation
  have hdeviationBound :=
    process.integral_finiteContinuationValue_deviation_le cutoff hδ
      tailValue htail who deviation hdeviation deviatedTail
      hdeviatedTailMeasurable hdeviatedTail tailError htailError
      htailErrorNonneg htailPointwise
  have hprescribed : process.expectedPayoff profile who =
      ∫ ω, process.finiteBackwardValue cutoff hδ
        (process.cutoffConditionalValue cutoff tailValue) cutoff ω who
        ∂process.μ := by
    rw [process.expectedPayoff_eq_integral_pathValue]
    calc
      (∫ ω, quittingVariableTailValue (fun time ↦ process.payoff time ω)
          (fun time player ↦ profile time player ω) who 0 ∂process.μ) =
          ∫ ω, process.finiteContinuationValue
            (process.finiteBackwardRoots cutoff hδ tailValue) tailValue
            0 cutoff ω who ∂process.μ := by
        apply integral_congr_ae
        filter_upwards with ω
        exact process.finitePrefixSoloExitPathValue_eq cutoff hδ hη ω who
      _ = _ := process.integral_finiteContinuationValue_eq_backward
        cutoff hδ tailValue htailMeasurable htail who
  have hdeviated : process.expectedPayoff
        (fun time ↦ Function.update (profile time) who (deviation time)) who =
      ∫ ω, process.finiteContinuationValue
        (process.finiteBackwardDeviationRoots cutoff hδ tailValue
          who deviation) deviatedTail 0 cutoff ω who ∂process.μ := by
    rw [process.expectedPayoff_eq_integral_pathValue]
    apply integral_congr_ae
    filter_upwards with ω
    have hroots :
        (fun time player ↦
          Function.update (profile time) who (deviation time) player ω) =
        fun time ↦ process.finitePrefixSoloExitDeviationRoots
          cutoff hδ hη who deviation time ω := by
      funext time player
      by_cases hplayer : player = who
      · subst player
        simp only [Function.update_self,
          QuittingPayoffProcess.finitePrefixSoloExitDeviationRoots]
      · simp only [Function.update_of_ne hplayer,
          QuittingPayoffProcess.finitePrefixSoloExitDeviationRoots]
        rfl
    rw [hroots]
    simpa only [tailValue, deviatedTail, tailDeviation] using
      process.finitePrefixSoloExitDeviationPathValue_eq
        cutoff hδ hη who deviation ω
  rw [hprescribed, hdeviated]
  have htailErrorIntegral : (∫ ω, tailError ω ∂process.μ) =
      9 * η +
        2 * (∫ ω, process.badTailEnvelope bound cutoff η ω
          ∂process.μ) := by
    dsimp only [tailError]
    rw [integral_add (integrable_const (9 * η)) (hbad.const_mul 2),
      integral_const, probReal_univ, one_smul, integral_const_mul]
  rw [htailErrorIntegral] at hdeviationBound
  linarith

/-- Every positive accuracy admits an adapted equilibrium of the random
quitting payoff process under the almost-sure solo-exit assumptions.  This is
the reusable process-semantic form of Solan--Vieille's Theorem 2.14. -/
theorem QuittingPayoffProcess.exists_adapted_isεEquilibrium
    (process : QuittingPayoffProcess ι)
    (hassumptions : process.SoloExitAssumptions)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ profile : QuittingProcessProfile process,
      process.Adapted profile ∧ process.IsεEquilibrium profile ε := by
  obtain ⟨bound, hbound, hrewardBound⟩ := process.integrableEnvelope
  let η : ℝ := ε / 36
  have hη : 0 < η := by
    dsimp only [η]
    positivity
  obtain ⟨cutoff, hbad⟩ := process.exists_integral_badTailEnvelope_lt
    bound hbound hη (show 0 < ε / 16 by positivity)
  let δ : ℝ := ε / (4 * ((cutoff : ℝ) + 1))
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  let profile := process.finitePrefixSoloExitProfile cutoff hδ hη
  refine ⟨profile,
    process.finitePrefixSoloExitProfile_adapted cutoff hδ hη, ?_⟩
  apply process.finitePrefixSoloExitProfile_isεEquilibrium
    hassumptions bound hbound hrewardBound cutoff hδ hη
  have hselector : 9 * η = ε / 4 := by
    dsimp only [η]
    ring
  have hbadScaled :
      2 * (∫ ω, process.badTailEnvelope bound cutoff η ω ∂process.μ) <
        ε / 8 := by
    nlinarith
  have hdenominator : 0 < 4 * ((cutoff : ℝ) + 1) := by positivity
  have hprefix : (cutoff : ℝ) * δ < ε / 4 := by
    rw [show (cutoff : ℝ) * δ =
        ((cutoff : ℝ) * ε) / (4 * ((cutoff : ℝ) + 1)) by
      dsimp only [δ]
      ring]
    rw [div_lt_iff₀ hdenominator]
    nlinarith
  rw [hselector]
  nlinarith

end GameTheory
