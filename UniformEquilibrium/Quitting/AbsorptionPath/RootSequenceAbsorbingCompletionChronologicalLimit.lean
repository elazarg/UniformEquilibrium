/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.ChronologicalMarkedRootSequenceLaw
import UniformEquilibrium.Quitting.AbsorptionPath.RootSequenceAbsorbingCompletionPath
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-!
# Chronological limits of absorbing root-sequence completions

The completely absorbing diagonal admits one further shared strict subsequence
whose chronological marked laws converge.  Its decoded càdlàg path satisfies
A1, and its clopen endpoint coalition fibers are the literal limits of the
completed terminal laws.  Their fixed reward moment is therefore the limit of
the completed prescribed payoffs and is a uniform-equilibrium payoff.

The result remains conditional on the supplied vanishing-Nash family and its
absorbing-completion diagonal.  It does not assert A2--A4, path convergence,
sequential perfection, or a fixed completion owner or branch.
-/

noncomputable section

namespace GameTheory

open Filter Finset MeasureTheory StochasticGame
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

namespace QuittingRootSequenceAbsorbingCompletionDiagonal

variable
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : QuittingRootSequenceVanishingNashFamily reward}

/-- The chronological marked law of one actual completed diagonal profile. -/
def chronologicalLaw
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source)
    (rank : ℕ) :
    ProbabilityMeasure
      (QuittingAbsorptionPath.QuittingChronologicalEvent reward) :=
  (diagonal.completion rank).finiteAbsorptionCertificate.chronologicalLaw reward

/-- One shared weakly convergent strict subsequence of the chronological
marked laws. -/
structure ChronologicalLimit
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source) where
  law : ProbabilityMeasure
    (QuittingAbsorptionPath.QuittingChronologicalEvent reward)
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  law_tendsto : Tendsto
    (fun rank => diagonal.chronologicalLaw (subsequence rank))
    atTop (𝓝 law)

omit [Nonempty ι] in
/-- Compactness of the marked-law carrier supplies a chronological limit. -/
theorem nonempty_chronologicalLimit
    (diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source) :
    Nonempty diagonal.ChronologicalLimit := by
  obtain ⟨law, subsequence, hstrict, hlaw⟩ :=
    CompactSpace.tendsto_subseq diagonal.chronologicalLaw
  exact ⟨{
    law := law
    subsequence := subsequence
    subsequence_strictMono := hstrict
    law_tendsto := by simpa [Function.comp_def] using hlaw
  }⟩

namespace ChronologicalLimit

variable
    {diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source}

/-- The càdlàg path decoded from the chronological limit law. -/
def path (limit : diagonal.ChronologicalLimit) :
    QuittingAbsorptionPath.CadlagPath (ι := ι) :=
  QuittingAbsorptionPath.chronologicalCadlagPath limit.law

omit [Nonempty ι] in
/-- The decoded limit satisfies absorption-path axiom A1. -/
theorem le_pathTotal
    (limit : diagonal.ChronologicalLimit)
    (time : ℝ) (htime : time ∈ Set.Icc (0 : ℝ) 1) :
    time ≤ QuittingAbsorptionPath.pathTotal limit.path time := by
  let certificates := fun rank =>
    (diagonal.completion (limit.subsequence rank)).finiteAbsorptionCertificate
  exact QuittingAbsorptionPath.le_pathTotal_chronologicalCadlagPath_of_tendsto
    certificates limit.law limit.law_tendsto time htime

/-- The terminal coalition coordinate of the decoded chronological path. -/
def endpointCoalitionMass
    (limit : diagonal.ChronologicalLimit)
    (coalition : {S : Finset ι // S.Nonempty}) : ℝ :=
  limit.path.value 1 coalition

omit [Nonempty ι] in
/-- Endpoint coalition coordinates are nonnegative. -/
theorem endpointCoalitionMass_nonneg
    (limit : diagonal.ChronologicalLimit)
    (coalition : {S : Finset ι // S.Nonempty}) :
    0 ≤ limit.endpointCoalitionMass coalition :=
  (limit.path.value_mem 1 (by simp) coalition).1

omit [Nonempty ι] in
/-- The endpoint coalition coordinates sum to one. -/
theorem sum_endpointCoalitionMass
    (limit : diagonal.ChronologicalLimit) :
    ∑ coalition, limit.endpointCoalitionMass coalition = 1 := by
  unfold endpointCoalitionMass path
  change QuittingAbsorptionPath.pathTotal
    (QuittingAbsorptionPath.chronologicalCadlagPath limit.law) 1 = 1
  rw [QuittingAbsorptionPath.pathTotal_chronologicalCadlagPath_eq_clockEvent_real
    limit.law le_rfl]
  have huniv : QuittingAbsorptionPath.chronologicalClockEvent
      (reward := reward) 1 = Set.univ := by
    ext event
    simp [QuittingAbsorptionPath.chronologicalClockEvent,
      QuittingAbsorptionPath.chronologicalEventClock, event.1.2.2]
  rw [huniv]
  exact probReal_univ

/-- Every endpoint coalition coordinate is the limit of the actual completed
terminal coalition probability along the one shared subsequence. -/
theorem completedTerminalOutcomeMass_tendsto
    (limit : diagonal.ChronologicalLimit)
    (coalition : {S : Finset ι // S.Nonempty}) :
    Tendsto (fun rank =>
      quittingTerminalOutcomeMass reward
        (quittingRootSequenceProfile reward
          (diagonal.completedRoots (limit.subsequence rank)) 0)
        (some coalition)) atTop
      (𝓝 (limit.endpointCoalitionMass coalition)) := by
  have hmass :=
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
      limit.law_tendsto
      (QuittingAbsorptionPath.isClopen_chronologicalCoalitionEvent
        (reward := reward) coalition)
  have hreal := NNReal.continuous_coe.continuousAt.tendsto.comp hmass
  have hendpoint : limit.endpointCoalitionMass coalition =
      (limit.law (QuittingAbsorptionPath.chronologicalCoalitionEvent
        coalition) : NNReal) := by
    unfold endpointCoalitionMass path
    change QuittingAbsorptionPath.chronologicalCoalitionCDF
      limit.law coalition 1 = _
    rw [QuittingAbsorptionPath.chronologicalCoalitionCDF_one_eq_coalitionEvent_real,
      ProbabilityMeasure.measureReal_eq_coe_coeFn]
  rw [hendpoint]
  apply hreal.congr'
  filter_upwards [] with rank
  change ((diagonal.chronologicalLaw (limit.subsequence rank))
      (QuittingAbsorptionPath.chronologicalCoalitionEvent coalition) :
        NNReal) = quittingTerminalOutcomeMass reward
      (quittingRootSequenceProfile reward
        (diagonal.completedRoots (limit.subsequence rank)) 0)
      (some coalition)
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn,
    ← QuittingAbsorptionPath.chronologicalCoalitionCDF_one_eq_coalitionEvent_real]
  unfold QuittingRootSequenceAbsorbingCompletionDiagonal.chronologicalLaw
  change (QuittingAbsorptionPath.chronologicalCadlagPath
    ((diagonal.completion (limit.subsequence rank))
      |>.finiteAbsorptionCertificate.chronologicalLaw reward)).value
      1 coalition = _
  rw [(diagonal.completion (limit.subsequence rank))
    |>.finiteAbsorptionCertificate.chronologicalCadlagPath_value_eq
      (reward := reward) 1 (by simp) coalition]
  exact (diagonal.completion (limit.subsequence rank))
    |>.finiteAbsorptionCertificate.value_one_eq_terminalOutcomeMass_some
      reward coalition

/-- The fixed reward moment of the chronological endpoint. -/
def payoff (limit : diagonal.ChronologicalLimit) : Payoff ι :=
  fun who => ∑ coalition,
    limit.endpointCoalitionMass coalition * reward coalition who

/-- The actual completed prescribed payoff converges to the fixed endpoint
reward moment along the shared subsequence. -/
theorem completedTerminalPayoff_tendsto
    (limit : diagonal.ChronologicalLimit) :
    Tendsto (fun rank =>
      quittingTerminalPayoff reward
        (quittingRootSequenceProfile reward
          (diagonal.completedRoots (limit.subsequence rank)) 0))
      atTop (𝓝 limit.payoff) := by
  rw [tendsto_pi_nhds]
  intro who
  have hsum : Tendsto (fun rank =>
      ∑ coalition,
        quittingTerminalOutcomeMass reward
          (quittingRootSequenceProfile reward
            (diagonal.completedRoots (limit.subsequence rank)) 0)
          (some coalition) * reward coalition who) atTop
      (𝓝 (∑ coalition,
        limit.endpointCoalitionMass coalition * reward coalition who)) := by
    apply tendsto_finsetSum
    intro coalition _
    exact (limit.completedTerminalOutcomeMass_tendsto coalition).mul_const _
  apply hsum.congr'
  filter_upwards [] with rank
  have hmoment := congrFun
    (quittingTerminalRewardMoment_outcomeMass reward
      (quittingRootSequenceProfile reward
        (diagonal.completedRoots (limit.subsequence rank)) 0)) who
  simpa only [quittingTerminalRewardMoment,
    quittingTerminalOutcomeReward, Fintype.sum_option, Pi.zero_apply,
    mul_zero, zero_add] using hmoment

/-- Conditional on the supplied vanishing-Nash source and completion
diagonal, the fixed chronological endpoint reward moment is a uniform-
equilibrium payoff. -/
theorem payoff_isUniformEquilibriumPayoff
    (limit : diagonal.ChronologicalLimit) :
    (quittingGame reward).IsUniformEquilibriumPayoff none limit.payoff := by
  apply quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto
    reward limit.payoff
    (fun rank => diagonal.completedError (limit.subsequence rank))
    (fun rank => quittingRootSequenceProfile reward
      (diagonal.completedRoots (limit.subsequence rank)) 0)
  · exact diagonal.completedError_tendsto_zero.comp
      limit.subsequence_strictMono.tendsto_atTop
  · exact Filter.Frequently.of_forall fun rank =>
      diagonal.profile_isεAsymptoticNash (limit.subsequence rank)
  · exact limit.completedTerminalPayoff_tendsto

end ChronologicalLimit

end QuittingRootSequenceAbsorbingCompletionDiagonal

end GameTheory
