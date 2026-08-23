/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.OffDiagonal.PotentialCoDecreaseCurvature
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPaidFirstDisagreementOrientation

/-!
# Data-bearing temporal dispatch of potential co-decrease curvature

The lower-level normalized-curvature decoder constructs approximate pure-time
witnesses at both the source and the full-reset endpoint.  This module retains
those two inequalities together with the paid first-disagreement row and then
consumes the row's temporal orientation.

The error budget is parameterized.  At scale `lambda`, the source error is
`lambda * sourceBudget`, while the endpoint error is independent of `lambda`.
The old fixed choices `gain = curvature / 4` and
`endpointError = curvature / 16` meet the terminal-gap threshold only when
`quittingRewardBound reward < 2 * gamma`; that comparison is unavailable in
general.  Allowing an arbitrarily smaller positive endpoint error removes this
ratio artifact without strengthening the curvature hypothesis.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A paid first-disagreement row together with the two approximate witness
inequalities produced by the normalized-curvature decoder. -/
structure QuittingStoppingLawCurvaturePaidWitness
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (sourceError endpointError gain : ℝ) where
  row : QuittingPaidFirstDisagreementRow reward
    (Function.update profile mover target) observer gain
  source_approx :
    quittingContinuationBestResponseValue reward profile observer -
        sourceError ≤
      quittingPureTimeDeviationPayoff reward profile observer
        row.sourceWitness
  receiving_approx :
    quittingContinuationBestResponseValue reward
          (Function.update profile mover target) observer - endpointError ≤
      quittingPureTimeDeviationPayoff reward
        (Function.update profile mover target) observer row.receivingWitness

/-- Data-preserving wrapper around the one-ray normalized-curvature decoder. -/
theorem exists_quittingStoppingLawCurvaturePaidWitness
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (lambda sourceError endpointError gain : ℝ)
    (hne : observer ≠ mover) (hlambda : 0 < lambda)
    (hlambdaOne : lambda ≤ 1)
    (hsourceError : 0 < sourceError) (hendpointError : 0 < endpointError)
    (hgain : 0 < gain)
    (hcurvature :
      lambda * (gain + endpointError) + (1 - lambda) * sourceError ≤
        lambda *
          (quittingTerminalSemanticDebtChange
              (quittingTerminalSemanticPair reward profile)
              (quittingTerminalSemanticPair reward
                (Function.update profile mover target)) observer -
            quittingStoppingLawNormalizedDebtDirection reward profile mover
              target lambda hlambda.le hlambdaOne observer)) :
    Nonempty (QuittingStoppingLawCurvaturePaidWitness reward profile mover
      observer target sourceError endpointError gain) := by
  obtain ⟨row, hsource, hreceiving⟩ :=
    exists_paidFirstDisagreementRow_of_stoppingLawNormalizedCurvature
      reward profile mover observer target lambda sourceError endpointError
      gain hne hlambda hlambdaOne hsourceError hendpointError hgain hcurvature
  exact ⟨⟨row, hsource, hreceiving⟩⟩

/-- The strongest existing temporal consumer of a curvature-paid witness.
The later-receiving branch is a legal deviation by the observer.  Under a
terminal gap and the sharp endpoint-error threshold, the earlier-receiving
branch is a reached pure endpoint deviation by an outsider. -/
inductive QuittingStoppingLawCurvatureStrategicDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {mover observer : ι}
    {target : (quittingGame reward).BehaviorStrategy mover}
    {sourceError endpointError gain gamma : ℝ}
    (carrier : QuittingStoppingLawCurvaturePaidWitness reward profile mover
      observer target sourceError endpointError gain) : Type
  | owner
      (hlater : carrier.row.receivingEarlier = false)
      (deviation : (quittingGame reward).BehaviorStrategy observer)
      (gain_le :
        let receiving := Function.update profile mover target
        let earlierProfile := Function.update receiving observer
          (quittingPureTimeBehaviorStrategy reward observer
            carrier.row.sourceWitness)
        quittingTerminalPayoff reward earlierProfile observer + gain ≤
          quittingTerminalPayoff reward
            (Function.update earlierProfile observer deviation) observer) :
      QuittingStoppingLawCurvatureStrategicDispatch carrier
  | outsider
      (hearlier : carrier.row.receivingEarlier = true)
      (who : ι) (hwho : who ≠ observer) (action : Bool)
      (endpoint_gain :
        let receiving := Function.update profile mover target
        let endpointProfile := Function.update receiving observer
          (quittingPureTimeBehaviorStrategy reward observer
            carrier.row.receivingWitness)
        gamma * gain / (2 * quittingRewardBound reward) ≤
          carrier.row.liveMass *
            (quittingRootExpectedPayoff reward 0
                (Function.update
                  (quittingProfileLiveRoot reward endpointProfile
                    carrier.row.start) who (PMF.pure action)) who -
              quittingRootExpectedPayoff reward 0
                (quittingProfileLiveRoot reward endpointProfile
                  carrier.row.start) who))
      (behavior_gain :
        let receiving := Function.update profile mover target
        let endpointProfile := Function.update receiving observer
          (quittingPureTimeBehaviorStrategy reward observer
            carrier.row.receivingWitness)
        let deviation := quittingStagePureEndpointBehaviorDeviation reward
          endpointProfile who carrier.row.start action
        gamma * gain / (2 * quittingRewardBound reward) ≤
          quittingTerminalPayoff reward
              (Function.update endpointProfile who deviation) who -
            quittingTerminalPayoff reward endpointProfile who) :
      QuittingStoppingLawCurvatureStrategicDispatch carrier

/-- Dispatch a data-bearing curvature witness according to its exact temporal
orientation.  The source approximation remains stored in the carrier; the
earlier-receiving branch consumes the endpoint approximation. -/
theorem QuittingStoppingLawCurvaturePaidWitness.nonempty_strategicDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {mover observer : ι}
    {target : (quittingGame reward).BehaviorStrategy mover}
    {sourceError endpointError gain gamma : ℝ}
    (carrier : QuittingStoppingLawCurvaturePaidWitness reward profile mover
      observer target sourceError endpointError gain)
    (hgain : 0 < gain) (hgamma : 0 < gamma)
    (hgap : HasTerminalExploitabilityGap reward gamma)
    (hsmall : endpointError <
      gamma * gain / (2 * quittingRewardBound reward)) :
    Nonempty (QuittingStoppingLawCurvatureStrategicDispatch
      (gamma := gamma) carrier) := by
  cases htime : carrier.row.receivingEarlier with
  | false =>
      obtain ⟨deviation, hdeviation⟩ :=
        carrier.row.exists_ownerDeviation_of_receivingLater htime
      exact ⟨.owner htime deviation hdeviation⟩
  | true =>
      obtain ⟨who, hwho, action, hendpoint, hbehavior⟩ :=
        carrier.row.exists_outsiderDeviation_of_receivingEarlier htime hgain
          hgamma hgap carrier.receiving_approx hsmall
      exact ⟨.outsider htime who hwho action hendpoint hbehavior⟩

/-- The hard-coded curvature ratios used by the earlier row-only consumer
satisfy the terminal-gap smallness test exactly when the reward bound is
strictly below twice the gap. -/
theorem fixedCurvatureRatios_terminalGapBudget_iff
    {curvature gamma bound : ℝ}
    (hcurvature : 0 < curvature) (hbound : 0 < bound) :
    curvature / 16 < gamma * (curvature / 4) / (2 * bound) ↔
      bound < 2 * gamma := by
  constructor
  · intro h
    have h' := (lt_div_iff₀ (by positivity : 0 < 2 * bound)).mp h
    by_contra hnot
    have hproduct :
        0 ≤ curvature * (bound - 2 * gamma) :=
      mul_nonneg hcurvature.le (sub_nonneg.mpr (le_of_not_gt hnot))
    nlinarith
  · intro h
    apply (lt_div_iff₀ (by positivity : 0 < 2 * bound)).mpr
    have hproduct : 0 < curvature * (2 * gamma - bound) :=
      mul_pos hcurvature (sub_pos.mpr h)
    nlinarith

namespace QuittingCounterexampleStoppingLawFrontier

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {regime : QuittingCounterexampleRegime reward}
  {frontier : QuittingCounterexampleStoppingLawFrontier regime}
  {mover : {who // who ∈ frontier.active}}

namespace FullResetEndpointCluster

/-- Parameterized eventual temporal dispatch of an off-minimum full-reset
curvature coordinate.  Any positive gain, source budget, and endpoint error
whose sum is below the limiting curvature produce the paid carrier.  If the
endpoint error also meets the terminal-gap threshold, every sufficiently late
rank yields either the owner or outsider strategic dispatch.

The conclusion remains attached to the literal source/full-reset profiles; it
does not re-enter the resulting outsider endpoint into the tangent family. -/
theorem exists_eventually_curvatureStrategicDispatch
    (endpoint : FullResetEndpointCluster frontier mover)
    (hflat : ∑ observer, frontier.tangent mover observer = 0)
    (hseparated : quittingTerminalSemanticDebtSum frontier.base <
      quittingTerminalSemanticDebtSum endpoint.cluster)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : HasTerminalExploitabilityGap reward gamma) :
    ∃ observer : ι, ∃ curvature : ℝ,
      observer ≠ mover.1 ∧ 0 < curvature ∧
      ∀ gain sourceBudget endpointError : ℝ,
        0 < gain → 0 < sourceBudget → 0 < endpointError →
        gain + endpointError + sourceBudget < curvature →
        endpointError <
          gamma * gain / (2 * quittingRewardBound reward) →
        ∀ᶠ rank in atTop,
          ∃ carrier : QuittingStoppingLawCurvaturePaidWitness reward
              (frontier.profiles (frontier.subseq (endpoint.subseq rank)))
              mover.1 observer
              (frontier.bestResponse mover
                (frontier.subseq (endpoint.subseq rank)))
              (frontier.lambda (frontier.subseq (endpoint.subseq rank)) *
                sourceBudget) endpointError gain,
            Nonempty (QuittingStoppingLawCurvatureStrategicDispatch
              (gamma := gamma) carrier) := by
  obtain ⟨observer, hne, hlower⟩ :=
    endpoint.exists_curvature_ge_opponentAverage hflat
  let curvature := endpoint.curvature observer
  have hcardPos : 0 < ((Finset.univ.erase mover.1).card : ℝ) := by
    obtain ⟨positiveObserver, hpositiveNe, _hpositive⟩ :=
      frontier.exists_positiveOffDiagonal mover.2
    exact_mod_cast Finset.card_pos.mpr
      ⟨positiveObserver, Finset.mem_erase.mpr
        ⟨hpositiveNe, Finset.mem_univ positiveObserver⟩⟩
  have hcurvature : 0 < curvature := by
    have hexcess : 0 < quittingTerminalSemanticDebtSum endpoint.cluster -
        quittingTerminalSemanticDebtSum frontier.base := sub_pos.mpr hseparated
    have haverage : 0 <
        (quittingTerminalSemanticDebtSum endpoint.cluster -
          quittingTerminalSemanticDebtSum frontier.base) /
          ((Finset.univ.erase mover.1).card : ℝ) :=
      div_pos hexcess hcardPos
    exact haverage.trans_le hlower
  refine ⟨observer, curvature, hne, hcurvature, ?_⟩
  intro gain sourceBudget endpointError hgain hsourceBudget hendpointError
    hsum hsmall
  have heventually := (endpoint.normalizedCurvature_tendsto observer).eventually
    (Ioi_mem_nhds hsum)
  filter_upwards [heventually] with rank hrank
  let lambda := frontier.lambda (frontier.subseq (endpoint.subseq rank))
  have hlambda : 0 < lambda :=
    frontier.lambda_pos (frontier.subseq (endpoint.subseq rank))
  have hlambdaOne : lambda ≤ 1 :=
    frontier.lambda_le_one (frontier.subseq (endpoint.subseq rank))
  let sourceError := lambda * sourceBudget
  have hsourceError : 0 < sourceError := mul_pos hlambda hsourceBudget
  have hsourceTerm :
      (1 - lambda) * sourceBudget ≤ sourceBudget := by
    nlinarith [mul_nonneg hlambda.le hsourceBudget.le]
  have hsumRank :
      gain + endpointError + (1 - lambda) * sourceBudget <
        quittingTerminalSemanticDebtChange
            (frontier.sourcePair (endpoint.subseq rank))
            (frontier.fullResetPair mover (endpoint.subseq rank)) observer -
          quittingStoppingLawNormalizedDebtDirection reward
            (frontier.profiles (frontier.subseq (endpoint.subseq rank)))
            mover.1
            (frontier.bestResponse mover
              (frontier.subseq (endpoint.subseq rank)))
            lambda hlambda.le hlambdaOne observer := by
    have hsumLe :
        gain + endpointError + (1 - lambda) * sourceBudget ≤
          gain + endpointError + sourceBudget := by
      linarith
    exact lt_of_le_of_lt hsumLe hrank
  have hbudget :
      lambda * (gain + endpointError) + (1 - lambda) * sourceError ≤
        lambda *
          (quittingTerminalSemanticDebtChange
              (frontier.sourcePair (endpoint.subseq rank))
              (frontier.fullResetPair mover (endpoint.subseq rank)) observer -
            quittingStoppingLawNormalizedDebtDirection reward
              (frontier.profiles (frontier.subseq (endpoint.subseq rank)))
              mover.1
              (frontier.bestResponse mover
                (frontier.subseq (endpoint.subseq rank)))
              lambda hlambda.le hlambdaOne observer) := by
    dsimp only [sourceError]
    nlinarith [mul_pos hlambda (sub_pos.mpr hsumRank)]
  obtain ⟨carrier⟩ := exists_quittingStoppingLawCurvaturePaidWitness
    reward (frontier.profiles (frontier.subseq (endpoint.subseq rank)))
    mover.1 observer
    (frontier.bestResponse mover (frontier.subseq (endpoint.subseq rank)))
    lambda sourceError endpointError gain hne hlambda hlambdaOne
    hsourceError hendpointError hgain hbudget
  exact ⟨carrier, carrier.nonempty_strategicDispatch
    hgain hgamma hgap hsmall⟩

end FullResetEndpointCluster

end QuittingCounterexampleStoppingLawFrontier

end GameTheory
