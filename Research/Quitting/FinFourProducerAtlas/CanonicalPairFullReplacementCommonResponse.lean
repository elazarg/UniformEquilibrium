/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourProducerAtlas.CanonicalPairFullReplacementSourceRegeneration
import Research.Quitting.StoppingLawMixtureFiniteWitnessPassport
import Research.Quitting.StoppingLawMixtureWitnessStrata

/-!
# Common pure-time responses for renewable Fin4 full replacement

A minimum-fibre stopping-law chord admits one pure-time response which is
simultaneously near-best at both horizontal endpoints.  The endpoint cap
movement is therefore approximated by the payoff movement of that same literal
response, with an error controlled by the two endpoint debt excesses.

The Fin4 adapter applies this certificate to the source-preserving
full-replacement sequence used by the renewable support descent.  Both endpoint
excesses vanish on the retained subsequence, so the common-response error tends
to zero.  This supplies source-matched cap control for one selected response;
it does not bound every behavioral response across the horizontal seam and does
not itself give a backward compiler or a uniform-equilibrium payoff.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Near-minimum common pure-time responses -/

/-- One pure-time response which is simultaneously close to the unrestricted
best-response envelope at both endpoints of a stopping-law chord.  The two
stored gaps are cap regrets, written as semantic debt minus deviation gain. -/
structure QuittingStoppingLawNearMinimumCommonPureTimeResponse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (minimum : QuittingTerminalSemanticPair ι) (eta : ℝ) where
  choice : Option ℕ
  sourceGap_le :
    quittingPureTimeDebtAtlasGap reward
        (Function.update profile mover source) observer choice ≤
      (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (Function.update profile mover source)) -
          quittingTerminalSemanticDebtSum minimum) +
        (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (Function.update profile mover target)) -
          quittingTerminalSemanticDebtSum minimum) +
        2 * eta
  targetGap_le :
    quittingPureTimeDebtAtlasGap reward
        (Function.update profile mover target) observer choice ≤
      (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (Function.update profile mover source)) -
          quittingTerminalSemanticDebtSum minimum) +
        (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (Function.update profile mover target)) -
          quittingTerminalSemanticDebtSum minimum) +
        2 * eta

namespace QuittingStoppingLawNearMinimumCommonPureTimeResponse

/-- The common response also approximates the horizontal cap displacement.
The factor two only sums its two nonnegative endpoint regrets. -/
theorem abs_capDifference_sub_responseDifference_le
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {mover observer : ι}
    {source target : (quittingGame reward).BehaviorStrategy mover}
    {minimum : QuittingTerminalSemanticPair ι} {eta error : ℝ}
    (response : QuittingStoppingLawNearMinimumCommonPureTimeResponse
      reward profile mover observer source target minimum eta)
    (herror :
      (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (Function.update profile mover source)) -
          quittingTerminalSemanticDebtSum minimum) +
        (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (Function.update profile mover target)) -
          quittingTerminalSemanticDebtSum minimum) +
        2 * eta ≤ error) :
    |(quittingContinuationBestResponseValue reward
          (Function.update profile mover target) observer -
        quittingContinuationBestResponseValue reward
          (Function.update profile mover source) observer) -
      (quittingTerminalPayoff reward
          (Function.update (Function.update profile mover target) observer
            (quittingPureTimeBehaviorStrategy reward observer response.choice))
          observer -
        quittingTerminalPayoff reward
          (Function.update (Function.update profile mover source) observer
            (quittingPureTimeBehaviorStrategy reward observer response.choice))
          observer)| ≤ 2 * error := by
  have hsourceNonneg : 0 ≤ quittingPureTimeDebtAtlasGap reward
      (Function.update profile mover source) observer response.choice := by
    unfold quittingPureTimeDebtAtlasGap quittingPureTimeDeviationGain
      quittingTerminalSemanticDebt quittingTerminalSemanticPair
    have hcap := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward (Function.update profile mover source) observer
        (quittingPureTimeBehaviorStrategy reward observer response.choice)
    linarith
  have htargetNonneg : 0 ≤ quittingPureTimeDebtAtlasGap reward
      (Function.update profile mover target) observer response.choice := by
    unfold quittingPureTimeDebtAtlasGap quittingPureTimeDeviationGain
      quittingTerminalSemanticDebt quittingTerminalSemanticPair
    have hcap := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward (Function.update profile mover target) observer
        (quittingPureTimeBehaviorStrategy reward observer response.choice)
    linarith
  have hsource : quittingPureTimeDebtAtlasGap reward
      (Function.update profile mover source) observer response.choice ≤ error :=
    response.sourceGap_le.trans herror
  have htarget : quittingPureTimeDebtAtlasGap reward
      (Function.update profile mover target) observer response.choice ≤ error :=
    response.targetGap_le.trans herror
  unfold quittingPureTimeDebtAtlasGap quittingPureTimeDeviationGain
    quittingTerminalSemanticDebt quittingTerminalSemanticPair at
      hsourceNonneg htargetNonneg hsource htarget ⊢
  rw [abs_le]
  constructor <;> linarith

end QuittingStoppingLawNearMinimumCommonPureTimeResponse

/-- Near a global minimum, the midpoint of any complete stopping-law chord has
one pure-time response which is near-best at both endpoints.  The error is the
sum of the two endpoint total-debt excesses plus the midpoint response error.
No best-response supremum is assumed attained. -/
theorem nonempty_quittingStoppingLawNearMinimumCommonPureTimeResponse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hne : observer ≠ mover)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (eta : ℝ) (heta : 0 < eta) :
    Nonempty (QuittingStoppingLawNearMinimumCommonPureTimeResponse
      reward profile mover observer source target minimum eta) := by
  let sourceProfile := Function.update profile mover source
  let targetProfile := Function.update profile mover target
  let mixedProfile := Function.update profile mover
    (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
      (1 / 2 : ℝ) (by norm_num) (by norm_num))
  let sourcePair := quittingTerminalSemanticPair reward sourceProfile
  let targetPair := quittingTerminalSemanticPair reward targetProfile
  let mixedPair := quittingTerminalSemanticPair reward mixedProfile
  obtain ⟨choice, hchoice⟩ :=
    exists_quittingPureTime_terminalPayoff_ge_bestResponse_sub
      reward mixedProfile observer eta heta
  let sourceGap := quittingPureTimeDebtAtlasGap reward sourceProfile observer choice
  let targetGap := quittingPureTimeDebtAtlasGap reward targetProfile observer choice
  let mixedGap := quittingPureTimeDebtAtlasGap reward mixedProfile observer choice
  let coordinateGap :=
    (quittingTerminalSemanticDebt sourcePair observer +
        quittingTerminalSemanticDebt targetPair observer) / 2 -
      quittingTerminalSemanticDebt mixedPair observer
  have hsourceGapNonneg : 0 ≤ sourceGap := by
    dsimp only [sourceGap]
    unfold quittingPureTimeDebtAtlasGap quittingPureTimeDeviationGain
      quittingTerminalSemanticDebt quittingTerminalSemanticPair
    have hcap := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward sourceProfile observer
        (quittingPureTimeBehaviorStrategy reward observer choice)
    linarith
  have htargetGapNonneg : 0 ≤ targetGap := by
    dsimp only [targetGap]
    unfold quittingPureTimeDebtAtlasGap quittingPureTimeDeviationGain
      quittingTerminalSemanticDebt quittingTerminalSemanticPair
    have hcap := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward targetProfile observer
        (quittingPureTimeBehaviorStrategy reward observer choice)
    linarith
  have hmixedGapLe : mixedGap ≤ eta := by
    dsimp only [mixedGap]
    unfold quittingPureTimeDebtAtlasGap quittingPureTimeDeviationGain
      quittingTerminalSemanticDebt quittingTerminalSemanticPair
    linarith
  have hcoordinateGapNonneg : 0 ≤ coordinateGap := by
    dsimp only [coordinateGap, sourcePair, targetPair, mixedPair,
      sourceProfile, targetProfile, mixedProfile]
    have hconvex := quittingTerminalSemanticDebt_stoppingLawMixture_le
      reward profile mover observer source target (1 / 2 : ℝ)
        (by norm_num) (by norm_num)
    linarith
  let gap : ι → ℝ := fun who ↦
    (quittingTerminalSemanticDebt sourcePair who +
        quittingTerminalSemanticDebt targetPair who) / 2 -
      quittingTerminalSemanticDebt mixedPair who
  have hgapNonneg : ∀ who, 0 ≤ gap who := by
    intro who
    dsimp only [gap, sourcePair, targetPair, mixedPair,
      sourceProfile, targetProfile, mixedProfile]
    have hconvex := quittingTerminalSemanticDebt_stoppingLawMixture_le
      reward profile mover who source target (1 / 2 : ℝ)
        (by norm_num) (by norm_num)
    linarith
  have hgapSum : (∑ who, gap who) =
      (quittingTerminalSemanticDebtSum sourcePair +
          quittingTerminalSemanticDebtSum targetPair) / 2 -
        quittingTerminalSemanticDebtSum mixedPair := by
    unfold gap quittingTerminalSemanticDebtSum
    rw [Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_add_distrib]
  have hmixedMinimum : quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum mixedPair := by
    apply hminimum mixedPair
    dsimp only [mixedPair, mixedProfile]
    exact quittingTerminalSemanticPair_mem_carrier reward _
  have hcoordinateGapLe : coordinateGap ≤
      ((quittingTerminalSemanticDebtSum sourcePair -
          quittingTerminalSemanticDebtSum minimum) +
        (quittingTerminalSemanticDebtSum targetPair -
          quittingTerminalSemanticDebtSum minimum)) / 2 := by
    calc
      coordinateGap = gap observer := rfl
      _ ≤ ∑ who, gap who :=
        Finset.single_le_sum (fun who _ ↦ hgapNonneg who)
          (Finset.mem_univ observer)
      _ = (quittingTerminalSemanticDebtSum sourcePair +
          quittingTerminalSemanticDebtSum targetPair) / 2 -
            quittingTerminalSemanticDebtSum mixedPair := hgapSum
      _ ≤ ((quittingTerminalSemanticDebtSum sourcePair -
            quittingTerminalSemanticDebtSum minimum) +
          (quittingTerminalSemanticDebtSum targetPair -
            quittingTerminalSemanticDebtSum minimum)) / 2 := by
        linarith
  have hgainAffine := quittingPureTimeDeviationGain_stoppingLawMixture_eq
    reward profile mover observer hne source target choice (1 / 2 : ℝ)
      (by norm_num) (by norm_num)
  have hgapIdentity : sourceGap + targetGap =
      2 * coordinateGap + 2 * mixedGap := by
    dsimp only [sourceGap, targetGap, mixedGap, coordinateGap,
      sourcePair, targetPair, mixedPair, sourceProfile, targetProfile,
      mixedProfile]
    unfold quittingPureTimeDebtAtlasGap
    rw [hgainAffine]
    ring
  have hsumGapLe : sourceGap + targetGap ≤
      (quittingTerminalSemanticDebtSum sourcePair -
          quittingTerminalSemanticDebtSum minimum) +
        (quittingTerminalSemanticDebtSum targetPair -
          quittingTerminalSemanticDebtSum minimum) +
        2 * eta := by
    rw [hgapIdentity]
    linarith
  refine ⟨{
    choice := choice
    sourceGap_le := ?_
    targetGap_le := ?_ }⟩
  · dsimp only [sourceGap, sourcePair, targetPair, sourceProfile, targetProfile]
    linarith
  · dsimp only [targetGap, sourcePair, targetPair, sourceProfile, targetProfile]
    linarith

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ}

/-! ## Automatic common-response control of the horizontal seam -/

namespace QuittingPositiveMinimumDebtTangentFamily.FullReplacementCluster

variable
  {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
  {mover : {who // who ∈ frontier.positiveDebtSupport}}

/-- Reciprocal midpoint-response error. -/
def commonResponseEta
    (_endpoint : FullReplacementCluster frontier mover) (rank : ℕ) : ℝ :=
  1 / (rank + 1 : ℝ)

/-- The exact two-endpoint excess which pays for a common response. -/
def commonResponseError
    (endpoint : FullReplacementCluster frontier mover) (rank : ℕ) : ℝ :=
  (quittingTerminalSemanticDebtSum
        (frontier.sourcePair (endpoint.subseq rank)) -
      quittingTerminalSemanticDebtSum frontier.base) +
    (quittingTerminalSemanticDebtSum
        (frontier.fullReplacementPair mover (endpoint.subseq rank)) -
      quittingTerminalSemanticDebtSum frontier.base) +
    2 * endpoint.commonResponseEta rank

/-- A pure-time common response for every non-mover and every retained rank.
The response is selected at the midpoint of the literal source-to-full-reset
stopping-law chord. -/
structure FinFourFullReplacementCommonResponsePassport
    (endpoint : FullReplacementCluster frontier mover)
    (hminimumFiber : quittingTerminalSemanticDebtSum endpoint.cluster =
      quittingTerminalSemanticDebtSum frontier.base) where
  response : ∀ rank (observer : {who : Fin 4 // who ≠ mover.1}),
    QuittingStoppingLawNearMinimumCommonPureTimeResponse reward
      (frontier.source (endpoint.subseq rank)) mover.1 observer.1
      (frontier.source (endpoint.subseq rank) mover.1)
      (frontier.replacement mover (endpoint.subseq rank)) frontier.base
      (endpoint.commonResponseEta rank)

namespace FinFourFullReplacementCommonResponsePassport

variable
  {endpoint : FullReplacementCluster frontier mover}
  {hminimumFiber : quittingTerminalSemanticDebtSum endpoint.cluster =
    quittingTerminalSemanticDebtSum frontier.base}

/-- The common-response error is nonnegative at every actual rank. -/
theorem error_nonneg
    (_passport : FinFourFullReplacementCommonResponsePassport endpoint
      hminimumFiber) (rank : ℕ) :
    0 ≤ endpoint.commonResponseError rank := by
  have hsource := frontier.base_minimum
    (frontier.sourcePair (endpoint.subseq rank))
    (quittingTerminalSemanticPair_mem_carrier reward _)
  have htarget := frontier.base_minimum
    (frontier.fullReplacementPair mover (endpoint.subseq rank))
    (quittingTerminalSemanticPair_mem_carrier reward _)
  have heta : 0 ≤ endpoint.commonResponseEta rank := by
    unfold commonResponseEta
    positivity
  unfold commonResponseError
  linarith

/-- Both endpoint excesses vanish, so the common-response error tends to
zero on the exact full-replacement subsequence. -/
theorem error_tendsto_zero
    (_passport : FinFourFullReplacementCommonResponsePassport endpoint
      hminimumFiber) :
    Tendsto endpoint.commonResponseError atTop (nhds 0) := by
  have hsourcePair : Tendsto
      (fun rank ↦ frontier.sourcePair (endpoint.subseq rank)) atTop
      (nhds frontier.base) := by
    exact frontier.source_tendsto.comp
      endpoint.subseq_strictMono.tendsto_atTop
  have hsourceDebt : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
        (frontier.sourcePair (endpoint.subseq rank))) atTop
      (nhds (quittingTerminalSemanticDebtSum frontier.base)) :=
    continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
      hsourcePair
  have htargetDebt : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
        (frontier.fullReplacementPair mover (endpoint.subseq rank))) atTop
      (nhds (quittingTerminalSemanticDebtSum frontier.base)) := by
    have hraw :=
      continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
        endpoint.fullReplacement_tendsto
    rwa [hminimumFiber] at hraw
  have heta : Tendsto endpoint.commonResponseEta atTop (nhds 0) := by
    unfold commonResponseEta
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hsourceExcess := hsourceDebt.sub_const
    (quittingTerminalSemanticDebtSum frontier.base)
  have htargetExcess := htargetDebt.sub_const
    (quittingTerminalSemanticDebtSum frontier.base)
  have htotal := (hsourceExcess.add htargetExcess).add (heta.const_mul 2)
  simpa only [commonResponseError, sub_self, zero_add, mul_zero] using htotal

/-- The selected pure-time response is near-best at the literal source. -/
theorem sourceGap_le_error
    (passport : FinFourFullReplacementCommonResponsePassport endpoint
      hminimumFiber)
    (rank : ℕ) (observer : {who : Fin 4 // who ≠ mover.1}) :
    quittingPureTimeDebtAtlasGap reward
        (frontier.source (endpoint.subseq rank)) observer.1
        (passport.response rank observer).choice ≤
      endpoint.commonResponseError rank := by
  have h := (passport.response rank observer).sourceGap_le
  simpa only [Function.update_eq_self, commonResponseError, sourcePair,
    fullReplacementPair, fullReplacementProfile] using h

/-- The same response is near-best at the literal full-replacement endpoint. -/
theorem targetGap_le_error
    (passport : FinFourFullReplacementCommonResponsePassport endpoint
      hminimumFiber)
    (rank : ℕ) (observer : {who : Fin 4 // who ≠ mover.1}) :
    quittingPureTimeDebtAtlasGap reward
        (frontier.fullReplacementProfile mover (endpoint.subseq rank))
        observer.1 (passport.response rank observer).choice ≤
      endpoint.commonResponseError rank := by
  have h := (passport.response rank observer).targetGap_le
  simpa only [Function.update_eq_self, commonResponseError, sourcePair,
    fullReplacementPair, fullReplacementProfile] using h

/-- Consequently one literal response approximates the horizontal cap
movement, uniformly along the selected sequence. -/
theorem abs_capDifference_sub_responseDifference_le
    (passport : FinFourFullReplacementCommonResponsePassport endpoint
      hminimumFiber)
    (rank : ℕ) (observer : {who : Fin 4 // who ≠ mover.1}) :
    |(quittingContinuationBestResponseValue reward
          (frontier.fullReplacementProfile mover (endpoint.subseq rank))
          observer.1 -
        quittingContinuationBestResponseValue reward
          (frontier.source (endpoint.subseq rank)) observer.1) -
      (quittingTerminalPayoff reward
          (Function.update
            (frontier.fullReplacementProfile mover (endpoint.subseq rank))
            observer.1
            (quittingPureTimeBehaviorStrategy reward observer.1
              (passport.response rank observer).choice)) observer.1 -
        quittingTerminalPayoff reward
          (Function.update (frontier.source (endpoint.subseq rank)) observer.1
            (quittingPureTimeBehaviorStrategy reward observer.1
              (passport.response rank observer).choice)) observer.1)| ≤
      2 * endpoint.commonResponseError rank := by
  have h :=
    (passport.response rank observer).abs_capDifference_sub_responseDifference_le
      (error := endpoint.commonResponseError rank) le_rfl
  simpa only [Function.update_eq_self, sourcePair, fullReplacementPair,
    fullReplacementProfile] using h

end FinFourFullReplacementCommonResponsePassport

/-- Minimum-fibre full replacement automatically supplies the common-response
passport.  This is weaker than controlling every response across the seam,
but it controls the unrestricted cap by one source-matched pure-time witness. -/
theorem nonempty_commonResponsePassport
    (endpoint : FullReplacementCluster frontier mover)
    (hminimumFiber : quittingTerminalSemanticDebtSum endpoint.cluster =
      quittingTerminalSemanticDebtSum frontier.base) :
    Nonempty (FinFourFullReplacementCommonResponsePassport endpoint
      hminimumFiber) := by
  refine ⟨{ response := ?_ }⟩
  intro rank observer
  exact Classical.choice
    (nonempty_quittingStoppingLawNearMinimumCommonPureTimeResponse
      reward (frontier.source (endpoint.subseq rank)) mover.1 observer.1
      observer.2 (frontier.source (endpoint.subseq rank) mover.1)
      (frontier.replacement mover (endpoint.subseq rank)) frontier.base
      frontier.base_minimum (endpoint.commonResponseEta rank) (by
        unfold commonResponseEta
        positivity))

end QuittingPositiveMinimumDebtTangentFamily.FullReplacementCluster

end GameTheory
