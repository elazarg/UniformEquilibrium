/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.StoppingLawMixtureWitnessStrata
import
  UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.MinimumFiberSupportDrop
import
  UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawMinimumFiberAffine

/-!
# Common cap responses across a minimum-fibre full replacement

A literal full replacement can change every non-mover's behavioral cap, so
source-faithful causalization alone does not transport responses across that
horizontal seam.  On a minimum-fibre full-replacement cluster, however, the
convexity defect of the half stopping-law mixture tends to zero.

Choose an approximate best response at the half profile.  Fixed-response
payoffs are affine in the mover's stopping law, while the two endpoint regrets
are nonnegative.  Their average is therefore bounded by the half-profile
optimization error plus the vanishing convexity defect.  The same actual
behavioral response is consequently asymptotically optimal at both endpoints.

This is a cap/response compiler across the parent-to-full-replacement seam.  It
does not bound the gain distortion of every supplied response and does not
identify the endpoint caps with the source caps.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingPositiveMinimumDebtTangentFamily

/-- The literal half stopping-law profile between a tangent source and its
full replacement endpoint. -/
def fullReplacementHalfProfile
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport})
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingStoppingLawResetProfile reward (frontier.source rank) mover.1
    (frontier.replacement mover rank) (1 / 2 : ℝ) (by norm_num) (by norm_num)

/-- Convexity defect of one observer's behavioral cap at the literal half
profile. -/
def fullReplacementHalfCapChordGap
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport})
    (observer : ι) (rank : ℕ) : ℝ :=
  (quittingContinuationBestResponseValue reward (frontier.source rank) observer +
      quittingContinuationBestResponseValue reward
        (frontier.fullReplacementProfile mover rank) observer) / 2 -
    quittingContinuationBestResponseValue reward
      (frontier.fullReplacementHalfProfile mover rank) observer

/-- Behavioral-cap convexity makes the half-profile chord gap nonnegative. -/
theorem fullReplacementHalfCapChordGap_nonneg
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport})
    (observer : ι) (rank : ℕ) :
    0 ≤ frontier.fullReplacementHalfCapChordGap mover observer rank := by
  have hconvex := quittingContinuationBestResponseValue_stoppingLawMixture_le
    reward (frontier.source rank) mover.1 observer
      (frontier.source rank mover.1) (frontier.replacement mover rank)
      (1 / 2 : ℝ) (by norm_num) (by norm_num)
  rw [Function.update_eq_self] at hconvex
  dsimp only [fullReplacementHalfCapChordGap, fullReplacementHalfProfile,
    quittingStoppingLawResetProfile, fullReplacementProfile]
  nlinarith

/-- Payoff affinity identifies the cap chord gap with the semantic-debt chord
gap. -/
theorem fullReplacementHalfCapChordGap_eq_debtChordGap
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport})
    (observer : ι) (rank : ℕ) :
    frontier.fullReplacementHalfCapChordGap mover observer rank =
      (quittingTerminalSemanticDebt (frontier.sourcePair rank) observer +
          quittingTerminalSemanticDebt
            (frontier.fullReplacementPair mover rank) observer) / 2 -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (frontier.fullReplacementHalfProfile mover rank)) observer := by
  have hpayoff := quittingTerminalPayoff_stoppingLawMixture_eq
    reward (frontier.source rank) mover.1 observer
      (frontier.source rank mover.1) (frontier.replacement mover rank)
      (1 / 2 : ℝ) (by norm_num) (by norm_num)
  rw [Function.update_eq_self] at hpayoff
  dsimp only [fullReplacementHalfCapChordGap, fullReplacementHalfProfile,
    quittingStoppingLawResetProfile, sourcePair, fullReplacementPair,
    fullReplacementProfile, quittingTerminalSemanticDebt,
    quittingTerminalSemanticPair]
  nlinarith

/-- At every literal tangent rank, the cap chord gap is bounded by the average
of the source and endpoint excesses above the exact minimum. -/
theorem fullReplacementHalfCapChordGap_le_averageExcess
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport})
    (observer : ι) (rank : ℕ) :
    frontier.fullReplacementHalfCapChordGap mover observer rank ≤
      ((quittingTerminalSemanticDebtSum (frontier.sourcePair rank) -
            quittingTerminalSemanticDebtSum frontier.base) +
          (quittingTerminalSemanticDebtSum
              (frontier.fullReplacementPair mover rank) -
            quittingTerminalSemanticDebtSum frontier.base)) / 2 := by
  let epsilon := quittingTerminalSemanticDebtSum (frontier.sourcePair rank) -
    quittingTerminalSemanticDebtSum frontier.base
  have hnear : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum (frontier.sourcePair rank) ≤
        quittingTerminalSemanticDebtSum candidate + epsilon := by
    intro candidate hcandidate
    have hminimum := frontier.base_minimum candidate hcandidate
    dsimp only [epsilon]
    linarith
  have hdebt :=
    quittingTerminalSemanticDebt_stoppingLawMixture_chordGap_le_nearMinimum
      reward (frontier.source rank) mover.1 observer
        (frontier.source rank mover.1) (frontier.replacement mover rank)
        (1 / 2 : ℝ) epsilon (by norm_num) (by norm_num) hnear
  have hbound :
      (quittingTerminalSemanticDebt (frontier.sourcePair rank) observer +
            quittingTerminalSemanticDebt
              (frontier.fullReplacementPair mover rank) observer) / 2 -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (frontier.fullReplacementHalfProfile mover rank)) observer ≤
        epsilon +
          (quittingTerminalSemanticDebtSum
              (frontier.fullReplacementPair mover rank) -
            quittingTerminalSemanticDebtSum (frontier.sourcePair rank)) / 2 := by
    dsimp only at hdebt
    rw [Function.update_eq_self] at hdebt
    dsimp only [sourcePair, fullReplacementPair, fullReplacementProfile,
      fullReplacementHalfProfile, quittingStoppingLawResetProfile] at hdebt
    nlinarith [hdebt.2]
  rw [frontier.fullReplacementHalfCapChordGap_eq_debtChordGap mover observer rank]
  dsimp only [epsilon] at hbound
  linarith

namespace FullReplacementCluster

variable {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
  {mover : {who // who ∈ frontier.positiveDebtSupport}}

/-- On a same-minimum full-replacement cluster, every observer's half-profile
cap chord gap tends to zero along the cluster's literal subsequence. -/
theorem fullReplacementHalfCapChordGap_tendsto_zero
    (endpoint : FullReplacementCluster frontier mover)
    (hminimumFiber : quittingTerminalSemanticDebtSum endpoint.cluster =
      quittingTerminalSemanticDebtSum frontier.base)
    (observer : ι) :
    Tendsto (fun rank ↦ frontier.fullReplacementHalfCapChordGap mover observer
      (endpoint.subseq rank)) atTop (nhds 0) := by
  have hsourcePair : Tendsto
      (fun rank ↦ frontier.sourcePair (endpoint.subseq rank)) atTop
      (nhds frontier.base) := by
    simpa only [sourcePair] using
      frontier.source_tendsto.comp endpoint.subseq_strictMono.tendsto_atTop
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
    have h :=
      continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
        endpoint.fullReplacement_tendsto
    rw [hminimumFiber] at h
    exact h
  have hsourceExcess : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
          (frontier.sourcePair (endpoint.subseq rank)) -
        quittingTerminalSemanticDebtSum frontier.base) atTop (nhds 0) := by
    simpa using hsourceDebt.sub_const
      (quittingTerminalSemanticDebtSum frontier.base)
  have htargetExcess : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
          (frontier.fullReplacementPair mover (endpoint.subseq rank)) -
        quittingTerminalSemanticDebtSum frontier.base) atTop (nhds 0) := by
    simpa using htargetDebt.sub_const
      (quittingTerminalSemanticDebtSum frontier.base)
  have haverage : Tendsto (fun rank ↦
      ((quittingTerminalSemanticDebtSum
              (frontier.sourcePair (endpoint.subseq rank)) -
            quittingTerminalSemanticDebtSum frontier.base) +
          (quittingTerminalSemanticDebtSum
              (frontier.fullReplacementPair mover (endpoint.subseq rank)) -
            quittingTerminalSemanticDebtSum frontier.base)) / 2) atTop
      (nhds 0) := by
    simpa using (hsourceExcess.add htargetExcess).div_const 2
  apply squeeze_zero'
  · exact Eventually.of_forall fun rank ↦
      frontier.fullReplacementHalfCapChordGap_nonneg mover observer
        (endpoint.subseq rank)
  · exact Eventually.of_forall fun rank ↦
      frontier.fullReplacementHalfCapChordGap_le_averageExcess mover observer
        (endpoint.subseq rank)
  · exact haverage

/-- Positive tolerance used to select an actual best response at each half
profile. -/
def commonResponseTolerance (_endpoint : FullReplacementCluster frontier mover)
    (rank : ℕ) : ℝ :=
  1 / ((rank : ℝ) + 1)

theorem commonResponseTolerance_pos
    (endpoint : FullReplacementCluster frontier mover) (rank : ℕ) :
    0 < endpoint.commonResponseTolerance rank := by
  simp only [commonResponseTolerance]
  positivity

theorem commonResponseTolerance_tendsto_zero
    (endpoint : FullReplacementCluster frontier mover) :
    Tendsto endpoint.commonResponseTolerance atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- An actual behavioral response chosen near-optimally at the half profile. -/
noncomputable def commonResponse
    (endpoint : FullReplacementCluster frontier mover)
    (observer : {who // who ≠ mover.1}) (rank : ℕ) :
    (quittingGame reward).BehaviorStrategy observer.1 :=
  Classical.choose (exists_quittingContinuation_deviation_ge_sub reward
    (frontier.fullReplacementHalfProfile mover (endpoint.subseq rank))
    observer.1 (endpoint.commonResponseTolerance_pos rank))

theorem commonResponse_half_approx
    (endpoint : FullReplacementCluster frontier mover)
    (observer : {who // who ≠ mover.1}) (rank : ℕ) :
    quittingContinuationBestResponseValue reward
          (frontier.fullReplacementHalfProfile mover (endpoint.subseq rank))
          observer.1 - endpoint.commonResponseTolerance rank ≤
      quittingTerminalPayoff reward
        (Function.update
          (frontier.fullReplacementHalfProfile mover (endpoint.subseq rank))
          observer.1 (endpoint.commonResponse observer rank)) observer.1 :=
  Classical.choose_spec (exists_quittingContinuation_deviation_ge_sub reward
    (frontier.fullReplacementHalfProfile mover (endpoint.subseq rank))
    observer.1 (endpoint.commonResponseTolerance_pos rank))

/-- A fixed non-mover response has exactly affine payoff across the source,
half, and full-replacement profiles. -/
theorem updatedHalfPayoff_eq_average
    (endpoint : FullReplacementCluster frontier mover)
    (observer : {who // who ≠ mover.1}) (rank : ℕ)
    (deviation : (quittingGame reward).BehaviorStrategy observer.1) :
    quittingTerminalPayoff reward
        (Function.update
          (frontier.fullReplacementHalfProfile mover (endpoint.subseq rank))
          observer.1 deviation) observer.1 =
      (quittingTerminalPayoff reward
            (Function.update (frontier.source (endpoint.subseq rank))
              observer.1 deviation) observer.1 +
          quittingTerminalPayoff reward
            (Function.update
              (frontier.fullReplacementProfile mover (endpoint.subseq rank))
              observer.1 deviation) observer.1) / 2 := by
  let index := endpoint.subseq rank
  let mixed := quittingStoppingLawMixtureBehaviorStrategy reward mover.1
    (frontier.source index mover.1) (frontier.replacement mover index)
      (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have haffine := quittingTerminalPayoff_stoppingLawMixture_eq
    reward (Function.update (frontier.source index) observer.1 deviation)
      mover.1 observer.1 (frontier.source index mover.1)
      (frontier.replacement mover index) (1 / 2 : ℝ)
      (by norm_num) (by norm_num)
  have hcommuteSource :
      Function.update
          (Function.update (frontier.source index) observer.1 deviation)
          mover.1 (frontier.source index mover.1) =
        Function.update
          (Function.update (frontier.source index) mover.1
            (frontier.source index mover.1)) observer.1 deviation :=
    Function.update_comm observer.2 deviation
      (frontier.source index mover.1) (frontier.source index)
  have hcommuteTarget :
      Function.update
          (Function.update (frontier.source index) observer.1 deviation)
          mover.1 (frontier.replacement mover index) =
        Function.update
          (Function.update (frontier.source index) mover.1
            (frontier.replacement mover index)) observer.1 deviation :=
    Function.update_comm observer.2 deviation
      (frontier.replacement mover index) (frontier.source index)
  have hcommuteMixed :
      Function.update
          (Function.update (frontier.source index) observer.1 deviation)
          mover.1 mixed =
        Function.update
          (Function.update (frontier.source index) mover.1 mixed)
            observer.1 deviation :=
    Function.update_comm observer.2 deviation mixed (frontier.source index)
  dsimp only [mixed] at hcommuteMixed
  rw [hcommuteSource, hcommuteTarget, hcommuteMixed] at haffine
  rw [Function.update_eq_self] at haffine
  dsimp only [index, fullReplacementHalfProfile,
    quittingStoppingLawResetProfile, fullReplacementProfile]
  nlinarith

/-- Endpoint regret bound for the common half-profile response. -/
def commonResponseError
    (endpoint : FullReplacementCluster frontier mover)
    (observer : {who // who ≠ mover.1}) (rank : ℕ) : ℝ :=
  2 * (frontier.fullReplacementHalfCapChordGap mover observer.1
    (endpoint.subseq rank) + endpoint.commonResponseTolerance rank)

theorem commonResponseError_nonneg
    (endpoint : FullReplacementCluster frontier mover)
    (observer : {who // who ≠ mover.1}) (rank : ℕ) :
    0 ≤ endpoint.commonResponseError observer rank := by
  dsimp only [commonResponseError]
  have hgap := frontier.fullReplacementHalfCapChordGap_nonneg mover observer.1
    (endpoint.subseq rank)
  have htolerance := (endpoint.commonResponseTolerance_pos rank).le
  nlinarith

/-- The common-response error vanishes on a minimum-fibre endpoint. -/
theorem commonResponseError_tendsto_zero
    (endpoint : FullReplacementCluster frontier mover)
    (hminimumFiber : quittingTerminalSemanticDebtSum endpoint.cluster =
      quittingTerminalSemanticDebtSum frontier.base)
    (observer : {who // who ≠ mover.1}) :
    Tendsto (endpoint.commonResponseError observer) atTop (nhds 0) := by
  have hsum :=
    (endpoint.fullReplacementHalfCapChordGap_tendsto_zero hminimumFiber
      observer.1).add endpoint.commonResponseTolerance_tendsto_zero
  simpa only [commonResponseError] using hsum.const_mul 2

/-- The selected common response is asymptotically optimal at the source
endpoint. -/
theorem sourceCap_le_commonResponsePayoff_add_error
    (endpoint : FullReplacementCluster frontier mover)
    (observer : {who // who ≠ mover.1}) (rank : ℕ) :
    quittingContinuationBestResponseValue reward
        (frontier.source (endpoint.subseq rank)) observer.1 ≤
      quittingTerminalPayoff reward
          (Function.update (frontier.source (endpoint.subseq rank)) observer.1
            (endpoint.commonResponse observer rank)) observer.1 +
        endpoint.commonResponseError observer rank := by
  have hhalf := endpoint.commonResponse_half_approx observer rank
  have haffine := endpoint.updatedHalfPayoff_eq_average observer rank
    (endpoint.commonResponse observer rank)
  have hsource := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward (frontier.source (endpoint.subseq rank)) observer.1
      (endpoint.commonResponse observer rank)
  have htarget := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward (frontier.fullReplacementProfile mover (endpoint.subseq rank))
      observer.1 (endpoint.commonResponse observer rank)
  dsimp only [commonResponseError, commonResponseTolerance,
    fullReplacementHalfCapChordGap] at hhalf haffine hsource htarget ⊢
  nlinarith

/-- The very same response is asymptotically optimal at the literal full
replacement endpoint. -/
theorem endpointCap_le_commonResponsePayoff_add_error
    (endpoint : FullReplacementCluster frontier mover)
    (observer : {who // who ≠ mover.1}) (rank : ℕ) :
    quittingContinuationBestResponseValue reward
        (frontier.fullReplacementProfile mover (endpoint.subseq rank))
        observer.1 ≤
      quittingTerminalPayoff reward
          (Function.update
            (frontier.fullReplacementProfile mover (endpoint.subseq rank))
            observer.1 (endpoint.commonResponse observer rank)) observer.1 +
        endpoint.commonResponseError observer rank := by
  have hhalf := endpoint.commonResponse_half_approx observer rank
  have haffine := endpoint.updatedHalfPayoff_eq_average observer rank
    (endpoint.commonResponse observer rank)
  have hsource := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward (frontier.source (endpoint.subseq rank)) observer.1
      (endpoint.commonResponse observer rank)
  have htarget := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward (frontier.fullReplacementProfile mover (endpoint.subseq rank))
      observer.1 (endpoint.commonResponse observer rank)
  dsimp only [commonResponseError, commonResponseTolerance,
    fullReplacementHalfCapChordGap] at hhalf haffine hsource htarget ⊢
  nlinarith

/-- The mover's cap is unchanged exactly across its own full replacement. -/
theorem moverCap_eq_sourceCap
    (endpoint : FullReplacementCluster frontier mover) (rank : ℕ) :
    quittingContinuationBestResponseValue reward
        (frontier.fullReplacementProfile mover (endpoint.subseq rank)) mover.1 =
      quittingContinuationBestResponseValue reward
        (frontier.source (endpoint.subseq rank)) mover.1 := by
  unfold fullReplacementProfile
  exact quittingContinuationBestResponseValue_update_self _ _ _ _

/-- A common asymptotic cap chart across one minimum-fibre horizontal seam.
For every non-mover, one actual response is simultaneously near-optimal at the
parent source and child endpoint; the mover's cap is invariant exactly. -/
structure MinimumFiberCommonResponseCompiler
    (endpoint : FullReplacementCluster frontier mover)
    (hminimumFiber : quittingTerminalSemanticDebtSum endpoint.cluster =
      quittingTerminalSemanticDebtSum frontier.base) where
  response : ∀ observer : {who // who ≠ mover.1}, ℕ →
    (quittingGame reward).BehaviorStrategy observer.1
  error : {who // who ≠ mover.1} → ℕ → ℝ
  error_nonneg : ∀ observer rank, 0 ≤ error observer rank
  error_tendsto_zero : ∀ observer,
    Tendsto (error observer) atTop (nhds 0)
  source_cap_le : ∀ observer rank,
    quittingContinuationBestResponseValue reward
        (frontier.source (endpoint.subseq rank)) observer.1 ≤
      quittingTerminalPayoff reward
          (Function.update (frontier.source (endpoint.subseq rank)) observer.1
            (response observer rank)) observer.1 + error observer rank
  endpoint_cap_le : ∀ observer rank,
    quittingContinuationBestResponseValue reward
        (frontier.fullReplacementProfile mover (endpoint.subseq rank))
        observer.1 ≤
      quittingTerminalPayoff reward
          (Function.update
            (frontier.fullReplacementProfile mover (endpoint.subseq rank))
            observer.1 (response observer rank)) observer.1 + error observer rank
  mover_cap_eq : ∀ rank,
    quittingContinuationBestResponseValue reward
        (frontier.fullReplacementProfile mover (endpoint.subseq rank)) mover.1 =
      quittingContinuationBestResponseValue reward
        (frontier.source (endpoint.subseq rank)) mover.1

/-- Every minimum-fibre full-replacement cluster carries the common response
compiler. -/
noncomputable def minimumFiberCommonResponseCompiler
    (endpoint : FullReplacementCluster frontier mover)
    (hminimumFiber : quittingTerminalSemanticDebtSum endpoint.cluster =
      quittingTerminalSemanticDebtSum frontier.base) :
    MinimumFiberCommonResponseCompiler endpoint hminimumFiber where
  response := endpoint.commonResponse
  error := endpoint.commonResponseError
  error_nonneg := endpoint.commonResponseError_nonneg
  error_tendsto_zero := endpoint.commonResponseError_tendsto_zero hminimumFiber
  source_cap_le := endpoint.sourceCap_le_commonResponsePayoff_add_error
  endpoint_cap_le := endpoint.endpointCap_le_commonResponsePayoff_add_error
  mover_cap_eq := endpoint.moverCap_eq_sourceCap

end FullReplacementCluster
end QuittingPositiveMinimumDebtTangentFamily

end GameTheory
