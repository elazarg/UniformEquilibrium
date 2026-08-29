/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.StoppingLawMinimumEndpointSupportRankHandoff
import Research.Quitting.StoppingLawMixtureFiniteWitnessPassport
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.MinimumFiberSupportDrop

/-!
# Common pure-time responses across a near-minimum stopping-law seam

Two profiles which differ only in one player's complete stopping law need not
have the same caps for the other players.  Nevertheless, when both endpoint
total debts are close to the global minimum, every nonmover has one pure-time
response which is simultaneously close to optimal at both endpoints.
-/

noncomputable section

namespace GameTheory

open Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Regret of one deterministic pure-time response against a behavioral
profile.  `none` is the Never response. -/
def quittingPureTimeResponseRegret
    (profile : (quittingGame reward).BehaviorProfile)
    (observer : ι) (choice : Option ℕ) : ℝ :=
  quittingContinuationBestResponseValue reward profile observer -
    quittingTerminalPayoff reward
      (Function.update profile observer
        (quittingPureTimeBehaviorStrategy reward observer choice)) observer

theorem quittingPureTimeResponseRegret_nonneg
    (profile : (quittingGame reward).BehaviorProfile)
    (observer : ι) (choice : Option ℕ) :
    0 ≤ quittingPureTimeResponseRegret
      (reward := reward) profile observer choice := by
  unfold quittingPureTimeResponseRegret
  exact sub_nonneg.mpr
    (quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward profile observer
        (quittingPureTimeBehaviorStrategy reward observer choice))

/-- Excess of the average endpoint debt above a fixed global minimum. -/
def quittingStoppingLawSeamExcess
    (minimum : QuittingTerminalSemanticPair ι)
    (source target : (quittingGame reward).BehaviorProfile) : ℝ :=
  (quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward source) +
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward target)) / 2 -
    quittingTerminalSemanticDebtSum minimum

/-- One common pure-time response is quantitatively close to optimal at both
sides of a one-player stopping-law seam. -/
theorem exists_commonPureTimeResponse_of_nearMinimumSeam
    (minimum : QuittingTerminalSemanticPair ι)
    (source target : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hne : observer ≠ mover)
    (hopponents : ∀ other, other ≠ mover → target other = source other)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ choice : Option ℕ,
      quittingPureTimeResponseRegret
          (reward := reward) source observer choice ≤
        2 * (quittingStoppingLawSeamExcess
          (reward := reward) minimum source target + epsilon) ∧
      quittingPureTimeResponseRegret
          (reward := reward) target observer choice ≤
        2 * (quittingStoppingLawSeamExcess
          (reward := reward) minimum source target + epsilon) := by
  let half := quittingHalfStoppingLawProfile reward source target mover
  obtain ⟨choice, hchoice⟩ :=
    exists_quittingPureTime_terminalPayoff_ge_bestResponse_sub
      reward half observer epsilon hepsilon
  let deviation :=
    quittingPureTimeBehaviorStrategy reward observer choice
  let gap : ι → ℝ := fun who =>
    (quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) who +
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward target) who) / 2 -
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward half) who
  have hgapNonneg : ∀ who, 0 ≤ gap who := by
    intro who
    dsimp only [gap, half]
    exact sub_nonneg.mpr
      (quittingTerminalSemanticDebt_halfStoppingLawProfile_le
        reward source target mover who hopponents)
  have hgapSum :
      (∑ who, gap who) =
        (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward source) +
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward target)) / 2 -
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward half) := by
    dsimp only [gap]
    unfold quittingTerminalSemanticDebtSum
    rw [Finset.sum_sub_distrib, ← Finset.sum_div,
      Finset.sum_add_distrib]
  have hhalfMinimum :
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward half) :=
    hminimum _ (quittingTerminalSemanticPair_mem_carrier reward half)
  have hgapObserver : gap observer ≤
      quittingStoppingLawSeamExcess
        (reward := reward) minimum source target := by
    have hsingle : gap observer ≤ ∑ who, gap who :=
      Finset.single_le_sum
        (fun who _ => hgapNonneg who) (Finset.mem_univ observer)
    rw [hgapSum] at hsingle
    unfold quittingStoppingLawSeamExcess
    linarith
  have htarget : Function.update source mover (target mover) = target :=
    update_source_with_target_mover_eq_target
      reward source target mover hopponents
  have hprescribedRaw := quittingTerminalPayoff_stoppingLawMixture_eq
    reward source mover observer (source mover) (target mover)
      (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have hprescribed :
      quittingTerminalPayoff reward half observer =
        (quittingTerminalPayoff reward source observer +
          quittingTerminalPayoff reward target observer) / 2 := by
    rw [Function.update_eq_self, htarget] at hprescribedRaw
    dsimp only [half, quittingHalfStoppingLawProfile]
    linarith
  have hresponseRaw := quittingTerminalPayoff_stoppingLawMixture_eq
    reward (Function.update source observer deviation) mover observer
      (source mover) (target mover) (1 / 2 : ℝ)
        (by norm_num) (by norm_num)
  have hsourceCommute :
      Function.update (Function.update source observer deviation)
          mover (source mover) =
        Function.update source observer deviation := by
    rw [Function.update_comm hne deviation (source mover) source,
      Function.update_eq_self]
  have htargetCommute :
      Function.update (Function.update source observer deviation)
          mover (target mover) =
        Function.update target observer deviation := by
    rw [Function.update_comm hne deviation (target mover) source,
      htarget]
  have hhalfCommute :
      Function.update (Function.update source observer deviation) mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover
            (source mover) (target mover) (1 / 2 : ℝ)
              (by norm_num) (by norm_num)) =
        Function.update half observer deviation := by
    rw [Function.update_comm hne deviation _ source]
    rfl
  have hresponse :
      quittingTerminalPayoff reward
          (Function.update half observer deviation) observer =
        (quittingTerminalPayoff reward
            (Function.update source observer deviation) observer +
          quittingTerminalPayoff reward
            (Function.update target observer deviation) observer) / 2 := by
    rw [hhalfCommute, hsourceCommute, htargetCommute] at hresponseRaw
    linarith
  have hcapGap :
      (quittingContinuationBestResponseValue reward source observer +
          quittingContinuationBestResponseValue reward target observer) / 2 -
        quittingContinuationBestResponseValue reward half observer =
      gap observer := by
    dsimp only [gap, quittingTerminalSemanticDebt,
      quittingTerminalSemanticPair]
    linarith
  have hhalfRegret :
      quittingPureTimeResponseRegret
          (reward := reward) half observer choice ≤ epsilon := by
    unfold quittingPureTimeResponseRegret
    linarith
  have haverage :
      (quittingPureTimeResponseRegret
            (reward := reward) source observer choice +
        quittingPureTimeResponseRegret
            (reward := reward) target observer choice) / 2 =
      gap observer +
        quittingPureTimeResponseRegret
          (reward := reward) half observer choice := by
    unfold quittingPureTimeResponseRegret
    dsimp only [deviation] at hresponse
    linarith
  have haverageLe :
      (quittingPureTimeResponseRegret
            (reward := reward) source observer choice +
        quittingPureTimeResponseRegret
            (reward := reward) target observer choice) / 2 ≤
      quittingStoppingLawSeamExcess
          (reward := reward) minimum source target + epsilon := by
    rw [haverage]
    exact add_le_add hgapObserver hhalfRegret
  have hsourceNonneg := quittingPureTimeResponseRegret_nonneg
    (reward := reward) target observer choice
  have htargetNonneg := quittingPureTimeResponseRegret_nonneg
    (reward := reward) source observer choice
  refine ⟨choice, ?_, ?_⟩ <;> linarith

/-- One pure-time response sequence which is asymptotically optimal on
both sides of a one-player stopping-law replacement seam. -/
structure QuittingStoppingLawCommonPureTimeCompiler
    (source target : ℕ → (quittingGame reward).BehaviorProfile)
    (observer : ι) where
  choice : ℕ → Option ℕ
  source_regret_tendsto_zero : Tendsto (fun rank =>
    quittingPureTimeResponseRegret
      (reward := reward) (source rank) observer (choice rank)) atTop (nhds 0)
  target_regret_tendsto_zero : Tendsto (fun rank =>
    quittingPureTimeResponseRegret
      (reward := reward) (target rank) observer (choice rank)) atTop (nhds 0)

/-- If both sides of a sequence approach the same global minimum total debt,
there are pure-time responses simultaneously asymptotically optimal at both
endpoints. -/
theorem nonempty_stoppingLawCommonPureTimeCompiler_of_minimumFiber
    (minimum : QuittingTerminalSemanticPair ι)
    (source target : ℕ → (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hne : observer ≠ mover)
    (hopponents : ∀ rank other, other ≠ mover →
      target rank other = source rank other)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsource : Tendsto (fun rank => quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward (source rank))) atTop
        (nhds (quittingTerminalSemanticDebtSum minimum)))
    (htarget : Tendsto (fun rank => quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward (target rank))) atTop
        (nhds (quittingTerminalSemanticDebtSum minimum))) :
    Nonempty (QuittingStoppingLawCommonPureTimeCompiler
      source target observer) := by
  let epsilon : ℕ → ℝ := fun rank => 1 / ((rank : ℝ) + 1)
  have hepsilon : ∀ rank, 0 < epsilon rank := by
    intro rank
    dsimp only [epsilon]
    positivity
  have hepsilonZero : Tendsto epsilon atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hexists : ∀ rank, ∃ choice : Option ℕ,
      quittingPureTimeResponseRegret
          (reward := reward) (source rank) observer choice ≤
        2 * (quittingStoppingLawSeamExcess
          (reward := reward) minimum (source rank) (target rank) +
            epsilon rank) ∧
      quittingPureTimeResponseRegret
          (reward := reward) (target rank) observer choice ≤
        2 * (quittingStoppingLawSeamExcess
          (reward := reward) minimum (source rank) (target rank) +
            epsilon rank) := by
    intro rank
    exact exists_commonPureTimeResponse_of_nearMinimumSeam
      minimum (source rank) (target rank) mover observer hne
        (hopponents rank) hminimum (epsilon rank) (hepsilon rank)
  choose choice hchoice using hexists
  let bound : ℕ → ℝ := fun rank =>
    2 * (quittingStoppingLawSeamExcess
      (reward := reward) minimum (source rank) (target rank) +
        epsilon rank)
  have haverage : Tendsto (fun rank =>
      (quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (source rank)) +
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (target rank))) / 2)
      atTop (nhds (quittingTerminalSemanticDebtSum minimum)) := by
    convert (hsource.add htarget).div_const 2 using 1 <;> ring_nf
  have hexcess : Tendsto (fun rank =>
      quittingStoppingLawSeamExcess
        (reward := reward) minimum (source rank) (target rank))
      atTop (nhds 0) := by
    simpa only [quittingStoppingLawSeamExcess, sub_self] using
      haverage.sub_const (quittingTerminalSemanticDebtSum minimum)
  have hbound : Tendsto bound atTop (nhds 0) := by
    dsimp only [bound]
    convert (hexcess.add hepsilonZero).const_mul 2 using 1 <;> ring_nf
  refine ⟨⟨choice, ?_, ?_⟩⟩
  · apply squeeze_zero'
    · exact Eventually.of_forall fun rank =>
        quittingPureTimeResponseRegret_nonneg
          (reward := reward) (source rank) observer (choice rank)
    · exact Eventually.of_forall fun rank => (hchoice rank).1
    · exact hbound
  · apply squeeze_zero'
    · exact Eventually.of_forall fun rank =>
        quittingPureTimeResponseRegret_nonneg
          (reward := reward) (target rank) observer (choice rank)
    · exact Eventually.of_forall fun rank => (hchoice rank).2
    · exact hbound

namespace QuittingStoppingLawCommonPureTimeCompiler

/-- The same common response sequence asymptotically computes the cap change. -/
theorem capDifference_sub_responseDifference_tendsto_zero
    {source target : ℕ → (quittingGame reward).BehaviorProfile}
    {observer : ι}
    (compiler : QuittingStoppingLawCommonPureTimeCompiler
      source target observer) :
    Tendsto (fun rank =>
      (quittingContinuationBestResponseValue reward (target rank) observer -
          quittingContinuationBestResponseValue reward (source rank) observer) -
        (quittingTerminalPayoff reward
            (Function.update (target rank) observer
              (quittingPureTimeBehaviorStrategy reward observer
                (compiler.choice rank))) observer -
          quittingTerminalPayoff reward
            (Function.update (source rank) observer
              (quittingPureTimeBehaviorStrategy reward observer
                (compiler.choice rank))) observer)) atTop (nhds 0) := by
  have hdifference := compiler.target_regret_tendsto_zero.sub
    compiler.source_regret_tendsto_zero
  convert hdifference using 1
  · funext rank
    unfold quittingPureTimeResponseRegret
    ring_nf
  · ring_nf

end QuittingStoppingLawCommonPureTimeCompiler

namespace QuittingPositiveMinimumDebtTangentFamily.FullReplacementCluster

/-- Every nonmover has a common asymptotic best-response sequence across a
minimum-fibre full-replacement seam. -/
theorem nonempty_commonPureTimeResponseCompiler
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    {mover : {who // who ∈ frontier.positiveDebtSupport}}
    (endpoint : FullReplacementCluster frontier mover)
    (hminimumFiber : quittingTerminalSemanticDebtSum endpoint.cluster =
      quittingTerminalSemanticDebtSum frontier.base)
    (observer : ι) (hobserver : observer ≠ mover.1) :
    Nonempty (QuittingStoppingLawCommonPureTimeCompiler
      (fun rank => frontier.source (endpoint.subseq rank))
      (fun rank => frontier.fullReplacementProfile mover
        (endpoint.subseq rank)) observer) := by
  apply nonempty_stoppingLawCommonPureTimeCompiler_of_minimumFiber
    (reward := reward) frontier.base
    (fun rank => frontier.source (endpoint.subseq rank))
    (fun rank => frontier.fullReplacementProfile mover
      (endpoint.subseq rank)) mover.1 observer hobserver
  · intro rank other hother
    simp only [QuittingPositiveMinimumDebtTangentFamily.fullReplacementProfile]
    rw [Function.update_of_ne hother]
  · exact frontier.base_minimum
  · have hpair := frontier.source_tendsto.comp
      endpoint.subseq_strictMono.tendsto_atTop
    exact continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
      hpair
  · have hsum :=
      continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
        endpoint.fullReplacement_tendsto
    rw [hminimumFiber] at hsum
    exact hsum

end QuittingPositiveMinimumDebtTangentFamily.FullReplacementCluster

end GameTheory
