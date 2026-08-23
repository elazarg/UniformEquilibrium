/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.OffDiagonal.PotentialCoDecreaseEndpoint
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPaidFirstDisagreement

/-!
# Curvature alternative for a potential-guided full reset

A flat full-reset endpoint differs from its limiting tangent column by a
nonnegative coordinatewise curvature vector.  Its total curvature is exactly
the endpoint's total-debt excess above the frontier minimum, and the mover
coordinate has zero curvature.  Hence every off-minimum endpoint has a
quantitatively positive opponent coordinate.

At finite rank, normalized curvature along one literal stopping-law ray can
be decoded into two pure-time witnesses and an exact paid first-disagreement
row.  The resulting row is a strategic certificate, not a chronology or a
consumer of the paid event.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.Optimization
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingCounterexampleStoppingLawFrontier

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {witness : QuittingTerminalExploitabilityWitness reward}
  {frontier : QuittingCounterexampleStoppingLawFrontier witness}
  {mover : {who // who ∈ frontier.active}}

namespace FullResetEndpointCluster

/-- Coordinatewise curvature needed to complete the tangent column to the
literal full-reset endpoint. -/
def curvature (endpoint : FullResetEndpointCluster frontier mover)
    (observer : ι) : ℝ :=
  quittingTerminalSemanticDebtChange frontier.base endpoint.cluster observer -
    frontier.tangent mover observer

theorem curvature_nonneg
    (endpoint : FullResetEndpointCluster frontier mover) (observer : ι) :
    0 ≤ endpoint.curvature observer :=
  sub_nonneg.mpr (endpoint.coordinate_excess observer)

theorem curvature_mover_eq_zero
    (endpoint : FullResetEndpointCluster frontier mover) :
    endpoint.curvature mover.1 = 0 := by
  unfold curvature
  rw [endpoint.mover_excess_eq]
  ring

/-- For a flat column, total endpoint curvature is exactly total semantic
debt excess above the frontier minimum. -/
theorem sum_curvature_eq_totalDebtExcess
    (endpoint : FullResetEndpointCluster frontier mover)
    (hflat : ∑ observer, frontier.tangent mover observer = 0) :
    (∑ observer, endpoint.curvature observer) =
      quittingTerminalSemanticDebtSum endpoint.cluster -
        quittingTerminalSemanticDebtSum frontier.base := by
  unfold curvature quittingTerminalSemanticDebtChange
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hflat, sub_zero]
  unfold quittingTerminalSemanticDebtSum
  rfl

/-- Off the minimum fiber, one non-mover coordinate carries at least average
curvature over all opponents. -/
theorem exists_curvature_ge_opponentAverage
    (endpoint : FullResetEndpointCluster frontier mover)
    (hflat : ∑ observer, frontier.tangent mover observer = 0) :
    ∃ observer : ι, observer ≠ mover.1 ∧
      (quittingTerminalSemanticDebtSum endpoint.cluster -
          quittingTerminalSemanticDebtSum frontier.base) /
          ((Finset.univ.erase mover.1).card : ℝ) ≤
        endpoint.curvature observer := by
  have hopponents : (Finset.univ.erase mover.1).Nonempty := by
    obtain ⟨observer, hne, _hpositive⟩ :=
      frontier.exists_positiveOffDiagonal mover.2
    exact ⟨observer, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ observer⟩⟩
  obtain ⟨observer, hobserver, hmax⟩ :=
    Finset.exists_max_image (Finset.univ.erase mover.1)
      endpoint.curvature hopponents
  have hsumErase : (∑ who ∈ Finset.univ.erase mover.1,
      endpoint.curvature who) =
      quittingTerminalSemanticDebtSum endpoint.cluster -
        quittingTerminalSemanticDebtSum frontier.base := by
    have hsum := endpoint.sum_curvature_eq_totalDebtExcess hflat
    have hsplit := Finset.sum_erase_add Finset.univ endpoint.curvature
      (Finset.mem_univ mover.1)
    rw [endpoint.curvature_mover_eq_zero, add_zero] at hsplit
    exact hsplit.trans hsum
  have hsumLe : (∑ who ∈ Finset.univ.erase mover.1,
      endpoint.curvature who) ≤
      ((Finset.univ.erase mover.1).card : ℝ) *
        endpoint.curvature observer := by
    simpa [nsmul_eq_mul, mul_comm] using
      (Finset.univ.erase mover.1).sum_le_card_nsmul endpoint.curvature
        (endpoint.curvature observer) (fun who hwho ↦ hmax who hwho)
  have hcardPos : 0 < ((Finset.univ.erase mover.1).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hopponents
  refine ⟨observer, (Finset.mem_erase.mp hobserver).1, ?_⟩
  apply (div_le_iff₀ hcardPos).2
  rw [← hsumErase]
  simpa only [mul_comm] using hsumLe

/-- The finite-rank normalized endpoint-curvature coordinate converges to the
curvature of the compact full-reset cluster. -/
theorem normalizedCurvature_tendsto
    (endpoint : FullResetEndpointCluster frontier mover) (observer : ι) :
    Tendsto (fun rank ↦
      quittingTerminalSemanticDebtChange
          (frontier.sourcePair (endpoint.subseq rank))
          (frontier.fullResetPair mover (endpoint.subseq rank)) observer -
        quittingStoppingLawNormalizedDebtDirection reward
          (frontier.profiles (frontier.subseq (endpoint.subseq rank))) mover.1
          (frontier.bestResponse mover
            (frontier.subseq (endpoint.subseq rank)))
          (frontier.lambda (frontier.subseq (endpoint.subseq rank)))
          (frontier.lambda_pos
            (frontier.subseq (endpoint.subseq rank))).le
          (frontier.lambda_le_one
            (frontier.subseq (endpoint.subseq rank))) observer)
      atTop (nhds (endpoint.curvature observer)) := by
  have hsource : Tendsto (fun rank ↦
      frontier.sourcePair (endpoint.subseq rank)) atTop
      (nhds frontier.base) := by
    unfold sourcePair
    exact frontier.profiles_tendsto.comp
      endpoint.sourceSubseq_strictMono.tendsto_atTop
  have hchange : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtChange
        (frontier.sourcePair (endpoint.subseq rank))
        (frontier.fullResetPair mover (endpoint.subseq rank)) observer)
      atTop (nhds (quittingTerminalSemanticDebtChange
        frontier.base endpoint.cluster observer)) := by
    unfold quittingTerminalSemanticDebtChange
    exact ((continuous_quittingTerminalSemanticDebt observer).tendsto
      endpoint.cluster |>.comp endpoint.fullReset_tendsto).sub
        ((continuous_quittingTerminalSemanticDebt observer).tendsto
          frontier.base |>.comp hsource)
  exact hchange.sub ((frontier.tangent_tendsto mover observer).comp
    endpoint.subseq_strictMono.tendsto_atTop)

end FullResetEndpointCluster

end QuittingCounterexampleStoppingLawFrontier

/-! ## Finite-rank one-ray curvature decoder -/

/-- A normalized debt-convexity gap along one literal stopping-law mixture
forces two pure-time witnesses to disagree profitably at the full endpoint.
The conclusion is an exact paid first-disagreement row. -/
theorem exists_paidFirstDisagreementRow_of_stoppingLawNormalizedCurvature
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
    ∃ row : QuittingPaidFirstDisagreementRow reward
        (Function.update profile mover target) observer gain,
      quittingContinuationBestResponseValue reward profile observer -
          sourceError ≤
        quittingPureTimeDeviationPayoff reward profile observer
          row.sourceWitness ∧
      quittingContinuationBestResponseValue reward
            (Function.update profile mover target) observer - endpointError ≤
        quittingPureTimeDeviationPayoff reward
          (Function.update profile mover target) observer
          row.receivingWitness := by
  let sourceValue : Option ℕ → ℝ :=
    quittingPureTimeDeviationPayoff reward profile observer
  let targetProfile := Function.update profile mover target
  let targetValue : Option ℕ → ℝ :=
    quittingPureTimeDeviationPayoff reward targetProfile observer
  obtain ⟨sourceWitness, hsourceWitness⟩ :=
    exists_ge_sSup_sub sourceValue sourceError hsourceError
  obtain ⟨receivingWitness, hreceivingWitness⟩ :=
    exists_ge_sSup_sub targetValue endpointError hendpointError
  have hsourceCap : sSup (Set.range sourceValue) =
      quittingContinuationBestResponseValue reward profile observer :=
    (quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff
      reward profile observer).symm
  have htargetCap : sSup (Set.range targetValue) =
      quittingContinuationBestResponseValue reward targetProfile observer :=
    (quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff
      reward targetProfile observer).symm
  rw [hsourceCap] at hsourceWitness
  rw [htargetCap] at hreceivingWitness
  let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy reward mover
    (profile mover) target lambda hlambda.le hlambdaOne
  let mixedProfile := Function.update profile mover mixedStrategy
  have hsourceAffine : quittingPureTimeDeviationPayoff reward mixedProfile
      observer sourceWitness =
      (1 - lambda) * sourceValue sourceWitness +
        lambda * targetValue sourceWitness := by
    have haffine := quittingTerminalPayoff_stoppingLawMixture_eq
      reward (Function.update profile observer
        (quittingPureTimeBehaviorStrategy reward observer sourceWitness))
      mover observer (profile mover) target lambda hlambda.le hlambdaOne
    have hsourceCommute : Function.update
        (Function.update profile observer
          (quittingPureTimeBehaviorStrategy reward observer sourceWitness))
        mover (profile mover) = Function.update profile observer
          (quittingPureTimeBehaviorStrategy reward observer sourceWitness) := by
      rw [Function.update_comm hne]
      simp
    have htargetCommute : Function.update
        (Function.update profile observer
          (quittingPureTimeBehaviorStrategy reward observer sourceWitness))
        mover target = Function.update targetProfile observer
          (quittingPureTimeBehaviorStrategy reward observer sourceWitness) := by
      rw [Function.update_comm hne]
    have hmixedCommute : Function.update
        (Function.update profile observer
          (quittingPureTimeBehaviorStrategy reward observer sourceWitness))
        mover mixedStrategy = Function.update mixedProfile observer
          (quittingPureTimeBehaviorStrategy reward observer sourceWitness) := by
      rw [Function.update_comm hne]
    rw [hsourceCommute, htargetCommute, hmixedCommute] at haffine
    simpa only [sourceValue, targetValue, targetProfile, mixedProfile,
      mixedStrategy, quittingPureTimeDeviationPayoff] using haffine
  have hmixedBound : quittingPureTimeDeviationPayoff reward mixedProfile
      observer sourceWitness ≤
      quittingContinuationBestResponseValue reward mixedProfile observer :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue reward
      mixedProfile observer
      (quittingPureTimeBehaviorStrategy reward observer sourceWitness)
  have hprescribedAffine := quittingTerminalPayoff_stoppingLawMixture_eq
    reward profile mover observer (profile mover) target lambda hlambda.le
      hlambdaOne
  rw [Function.update_eq_self] at hprescribedAffine
  have hcurvatureIdentity :
      lambda *
          (quittingTerminalSemanticDebtChange
              (quittingTerminalSemanticPair reward profile)
              (quittingTerminalSemanticPair reward targetProfile) observer -
            quittingStoppingLawNormalizedDebtDirection reward profile mover
              target lambda hlambda.le hlambdaOne observer) =
        (1 - lambda) *
            quittingContinuationBestResponseValue reward profile observer +
          lambda * quittingContinuationBestResponseValue reward
            targetProfile observer -
          quittingContinuationBestResponseValue reward mixedProfile observer := by
    unfold quittingStoppingLawNormalizedDebtDirection
      quittingStoppingLawResetProfile quittingTerminalSemanticDebtChange
      quittingTerminalSemanticDebt quittingTerminalSemanticPair
    change lambda *
      ((quittingContinuationBestResponseValue reward targetProfile observer -
          quittingTerminalPayoff reward targetProfile observer -
        (quittingContinuationBestResponseValue reward profile observer -
          quittingTerminalPayoff reward profile observer)) -
        ((quittingContinuationBestResponseValue reward mixedProfile observer -
            quittingTerminalPayoff reward mixedProfile observer) -
          (quittingContinuationBestResponseValue reward profile observer -
            quittingTerminalPayoff reward profile observer)) / lambda) = _
    rw [div_eq_mul_inv]
    field_simp
    change quittingTerminalPayoff reward mixedProfile observer = _ at hprescribedAffine
    nlinarith
  rw [hcurvatureIdentity] at hcurvature
  rw [hsourceAffine] at hmixedBound
  have hsourceRegret :
      quittingContinuationBestResponseValue reward profile observer -
          sourceValue sourceWitness ≤ sourceError := by
    linarith
  have hsourceWeighted := mul_le_mul_of_nonneg_left hsourceRegret
    (sub_nonneg.mpr hlambdaOne)
  have hscaled : lambda * (gain + endpointError) ≤
      lambda * (quittingContinuationBestResponseValue reward targetProfile
        observer - targetValue sourceWitness) := by
    linarith
  have htargetRegret : gain + endpointError ≤
      quittingContinuationBestResponseValue reward targetProfile observer -
        targetValue sourceWitness := by
    nlinarith
  have hedge : gain ≤
      targetValue receivingWitness - targetValue sourceWitness := by
    linarith
  obtain ⟨row, hrowSource, hrowReceiving⟩ :=
    exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub reward
      targetProfile observer sourceWitness receivingWitness gain hgain hedge
  refine ⟨row, ?_, ?_⟩
  · simpa only [hrowSource, sourceValue] using hsourceWitness
  · simpa only [hrowReceiving, targetValue, targetProfile] using
      hreceivingWitness

namespace QuittingCounterexampleStoppingLawFrontier

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {witness : QuittingTerminalExploitabilityWitness reward}
  {frontier : QuittingCounterexampleStoppingLawFrontier witness}
  {mover : {who // who ∈ frontier.active}}

namespace FullResetEndpointCluster

/-- Every off-minimum flat full-reset cluster exports a fixed positive-gain
paid first-disagreement row along its exact source/reset subsequence. -/
theorem exists_eventually_paidFirstDisagreement
    (endpoint : FullResetEndpointCluster frontier mover)
    (hflat : ∑ observer, frontier.tangent mover observer = 0)
    (hseparated : quittingTerminalSemanticDebtSum frontier.base <
      quittingTerminalSemanticDebtSum endpoint.cluster) :
    ∃ observer : ι, ∃ gain : ℝ,
      observer ≠ mover.1 ∧ 0 < gain ∧
      ∀ᶠ rank in atTop,
        Nonempty (QuittingPaidFirstDisagreementRow reward
          (frontier.fullResetProfile mover (endpoint.subseq rank))
          observer gain) := by
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
  have heventually := (endpoint.normalizedCurvature_tendsto observer).eventually
    (Ioi_mem_nhds (half_lt_self hcurvature))
  let gain := curvature / 4
  have hgain : 0 < gain := div_pos hcurvature (by norm_num)
  refine ⟨observer, gain, hne, hgain, ?_⟩
  filter_upwards [heventually] with rank hrank
  let lambda := frontier.lambda (frontier.subseq (endpoint.subseq rank))
  have hlambda : 0 < lambda :=
    frontier.lambda_pos (frontier.subseq (endpoint.subseq rank))
  have hlambdaOne : lambda ≤ 1 :=
    frontier.lambda_le_one (frontier.subseq (endpoint.subseq rank))
  let sourceError := lambda * curvature / 16
  let endpointError := curvature / 16
  have hsourceError : 0 < sourceError := by
    dsimp only [sourceError]
    positivity
  have hendpointError : 0 < endpointError := by
    dsimp only [endpointError]
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hrank.le hlambda.le
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
    dsimp only [gain, endpointError, sourceError]
    nlinarith [mul_nonneg hlambda.le hcurvature.le,
      mul_nonneg (sub_nonneg.mpr hlambdaOne)
        (mul_nonneg hlambda.le hcurvature.le)]
  obtain ⟨row, _hsource, _hreceiving⟩ :=
    exists_paidFirstDisagreementRow_of_stoppingLawNormalizedCurvature
      reward (frontier.profiles (frontier.subseq (endpoint.subseq rank)))
      mover.1 observer
      (frontier.bestResponse mover (frontier.subseq (endpoint.subseq rank)))
      lambda sourceError endpointError gain hne hlambda hlambdaOne
      hsourceError hendpointError hgain hbudget
  exact ⟨row⟩

end FullResetEndpointCluster

/-- **Connected potential-endpoint alternative.**  A flat potential-guided
co-decrease selects one literal full-reset endpoint cluster.  Either the
cluster remains on the minimum-total-debt fiber, where its positive-debt
support and cardinal rank strictly deflate and the stored companion debt
falls, or it is strictly separated from the minimum and exports a fixed
positive paid first-disagreement row along the same source/reset subsequence.

The second arm retains the exact row but does not consume it chronologically. -/
theorem potentialCoDecrease_minimumFiberDeflation_or_paidFirstDisagreement
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (hflat : ∀ mover, ∑ observer, frontier.tangent mover observer = 0)
    (hnoEntry : ¬HasQuittingStoppingLawFlatSupportEntry
      frontier.base frontier.active frontier.tangent)
    (hpotential : HasQuittingStoppingLawFlatPotentialCoDecrease
      frontier.active frontier.tangent) :
    ∃ mover : {who // who ∈ frontier.active},
      ∃ other ∈ frontier.active.erase mover.1,
        frontier.tangent mover other < 0 ∧
        ∃ endpoint : FullResetEndpointCluster frontier mover,
          (quittingTerminalSemanticDebtSum endpoint.cluster =
                quittingTerminalSemanticDebtSum frontier.base ∧
              (Finset.univ.filter fun who ↦
                0 < quittingTerminalSemanticDebt endpoint.cluster who) ⊂
                  frontier.active ∧
              (Finset.univ.filter fun who ↦
                0 < quittingTerminalSemanticDebt endpoint.cluster who).card <
                  frontier.active.card ∧
              quittingTerminalSemanticDebt endpoint.cluster other <
                quittingTerminalSemanticDebt frontier.base other) ∨
            (quittingTerminalSemanticDebtSum frontier.base <
                quittingTerminalSemanticDebtSum endpoint.cluster ∧
              ∃ observer : ι, ∃ gain : ℝ,
                observer ≠ mover.1 ∧ 0 < gain ∧
                ∀ᶠ rank in atTop,
                  Nonempty (QuittingPaidFirstDisagreementRow reward
                    (frontier.fullResetProfile mover (endpoint.subseq rank))
                    observer gain)) := by
  obtain ⟨mover, other, hotherMem, hotherDecrease, ⟨endpoint⟩,
      hminimumConsumer⟩ :=
    frontier.exists_potentialCoDecrease_fullResetEndpointCluster
      hpotential hflat hnoEntry
  refine ⟨mover, other, hotherMem, hotherDecrease, endpoint, ?_⟩
  have hfloor := frontier.base_minimum endpoint.cluster endpoint.cluster_mem
  rcases hfloor.eq_or_lt with hsame | hseparated
  · left
    have hsame' := hsame.symm
    obtain ⟨hsupport, hotherDebt⟩ := hminimumConsumer endpoint hsame'
    exact ⟨hsame', hsupport, Finset.card_lt_card hsupport, hotherDebt⟩
  · right
    obtain ⟨observer, gain, hobserver, hgain, hpaid⟩ :=
      endpoint.exists_eventually_paidFirstDisagreement
        (hflat mover) hseparated
    exact ⟨hseparated, observer, gain, hobserver, hgain, hpaid⟩

/-! ## Finite support-rank iteration -/

/-- A minimum-fiber full-reset endpoint is itself a positive minimum
all-Continue plateau and can therefore serve as the base of a fresh
stopping-law extraction. -/
theorem FullResetEndpointCluster.hasPositiveMinimumTerminalSemanticPlateau_of_minimumFiber
    {frontier : QuittingCounterexampleStoppingLawFrontier witness}
    {mover : {who // who ∈ frontier.active}}
    (endpoint : FullResetEndpointCluster frontier mover)
    (hminimumFiber : quittingTerminalSemanticDebtSum endpoint.cluster =
      quittingTerminalSemanticDebtSum frontier.base) :
    HasPositiveMinimumTerminalSemanticPlateau reward := by
  have hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum endpoint.cluster ≤
        quittingTerminalSemanticDebtSum candidate := by
    intro candidate hcandidate
    rw [hminimumFiber]
    exact frontier.base_minimum candidate hcandidate
  have hpositive : 0 < quittingTerminalSemanticDebtSum endpoint.cluster := by
    rw [hminimumFiber]
    exact frontier.base_positive
  have hnonneg : ∀ who,
      0 ≤ quittingTerminalSemanticDebt endpoint.cluster who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward endpoint.cluster_mem
  have hcoordinate : ∃ who,
      0 < quittingTerminalSemanticDebt endpoint.cluster who := by
    by_contra hnone
    have hzero : ∀ who,
        quittingTerminalSemanticDebt endpoint.cluster who = 0 := by
      intro who
      exact le_antisymm
        (le_of_not_gt fun hwho ↦ hnone ⟨who, hwho⟩) (hnonneg who)
    unfold quittingTerminalSemanticDebtSum at hpositive
    simp only [hzero, Finset.sum_const_zero] at hpositive
    exact (lt_irrefl 0) hpositive
  obtain ⟨hnash, hprefix, _hmargin⟩ :=
    minimumTerminalSemantic_is_allContinuePlateau
      (reward := reward) endpoint.cluster endpoint.cluster_mem hminimum hpositive
  exact ⟨endpoint.cluster, endpoint.cluster_mem, hminimum, hcoordinate,
    hnash, hprefix⟩

/-- Re-extraction at a flat no-entry minimum-fiber endpoint strictly lowers
the active-support cardinal rank.  This is the reusable adapter needed for
well-founded iteration; it asserts no relation between the old and new
tangent families beyond their semantic base. -/
theorem exists_reextractedFrontier_of_minimumFiberEndpoint
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    {mover : {who // who ∈ frontier.active}}
    (endpoint : FullResetEndpointCluster frontier mover)
    (hflat : ∀ source, ∑ observer, frontier.tangent source observer = 0)
    (hnoEntry : ¬HasQuittingStoppingLawFlatSupportEntry
      frontier.base frontier.active frontier.tangent)
    (hminimumFiber : quittingTerminalSemanticDebtSum endpoint.cluster =
      quittingTerminalSemanticDebtSum frontier.base) :
    ∃ next : QuittingCounterexampleStoppingLawFrontier witness,
      next.base = endpoint.cluster ∧
      next.active.card < frontier.active.card := by
  have hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum endpoint.cluster ≤
        quittingTerminalSemanticDebtSum candidate := by
    intro candidate hcandidate
    rw [hminimumFiber]
    exact frontier.base_minimum candidate hcandidate
  have hpositive : 0 < quittingTerminalSemanticDebtSum endpoint.cluster := by
    rw [hminimumFiber]
    exact frontier.base_positive
  have hnonneg : ∀ who,
      0 ≤ quittingTerminalSemanticDebt endpoint.cluster who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward endpoint.cluster_mem
  have hcoordinate : ∃ who,
      0 < quittingTerminalSemanticDebt endpoint.cluster who := by
    by_contra hnone
    have hzero : ∀ who,
        quittingTerminalSemanticDebt endpoint.cluster who = 0 := by
      intro who
      exact le_antisymm
        (le_of_not_gt fun hwho ↦ hnone ⟨who, hwho⟩) (hnonneg who)
    unfold quittingTerminalSemanticDebtSum at hpositive
    simp only [hzero, Finset.sum_const_zero] at hpositive
    exact (lt_irrefl 0) hpositive
  obtain ⟨hnash, hprefix, _hmargin⟩ :=
    minimumTerminalSemantic_is_allContinuePlateau
      (reward := reward) endpoint.cluster endpoint.cluster_mem hminimum hpositive
  obtain ⟨next, hbase⟩ :=
    exists_stoppingLaw_exhaustiveFrontier_of_positiveMinimumPair
      witness endpoint.cluster endpoint.cluster_mem hminimum
        hcoordinate hnash hprefix
  have hactive : next.active = Finset.univ.filter fun who ↦
      0 < quittingTerminalSemanticDebt endpoint.cluster who := by
    ext who
    rw [next.active_iff]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hbase]
  refine ⟨next, hbase, ?_⟩
  rw [hactive]
  exact endpoint.positiveDebtSupport_card_lt_of_exactDiagonal_of_flat_of_noEntry_of_minimumFiber
    (hflat mover) hnoEntry hminimumFiber

/-- A frontier has exited the potential-co-decrease recursion when it reaches
positive total slope, flat support entry, flat charged circulation, or an
off-minimum endpoint with an exact eventually paid first-disagreement row.
The final branch stores the row but does not claim a chronological consumer. -/
def HasQuittingStoppingLawFiniteSupportRankExit
    (witness : QuittingTerminalExploitabilityWitness reward) : Prop :=
  ∃ frontier : QuittingCounterexampleStoppingLawFrontier witness,
    (∃ mover, 0 < ∑ observer, frontier.tangent mover observer) ∨
    ((∀ mover, ∑ observer, frontier.tangent mover observer = 0) ∧
      HasQuittingStoppingLawFlatSupportEntry
        frontier.base frontier.active frontier.tangent) ∨
    ((∀ mover, ∑ observer, frontier.tangent mover observer = 0) ∧
      ¬HasQuittingStoppingLawFlatSupportEntry
        frontier.base frontier.active frontier.tangent ∧
      HasQuittingStoppingLawFlatChargedCirculation
        frontier.active frontier.tangent) ∨
    ∃ mover : {who // who ∈ frontier.active},
      ∃ endpoint : FullResetEndpointCluster frontier mover,
        quittingTerminalSemanticDebtSum frontier.base <
            quittingTerminalSemanticDebtSum endpoint.cluster ∧
          ∃ observer : ι, ∃ gain : ℝ,
            observer ≠ mover.1 ∧ 0 < gain ∧
            ∀ᶠ rank in atTop,
              Nonempty (QuittingPaidFirstDisagreementRow reward
                (frontier.fullResetProfile mover (endpoint.subseq rank))
                observer gain)

/-- **Finite support-rank termination.**  Repeatedly re-extracting the
stopping-law frontier at a minimum-fiber potential endpoint cannot continue
indefinitely: every such step strictly lowers the finite positive-debt support
cardinality.  Therefore some re-extracted frontier reaches one of the three
non-potential tangent branches or an off-minimum endpoint carrying an exact
eventually paid first-disagreement row.

This theorem deliberately does not turn the paid row into a chronology or a
directed recipient-return consumer. -/
theorem exists_finiteSupportRankExit
    (frontier : QuittingCounterexampleStoppingLawFrontier witness) :
    HasQuittingStoppingLawFiniteSupportRankExit witness := by
  classical
  generalize hrank : frontier.active.card = rank
  induction rank using Nat.strong_induction_on generalizing frontier with
  | h rank ih =>
      rcases frontier.exhaustive_branch with hpositive | hentry |
          hcirculation | hpotential
      · exact ⟨frontier, Or.inl hpositive⟩
      · exact ⟨frontier, Or.inr (Or.inl hentry)⟩
      · exact ⟨frontier, Or.inr (Or.inr (Or.inl hcirculation))⟩
      · rcases hpotential with
          ⟨hflat, hnoEntry, _hnoCirculation, hcoDecrease⟩
        obtain ⟨mover, other, _hotherMem, _hotherDecrease, endpoint,
            hminimum | hpaid⟩ :=
          potentialCoDecrease_minimumFiberDeflation_or_paidFirstDisagreement
            frontier hflat hnoEntry hcoDecrease
        · obtain ⟨hminimumFiber, _hsupport, _hcard, _hotherDebt⟩ := hminimum
          obtain ⟨next, _hnextBase, hnextCard⟩ :=
            exists_reextractedFrontier_of_minimumFiberEndpoint
              frontier endpoint hflat hnoEntry hminimumFiber
          apply ih next.active.card
          · exact hnextCard.trans_eq hrank
          · rfl
        · obtain ⟨hseparated, observer, gain, hobserver, hgain, hrow⟩ := hpaid
          exact ⟨frontier, Or.inr (Or.inr (Or.inr
            ⟨mover, endpoint, hseparated, observer, gain,
              hobserver, hgain, hrow⟩))⟩

end QuittingCounterexampleStoppingLawFrontier

end GameTheory
