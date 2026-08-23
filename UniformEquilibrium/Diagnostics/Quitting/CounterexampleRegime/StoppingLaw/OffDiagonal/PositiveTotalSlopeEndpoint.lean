/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.OffDiagonal.SlopeFrontier
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawDebtConvexity

/-!
# Full reset endpoints of a positive total stopping-law slope

A positive total normalized debt slope has a scale-free consequence at the
full unilateral reset endpoint.  Coordinatewise debt convexity cancels the
original positive reset scale without changing the source profile, mover, or
replacement strategy.

Compactness then yields an endpoint cluster retaining every coordinate
inequality, equality in the moved coordinate, strict total-debt separation,
and the moved player's fixed prescribed-payoff gain.  No root prefix, Bellman
return, or contradiction to the counterexample regime is asserted here.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingCounterexampleStoppingLawFrontier

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {regime : QuittingCounterexampleRegime reward}

/-- The actual source semantic pair at one rank of the frontier's selected
tangent subsequence. -/
def sourcePair (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) : QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticPair reward
    (frontier.profiles (frontier.subseq rank))

/-- The literal full unilateral reset using the frontier's supplied mover and
its actual selected replacement strategy at the original source rank. -/
def fullResetProfile
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) (rank : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  Function.update (frontier.profiles (frontier.subseq rank)) mover.1
    (frontier.bestResponse mover (frontier.subseq rank))

/-- Terminal semantic pair of the literal full unilateral reset endpoint. -/
def fullResetPair
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) (rank : ℕ) :
    QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticPair reward (frontier.fullResetProfile mover rank)

/-- Prescribed-payoff gain of the supplied mover at its literal full reset,
measured from the actual source profile at the same selected rank. -/
def fullResetPrescribedGain
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) (rank : ℕ) : ℝ :=
  quittingTerminalPayoff reward (frontier.fullResetProfile mover rank) mover.1 -
    quittingTerminalPayoff reward
      (frontier.profiles (frontier.subseq rank)) mover.1

/-- Coordinatewise scale cancellation: the normalized debt change at the
partial reset is bounded by the full endpoint's debt change from the same
literal source. -/
theorem normalizedDebtDirection_le_fullResetDebtChange
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) (observer : ι) (rank : ℕ) :
    quittingStoppingLawNormalizedDebtDirection reward
        (frontier.profiles (frontier.subseq rank)) mover.1
        (frontier.bestResponse mover (frontier.subseq rank))
        (frontier.lambda (frontier.subseq rank))
        (frontier.lambda_pos (frontier.subseq rank)).le
        (frontier.lambda_le_one (frontier.subseq rank)) observer ≤
      quittingTerminalSemanticDebtChange (frontier.sourcePair rank)
        (frontier.fullResetPair mover rank) observer := by
  have hconvex := quittingTerminalSemanticDebt_stoppingLawMixture_le
    reward (frontier.profiles (frontier.subseq rank)) mover.1 observer
      (frontier.profiles (frontier.subseq rank) mover.1)
      (frontier.bestResponse mover (frontier.subseq rank))
      (frontier.lambda (frontier.subseq rank))
      (frontier.lambda_pos (frontier.subseq rank)).le
      (frontier.lambda_le_one (frontier.subseq rank))
  rw [Function.update_eq_self] at hconvex
  unfold quittingStoppingLawNormalizedDebtDirection
    quittingStoppingLawResetProfile quittingTerminalSemanticDebtChange
    sourcePair fullResetPair fullResetProfile
  rw [div_le_iff₀ (frontier.lambda_pos (frontier.subseq rank))]
  nlinarith

/-- In the moved coordinate, scale cancellation is an equality because the
best-response envelope depends only on the fixed opponents. -/
theorem normalizedDebtDirection_self_eq_fullResetDebtChange
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) (rank : ℕ) :
    quittingStoppingLawNormalizedDebtDirection reward
        (frontier.profiles (frontier.subseq rank)) mover.1
        (frontier.bestResponse mover (frontier.subseq rank))
        (frontier.lambda (frontier.subseq rank))
        (frontier.lambda_pos (frontier.subseq rank)).le
        (frontier.lambda_le_one (frontier.subseq rank)) mover.1 =
      quittingTerminalSemanticDebtChange (frontier.sourcePair rank)
        (frontier.fullResetPair mover rank) mover.1 := by
  have haffine := quittingTerminalSemanticDebt_stoppingLawMixture_eq_self
    reward (frontier.profiles (frontier.subseq rank)) mover.1
      (frontier.profiles (frontier.subseq rank) mover.1)
      (frontier.bestResponse mover (frontier.subseq rank))
      (frontier.lambda (frontier.subseq rank))
      (frontier.lambda_pos (frontier.subseq rank)).le
      (frontier.lambda_le_one (frontier.subseq rank))
  rw [Function.update_eq_self] at haffine
  unfold quittingStoppingLawNormalizedDebtDirection
    quittingStoppingLawResetProfile quittingTerminalSemanticDebtChange
    sourcePair fullResetPair fullResetProfile
  apply (div_eq_iff (ne_of_gt
    (frontier.lambda_pos (frontier.subseq rank)))).2
  rw [haffine]
  ring

/-- The mover's full-reset prescribed gain is exactly the negative normalized
self-debt direction at every original tangent rank. -/
theorem fullResetPrescribedGain_eq_neg_normalizedDebtDirection
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) (rank : ℕ) :
    frontier.fullResetPrescribedGain mover rank =
      -quittingStoppingLawNormalizedDebtDirection reward
        (frontier.profiles (frontier.subseq rank)) mover.1
        (frontier.bestResponse mover (frontier.subseq rank))
        (frontier.lambda (frontier.subseq rank))
        (frontier.lambda_pos (frontier.subseq rank)).le
        (frontier.lambda_le_one (frontier.subseq rank)) mover.1 := by
  rw [frontier.normalizedDebtDirection_self_eq_fullResetDebtChange mover rank]
  unfold fullResetPrescribedGain quittingTerminalSemanticDebtChange
    sourcePair fullResetPair fullResetProfile quittingTerminalSemanticDebt
    quittingTerminalSemanticPair
  simp only
  rw [quittingContinuationBestResponseValue_update_self]
  ring

/-- The sum of normalized coordinate changes is bounded by the full
endpoint's total-debt change from the actual source. -/
theorem sum_normalizedDebtDirection_le_fullReset_totalDebtChange
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) (rank : ℕ) :
    (∑ observer,
      quittingStoppingLawNormalizedDebtDirection reward
        (frontier.profiles (frontier.subseq rank)) mover.1
        (frontier.bestResponse mover (frontier.subseq rank))
        (frontier.lambda (frontier.subseq rank))
        (frontier.lambda_pos (frontier.subseq rank)).le
        (frontier.lambda_le_one (frontier.subseq rank)) observer) ≤
      quittingTerminalSemanticDebtSum (frontier.fullResetPair mover rank) -
        quittingTerminalSemanticDebtSum (frontier.sourcePair rank) := by
  have hsum :
      (∑ observer,
        quittingStoppingLawNormalizedDebtDirection reward
          (frontier.profiles (frontier.subseq rank)) mover.1
          (frontier.bestResponse mover (frontier.subseq rank))
          (frontier.lambda (frontier.subseq rank))
          (frontier.lambda_pos (frontier.subseq rank)).le
          (frontier.lambda_le_one (frontier.subseq rank)) observer) ≤
        ∑ observer, quittingTerminalSemanticDebtChange
          (frontier.sourcePair rank) (frontier.fullResetPair mover rank)
            observer := by
    exact Finset.sum_le_sum fun observer _ ↦
      frontier.normalizedDebtDirection_le_fullResetDebtChange mover observer rank
  unfold quittingTerminalSemanticDebtChange at hsum
  rw [Finset.sum_sub_distrib] at hsum
  exact hsum

/-- Every threshold strictly below a positive total tangent slope is
eventually realized as a scale-free full-reset total-debt excursion above the
global minimum. -/
theorem eventually_fullReset_totalDebt_excess_of_lt_positiveTotalSlope
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) (eta : ℝ)
    (heta : eta < ∑ observer, frontier.tangent mover observer) :
    ∀ᶠ rank in atTop,
      eta ≤ quittingTerminalSemanticDebtSum
          (frontier.fullResetPair mover rank) -
        quittingTerminalSemanticDebtSum frontier.base := by
  have hsumTendsto : Tendsto (fun rank ↦ ∑ observer,
      quittingStoppingLawNormalizedDebtDirection reward
        (frontier.profiles (frontier.subseq rank)) mover.1
        (frontier.bestResponse mover (frontier.subseq rank))
        (frontier.lambda (frontier.subseq rank))
        (frontier.lambda_pos (frontier.subseq rank)).le
        (frontier.lambda_le_one (frontier.subseq rank)) observer)
      atTop (nhds (∑ observer, frontier.tangent mover observer)) :=
    tendsto_finsetSum Finset.univ fun observer _ ↦
      frontier.tangent_tendsto mover observer
  filter_upwards [hsumTendsto.eventually (Ioi_mem_nhds heta)] with rank hrank
  have hendpoint :=
    frontier.sum_normalizedDebtDirection_le_fullReset_totalDebtChange mover rank
  have hsourceMinimum := frontier.base_minimum (frontier.sourcePair rank)
    (quittingTerminalSemanticPair_mem_carrier reward
      (frontier.profiles (frontier.subseq rank)))
  linarith

/-- A positive total tangent slope yields the canonical half-slope endpoint
excursion, with no residual reset-scale factor. -/
theorem eventually_fullReset_totalDebt_excess_of_positiveTotalSlope
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active})
    (hslope : 0 < ∑ observer, frontier.tangent mover observer) :
    ∀ᶠ rank in atTop,
      (∑ observer, frontier.tangent mover observer) / 2 ≤
        quittingTerminalSemanticDebtSum (frontier.fullResetPair mover rank) -
          quittingTerminalSemanticDebtSum frontier.base := by
  apply frontier.eventually_fullReset_totalDebt_excess_of_lt_positiveTotalSlope
    mover ((∑ observer, frontier.tangent mover observer) / 2)
  linarith

/-- Compact full-reset endpoint data produced by one supplied positive-slope
mover.  Every field retains the actual frontier subsequence and replacement
strategies. -/
structure PositiveTotalSlopeEndpointCluster
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) where
  cluster : QuittingTerminalSemanticPair ι
  subseq : ℕ → ℕ
  cluster_mem : cluster ∈ quittingTerminalSemanticCarrier reward
  subseq_strictMono : StrictMono subseq
  sourceSubseq_strictMono : StrictMono (frontier.subseq ∘ subseq)
  fullReset_tendsto : Tendsto (fun rank ↦
      frontier.fullResetPair mover (subseq rank)) atTop (nhds cluster)
  coordinate_excess : ∀ observer,
    frontier.tangent mover observer ≤
      quittingTerminalSemanticDebtChange frontier.base cluster observer
  mover_excess_eq : quittingTerminalSemanticDebtChange frontier.base cluster mover.1 =
    frontier.tangent mover mover.1
  mover_debt_nonneg : 0 ≤ quittingTerminalSemanticDebt cluster mover.1
  mover_debt_le_half : quittingTerminalSemanticDebt cluster mover.1 ≤
    quittingTerminalSemanticDebt frontier.base mover.1 / 2
  total_excess : (∑ observer, frontier.tangent mover observer) ≤
    quittingTerminalSemanticDebtSum cluster -
      quittingTerminalSemanticDebtSum frontier.base
  totalDebt_separated : quittingTerminalSemanticDebtSum frontier.base <
    quittingTerminalSemanticDebtSum cluster
  prescribedGain_tendsto : Tendsto (fun rank ↦
      frontier.fullResetPrescribedGain mover (subseq rank)) atTop
        (nhds (-frontier.tangent mover mover.1))
  prescribedGain_eventually : ∀ᶠ rank in atTop,
    quittingTerminalSemanticDebt frontier.base mover.1 / 4 ≤
      frontier.fullResetPrescribedGain mover (subseq rank)

/-- A supplied positive-total-slope mover has a compact full-reset endpoint
cluster with coordinatewise tangent domination, exact self-coordinate
change, half-debt reduction, strict total separation, and fixed prescribed
gain along the same source-matched reset sequence. -/
theorem exists_positiveTotalSlopeEndpointCluster
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active})
    (hslope : 0 < ∑ observer, frontier.tangent mover observer) :
    Nonempty (PositiveTotalSlopeEndpointCluster frontier mover) := by
  let endpoint : ℕ → QuittingTerminalSemanticPair ι :=
    fun rank ↦ frontier.fullResetPair mover rank
  have hendpointMem : ∀ rank,
      endpoint rank ∈ quittingTerminalSemanticCarrier reward := by
    intro rank
    exact quittingTerminalSemanticPair_mem_carrier reward
      (frontier.fullResetProfile mover rank)
  obtain ⟨cluster, hcluster, subseq, hsubseq, hendpoint⟩ :=
    (quittingTerminalSemanticCarrier_isCompact reward).tendsto_subseq
      hendpointMem
  have hsource : Tendsto (fun rank ↦ frontier.sourcePair (subseq rank))
      atTop (nhds frontier.base) := by
    unfold sourcePair
    exact frontier.profiles_tendsto.comp
      ((frontier.subseq_strictMono.comp hsubseq).tendsto_atTop)
  have hcoordinate : ∀ observer,
      frontier.tangent mover observer ≤
        quittingTerminalSemanticDebtChange frontier.base cluster observer := by
    intro observer
    have hleft := (frontier.tangent_tendsto mover observer).comp
      hsubseq.tendsto_atTop
    have hright : Tendsto (fun rank ↦
        quittingTerminalSemanticDebtChange
          (frontier.sourcePair (subseq rank))
          (frontier.fullResetPair mover (subseq rank)) observer)
        atTop (nhds
          (quittingTerminalSemanticDebtChange frontier.base cluster observer)) := by
      unfold quittingTerminalSemanticDebtChange
      exact ((continuous_quittingTerminalSemanticDebt observer).tendsto cluster
        |>.comp hendpoint).sub
          ((continuous_quittingTerminalSemanticDebt observer).tendsto frontier.base
            |>.comp hsource)
    exact le_of_tendsto_of_tendsto hleft hright
      (Eventually.of_forall fun rank ↦
        frontier.normalizedDebtDirection_le_fullResetDebtChange
          mover observer (subseq rank))
  have hmoverEq : quittingTerminalSemanticDebtChange frontier.base cluster mover.1 =
      frontier.tangent mover mover.1 := by
    have hleft := (frontier.tangent_tendsto mover mover.1).comp
      hsubseq.tendsto_atTop
    have hright : Tendsto (fun rank ↦
        quittingTerminalSemanticDebtChange
          (frontier.sourcePair (subseq rank))
          (frontier.fullResetPair mover (subseq rank)) mover.1)
        atTop (nhds
          (quittingTerminalSemanticDebtChange frontier.base cluster mover.1)) := by
      unfold quittingTerminalSemanticDebtChange
      exact ((continuous_quittingTerminalSemanticDebt mover.1).tendsto cluster
        |>.comp hendpoint).sub
          ((continuous_quittingTerminalSemanticDebt mover.1).tendsto frontier.base
            |>.comp hsource)
    have heq : (fun rank ↦
        quittingStoppingLawNormalizedDebtDirection reward
          (frontier.profiles (frontier.subseq (subseq rank))) mover.1
          (frontier.bestResponse mover (frontier.subseq (subseq rank)))
          (frontier.lambda (frontier.subseq (subseq rank)))
          (frontier.lambda_pos (frontier.subseq (subseq rank))).le
          (frontier.lambda_le_one (frontier.subseq (subseq rank))) mover.1) =
        (fun rank ↦ quittingTerminalSemanticDebtChange
          (frontier.sourcePair (subseq rank))
          (frontier.fullResetPair mover (subseq rank)) mover.1) := by
      funext rank
      exact frontier.normalizedDebtDirection_self_eq_fullResetDebtChange
        mover (subseq rank)
    change Tendsto (fun rank ↦
      quittingStoppingLawNormalizedDebtDirection reward
        (frontier.profiles (frontier.subseq (subseq rank))) mover.1
        (frontier.bestResponse mover (frontier.subseq (subseq rank)))
        (frontier.lambda (frontier.subseq (subseq rank)))
        (frontier.lambda_pos (frontier.subseq (subseq rank))).le
        (frontier.lambda_le_one (frontier.subseq (subseq rank))) mover.1)
      atTop (nhds (frontier.tangent mover mover.1)) at hleft
    rw [heq] at hleft
    exact (tendsto_nhds_unique hleft hright).symm
  have hmoverNonneg : 0 ≤ quittingTerminalSemanticDebt cluster mover.1 :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hcluster mover.1
  have hmoverLeHalf : quittingTerminalSemanticDebt cluster mover.1 ≤
      quittingTerminalSemanticDebt frontier.base mover.1 / 2 := by
    have hdiagonal := frontier.tangent_diagonal mover
    unfold quittingTerminalSemanticDebtChange at hmoverEq
    linarith
  have htotal : (∑ observer, frontier.tangent mover observer) ≤
      quittingTerminalSemanticDebtSum cluster -
        quittingTerminalSemanticDebtSum frontier.base := by
    have hsum : (∑ observer, frontier.tangent mover observer) ≤
        ∑ observer,
          quittingTerminalSemanticDebtChange frontier.base cluster observer := by
      exact Finset.sum_le_sum fun observer _ ↦ hcoordinate observer
    unfold quittingTerminalSemanticDebtChange at hsum
    rw [Finset.sum_sub_distrib] at hsum
    exact hsum
  have hseparated : quittingTerminalSemanticDebtSum frontier.base <
      quittingTerminalSemanticDebtSum cluster := by
    linarith
  have hgain : Tendsto (fun rank ↦
      frontier.fullResetPrescribedGain mover (subseq rank)) atTop
        (nhds (-frontier.tangent mover mover.1)) := by
    have htangent := (frontier.tangent_tendsto mover mover.1).neg.comp
      hsubseq.tendsto_atTop
    change Tendsto (fun rank ↦
      -quittingStoppingLawNormalizedDebtDirection reward
        (frontier.profiles (frontier.subseq (subseq rank))) mover.1
        (frontier.bestResponse mover (frontier.subseq (subseq rank)))
        (frontier.lambda (frontier.subseq (subseq rank)))
        (frontier.lambda_pos (frontier.subseq (subseq rank))).le
        (frontier.lambda_le_one (frontier.subseq (subseq rank))) mover.1)
      atTop (nhds (-frontier.tangent mover mover.1)) at htangent
    have heqGain : (fun rank ↦
        frontier.fullResetPrescribedGain mover (subseq rank)) =
        (fun rank ↦
          -quittingStoppingLawNormalizedDebtDirection reward
            (frontier.profiles (frontier.subseq (subseq rank))) mover.1
            (frontier.bestResponse mover (frontier.subseq (subseq rank)))
            (frontier.lambda (frontier.subseq (subseq rank)))
            (frontier.lambda_pos (frontier.subseq (subseq rank))).le
            (frontier.lambda_le_one (frontier.subseq (subseq rank))) mover.1) := by
      funext rank
      exact frontier.fullResetPrescribedGain_eq_neg_normalizedDebtDirection
        mover (subseq rank)
    rw [heqGain]
    exact htangent
  have hbaseDebtPos : 0 < quittingTerminalSemanticDebt frontier.base mover.1 :=
    (frontier.active_iff mover.1).1 mover.2
  have hgainThreshold : quittingTerminalSemanticDebt frontier.base mover.1 / 4 <
      -frontier.tangent mover mover.1 := by
    have hdiagonal := frontier.tangent_diagonal mover
    linarith
  have hgainEventually : ∀ᶠ rank in atTop,
      quittingTerminalSemanticDebt frontier.base mover.1 / 4 ≤
        frontier.fullResetPrescribedGain mover (subseq rank) :=
    (hgain.eventually (Ioi_mem_nhds hgainThreshold)).mono fun _ h ↦ h.le
  refine ⟨⟨cluster, subseq, hcluster, hsubseq,
    frontier.subseq_strictMono.comp hsubseq, ?_, hcoordinate, hmoverEq,
    hmoverNonneg, hmoverLeHalf, htotal, hseparated, hgain,
    hgainEventually⟩⟩
  change Tendsto (endpoint ∘ subseq) atTop (nhds cluster)
  exact hendpoint

/-- **Supplied-mover atom adapter.**  Every supplied active mover retains its
actual source profiles, selected replacement strategies, original reset
scales, and frontier subsequence while a distinct positive observer and fixed
atom charge are selected.  In particular, this applies to the mover already
supplied by a positive-total-slope branch. -/
theorem exists_fixedAtomAlternative_of_mover
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) :
    ∃ (observer : ι) (charge : ℝ),
      observer ≠ mover.1 ∧
      0 < frontier.tangent mover observer ∧
      charge = frontier.tangent mover observer / 2 ∧
      0 < charge ∧
      ∀ᶠ rank in atTop,
        HasQuittingStoppingLawDebtSlopeAtomAlternative reward
          (frontier.profiles (frontier.subseq rank)) mover.1 observer
          (frontier.bestResponse mover (frontier.subseq rank)) charge := by
  obtain ⟨observer, hobserverNe, hpositive⟩ :=
    frontier.exists_positiveOffDiagonal mover.2
  let charge := frontier.tangent mover observer / 2
  have hcharge : 0 < charge := div_pos hpositive (by norm_num)
  have hchargeLt : charge < frontier.tangent mover observer := by
    dsimp only [charge]
    linarith
  have heventuallySlope : ∀ᶠ rank in atTop,
      charge ≤ quittingStoppingLawNormalizedDebtDirection reward
        (frontier.profiles (frontier.subseq rank)) mover.1
        (frontier.bestResponse mover (frontier.subseq rank))
        (frontier.lambda (frontier.subseq rank))
        (frontier.lambda_pos (frontier.subseq rank)).le
        (frontier.lambda_le_one (frontier.subseq rank)) observer :=
    (frontier.tangent_tendsto mover observer).eventually
      (Ioi_mem_nhds hchargeLt) |>.mono fun _ hlt ↦ hlt.le
  refine ⟨observer, charge, hobserverNe, hpositive, rfl, hcharge, ?_⟩
  filter_upwards [heventuallySlope] with rank hslopeNormalized
  have hlambda := frontier.lambda_pos (frontier.subseq rank)
  have hslope : frontier.lambda (frontier.subseq rank) * charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update
              (frontier.profiles (frontier.subseq rank)) mover.1
              (quittingStoppingLawMixtureBehaviorStrategy reward mover.1
                (frontier.profiles (frontier.subseq rank) mover.1)
                (frontier.bestResponse mover (frontier.subseq rank))
                (frontier.lambda (frontier.subseq rank)) hlambda.le
                (frontier.lambda_le_one (frontier.subseq rank))))) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (frontier.profiles (frontier.subseq rank))) observer := by
    unfold quittingStoppingLawNormalizedDebtDirection
      quittingTerminalSemanticDebtChange quittingStoppingLawResetProfile
        at hslopeNormalized
    have hscaled := (le_div_iff₀ hlambda).mp hslopeNormalized
    nlinarith
  simpa only [HasQuittingStoppingLawDebtSlopeAtomAlternative] using
    (exists_prescribedAtom_or_pureTimeRectangleAtom_of_stoppingLawDebtSlope
      reward (frontier.profiles (frontier.subseq rank)) mover.1 observer
        (frontier.bestResponse mover (frontier.subseq rank))
        (frontier.lambda (frontier.subseq rank)) charge hlambda
        (frontier.lambda_le_one (frontier.subseq rank)) hcharge hslope)

end QuittingCounterexampleStoppingLawFrontier

end GameTheory
