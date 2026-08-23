/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.OffDiagonal.SlopeFrontier
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.VanishingDebtAtomAlternative
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

/-- The literal full-reset gain is exactly the mover's source debt minus its
remaining debt at the full replacement endpoint. -/
theorem fullResetPrescribedGain_eq_sourceDebt_sub_endpointDebt
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) (rank : ℕ) :
    frontier.fullResetPrescribedGain mover rank =
      quittingTerminalSemanticDebt (frontier.sourcePair rank) mover.1 -
        quittingTerminalSemanticDebt
          (frontier.fullResetPair mover rank) mover.1 := by
  rw [frontier.fullResetPrescribedGain_eq_neg_normalizedDebtDirection mover rank,
    frontier.normalizedDebtDirection_self_eq_fullResetDebtChange mover rank]
  unfold quittingTerminalSemanticDebtChange
  ring

/-- The selected full reset has own debt at most the square of the original
reset scale at every tangent rank. -/
theorem fullReset_moverDebt_le_lambda_sq
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) (rank : ℕ) :
    quittingTerminalSemanticDebt (frontier.fullResetPair mover rank) mover.1 ≤
      frontier.lambda (frontier.subseq rank) ^ 2 := by
  have hbound := frontier.fullReset_moverDebt_le_tolerance mover rank
  exact hbound.trans (min_le_left _ _)

/-- Pointwise full-reset gain loses at most the squared reset scale from the
mover's actual source debt. -/
theorem sourceDebt_sub_lambda_sq_le_fullResetPrescribedGain
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) (rank : ℕ) :
    quittingTerminalSemanticDebt (frontier.sourcePair rank) mover.1 -
        frontier.lambda (frontier.subseq rank) ^ 2 ≤
      frontier.fullResetPrescribedGain mover rank := by
  rw [frontier.fullResetPrescribedGain_eq_sourceDebt_sub_endpointDebt mover rank]
  linarith [frontier.fullReset_moverDebt_le_lambda_sq mover rank]

/-- Pointwise, not merely eventually, the selected full replacement gains at
least half of the mover's actual source debt. -/
theorem sourceDebt_half_le_fullResetPrescribedGain
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) (rank : ℕ) :
    quittingTerminalSemanticDebt (frontier.sourcePair rank) mover.1 / 2 ≤
      frontier.fullResetPrescribedGain mover rank := by
  have hbound := frontier.fullReset_moverDebt_le_tolerance mover rank
  have hhalf : quittingTerminalSemanticDebt
      (frontier.fullResetPair mover rank) mover.1 ≤
      quittingTerminalSemanticDebt (frontier.sourcePair rank) mover.1 / 2 :=
    hbound.trans (min_le_right _ _)
  rw [frontier.fullResetPrescribedGain_eq_sourceDebt_sub_endpointDebt mover rank]
  linarith

/-- The supplied mover's literal full-reset payoff gain converges, along all
selected frontier ranks, to the negative diagonal tangent. -/
theorem fullResetPrescribedGain_tendsto_neg_tangentDiagonal
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) :
    Tendsto (fun rank => frontier.fullResetPrescribedGain mover rank) atTop
      (nhds (-frontier.tangent mover mover.1)) := by
  have htangent := (frontier.tangent_tendsto mover mover.1).neg
  apply htangent.congr'
  exact Eventually.of_forall fun rank =>
    (frontier.fullResetPrescribedGain_eq_neg_normalizedDebtDirection
      mover rank).symm

/-- Exact-diagonal extraction identifies the limiting full-reset gain with
the mover's entire base debt. -/
theorem fullResetPrescribedGain_tendsto_baseDebt
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) :
    Tendsto (fun rank => frontier.fullResetPrescribedGain mover rank) atTop
      (nhds (quittingTerminalSemanticDebt frontier.base mover.1)) := by
  simpa [frontier.tangent_diagonal_eq mover] using
    frontier.fullResetPrescribedGain_tendsto_neg_tangentDiagonal mover

/-- Every threshold strictly below the mover's base debt is eventually below
the literal full-reset payoff gain. -/
theorem eventually_lt_fullResetPrescribedGain_of_lt_baseDebt
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) (threshold : ℝ)
    (hthreshold : threshold <
      quittingTerminalSemanticDebt frontier.base mover.1) :
    ∀ᶠ rank in atTop,
      threshold < frontier.fullResetPrescribedGain mover rank :=
  (frontier.fullResetPrescribedGain_tendsto_baseDebt mover).eventually
    (Ioi_mem_nhds hthreshold)

/-- Every supplied active mover is eventually a fixed-gain legal deviation
from its literal source to its full reset endpoint. -/
theorem eventually_baseDebt_quarter_le_fullResetPrescribedGain
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) :
    ∀ᶠ rank in atTop,
      quittingTerminalSemanticDebt frontier.base mover.1 / 4 ≤
        frontier.fullResetPrescribedGain mover rank := by
  have hdebt : 0 < quittingTerminalSemanticDebt frontier.base mover.1 :=
    (frontier.active_iff mover.1).1 mover.2
  exact (frontier.eventually_lt_fullResetPrescribedGain_of_lt_baseDebt mover
    (quittingTerminalSemanticDebt frontier.base mover.1 / 4) (by linarith)).mono
      fun _ h => h.le

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

/-- Every threshold strictly below a total tangent slope is eventually
realized as a scale-free full-reset total-debt excursion from the literal
source profile at the same frontier rank.  This is the strongest finite-rank
form of the endpoint amplification: no passage to the limiting minimum is
needed. -/
theorem eventually_fullReset_sourceRelative_totalDebtChange_of_lt_totalSlope
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) (eta : ℝ)
    (heta : eta < ∑ observer, frontier.tangent mover observer) :
    ∀ᶠ rank in atTop,
      eta ≤ quittingTerminalSemanticDebtSum
          (frontier.fullResetPair mover rank) -
        quittingTerminalSemanticDebtSum (frontier.sourcePair rank) := by
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
  exact hrank.le.trans
    (frontier.sum_normalizedDebtDirection_le_fullReset_totalDebtChange
      mover rank)

/-- Base-relative corollary of the literal source-relative endpoint
amplification.  Every source semantic pair lies above the frontier's global
minimum, so forgetting the source only weakens the conclusion. -/
theorem eventually_fullReset_totalDebt_excess_of_lt_positiveTotalSlope
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) (eta : ℝ)
    (heta : eta < ∑ observer, frontier.tangent mover observer) :
    ∀ᶠ rank in atTop,
      eta ≤ quittingTerminalSemanticDebtSum
          (frontier.fullResetPair mover rank) -
        quittingTerminalSemanticDebtSum frontier.base := by
  filter_upwards [
    frontier.eventually_fullReset_sourceRelative_totalDebtChange_of_lt_totalSlope
      mover eta heta] with rank hrank
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

/-- Every active mover has one quantitatively large off-diagonal recipient.
Its tangent entry is at least the average of the total slope plus the mover's
entire base debt over all other players. -/
theorem exists_offDiagonal_tangent_ge_average
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) :
    ∃ observer : ι, observer ≠ mover.1 ∧
      ((∑ who, frontier.tangent mover who) +
          quittingTerminalSemanticDebt frontier.base mover.1) /
        ((Finset.univ.erase mover.1).card : ℝ) ≤
      frontier.tangent mover observer := by
  classical
  obtain ⟨positiveObserver, hpositiveNe, _hpositive⟩ :=
    frontier.exists_positiveOffDiagonal mover.2
  have hopponents : (Finset.univ.erase mover.1).Nonempty :=
    ⟨positiveObserver, Finset.mem_erase.mpr
      ⟨hpositiveNe, Finset.mem_univ positiveObserver⟩⟩
  obtain ⟨observer, hobserver, hobserverMax⟩ :=
    Finset.exists_max_image (Finset.univ.erase mover.1)
      (frontier.tangent mover) hopponents
  have hsumLe :
      (∑ who ∈ Finset.univ.erase mover.1, frontier.tangent mover who) ≤
        ((Finset.univ.erase mover.1).card : ℝ) *
          frontier.tangent mover observer := by
    have hbound := (Finset.univ.erase mover.1).sum_le_card_nsmul
      (frontier.tangent mover) (frontier.tangent mover observer)
      (fun who hwho => hobserverMax who hwho)
    simpa [nsmul_eq_mul, mul_comm] using hbound
  have hsumSplit := Finset.sum_erase_add Finset.univ
    (frontier.tangent mover) (Finset.mem_univ mover.1)
  have hdiagonal := frontier.tangent_diagonal_eq mover
  have hsumLower :
      (∑ who, frontier.tangent mover who) +
          quittingTerminalSemanticDebt frontier.base mover.1 ≤
        ∑ who ∈ Finset.univ.erase mover.1, frontier.tangent mover who := by
    linarith
  have hcardPos : 0 < ((Finset.univ.erase mover.1).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hopponents
  refine ⟨observer, (Finset.mem_erase.mp hobserver).1, ?_⟩
  apply (div_le_iff₀ hcardPos).2
  simpa only [mul_comm] using hsumLower.trans hsumLe

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

/-- Exact diagonal upgrades every positive-slope full-reset endpoint's
half-debt estimate to zero own debt. -/
theorem PositiveTotalSlopeEndpointCluster.mover_debt_eq_zero
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    {mover : {who // who ∈ frontier.active}}
    (endpoint : PositiveTotalSlopeEndpointCluster frontier mover) :
    quittingTerminalSemanticDebt endpoint.cluster mover.1 = 0 := by
  have hchange := endpoint.mover_excess_eq
  have hexactDiagonal := frontier.tangent_diagonal_eq mover
  unfold quittingTerminalSemanticDebtChange at hchange
  linarith

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

/-- A supplied positive off-diagonal tangent entry exports the strong
common-response atom alternative at exactly `7/16` of that entry. -/
theorem exists_fixedStrongVanishingDebtAtomAlternative_of_positiveOffDiagonal
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) (observer : ι)
    (hpositive : 0 < frontier.tangent mover observer) :
    ∃ charge : ℝ,
      charge = 7 * frontier.tangent mover observer / 16 ∧
      0 < charge ∧
      ∀ᶠ rank in atTop,
        HasQuittingStoppingLawVanishingDebtAtomAlternative reward
          (frontier.profiles (frontier.subseq rank)) mover.1 observer
          (frontier.bestResponse mover (frontier.subseq rank)) charge
          (quittingStoppingLawAtomDecoderError charge rank) := by
  let rawCharge := frontier.tangent mover observer / 2
  let charge := 7 * rawCharge / 8
  have hrawCharge : 0 < rawCharge := div_pos hpositive (by norm_num)
  have hcharge : 0 < charge := by
    dsimp only [charge]
    positivity
  have hrawChargeLt : rawCharge < frontier.tangent mover observer := by
    dsimp only [rawCharge]
    linarith
  have heventuallyDirection : ∀ᶠ rank in atTop,
      rawCharge ≤ quittingStoppingLawNormalizedDebtDirection reward
        (frontier.profiles (frontier.subseq rank)) mover.1
        (frontier.bestResponse mover (frontier.subseq rank))
        (frontier.lambda (frontier.subseq rank))
        (frontier.lambda_pos (frontier.subseq rank)).le
        (frontier.lambda_le_one (frontier.subseq rank)) observer :=
    (frontier.tangent_tendsto mover observer).eventually
      (Ioi_mem_nhds hrawChargeLt) |>.mono fun _ hlt => hlt.le
  refine ⟨charge, ?_, hcharge, ?_⟩
  · dsimp only [charge, rawCharge]
    ring
  · filter_upwards [heventuallyDirection] with rank hdirection
    have hrise : rawCharge ≤
        quittingTerminalSemanticDebt
            (frontier.fullResetPair mover rank) observer -
          quittingTerminalSemanticDebt (frontier.sourcePair rank) observer :=
      hdirection.trans
        (frontier.normalizedDebtDirection_le_fullResetDebtChange
          mover observer rank)
    have herror := quittingStoppingLawAtomDecoderError_pos hcharge rank
    have herrorLeCharge :=
      quittingStoppingLawAtomDecoderError_le hcharge.le rank
    have hchargeLeRaw : charge ≤ rawCharge := by
      dsimp only [charge]
      linarith
    have herrorLeRaw : quittingStoppingLawAtomDecoderError charge rank ≤
        rawCharge / 8 := herrorLeCharge.trans
      (div_le_div_of_nonneg_right hchargeLeRaw (by norm_num))
    have halternative := hasVanishingDebtAtomAlternative_of_endpointDebtRise
      reward (frontier.profiles (frontier.subseq rank)) mover.1 observer
      (frontier.bestResponse mover (frontier.subseq rank)) rawCharge
      (quittingStoppingLawAtomDecoderError charge rank) hrawCharge herror
      herrorLeRaw (by
        simpa only [fullResetPair, fullResetProfile, sourcePair] using hrise)
    have hchargeEq : 7 * rawCharge / 8 = charge := rfl
    rw [hchargeEq] at halternative
    exact halternative

/-- **Supplied-mover strong atom adapter.**  Every active mover has a fixed
positive off-diagonal observer for which the literal full-reset debt rise
exports the common-response vanishing-debt atom alternative.  If the tangent
entry is `tau`, the retained atom-interface charge is exactly `7 * tau / 16`.
No zero-debt assumption on the observer is used. -/
theorem exists_fixedStrongVanishingDebtAtomAlternative_of_mover
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) :
    ∃ (observer : ι) (charge : ℝ),
      observer ≠ mover.1 ∧
      0 < frontier.tangent mover observer ∧
      charge = 7 * frontier.tangent mover observer / 16 ∧
      0 < charge ∧
      ∀ᶠ rank in atTop,
        HasQuittingStoppingLawVanishingDebtAtomAlternative reward
          (frontier.profiles (frontier.subseq rank)) mover.1 observer
          (frontier.bestResponse mover (frontier.subseq rank)) charge
          (quittingStoppingLawAtomDecoderError charge rank) := by
  obtain ⟨observer, hobserverNe, hpositive⟩ :=
    frontier.exists_positiveOffDiagonal mover.2
  obtain ⟨charge, hchargeEq, hcharge, halternative⟩ :=
    frontier.exists_fixedStrongVanishingDebtAtomAlternative_of_positiveOffDiagonal
      mover observer hpositive
  exact ⟨observer, charge, hobserverNe, hpositive, hchargeEq, hcharge,
    halternative⟩

/-- Quantitative supplied-mover form of the strong atom adapter.  The chosen
observer is at least the average forced by the total slope and the mover's
negative diagonal, and its atom charge remains exactly `7/16` of that entry. -/
theorem exists_quantitativeStrongVanishingDebtAtomAlternative_of_mover
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) :
    ∃ (observer : ι) (charge : ℝ),
      observer ≠ mover.1 ∧
      ((∑ who, frontier.tangent mover who) +
          quittingTerminalSemanticDebt frontier.base mover.1) /
          ((Finset.univ.erase mover.1).card : ℝ) ≤
        frontier.tangent mover observer ∧
      charge = 7 * frontier.tangent mover observer / 16 ∧
      0 < charge ∧
      ∀ᶠ rank in atTop,
        HasQuittingStoppingLawVanishingDebtAtomAlternative reward
          (frontier.profiles (frontier.subseq rank)) mover.1 observer
          (frontier.bestResponse mover (frontier.subseq rank)) charge
          (quittingStoppingLawAtomDecoderError charge rank) := by
  obtain ⟨observer, hobserverNe, hobserverLower⟩ :=
    frontier.exists_offDiagonal_tangent_ge_average mover
  have hsum : 0 ≤ ∑ who, frontier.tangent mover who :=
    frontier.tangent_sum_nonneg mover
  have hdebt : 0 < quittingTerminalSemanticDebt frontier.base mover.1 :=
    (frontier.active_iff mover.1).1 mover.2
  have hcardPos : 0 < ((Finset.univ.erase mover.1).card : ℝ) := by
    have hpositiveObserver := frontier.exists_positiveOffDiagonal mover.2
    obtain ⟨positiveObserver, hpositiveNe, _hpositive⟩ := hpositiveObserver
    exact_mod_cast Finset.card_pos.mpr
      ⟨positiveObserver, Finset.mem_erase.mpr
        ⟨hpositiveNe, Finset.mem_univ positiveObserver⟩⟩
  have haveragePos : 0 <
      ((∑ who, frontier.tangent mover who) +
          quittingTerminalSemanticDebt frontier.base mover.1) /
        ((Finset.univ.erase mover.1).card : ℝ) := by
    positivity
  have hpositive : 0 < frontier.tangent mover observer :=
    haveragePos.trans_le hobserverLower
  obtain ⟨charge, hchargeEq, hcharge, halternative⟩ :=
    frontier.exists_fixedStrongVanishingDebtAtomAlternative_of_positiveOffDiagonal
      mover observer hpositive
  exact ⟨observer, charge, hobserverNe, hobserverLower, hchargeEq, hcharge,
    halternative⟩

end QuittingCounterexampleStoppingLawFrontier

end GameTheory
