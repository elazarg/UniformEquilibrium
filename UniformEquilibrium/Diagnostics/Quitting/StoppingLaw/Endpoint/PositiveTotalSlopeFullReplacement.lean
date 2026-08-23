/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.OffDiagonal.SlopeFrontier
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.VanishingDebtAtomAlternative
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeAtom
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawDebtConvexity

/-!
# Full-replacement endpoints of a positive total stopping-law slope

A positive total normalized debt slope has a scale-free consequence at the
full unilateral reset endpoint.  Coordinatewise debt convexity cancels the
original positive reset scale without changing the source profile, mover, or
replacement strategy.

Compactness then yields an endpoint cluster retaining every coordinate
inequality, equality in the moved coordinate, strict total-debt separation,
and the moved player's fixed prescribed-payoff gain.  No root prefix, Bellman
return, or contradiction to the terminal exploitability witness is asserted here.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingPositiveMinimumDebtTangentFamily

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The actual source semantic pair at one rank of the frontier's selected
tangent subsequence. -/
def sourcePair (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) : QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticPair reward
    (frontier.source rank)

/-- The literal full unilateral reset using the frontier's supplied mover and
its actual selected replacement strategy at the original source rank. -/
def fullReplacementProfile
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) (rank : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  Function.update (frontier.source rank) mover.1
    (frontier.replacement mover rank)

/-- Terminal semantic pair of the literal full unilateral reset endpoint. -/
def fullReplacementPair
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) (rank : ℕ) :
    QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticPair reward (frontier.fullReplacementProfile mover rank)

/-- Prescribed-payoff gain of the supplied mover at its literal full replacement,
measured from the actual source profile at the same selected rank. -/
def fullReplacementPrescribedGain
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) (rank : ℕ) : ℝ :=
  quittingTerminalPayoff reward (frontier.fullReplacementProfile mover rank) mover.1 -
    quittingTerminalPayoff reward
      (frontier.source rank) mover.1

/-- Coordinatewise scale cancellation: the normalized debt change at the
partial reset is bounded by the full endpoint's debt change from the same
literal source. -/
theorem normalizedDebtDirection_le_fullReplacementDebtChange
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) (observer : ι) (rank : ℕ) :
    quittingStoppingLawNormalizedDebtDirection reward
        (frontier.source rank) mover.1
        (frontier.replacement mover rank)
        (frontier.scale rank)
        (frontier.scale_pos rank).le
        (frontier.scale_le_one rank) observer ≤
      quittingTerminalSemanticDebtChange (frontier.sourcePair rank)
        (frontier.fullReplacementPair mover rank) observer := by
  have hconvex := quittingTerminalSemanticDebt_stoppingLawMixture_le
    reward (frontier.source rank) mover.1 observer
      (frontier.source rank mover.1)
      (frontier.replacement mover rank)
      (frontier.scale rank)
      (frontier.scale_pos rank).le
      (frontier.scale_le_one rank)
  rw [Function.update_eq_self] at hconvex
  unfold quittingStoppingLawNormalizedDebtDirection
    quittingStoppingLawResetProfile quittingTerminalSemanticDebtChange
    sourcePair fullReplacementPair fullReplacementProfile
  rw [div_le_iff₀ (frontier.scale_pos rank)]
  nlinarith

/-- In the moved coordinate, scale cancellation is an equality because the
best-response envelope depends only on the fixed opponents. -/
theorem normalizedDebtDirection_self_eq_fullReplacementDebtChange
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) (rank : ℕ) :
    quittingStoppingLawNormalizedDebtDirection reward
        (frontier.source rank) mover.1
        (frontier.replacement mover rank)
        (frontier.scale rank)
        (frontier.scale_pos rank).le
        (frontier.scale_le_one rank) mover.1 =
      quittingTerminalSemanticDebtChange (frontier.sourcePair rank)
        (frontier.fullReplacementPair mover rank) mover.1 := by
  have haffine := quittingTerminalSemanticDebt_stoppingLawMixture_eq_self
    reward (frontier.source rank) mover.1
      (frontier.source rank mover.1)
      (frontier.replacement mover rank)
      (frontier.scale rank)
      (frontier.scale_pos rank).le
      (frontier.scale_le_one rank)
  rw [Function.update_eq_self] at haffine
  unfold quittingStoppingLawNormalizedDebtDirection
    quittingStoppingLawResetProfile quittingTerminalSemanticDebtChange
    sourcePair fullReplacementPair fullReplacementProfile
  apply (div_eq_iff (ne_of_gt
    (frontier.scale_pos rank))).2
  rw [haffine]
  ring

/-- The mover's full-replacement prescribed gain is exactly the negative normalized
self-debt direction at every original tangent rank. -/
theorem fullReplacementPrescribedGain_eq_neg_normalizedDebtDirection
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) (rank : ℕ) :
    frontier.fullReplacementPrescribedGain mover rank =
      -quittingStoppingLawNormalizedDebtDirection reward
        (frontier.source rank) mover.1
        (frontier.replacement mover rank)
        (frontier.scale rank)
        (frontier.scale_pos rank).le
        (frontier.scale_le_one rank) mover.1 := by
  rw [frontier.normalizedDebtDirection_self_eq_fullReplacementDebtChange mover rank]
  unfold fullReplacementPrescribedGain quittingTerminalSemanticDebtChange
    sourcePair fullReplacementPair fullReplacementProfile quittingTerminalSemanticDebt
    quittingTerminalSemanticPair
  simp only
  rw [quittingContinuationBestResponseValue_update_self]
  ring

/-- The literal full-replacement gain is exactly the mover's source debt minus its
remaining debt at the full replacement endpoint. -/
theorem fullReplacementPrescribedGain_eq_sourceDebt_sub_endpointDebt
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) (rank : ℕ) :
    frontier.fullReplacementPrescribedGain mover rank =
      quittingTerminalSemanticDebt (frontier.sourcePair rank) mover.1 -
        quittingTerminalSemanticDebt
          (frontier.fullReplacementPair mover rank) mover.1 := by
  rw [frontier.fullReplacementPrescribedGain_eq_neg_normalizedDebtDirection mover rank,
    frontier.normalizedDebtDirection_self_eq_fullReplacementDebtChange mover rank]
  unfold quittingTerminalSemanticDebtChange
  ring

/-- The selected full replacement has own debt at most the square of the original
reset scale at every tangent rank. -/
theorem fullReplacement_moverDebt_le_lambda_sq
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) (rank : ℕ) :
    quittingTerminalSemanticDebt (frontier.fullReplacementPair mover rank) mover.1 ≤
      frontier.scale rank ^ 2 := by
  have hbound := frontier.replacement_moverDebt_le_tolerance mover rank
  exact hbound.trans (min_le_left _ _)

/-- Pointwise full-replacement gain loses at most the squared reset scale from the
mover's actual source debt. -/
theorem sourceDebt_sub_lambda_sq_le_fullReplacementPrescribedGain
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) (rank : ℕ) :
    quittingTerminalSemanticDebt (frontier.sourcePair rank) mover.1 -
        frontier.scale rank ^ 2 ≤
      frontier.fullReplacementPrescribedGain mover rank := by
  rw [frontier.fullReplacementPrescribedGain_eq_sourceDebt_sub_endpointDebt mover rank]
  linarith [frontier.fullReplacement_moverDebt_le_lambda_sq mover rank]

/-- Pointwise, not merely eventually, the selected full replacement gains at
least half of the mover's actual source debt. -/
theorem sourceDebt_half_le_fullReplacementPrescribedGain
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) (rank : ℕ) :
    quittingTerminalSemanticDebt (frontier.sourcePair rank) mover.1 / 2 ≤
      frontier.fullReplacementPrescribedGain mover rank := by
  have hbound := frontier.replacement_moverDebt_le_tolerance mover rank
  have hhalf : quittingTerminalSemanticDebt
      (frontier.fullReplacementPair mover rank) mover.1 ≤
      quittingTerminalSemanticDebt (frontier.sourcePair rank) mover.1 / 2 :=
    hbound.trans (min_le_right _ _)
  rw [frontier.fullReplacementPrescribedGain_eq_sourceDebt_sub_endpointDebt mover rank]
  linarith

/-- The supplied mover's literal full-replacement payoff gain converges, along all
selected frontier ranks, to the negative diagonal tangent. -/
theorem fullReplacementPrescribedGain_tendsto_neg_tangentDiagonal
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) :
    Tendsto (fun rank => frontier.fullReplacementPrescribedGain mover rank) atTop
      (nhds (-frontier.tangent mover mover.1)) := by
  have htangent := (frontier.tangent_tendsto mover mover.1).neg
  apply htangent.congr'
  exact Eventually.of_forall fun rank =>
    (frontier.fullReplacementPrescribedGain_eq_neg_normalizedDebtDirection
      mover rank).symm

/-- Exact-diagonal extraction identifies the limiting full-replacement gain with
the mover's entire base debt. -/
theorem fullReplacementPrescribedGain_tendsto_baseDebt
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) :
    Tendsto (fun rank => frontier.fullReplacementPrescribedGain mover rank) atTop
      (nhds (quittingTerminalSemanticDebt frontier.base mover.1)) := by
  simpa [frontier.tangent_diagonal_eq mover] using
    frontier.fullReplacementPrescribedGain_tendsto_neg_tangentDiagonal mover

/-- Every threshold strictly below the mover's base debt is eventually below
the literal full-replacement payoff gain. -/
theorem eventually_lt_fullReplacementPrescribedGain_of_lt_baseDebt
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) (threshold : ℝ)
    (hthreshold : threshold <
      quittingTerminalSemanticDebt frontier.base mover.1) :
    ∀ᶠ rank in atTop,
      threshold < frontier.fullReplacementPrescribedGain mover rank :=
  (frontier.fullReplacementPrescribedGain_tendsto_baseDebt mover).eventually
    (Ioi_mem_nhds hthreshold)

/-- Every supplied active mover is eventually a fixed-gain legal deviation
from its literal source to its full replacement endpoint. -/
theorem eventually_baseDebt_quarter_le_fullReplacementPrescribedGain
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) :
    ∀ᶠ rank in atTop,
      quittingTerminalSemanticDebt frontier.base mover.1 / 4 ≤
        frontier.fullReplacementPrescribedGain mover rank := by
  have hdebt : 0 < quittingTerminalSemanticDebt frontier.base mover.1 :=
    (frontier.positiveDebtSupport_iff mover.1).1 mover.2
  exact (frontier.eventually_lt_fullReplacementPrescribedGain_of_lt_baseDebt mover
    (quittingTerminalSemanticDebt frontier.base mover.1 / 4) (by linarith)).mono
      fun _ h => h.le

/-- The sum of normalized coordinate changes is bounded by the full
endpoint's total-debt change from the actual source. -/
theorem sum_normalizedDebtDirection_le_fullReplacement_totalDebtChange
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) (rank : ℕ) :
    (∑ observer,
      quittingStoppingLawNormalizedDebtDirection reward
        (frontier.source rank) mover.1
        (frontier.replacement mover rank)
        (frontier.scale rank)
        (frontier.scale_pos rank).le
        (frontier.scale_le_one rank) observer) ≤
      quittingTerminalSemanticDebtSum (frontier.fullReplacementPair mover rank) -
        quittingTerminalSemanticDebtSum (frontier.sourcePair rank) := by
  have hsum :
      (∑ observer,
        quittingStoppingLawNormalizedDebtDirection reward
          (frontier.source rank) mover.1
          (frontier.replacement mover rank)
          (frontier.scale rank)
          (frontier.scale_pos rank).le
          (frontier.scale_le_one rank) observer) ≤
        ∑ observer, quittingTerminalSemanticDebtChange
          (frontier.sourcePair rank) (frontier.fullReplacementPair mover rank)
            observer := by
    exact Finset.sum_le_sum fun observer _ ↦
      frontier.normalizedDebtDirection_le_fullReplacementDebtChange mover observer rank
  unfold quittingTerminalSemanticDebtChange at hsum
  rw [Finset.sum_sub_distrib] at hsum
  exact hsum

/-- Every threshold strictly below a total tangent slope is eventually
realized as a scale-free full-replacement total-debt excursion from the literal
source profile at the same frontier rank.  This is the strongest finite-rank
form of the endpoint amplification: no passage to the limiting minimum is
needed. -/
theorem eventually_fullReplacement_sourceRelative_totalDebtChange_of_lt_totalSlope
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) (eta : ℝ)
    (heta : eta < ∑ observer, frontier.tangent mover observer) :
    ∀ᶠ rank in atTop,
      eta ≤ quittingTerminalSemanticDebtSum
          (frontier.fullReplacementPair mover rank) -
        quittingTerminalSemanticDebtSum (frontier.sourcePair rank) := by
  have hsumTendsto : Tendsto (fun rank ↦ ∑ observer,
      quittingStoppingLawNormalizedDebtDirection reward
        (frontier.source rank) mover.1
        (frontier.replacement mover rank)
        (frontier.scale rank)
        (frontier.scale_pos rank).le
        (frontier.scale_le_one rank) observer)
      atTop (nhds (∑ observer, frontier.tangent mover observer)) :=
    tendsto_finsetSum Finset.univ fun observer _ ↦
      frontier.tangent_tendsto mover observer
  filter_upwards [hsumTendsto.eventually (Ioi_mem_nhds heta)] with rank hrank
  exact hrank.le.trans
    (frontier.sum_normalizedDebtDirection_le_fullReplacement_totalDebtChange
      mover rank)

/-- Base-relative corollary of the literal source-relative endpoint
amplification.  Every source semantic pair lies above the frontier's global
minimum, so forgetting the source only weakens the conclusion. -/
theorem eventually_fullReplacement_totalDebt_excess_of_lt_positiveTotalSlope
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) (eta : ℝ)
    (heta : eta < ∑ observer, frontier.tangent mover observer) :
    ∀ᶠ rank in atTop,
      eta ≤ quittingTerminalSemanticDebtSum
          (frontier.fullReplacementPair mover rank) -
        quittingTerminalSemanticDebtSum frontier.base := by
  filter_upwards [
    frontier.eventually_fullReplacement_sourceRelative_totalDebtChange_of_lt_totalSlope
      mover eta heta] with rank hrank
  have hsourceMinimum := frontier.base_minimum (frontier.sourcePair rank)
    (quittingTerminalSemanticPair_mem_carrier reward
      (frontier.source rank))
  linarith

/-- A positive total tangent slope yields the canonical half-slope endpoint
excursion, with no residual reset-scale factor. -/
theorem eventually_fullReplacement_totalDebt_excess_of_positiveTotalSlope
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport})
    (hslope : 0 < ∑ observer, frontier.tangent mover observer) :
    ∀ᶠ rank in atTop,
      (∑ observer, frontier.tangent mover observer) / 2 ≤
        quittingTerminalSemanticDebtSum (frontier.fullReplacementPair mover rank) -
          quittingTerminalSemanticDebtSum frontier.base := by
  apply frontier.eventually_fullReplacement_totalDebt_excess_of_lt_positiveTotalSlope
    mover ((∑ observer, frontier.tangent mover observer) / 2)
  linarith

/-- Every active mover has one quantitatively large off-diagonal recipient.
Its tangent entry is at least the average of the total slope plus the mover's
entire base debt over all other players. -/
theorem exists_offDiagonal_tangent_ge_average
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) :
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

/-- Compact full-replacement endpoint data produced by one supplied positive-slope
mover.  Every field retains the actual frontier subsequence and replacement
strategies. -/
structure PositiveTotalSlopeFullReplacement
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) where
  cluster : QuittingTerminalSemanticPair ι
  subseq : ℕ → ℕ
  cluster_mem : cluster ∈ quittingTerminalSemanticCarrier reward
  subseq_strictMono : StrictMono subseq
  fullReplacement_tendsto : Tendsto (fun rank ↦
      frontier.fullReplacementPair mover (subseq rank)) atTop (nhds cluster)
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
      frontier.fullReplacementPrescribedGain mover (subseq rank)) atTop
        (nhds (-frontier.tangent mover mover.1))
  prescribedGain_eventually : ∀ᶠ rank in atTop,
    quittingTerminalSemanticDebt frontier.base mover.1 / 4 ≤
      frontier.fullReplacementPrescribedGain mover (subseq rank)

/-- A supplied positive-total-slope mover has a compact full-replacement endpoint
cluster with coordinatewise tangent domination, exact self-coordinate
change, half-debt reduction, strict total separation, and fixed prescribed
gain along the same source-matched reset sequence. -/
theorem exists_positiveTotalSlopeEndpointCluster
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport})
    (hslope : 0 < ∑ observer, frontier.tangent mover observer) :
    Nonempty (PositiveTotalSlopeFullReplacement frontier mover) := by
  let endpoint : ℕ → QuittingTerminalSemanticPair ι :=
    fun rank ↦ frontier.fullReplacementPair mover rank
  have hendpointMem : ∀ rank,
      endpoint rank ∈ quittingTerminalSemanticCarrier reward := by
    intro rank
    exact quittingTerminalSemanticPair_mem_carrier reward
      (frontier.fullReplacementProfile mover rank)
  obtain ⟨cluster, hcluster, subseq, hsubseq, hendpoint⟩ :=
    (quittingTerminalSemanticCarrier_isCompact reward).tendsto_subseq
      hendpointMem
  have hsource : Tendsto (fun rank ↦ frontier.sourcePair (subseq rank))
      atTop (nhds frontier.base) := by
    unfold sourcePair
    exact frontier.source_tendsto.comp hsubseq.tendsto_atTop
  have hcoordinate : ∀ observer,
      frontier.tangent mover observer ≤
        quittingTerminalSemanticDebtChange frontier.base cluster observer := by
    intro observer
    have hleft := (frontier.tangent_tendsto mover observer).comp
      hsubseq.tendsto_atTop
    have hright : Tendsto (fun rank ↦
        quittingTerminalSemanticDebtChange
          (frontier.sourcePair (subseq rank))
          (frontier.fullReplacementPair mover (subseq rank)) observer)
        atTop (nhds
          (quittingTerminalSemanticDebtChange frontier.base cluster observer)) := by
      unfold quittingTerminalSemanticDebtChange
      exact ((continuous_quittingTerminalSemanticDebt observer).tendsto cluster
        |>.comp hendpoint).sub
          ((continuous_quittingTerminalSemanticDebt observer).tendsto frontier.base
            |>.comp hsource)
    exact le_of_tendsto_of_tendsto hleft hright
      (Eventually.of_forall fun rank ↦
        frontier.normalizedDebtDirection_le_fullReplacementDebtChange
          mover observer (subseq rank))
  have hmoverEq : quittingTerminalSemanticDebtChange frontier.base cluster mover.1 =
      frontier.tangent mover mover.1 := by
    have hleft := (frontier.tangent_tendsto mover mover.1).comp
      hsubseq.tendsto_atTop
    have hright : Tendsto (fun rank ↦
        quittingTerminalSemanticDebtChange
          (frontier.sourcePair (subseq rank))
          (frontier.fullReplacementPair mover (subseq rank)) mover.1)
        atTop (nhds
          (quittingTerminalSemanticDebtChange frontier.base cluster mover.1)) := by
      unfold quittingTerminalSemanticDebtChange
      exact ((continuous_quittingTerminalSemanticDebt mover.1).tendsto cluster
        |>.comp hendpoint).sub
          ((continuous_quittingTerminalSemanticDebt mover.1).tendsto frontier.base
            |>.comp hsource)
    have heq : (fun rank ↦
        quittingStoppingLawNormalizedDebtDirection reward
          (frontier.source (subseq rank)) mover.1
          (frontier.replacement mover (subseq rank))
          (frontier.scale (subseq rank))
          (frontier.scale_pos (subseq rank)).le
          (frontier.scale_le_one (subseq rank)) mover.1) =
        (fun rank ↦ quittingTerminalSemanticDebtChange
          (frontier.sourcePair (subseq rank))
          (frontier.fullReplacementPair mover (subseq rank)) mover.1) := by
      funext rank
      exact frontier.normalizedDebtDirection_self_eq_fullReplacementDebtChange
        mover (subseq rank)
    change Tendsto (fun rank ↦
      quittingStoppingLawNormalizedDebtDirection reward
        (frontier.source (subseq rank)) mover.1
        (frontier.replacement mover (subseq rank))
        (frontier.scale (subseq rank))
        (frontier.scale_pos (subseq rank)).le
        (frontier.scale_le_one (subseq rank)) mover.1)
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
      frontier.fullReplacementPrescribedGain mover (subseq rank)) atTop
        (nhds (-frontier.tangent mover mover.1)) := by
    have htangent := (frontier.tangent_tendsto mover mover.1).neg.comp
      hsubseq.tendsto_atTop
    change Tendsto (fun rank ↦
      -quittingStoppingLawNormalizedDebtDirection reward
        (frontier.source (subseq rank)) mover.1
        (frontier.replacement mover (subseq rank))
        (frontier.scale (subseq rank))
        (frontier.scale_pos (subseq rank)).le
        (frontier.scale_le_one (subseq rank)) mover.1)
      atTop (nhds (-frontier.tangent mover mover.1)) at htangent
    have heqGain : (fun rank ↦
        frontier.fullReplacementPrescribedGain mover (subseq rank)) =
        (fun rank ↦
          -quittingStoppingLawNormalizedDebtDirection reward
            (frontier.source (subseq rank)) mover.1
            (frontier.replacement mover (subseq rank))
            (frontier.scale (subseq rank))
            (frontier.scale_pos (subseq rank)).le
            (frontier.scale_le_one (subseq rank)) mover.1) := by
      funext rank
      exact frontier.fullReplacementPrescribedGain_eq_neg_normalizedDebtDirection
        mover (subseq rank)
    rw [heqGain]
    exact htangent
  have hbaseDebtPos : 0 < quittingTerminalSemanticDebt frontier.base mover.1 :=
    (frontier.positiveDebtSupport_iff mover.1).1 mover.2
  have hgainThreshold : quittingTerminalSemanticDebt frontier.base mover.1 / 4 <
      -frontier.tangent mover mover.1 := by
    have hdiagonal := frontier.tangent_diagonal mover
    linarith
  have hgainEventually : ∀ᶠ rank in atTop,
      quittingTerminalSemanticDebt frontier.base mover.1 / 4 ≤
        frontier.fullReplacementPrescribedGain mover (subseq rank) :=
    (hgain.eventually (Ioi_mem_nhds hgainThreshold)).mono fun _ h ↦ h.le
  refine ⟨⟨cluster, subseq, hcluster, hsubseq, ?_, hcoordinate, hmoverEq,
    hmoverNonneg, hmoverLeHalf, htotal, hseparated, hgain,
    hgainEventually⟩⟩
  change Tendsto (endpoint ∘ subseq) atTop (nhds cluster)
  exact hendpoint

/-- Exact diagonal upgrades every positive-slope full-replacement endpoint's
half-debt estimate to zero own debt. -/
theorem PositiveTotalSlopeFullReplacement.mover_debt_eq_zero
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    {mover : {who // who ∈ frontier.positiveDebtSupport}}
    (endpoint : PositiveTotalSlopeFullReplacement frontier mover) :
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
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) :
    ∃ (observer : ι) (charge : ℝ),
      observer ≠ mover.1 ∧
      0 < frontier.tangent mover observer ∧
      charge = frontier.tangent mover observer / 2 ∧
      0 < charge ∧
      ∀ᶠ rank in atTop,
        HasQuittingStoppingLawDebtSlopeAtomAlternative reward
          (frontier.source rank) mover.1 observer
          (frontier.replacement mover rank) charge := by
  obtain ⟨observer, hobserverNe, hpositive⟩ :=
    frontier.exists_positiveOffDiagonal mover.2
  let charge := frontier.tangent mover observer / 2
  have hpositive' : 0 < frontier.tangent mover observer := by
    have heq : mover = ⟨mover.1, _⟩ := Subtype.ext (by rfl)
    rw [heq]
    exact hpositive
  have hcharge : 0 < charge := div_pos hpositive' (by norm_num)
  have hchargeLt : charge < frontier.tangent mover observer := by
    dsimp only [charge]
    linarith
  have heventuallySlope : ∀ᶠ rank in atTop,
      charge ≤ quittingStoppingLawNormalizedDebtDirection reward
        (frontier.source rank) mover.1
        (frontier.replacement mover rank)
        (frontier.scale rank)
        (frontier.scale_pos rank).le
        (frontier.scale_le_one rank) observer :=
    (frontier.tangent_tendsto mover observer).eventually
      (Ioi_mem_nhds hchargeLt) |>.mono fun _ hlt ↦ hlt.le
  refine ⟨observer, charge, hobserverNe, hpositive, rfl, hcharge, ?_⟩
  filter_upwards [heventuallySlope] with rank hslopeNormalized
  have hlambda := frontier.scale_pos rank
  have hslope : frontier.scale rank * charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update
              (frontier.source rank) mover.1
              (quittingStoppingLawMixtureBehaviorStrategy reward mover.1
                (frontier.source rank mover.1)
                (frontier.replacement mover rank)
                (frontier.scale rank) hlambda.le
                (frontier.scale_le_one rank)))) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (frontier.source rank)) observer := by
    unfold quittingStoppingLawNormalizedDebtDirection
      quittingTerminalSemanticDebtChange quittingStoppingLawResetProfile
        at hslopeNormalized
    have hscaled := (le_div_iff₀ hlambda).mp hslopeNormalized
    nlinarith
  simpa only [HasQuittingStoppingLawDebtSlopeAtomAlternative] using
    (exists_prescribedAtom_or_pureTimeRectangleAtom_of_stoppingLawDebtSlope
      reward (frontier.source rank) mover.1 observer
        (frontier.replacement mover rank)
        (frontier.scale rank) charge hlambda
        (frontier.scale_le_one rank) hcharge hslope)

/-- A supplied positive off-diagonal tangent entry exports the strong
common-response atom alternative at exactly `7/16` of that entry. -/
theorem exists_fixedStrongVanishingDebtAtomAlternative_of_positiveOffDiagonal
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) (observer : ι)
    (hpositive : 0 < frontier.tangent mover observer) :
    ∃ charge : ℝ,
      charge = 7 * frontier.tangent mover observer / 16 ∧
      0 < charge ∧
      ∀ᶠ rank in atTop,
        HasQuittingStoppingLawVanishingDebtAtomAlternative reward
          (frontier.source rank) mover.1 observer
          (frontier.replacement mover rank) charge
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
        (frontier.source rank) mover.1
        (frontier.replacement mover rank)
        (frontier.scale rank)
        (frontier.scale_pos rank).le
        (frontier.scale_le_one rank) observer :=
    (frontier.tangent_tendsto mover observer).eventually
      (Ioi_mem_nhds hrawChargeLt) |>.mono fun _ hlt => hlt.le
  refine ⟨charge, ?_, hcharge, ?_⟩
  · dsimp only [charge, rawCharge]
    ring
  · filter_upwards [heventuallyDirection] with rank hdirection
    have hrise : rawCharge ≤
        quittingTerminalSemanticDebt
            (frontier.fullReplacementPair mover rank) observer -
          quittingTerminalSemanticDebt (frontier.sourcePair rank) observer :=
      hdirection.trans
        (frontier.normalizedDebtDirection_le_fullReplacementDebtChange
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
      reward (frontier.source rank) mover.1 observer
      (frontier.replacement mover rank) rawCharge
      (quittingStoppingLawAtomDecoderError charge rank) hrawCharge herror
      herrorLeRaw (by
        simpa only [fullReplacementPair, fullReplacementProfile, sourcePair] using hrise)
    have hchargeEq : 7 * rawCharge / 8 = charge := rfl
    rw [hchargeEq] at halternative
    exact halternative

/-- **Supplied-mover strong atom adapter.**  Every active mover has a fixed
positive off-diagonal observer for which the literal full-replacement debt rise
exports the common-response vanishing-debt atom alternative.  If the tangent
entry is `tau`, the retained atom-interface charge is exactly `7 * tau / 16`.
No zero-debt assumption on the observer is used. -/
theorem exists_fixedStrongVanishingDebtAtomAlternative_of_mover
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) :
    ∃ (observer : ι) (charge : ℝ),
      observer ≠ mover.1 ∧
      0 < frontier.tangent mover observer ∧
      charge = 7 * frontier.tangent mover observer / 16 ∧
      0 < charge ∧
      ∀ᶠ rank in atTop,
        HasQuittingStoppingLawVanishingDebtAtomAlternative reward
          (frontier.source rank) mover.1 observer
          (frontier.replacement mover rank) charge
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
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) :
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
          (frontier.source rank) mover.1 observer
          (frontier.replacement mover rank) charge
          (quittingStoppingLawAtomDecoderError charge rank) := by
  obtain ⟨observer, hobserverNe, hobserverLower⟩ :=
    frontier.exists_offDiagonal_tangent_ge_average mover
  have hsum : 0 ≤ ∑ who, frontier.tangent mover who :=
    frontier.tangent_sum_nonneg mover
  have hdebt : 0 < quittingTerminalSemanticDebt frontier.base mover.1 :=
    (frontier.positiveDebtSupport_iff mover.1).1 mover.2
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

end QuittingPositiveMinimumDebtTangentFamily

end GameTheory
