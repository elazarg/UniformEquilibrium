/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.SourceMatchedChattering
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawMinimumFiberAffine

/-!
# Radial scaling of source-matched stopping-law tangent columns

A source-matched tangent column is realized by one complete stopping-law reset
of weight `lambda`.  To scale that column by a coefficient in `[0, 1]`, use
that literal reset strategy as the endpoint of a second stopping-law mixture.
The resulting nested mixture is again one legal behavioral strategy.

The convexity loss of this radial scaling is controlled by the source's excess
above the exact minimum and by the full column's total-debt slope.  Both are
negligible relative to `lambda` on the selected frontier subsequence.  Hence a
flat tangent column scales homogeneously in every debt coordinate.

This removes the need to interpret a scalar coefficient as an external formal
multiplicity.  It does not yet combine several scaled columns into a temporal
quitting-game path.
-/

noncomputable section

namespace GameTheory

open Filter Finset Math.Probability
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {witness : QuittingTerminalExploitabilityWitness reward}

namespace QuittingCounterexampleStoppingLawFrontier

/-- The actual reset strategy which realizes one extracted normalized chord at
one selected common-source rank. -/
def sourceMatchedInnerResetStrategy
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (rank : ℕ) (mover : {who // who ∈ frontier.active}) :
    (quittingGame reward).BehaviorStrategy mover.1 :=
  quittingStoppingLawMixtureBehaviorStrategy reward mover.1
    (frontier.profiles (frontier.subseq rank) mover.1)
    (frontier.bestResponse mover (frontier.subseq rank))
    (frontier.lambda (frontier.subseq rank))
    (frontier.lambda_pos (frontier.subseq rank)).le
    (frontier.lambda_le_one (frontier.subseq rank))

/-- A literal radial scaling of one source-matched reset.  The outer weight is
independent of the frontier reset scale. -/
def sourceMatchedRadialResetProfile
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (rank : ℕ) (mover : {who // who ∈ frontier.active})
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1) :
    (quittingGame reward).BehaviorProfile :=
  let source := frontier.profiles (frontier.subseq rank)
  Function.update source mover.1
    (quittingStoppingLawMixtureBehaviorStrategy reward mover.1
      (source mover.1)
      (frontier.sourceMatchedInnerResetStrategy rank mover)
      weight hweight0 hweight1)

/-- Debt direction of the radial reset, normalized by the original frontier
scale rather than by the outer coefficient. -/
def sourceMatchedRadialDebtDirection
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (rank : ℕ) (mover : {who // who ∈ frontier.active})
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (observer : ι) : ℝ :=
  quittingTerminalSemanticDebtChange
      (quittingTerminalSemanticPair reward
        (frontier.profiles (frontier.subseq rank)))
      (quittingTerminalSemanticPair reward
        (frontier.sourceMatchedRadialResetProfile rank mover weight
          hweight0 hweight1)) observer /
    frontier.lambda (frontier.subseq rank)

/-- The total normalized debt slope of one actual source-matched reset is the
sum of its normalized coordinate directions. -/
theorem sourceMatched_totalDebtDirection_eq_sum
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (rank : ℕ) (mover : {who // who ∈ frontier.active}) :
    (quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (Function.update
              (frontier.profiles (frontier.subseq rank)) mover.1
              (frontier.sourceMatchedInnerResetStrategy rank mover))) -
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (frontier.profiles (frontier.subseq rank)))) /
        frontier.lambda (frontier.subseq rank) =
      ∑ observer, frontier.actualDebtDirection rank mover observer := by
  unfold quittingTerminalSemanticDebtSum actualDebtDirection
    quittingStoppingLawNormalizedDebtDirection
    quittingStoppingLawResetProfile quittingTerminalSemanticDebtChange
    sourceMatchedInnerResetStrategy
  rw [← Finset.sum_sub_distrib, Finset.sum_div]

/-- **Finite-rank radial scaling bound.**

The difference between the formally scaled source column and the literal
radial reset column is nonnegative coordinatewise.  After normalization by the
frontier scale it is bounded by the normalized source excess plus the outer
weight times the full column's total normalized slope. -/
theorem sourceMatchedRadialDebtDirection_gap_bounds
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (rank : ℕ) (mover : {who // who ∈ frontier.active})
    (observer : ι) (weight : ℝ)
    (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1) :
    0 ≤ weight * frontier.actualDebtDirection rank mover observer -
        frontier.sourceMatchedRadialDebtDirection rank mover weight
          hweight0 hweight1 observer ∧
      weight * frontier.actualDebtDirection rank mover observer -
          frontier.sourceMatchedRadialDebtDirection rank mover weight
            hweight0 hweight1 observer ≤
        (quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                (frontier.profiles (frontier.subseq rank))) -
            quittingTerminalSemanticDebtSum frontier.base) /
              frontier.lambda (frontier.subseq rank) +
          weight *
            (∑ who, frontier.actualDebtDirection rank mover who) := by
  let sourceProfile := frontier.profiles (frontier.subseq rank)
  let endpointStrategy := frontier.sourceMatchedInnerResetStrategy rank mover
  let endpointProfile := Function.update sourceProfile mover.1 endpointStrategy
  let radialProfile := frontier.sourceMatchedRadialResetProfile rank mover
    weight hweight0 hweight1
  let sourcePair := quittingTerminalSemanticPair reward sourceProfile
  let endpointPair := quittingTerminalSemanticPair reward endpointProfile
  let radialPair := quittingTerminalSemanticPair reward radialProfile
  let epsilon := quittingTerminalSemanticDebtSum sourcePair -
    quittingTerminalSemanticDebtSum frontier.base
  have hnear : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (Function.update sourceProfile mover.1 (sourceProfile mover.1))) ≤
        quittingTerminalSemanticDebtSum candidate + epsilon := by
    intro candidate hcandidate
    rw [Function.update_eq_self]
    dsimp only [epsilon, sourcePair]
    have hbase := frontier.base_minimum candidate hcandidate
    linarith
  have hraw :=
    quittingTerminalSemanticDebt_stoppingLawMixture_chordGap_le_nearMinimum
      reward sourceProfile mover.1 observer (sourceProfile mover.1)
        endpointStrategy weight epsilon hweight0 hweight1 hnear
  dsimp only at hraw
  rw [Function.update_eq_self] at hraw
  have hlambda := frontier.lambda_pos (frontier.subseq rank)
  have hgapIdentity :
      ((1 - weight) * quittingTerminalSemanticDebt sourcePair observer +
            weight * quittingTerminalSemanticDebt endpointPair observer -
          quittingTerminalSemanticDebt radialPair observer) /
          frontier.lambda (frontier.subseq rank) =
        weight * frontier.actualDebtDirection rank mover observer -
          frontier.sourceMatchedRadialDebtDirection rank mover weight
            hweight0 hweight1 observer := by
    dsimp only [sourcePair, endpointPair, radialPair, sourceProfile,
      endpointProfile, radialProfile, endpointStrategy]
    unfold actualDebtDirection quittingStoppingLawNormalizedDebtDirection
      sourceMatchedRadialDebtDirection sourceMatchedRadialResetProfile
      sourceMatchedInnerResetStrategy quittingStoppingLawResetProfile
      quittingTerminalSemanticDebtChange
    field_simp [ne_of_gt hlambda]
    ring
  have htotalIdentity :
      (quittingTerminalSemanticDebtSum endpointPair -
          quittingTerminalSemanticDebtSum sourcePair) /
          frontier.lambda (frontier.subseq rank) =
        ∑ who, frontier.actualDebtDirection rank mover who := by
    dsimp only [endpointPair, sourcePair, endpointProfile, sourceProfile]
    exact frontier.sourceMatched_totalDebtDirection_eq_sum rank mover
  have hlower := div_nonneg hraw.1 hlambda.le
  have hupper := (div_le_div_iff_of_pos_right hlambda).2 hraw.2
  change 0 ≤
    ((1 - weight) * quittingTerminalSemanticDebt sourcePair observer +
          weight * quittingTerminalSemanticDebt endpointPair observer -
        quittingTerminalSemanticDebt radialPair observer) /
      frontier.lambda (frontier.subseq rank) at hlower
  change
    ((1 - weight) * quittingTerminalSemanticDebt sourcePair observer +
          weight * quittingTerminalSemanticDebt endpointPair observer -
        quittingTerminalSemanticDebt radialPair observer) /
        frontier.lambda (frontier.subseq rank) ≤
      (epsilon + weight *
        (quittingTerminalSemanticDebtSum endpointPair -
          quittingTerminalSemanticDebtSum sourcePair)) /
        frontier.lambda (frontier.subseq rank) at hupper
  rw [hgapIdentity] at hlower hupper
  have hupperIdentity :
      (epsilon + weight *
          (quittingTerminalSemanticDebtSum endpointPair -
            quittingTerminalSemanticDebtSum sourcePair)) /
          frontier.lambda (frontier.subseq rank) =
        (quittingTerminalSemanticDebtSum sourcePair -
            quittingTerminalSemanticDebtSum frontier.base) /
              frontier.lambda (frontier.subseq rank) +
          weight * (∑ who,
            frontier.actualDebtDirection rank mover who) := by
    rw [← htotalIdentity]
    dsimp only [epsilon]
    ring
  rw [hupperIdentity] at hupper
  simpa only [sourcePair, sourceProfile] using And.intro hlower hupper

/-- **Radial homogeneity of every flat source-matched tangent column.**

For any fixed coefficient in `[0, 1]`, the nested literal reset direction
converges to that coefficient times the extracted tangent column.  The proof
uses the source-excess rate retained by the frontier and the vanishing total
slope of the flat column. -/
theorem sourceMatchedRadialDebtDirection_tendsto
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (mover : {who // who ∈ frontier.active}) (observer : ι)
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (hflat : ∑ who, frontier.tangent mover who = 0) :
    Tendsto (fun rank =>
      frontier.sourceMatchedRadialDebtDirection rank mover weight
        hweight0 hweight1 observer) atTop
      (nhds (weight * frontier.tangent mover observer)) := by
  let error : ℕ → ℝ := fun rank =>
    weight * frontier.actualDebtDirection rank mover observer -
      frontier.sourceMatchedRadialDebtDirection rank mover weight
        hweight0 hweight1 observer
  let upper : ℕ → ℝ := fun rank =>
    (quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (frontier.profiles (frontier.subseq rank))) -
        quittingTerminalSemanticDebtSum frontier.base) /
          frontier.lambda (frontier.subseq rank) +
      weight * (∑ who, frontier.actualDebtDirection rank mover who)
  have hsum : Tendsto (fun rank =>
      ∑ who, frontier.actualDebtDirection rank mover who) atTop (nhds 0) := by
    have hcoordinate := tendsto_finsetSum Finset.univ fun who _whoMem =>
      frontier.tangent_tendsto mover who
    simpa only [actualDebtDirection, hflat] using hcoordinate
  have hweight : Tendsto (fun _rank : ℕ => weight) atTop (nhds weight) :=
    tendsto_const_nhds
  have hupper : Tendsto upper atTop (nhds 0) := by
    have hcombined :=
      frontier.source_excess_over_lambda_tendsto_zero.add
        (hweight.mul hsum)
    simpa only [upper, zero_add, mul_zero] using hcombined
  have herror : Tendsto error atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun rank =>
        (frontier.sourceMatchedRadialDebtDirection_gap_bounds rank mover
          observer weight hweight0 hweight1).1
    · exact Eventually.of_forall fun rank =>
        (frontier.sourceMatchedRadialDebtDirection_gap_bounds rank mover
          observer weight hweight0 hweight1).2
    · exact hupper
  have hscaled := hweight.mul (frontier.tangent_tendsto mover observer)
  change Tendsto (fun rank =>
    weight * frontier.actualDebtDirection rank mover observer) atTop
      (nhds (weight * frontier.tangent mover observer)) at hscaled
  have hresult := hscaled.sub herror
  convert hresult using 1
  · funext rank
    dsimp only [error]
    ring
  · simp

/-- A normalized charged circulation can be rescaled into one literal
coefficient in `[0, 1]` for each active mover.  Balance is preserved and the
aggregate diagonal charge remains strictly positive. -/
theorem exists_boundedRadialCirculationWeights
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (hcirculation : HasQuittingStoppingLawFlatChargedCirculation
      frontier.active frontier.tangent) :
    ∃ weight : {who // who ∈ frontier.active} → ℝ,
      (∀ mover, 0 ≤ weight mover) ∧
      (∀ mover, weight mover ≤ 1) ∧
      (∀ observer,
        ∑ mover, weight mover * frontier.tangent mover observer = 0) ∧
      0 < ∑ mover,
        weight mover * (-frontier.tangent mover mover.1) := by
  dsimp [HasQuittingStoppingLawFlatChargedCirculation] at hcirculation
  rcases hcirculation with ⟨mass, hmass, hbalance, hcharge⟩
  let budget : ℝ := ∑ mover, mass mover
  let denominator : ℝ := 1 + budget
  let weight : {who // who ∈ frontier.active} → ℝ := fun mover =>
    mass mover / denominator
  have hbudget : 0 ≤ budget :=
    Finset.sum_nonneg fun mover _moverMem => hmass mover
  have hdenominator : 0 < denominator := by
    dsimp only [denominator]
    linarith
  have hbalance' : ∀ observer,
      ∑ mover, mass mover * frontier.tangent mover observer = 0 := by
    intro observer
    simpa [quittingActiveDebtTangentExtension] using hbalance observer
  have hcharge' :
      ∑ mover, mass mover * (-frontier.tangent mover mover.1) = 1 := by
    simpa [quittingActiveDebtTangentGain,
      quittingActiveDebtTangentExtension] using hcharge
  refine ⟨weight, ?_, ?_, ?_, ?_⟩
  · intro mover
    exact div_nonneg (hmass mover) hdenominator.le
  · intro mover
    have hmassLe : mass mover ≤ budget := by
      dsimp only [budget]
      exact Finset.single_le_sum
        (fun other _otherMem => hmass other) (Finset.mem_univ mover)
    dsimp only [weight]
    apply (div_le_one hdenominator).2
    linarith
  · intro observer
    calc
      (∑ mover, weight mover * frontier.tangent mover observer) =
          (∑ mover, mass mover * frontier.tangent mover observer) /
            denominator := by
        dsimp only [weight]
        simp only [div_mul_eq_mul_div]
        rw [Finset.sum_div]
      _ = 0 := by rw [hbalance' observer, zero_div]
  · calc
      0 < 1 / denominator := div_pos zero_lt_one hdenominator
      _ = ∑ mover,
          weight mover * (-frontier.tangent mover mover.1) := by
        rw [← hcharge']
        dsimp only [weight]
        simp only [div_mul_eq_mul_div]
        rw [Finset.sum_div]

/-- **The charged circulation is realized by one radially scaled reset per
active player.**

The external real multiplicities of the abstract circulation are absorbed
into legal outer stopping-law mixture weights.  The finite sum of the literal
normalized reset directions converges coordinatewise to zero, while its
aggregate mover-diagonal charge converges to a strictly positive number. -/
theorem exists_boundedRadialSourceMatchedCirculation
    (frontier : QuittingCounterexampleStoppingLawFrontier witness)
    (hflat : ∀ mover, ∑ observer, frontier.tangent mover observer = 0)
    (hcirculation : HasQuittingStoppingLawFlatChargedCirculation
      frontier.active frontier.tangent) :
    ∃ weight : {who // who ∈ frontier.active} → ℝ,
      ∃ hweight0 : ∀ mover, 0 ≤ weight mover,
      ∃ hweight1 : ∀ mover, weight mover ≤ 1,
      (∀ observer,
        Tendsto (fun rank =>
          ∑ mover,
            frontier.sourceMatchedRadialDebtDirection rank mover
              (weight mover) (hweight0 mover) (hweight1 mover) observer)
          atTop (nhds 0)) ∧
      ∃ charge : ℝ, 0 < charge ∧
        Tendsto (fun rank =>
          ∑ mover,
            -frontier.sourceMatchedRadialDebtDirection rank mover
              (weight mover) (hweight0 mover) (hweight1 mover) mover.1)
          atTop (nhds charge) := by
  obtain ⟨weight, hweight0, hweight1, hbalance, hcharge⟩ :=
    frontier.exists_boundedRadialCirculationWeights hcirculation
  let charge := ∑ mover,
    weight mover * (-frontier.tangent mover mover.1)
  refine ⟨weight, hweight0, hweight1, ?_, charge, ?_, ?_⟩
  · intro observer
    have hsum := tendsto_finsetSum Finset.univ fun mover _moverMem =>
      frontier.sourceMatchedRadialDebtDirection_tendsto mover observer
        (weight mover) (hweight0 mover) (hweight1 mover) (hflat mover)
    simpa only [hbalance observer] using hsum
  · simpa only [charge] using hcharge
  · have hsum := tendsto_finsetSum Finset.univ fun mover _moverMem =>
      (frontier.sourceMatchedRadialDebtDirection_tendsto mover mover.1
        (weight mover) (hweight0 mover) (hweight1 mover) (hflat mover)).neg
    simpa only [charge, mul_neg] using hsum

end QuittingCounterexampleStoppingLawFrontier
end GameTheory
