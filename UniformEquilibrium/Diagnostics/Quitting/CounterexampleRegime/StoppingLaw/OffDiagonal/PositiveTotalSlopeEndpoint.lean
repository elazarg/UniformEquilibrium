/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.SourceMatchedChattering
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawDebtConvexity

/-!
# Scale-free full-endpoint amplification of a positive stopping-law slope

A normalized stopping-law tangent is measured on a vanishing mixture edge.
Coordinatewise debt convexity compares that mixed edge with the complete
replacement endpoint.  Dividing by the positive reset scale therefore gives a
scale-free lower bound on every full-endpoint debt change.

For a fixed frontier mover, summing those coordinate inequalities yields the
strong source-relative conclusion

`eta <= D(fullEndpoint rank) - D(source rank)`

for every `eta` strictly below the limiting total tangent slope and all
sufficiently large ranks.  The weaker comparison with the limiting minimum
base is an immediate corollary.

The mover coordinate is exact rather than one-sided.  Consequently the
supplied complete replacement is one literal unilateral deviation whose payoff
gain converges to the negative diagonal tangent and is eventually bounded
below by one quarter of the mover's positive base debt.

This is a source-matched endpoint amplification theorem, not a punishment-floor
or capacity rebase.  It does not identify the endpoint with the target of an
admissible incoming Nash--Bellman path.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A normalized mixed stopping-law debt direction is bounded above by the
corresponding complete-endpoint debt change. -/
theorem quittingStoppingLawNormalizedDebtDirection_le_fullEndpointDebtChange
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ) (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1) :
    quittingStoppingLawNormalizedDebtDirection reward profile mover target
        lambda hlambda0.le hlambda1 observer ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover target)) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer := by
  have hchord := quittingTerminalSemanticDebt_stoppingLawMixture_le
    reward profile mover observer (profile mover) target lambda hlambda0.le
      hlambda1
  rw [Function.update_eq_self] at hchord
  unfold quittingStoppingLawNormalizedDebtDirection
    quittingTerminalSemanticDebtChange quittingStoppingLawResetProfile
  apply (div_le_iff₀ hlambda0).2
  nlinarith

/-- On the moved coordinate, the normalized direction is exactly the complete
endpoint debt change because the mover's best-response envelope depends only
on its opponents. -/
theorem quittingStoppingLawNormalizedDebtDirection_self_eq_fullEndpointDebtChange
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ) (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1) :
    quittingStoppingLawNormalizedDebtDirection reward profile mover target
        lambda hlambda0.le hlambda1 mover =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover target)) mover -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) mover := by
  have hself := quittingTerminalSemanticDebt_stoppingLawMixture_eq_self
    reward profile mover (profile mover) target lambda hlambda0.le hlambda1
  rw [Function.update_eq_self] at hself
  unfold quittingStoppingLawNormalizedDebtDirection
    quittingStoppingLawResetProfile quittingTerminalSemanticDebtChange
  rw [hself]
  field_simp
  ring

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

namespace QuittingCounterexampleStoppingLawFrontier

/-- The literal full replacement endpoint for one selected frontier rank and
one active mover. -/
def sourceMatchedFullEndpointProfile
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (mover : {who // who ∈ frontier.active}) :
    (quittingGame reward).BehaviorProfile :=
  Function.update (frontier.profiles (frontier.subseq rank)) mover.1
    (frontier.bestResponse mover (frontier.subseq rank))

/-- Every actual normalized frontier coordinate is bounded by its literal
full-endpoint debt change at the same source rank. -/
theorem actualDebtDirection_le_fullEndpointDebtChange
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (mover : {who // who ∈ frontier.active})
    (observer : ι) :
    frontier.actualDebtDirection rank mover observer ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (frontier.sourceMatchedFullEndpointProfile rank mover)) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (frontier.profiles (frontier.subseq rank))) observer := by
  simpa only [actualDebtDirection, sourceMatchedFullEndpointProfile] using
    quittingStoppingLawNormalizedDebtDirection_le_fullEndpointDebtChange
      reward (frontier.profiles (frontier.subseq rank)) mover.1 observer
      (frontier.bestResponse mover (frontier.subseq rank))
      (frontier.lambda (frontier.subseq rank))
      (frontier.lambda_pos (frontier.subseq rank))
      (frontier.lambda_le_one (frontier.subseq rank))

/-- The mover-coordinate comparison is exact at every rank. -/
theorem actualDebtDirection_self_eq_fullEndpointDebtChange
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (mover : {who // who ∈ frontier.active}) :
    frontier.actualDebtDirection rank mover mover.1 =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (frontier.sourceMatchedFullEndpointProfile rank mover)) mover.1 -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (frontier.profiles (frontier.subseq rank))) mover.1 := by
  simpa only [actualDebtDirection, sourceMatchedFullEndpointProfile] using
    quittingStoppingLawNormalizedDebtDirection_self_eq_fullEndpointDebtChange
      reward (frontier.profiles (frontier.subseq rank)) mover.1
      (frontier.bestResponse mover (frontier.subseq rank))
      (frontier.lambda (frontier.subseq rank))
      (frontier.lambda_pos (frontier.subseq rank))
      (frontier.lambda_le_one (frontier.subseq rank))

/-- Summing coordinatewise convexity gives the source-relative total-debt
excursion at one literal full endpoint. -/
theorem sum_actualDebtDirection_le_fullEndpoint_totalDebtChange
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (mover : {who // who ∈ frontier.active}) :
    (∑ observer, frontier.actualDebtDirection rank mover observer) ≤
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (frontier.sourceMatchedFullEndpointProfile rank mover)) -
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (frontier.profiles (frontier.subseq rank))) := by
  calc
    (∑ observer, frontier.actualDebtDirection rank mover observer) ≤
        ∑ observer,
          (quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (frontier.sourceMatchedFullEndpointProfile rank mover)) observer -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (frontier.profiles (frontier.subseq rank))) observer) := by
      exact Finset.sum_le_sum fun observer _ =>
        frontier.actualDebtDirection_le_fullEndpointDebtChange
          rank mover observer
    _ = quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (frontier.sourceMatchedFullEndpointProfile rank mover)) -
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (frontier.profiles (frontier.subseq rank))) := by
      unfold quittingTerminalSemanticDebtSum
      rw [Finset.sum_sub_distrib]

/-- The actual total normalized chord converges to the total tangent slope. -/
theorem sum_actualDebtDirection_tendsto_tangentSum
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) :
    Tendsto
      (fun rank => ∑ observer,
        frontier.actualDebtDirection rank mover observer)
      atTop (nhds (∑ observer, frontier.tangent mover observer)) := by
  simpa only [actualDebtDirection] using
    tendsto_finsetSum Finset.univ
      (fun observer _ => frontier.tangent_tendsto mover observer)

/-- **Scale-free source-relative endpoint amplification.**

Every strict lower bound on one limiting total tangent slope is eventually a
lower bound on the total-debt excursion from the actual source profile to the
actual complete replacement endpoint. -/
theorem eventually_eta_le_fullEndpoint_totalDebtChange
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active})
    {eta : ℝ} (heta : eta < ∑ observer, frontier.tangent mover observer) :
    ∀ᶠ rank in atTop,
      eta ≤
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (frontier.sourceMatchedFullEndpointProfile rank mover)) -
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (frontier.profiles (frontier.subseq rank))) := by
  have hslope := frontier.sum_actualDebtDirection_tendsto_tangentSum mover
  have hlower : ∀ᶠ rank in atTop,
      eta < ∑ observer, frontier.actualDebtDirection rank mover observer :=
    hslope.eventually (Ioi_mem_nhds heta)
  filter_upwards [hlower] with rank hrank
  exact hrank.le.trans
    (frontier.sum_actualDebtDirection_le_fullEndpoint_totalDebtChange rank mover)

/-- Base-relative corollary.  It is weaker than the source-relative theorem
because every actual source lies above the global minimum base. -/
theorem eventually_eta_le_fullEndpoint_totalDebtChange_from_base
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active})
    {eta : ℝ} (heta : eta < ∑ observer, frontier.tangent mover observer) :
    ∀ᶠ rank in atTop,
      eta ≤
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (frontier.sourceMatchedFullEndpointProfile rank mover)) -
          quittingTerminalSemanticDebtSum frontier.base := by
  filter_upwards [frontier.eventually_eta_le_fullEndpoint_totalDebtChange
      mover heta] with rank hrank
  have hsource := frontier.base_minimum
    (quittingTerminalSemanticPair reward
      (frontier.profiles (frontier.subseq rank)))
    (quittingTerminalSemanticPair_mem_carrier reward _)
  linarith

/-- The complete replacement's literal mover payoff gain is the negative
mover-coordinate debt direction. -/
theorem fullEndpointPayoff_sub_source_eq_neg_actualDebtDirection_self
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (mover : {who // who ∈ frontier.active}) :
    quittingTerminalPayoff reward
          (frontier.sourceMatchedFullEndpointProfile rank mover) mover.1 -
        quittingTerminalPayoff reward
          (frontier.profiles (frontier.subseq rank)) mover.1 =
      -frontier.actualDebtDirection rank mover mover.1 := by
  rw [frontier.actualDebtDirection_self_eq_fullEndpointDebtChange]
  unfold sourceMatchedFullEndpointProfile
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  rw [quittingContinuationBestResponseValue_update_self]
  ring

/-- The literal mover gain converges to the negative diagonal tangent. -/
theorem fullEndpointGain_tendsto_neg_tangentDiagonal
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) :
    Tendsto (fun rank =>
      quittingTerminalPayoff reward
            (frontier.sourceMatchedFullEndpointProfile rank mover) mover.1 -
          quittingTerminalPayoff reward
            (frontier.profiles (frontier.subseq rank)) mover.1)
      atTop (nhds (-frontier.tangent mover mover.1)) := by
  have hdirection := (frontier.tangent_tendsto mover mover.1).neg
  apply hdirection.congr'
  exact Eventually.of_forall fun rank => by
    rw [frontier.fullEndpointPayoff_sub_source_eq_neg_actualDebtDirection_self]

/-- The supplied mover is eventually a fixed-gain legal source deviation.
The quarter-debt constant leaves strict room below the limiting half-debt
bound. -/
theorem eventually_baseDebt_quarter_le_fullEndpointGain
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover : {who // who ∈ frontier.active}) :
    ∀ᶠ rank in atTop,
      quittingTerminalSemanticDebt frontier.base mover.1 / 4 ≤
        quittingTerminalPayoff reward
            (frontier.sourceMatchedFullEndpointProfile rank mover) mover.1 -
          quittingTerminalPayoff reward
            (frontier.profiles (frontier.subseq rank)) mover.1 := by
  have hdebt : 0 < quittingTerminalSemanticDebt frontier.base mover.1 :=
    (frontier.active_iff mover.1).1 mover.2
  have hdiag := frontier.tangent_diagonal mover
  have hlower : quittingTerminalSemanticDebt frontier.base mover.1 / 4 <
      -frontier.tangent mover mover.1 := by
    linarith
  exact (frontier.fullEndpointGain_tendsto_neg_tangentDiagonal mover).eventually
    (Ioi_mem_nhds hlower) |>.mono fun _ h => h.le

/-- Positive total slope therefore produces one active mover with a
scale-free source-matched full-endpoint excursion and a fixed legal payoff
gain. -/
theorem exists_scaleFreeFullEndpointExcursion_of_positiveTotalSlope
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (hpositive : ∃ mover,
      0 < ∑ observer, frontier.tangent mover observer) :
    ∃ mover : {who // who ∈ frontier.active},
      0 < ∑ observer, frontier.tangent mover observer ∧
      (∀ {eta : ℝ}, eta < ∑ observer, frontier.tangent mover observer →
        ∀ᶠ rank in atTop,
          eta ≤
            quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward
                  (frontier.sourceMatchedFullEndpointProfile rank mover)) -
              quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward
                  (frontier.profiles (frontier.subseq rank)))) ∧
      ∀ᶠ rank in atTop,
        quittingTerminalSemanticDebt frontier.base mover.1 / 4 ≤
          quittingTerminalPayoff reward
              (frontier.sourceMatchedFullEndpointProfile rank mover) mover.1 -
            quittingTerminalPayoff reward
              (frontier.profiles (frontier.subseq rank)) mover.1 := by
  obtain ⟨mover, hslope⟩ := hpositive
  exact ⟨mover, hslope,
    fun _ heta => frontier.eventually_eta_le_fullEndpoint_totalDebtChange
      mover heta,
    frontier.eventually_baseDebt_quarter_le_fullEndpointGain mover⟩

end QuittingCounterexampleStoppingLawFrontier

end GameTheory
