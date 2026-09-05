/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.FixedCapPinCoordinateDebtDrop
import UniformEquilibrium.Quitting.Boundary.Repair.SupportEnlargementAlternative
import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseProductRescaling
import UniformEquilibrium.Quitting.Root.LiteralPrefixDeviationTransport

/-!
# First exact-root debt descent

A fixed cap pin forces both a uniform debt expenditure and
a uniform amount of one-stage absorption.  The root is an arbitrary exact
independent product root against the prescribed continuation payoff.

The compact survival classification and the behavioral reset alternatives are
not asserted here.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Copying the prescribed root marginal and changing only one's attached-tail
strategy is an actual unilateral behavioral response.  Its exact gain is the
old tail gain multiplied by the probability that every player Continues at
the new root. -/
theorem quittingTerminalPayoff_copiedRootAttachedTailDeviation_sub_eq_continueMass_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (player : ι)
    (tailDeviation : (quittingGame reward).BehaviorStrategy player) :
    quittingTerminalPayoff reward
          (Function.update
            (quittingRootThenContinuationProfile reward root continuation)
            player
            (quittingRootAndContinuationDeviation reward (root player)
              tailDeviation)) player -
        quittingTerminalPayoff reward
          (quittingRootThenContinuationProfile reward root continuation) player =
      quittingStationaryContinueMass root *
        (quittingTerminalPayoff reward
            (Function.update continuation player tailDeviation) player -
          quittingTerminalPayoff reward continuation player) := by
  rw [update_quittingRootThenContinuationProfile_eq,
    Function.update_eq_self,
    quittingTerminalPayoff_rootThenContinuation_eq,
    quittingTerminalPayoff_rootThenContinuation_eq,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add]
  ring

/-- A fixed cap pin forces every exact product root to absorb with a uniform
positive probability.  This is the scalar dichotomy behind the fixed-cap-pin
debt drop: either an opponent already supplies the stated absorption, or the
pinned player's positive endpoint difference forces that player to Quit
surely. -/
theorem fixedCapPin_exactRoot_absorptionMass_lowerBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (player : ι) {M gamma : ℝ}
    (hM : 0 < M) (hgamma : 0 < gamma)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hvalue : |pair.1 player| ≤ M)
    (hdebt : gamma ≤ quittingTerminalSemanticDebt pair player)
    (hcap : |pair.2 player -
        reward (quittingSingletonTerminal player) player| ≤ gamma / 4)
    (hnash : IsεQuittingRootNash reward pair.1 0 root) :
    min 1 (gamma / (16 * M)) ≤ quittingRootAbsorptionMass root := by
  let opponentAbsorption := quittingRootOpponentAbsorptionMass root player
  let endpoint := quittingRootEndpointDifference reward pair.1 root player
  let singleton := reward (quittingSingletonTerminal player) player
  have hopponentNonneg : 0 ≤ opponentAbsorption :=
    quittingRootOpponentAbsorptionMass_nonneg root player
  have hsingletonTail : 3 * gamma / 4 ≤ singleton - pair.1 player := by
    have hcapUpper := (abs_le.mp hcap).2
    dsimp only [singleton, quittingTerminalSemanticDebt] at hdebt ⊢
    linarith
  have hquit :=
    abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
      reward pair.1 root player M hreward
  have hcontinue :=
    QuittingAbsorptionPath.abs_quittingRootContinuePayoff_sub_tail_le_two_mul_opponentAbsorptionMass
      reward pair.1 root player M hreward hvalue
  have hendpointClose :
      |endpoint - (singleton - pair.1 player)| ≤
        4 * M * opponentAbsorption := by
    dsimp only [endpoint, singleton]
    rw [quittingRootEndpointDifference]
    calc
      |(quittingRootQuitPayoff reward pair.1 root player -
            quittingRootContinuePayoff reward pair.1 root player) -
          (reward (quittingSingletonTerminal player) player - pair.1 player)| =
          |(quittingRootQuitPayoff reward pair.1 root player -
              reward (quittingSingletonTerminal player) player) -
            (quittingRootContinuePayoff reward pair.1 root player -
              pair.1 player)| := by ring_nf
      _ ≤ |quittingRootQuitPayoff reward pair.1 root player -
              reward (quittingSingletonTerminal player) player| +
            |quittingRootContinuePayoff reward pair.1 root player -
              pair.1 player| := abs_sub _ _
      _ ≤ 2 * M * opponentAbsorption + 2 * M * opponentAbsorption :=
        add_le_add hquit hcontinue
      _ = 4 * M * opponentAbsorption := by ring_nf
  by_cases hlarge : gamma / (16 * M) ≤ opponentAbsorption
  · exact (min_le_right 1 _).trans <|
      hlarge.trans (quittingRootOpponentAbsorptionMass_le_absorptionMass root player)
  · have hsmall : opponentAbsorption < gamma / (16 * M) := lt_of_not_ge hlarge
    have hscaledSmall : 4 * M * opponentAbsorption < gamma / 4 := by
      have hdenominator : 0 < 16 * M := mul_pos (by norm_num) hM
      have hmul := (lt_div_iff₀ hdenominator).mp hsmall
      nlinarith
    have hendpointPositive : 0 < endpoint := by
      have hlower := (abs_le.mp hendpointClose).1
      linarith
    have hendpointNash : IsεQuittingRootEndpointNash reward pair.1 0 root :=
      (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        reward pair.1 root).2 hnash
    have hquitOne :=
      quitProbability_eq_one_of_positive_endpointDifference_of_isZeroNash
        reward pair.1 root player hendpointNash hendpointPositive
    exact (min_le_left 1 _).trans <| hquitOne.ge.trans
      (quittingRoot_quitProbability_le_absorptionMass root player)

/-- Convergence of one fixed cap pin makes the absorption lower bound uniform
over every exact root at every sufficiently late source. -/
theorem eventually_fixedCapLimit_exactRoot_absorptionMass_lowerBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : ℕ → QuittingTerminalSemanticPair ι)
    (player : ι) {M gamma : ℝ}
    (hM : 0 < M) (hgamma : 0 < gamma)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hvalue : ∀ index, |(pair index).1 player| ≤ M)
    (hdebt : ∀ index,
      gamma ≤ quittingTerminalSemanticDebt (pair index) player)
    (hcap : Tendsto (fun index ↦ (pair index).2 player) atTop
      (nhds (reward (quittingSingletonTerminal player) player))) :
    ∀ᶠ index in atTop, ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward (pair index).1 0 root →
        min 1 (gamma / (16 * M)) ≤ quittingRootAbsorptionMass root := by
  have hradius : 0 < gamma / 4 := div_pos hgamma (by norm_num)
  have hnear : ∀ᶠ index in atTop,
      |(pair index).2 player -
        reward (quittingSingletonTerminal player) player| ≤ gamma / 4 := by
    have hball : ∀ᶠ cap : ℝ in
        nhds (reward (quittingSingletonTerminal player) player),
        |cap - reward (quittingSingletonTerminal player) player| ≤
          gamma / 4 := by
      filter_upwards [Metric.closedBall_mem_nhds
        (reward (quittingSingletonTerminal player) player) hradius] with cap hcap
      simpa only [Metric.mem_closedBall, Real.dist_eq] using hcap
    exact hcap.eventually hball
  filter_upwards [hnear] with index hnearIndex
  intro root hnash
  exact fixedCapPin_exactRoot_absorptionMass_lowerBound reward (pair index)
    root player hM hgamma hreward (hvalue index) (hdebt index) hnearIndex hnash

end GameTheory
