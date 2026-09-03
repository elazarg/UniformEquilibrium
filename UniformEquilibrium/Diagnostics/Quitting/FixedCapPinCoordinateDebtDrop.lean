/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.QuitEndpointOpponentBound
import UniformEquilibrium.Quitting.Root.BoundedEndpoint
import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum

/-!
# Coordinate debt drop from a fixed cap pin

If one player's continuation cap is close to that player's singleton reward
and the same player carries positive terminal-semantic debt, every exact
product Nash root spends a fixed amount of that debt.  The conclusion is
pointwise in the semantic pair and does not require a minimum-debt carrier,
compactness, or a separately supplied root-absorption lower bound.

The sequential corollaries make the quantifiers explicit: convergence of one
fixed player's cap to the singleton reward yields one uniform late debt-drop
bound for every exact root at every sufficiently late index.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.SurvivalWeightedObstruction
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The quantitative debt-drop bound is positive when both input constants
are positive. -/
theorem fixedCapPinDebtDropBound_pos {M gamma : ℝ}
    (hM : 0 < M) (hgamma : 0 < gamma) :
    0 < min (gamma / 2) (gamma ^ 2 / (16 * M)) := by
  exact lt_min (div_pos hgamma (by norm_num))
    (div_pos (sq_pos_of_pos hgamma) (mul_pos (by norm_num) hM))

/-- A cap pin at one fixed player forces every exact product Nash root to
decrease that player's terminal-semantic debt by a dimension-free amount. -/
theorem fixedCapPin_coordinateDebtDrop
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
    min (gamma / 2) (gamma ^ 2 / (16 * M)) ≤
      quittingTerminalSemanticDebt pair player -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root pair) player := by
  let debt := quittingTerminalSemanticDebt pair player
  let opponentAbsorption := quittingRootOpponentAbsorptionMass root player
  let opponentContinue := quittingRootOpponentContinueMass root player
  let endpoint := quittingRootEndpointDifference reward pair.1 root player
  let singleton := reward (quittingSingletonTerminal player) player
  have hdebtNonneg : 0 ≤ debt := hgamma.le.trans hdebt
  have hopponentNonneg : 0 ≤ opponentAbsorption :=
    quittingRootOpponentAbsorptionMass_nonneg root player
  have hcontinueOne : opponentContinue ≤ 1 :=
    quittingRootOpponentContinueMass_le_one root player
  have hcomplement : opponentContinue = 1 - opponentAbsorption := by
    exact quittingRootOpponentContinueMass_eq_one_sub_absorptionMass root player
  have hsingletonTail : 3 * gamma / 4 ≤ singleton - pair.1 player := by
    have hcapUpper := (abs_le.mp hcap).2
    dsimp only [debt, singleton, quittingTerminalSemanticDebt] at hdebt ⊢
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
  have hprefixAct := quittingTerminalSemanticDebt_prefix_eq_blockAct
    reward pair root player hdebtNonneg hnash
  by_cases hlarge : gamma / (16 * M) ≤ opponentAbsorption
  · have hprefixLe :
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPrefix reward root pair) player ≤
          opponentContinue * debt := by
      rw [hprefixAct]
      exact Block.act_le_survival_mul_debt
        (quittingTerminalSemanticDebtBlock reward pair root player) ()
        hdebtNonneg
    have hproduct :
        (gamma / (16 * M)) * gamma ≤ opponentAbsorption * debt :=
      mul_le_mul hlarge hdebt hgamma.le hopponentNonneg
    have hrewrite :
        (gamma / (16 * M)) * gamma = gamma ^ 2 / (16 * M) := by
      simp only [div_eq_mul_inv, pow_two]
      ring_nf
    rw [hrewrite] at hproduct
    have hdrop : gamma ^ 2 / (16 * M) ≤
        quittingTerminalSemanticDebt pair player -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPrefix reward root pair) player := by
      dsimp only [debt] at hproduct
      rw [hcomplement] at hprefixLe
      dsimp only [debt] at hprefixLe
      nlinarith
    exact (min_le_right _ _).trans hdrop
  · have hsmall : opponentAbsorption < gamma / (16 * M) :=
      lt_of_not_ge hlarge
    have hscaledSmall : 4 * M * opponentAbsorption < gamma / 4 := by
      have hdenominator : 0 < 16 * M := mul_pos (by norm_num) hM
      have hmul := (lt_div_iff₀ hdenominator).mp hsmall
      nlinarith
    have hendpointLower : gamma / 2 < endpoint := by
      have hlower := (abs_le.mp hendpointClose).1
      linarith
    have hsurvivedLe : opponentContinue * debt ≤ debt := by
      exact mul_le_of_le_one_left hdebtNonneg hcontinueOne
    rw [hprefixAct]
    dsimp only [quittingTerminalSemanticDebtBlock,
      Block.act, quittingRootExercisePremium]
    change min (gamma / 2) (gamma ^ 2 / (16 * M)) ≤
      debt - max 0 (opponentContinue * debt - max 0 endpoint)
    have hendpointNonneg : 0 ≤ endpoint :=
      (div_nonneg hgamma.le (by norm_num)).trans hendpointLower.le
    have hpremium : max 0 endpoint = endpoint := max_eq_right hendpointNonneg
    rw [hpremium]
    refine (min_le_left _ _).trans ?_
    by_cases hsurvivedPremium : 0 ≤ opponentContinue * debt - endpoint
    · rw [max_eq_right hsurvivedPremium]
      linarith
    · rw [max_eq_left (le_of_not_ge hsurvivedPremium)]
      linarith

/-- If every source debt coordinate is nonnegative, the same forced loss in
one fixed coordinate is a lower bound for the total terminal-semantic debt
drop. -/
theorem fixedCapPin_totalDebtDrop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (player : ι) {M gamma : ℝ}
    (hM : 0 < M) (hgamma : 0 < gamma)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hvalue : |pair.1 player| ≤ M)
    (hdebtNonneg : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who)
    (hdebt : gamma ≤ quittingTerminalSemanticDebt pair player)
    (hcap : |pair.2 player -
        reward (quittingSingletonTerminal player) player| ≤ gamma / 4)
    (hnash : IsεQuittingRootNash reward pair.1 0 root) :
    min (gamma / 2) (gamma ^ 2 / (16 * M)) ≤
      quittingTerminalSemanticDebtSum pair -
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPrefix reward root pair) := by
  have hcoordinate := fixedCapPin_coordinateDebtDrop reward pair root player
    hM hgamma hreward hvalue hdebt hcap hnash
  have hnonneg : ∀ who, 0 ≤
      quittingTerminalSemanticDebt pair who -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root pair) who := by
    intro who
    exact sub_nonneg.mpr <|
      quittingTerminalSemanticDebt_prefix_le reward pair root who
        (hdebtNonneg who) hnash
  calc
    min (gamma / 2) (gamma ^ 2 / (16 * M)) ≤
        quittingTerminalSemanticDebt pair player -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPrefix reward root pair) player :=
      hcoordinate
    _ ≤ ∑ who, (quittingTerminalSemanticDebt pair who -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPrefix reward root pair) who) := by
      exact Finset.single_le_sum (fun who _ ↦ hnonneg who)
        (Finset.mem_univ player)
    _ = quittingTerminalSemanticDebtSum pair -
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPrefix reward root pair) := by
      unfold quittingTerminalSemanticDebtSum
      rw [Finset.sum_sub_distrib]

/-- If one fixed player's cap converges to that player's singleton reward
while its debt stays above a fixed positive floor, then every sufficiently
late exact root spends the same fixed amount of that coordinate's debt. -/
theorem eventually_fixedCapLimit_coordinateDebtDrop
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
        min (gamma / 2) (gamma ^ 2 / (16 * M)) ≤
          quittingTerminalSemanticDebt (pair index) player -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPrefix reward root (pair index)) player := by
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
  exact fixedCapPin_coordinateDebtDrop reward (pair index) root player
    hM hgamma hreward (hvalue index) (hdebt index) hnearIndex hnash

/-- Under nonnegativity of every source debt coordinate, convergence of one
fixed cap also forces the same uniform late drop in total debt for every exact
root. -/
theorem eventually_fixedCapLimit_totalDebtDrop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : ℕ → QuittingTerminalSemanticPair ι)
    (player : ι) {M gamma : ℝ}
    (hM : 0 < M) (hgamma : 0 < gamma)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hvalue : ∀ index, |(pair index).1 player| ≤ M)
    (hdebtNonneg : ∀ index who,
      0 ≤ quittingTerminalSemanticDebt (pair index) who)
    (hdebt : ∀ index,
      gamma ≤ quittingTerminalSemanticDebt (pair index) player)
    (hcap : Tendsto (fun index ↦ (pair index).2 player) atTop
      (nhds (reward (quittingSingletonTerminal player) player))) :
    ∀ᶠ index in atTop, ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward (pair index).1 0 root →
        min (gamma / 2) (gamma ^ 2 / (16 * M)) ≤
          quittingTerminalSemanticDebtSum (pair index) -
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPrefix reward root (pair index)) := by
  have hcoordinate := eventually_fixedCapLimit_coordinateDebtDrop
    reward pair player hM hgamma hreward hvalue hdebt hcap
  filter_upwards [hcoordinate] with index hcoordinateIndex
  intro root hnash
  have hfixed := hcoordinateIndex root hnash
  have hnonneg : ∀ who, 0 ≤
      quittingTerminalSemanticDebt (pair index) who -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root (pair index)) who := by
    intro who
    exact sub_nonneg.mpr <|
      quittingTerminalSemanticDebt_prefix_le reward (pair index) root who
        (hdebtNonneg index who) hnash
  calc
    min (gamma / 2) (gamma ^ 2 / (16 * M)) ≤
        quittingTerminalSemanticDebt (pair index) player -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPrefix reward root (pair index)) player :=
      hfixed
    _ ≤ ∑ who, (quittingTerminalSemanticDebt (pair index) who -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPrefix reward root (pair index)) who) := by
      exact Finset.single_le_sum (fun who _ ↦ hnonneg who)
        (Finset.mem_univ player)
    _ = quittingTerminalSemanticDebtSum (pair index) -
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPrefix reward root (pair index)) := by
      unfold quittingTerminalSemanticDebtSum
      rw [Finset.sum_sub_distrib]

end GameTheory
