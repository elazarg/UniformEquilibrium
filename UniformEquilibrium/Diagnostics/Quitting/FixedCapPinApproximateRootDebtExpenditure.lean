/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.FixedCapPinCoordinateDebtDrop
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticOwnStrategyTransport

/-!
# Approximate-root debt expenditure at a fixed cap pin

Prefix debt has an exact scalar expression for an arbitrary product root.
Approximate root Nash bounds the possible error in the resulting debt action.
When one fixed player's cap is close to its singleton reward and its debt has
a positive floor, the exact cap-pin drop persists up to the root Nash error.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Exact debt action of an arbitrary product root, written with the signed
Quit-minus-Continue endpoint difference. No Nash hypothesis is used. -/
theorem quittingTerminalSemanticDebt_prefix_eq_max_endpoint_liveDebt_sub_quitWeight_endpoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (player : ι) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) player =
      max (quittingRootEndpointDifference reward pair.1 root player)
          (quittingRootOpponentContinueMass root player *
            quittingTerminalSemanticDebt pair player) -
        (root player true).toReal *
          quittingRootEndpointDifference reward pair.1 root player := by
  let quitValue := quittingRootQuitPayoff reward pair.1 root player
  let continueValue := quittingRootContinuePayoff reward pair.1 root player
  let endpoint := quittingRootEndpointDifference reward pair.1 root player
  let liveDebt := quittingRootOpponentContinueMass root player *
    quittingTerminalSemanticDebt pair player
  have hcontinue := quittingRootContinuePayoff_cap_eq_literal_add_opponentMass_mul_debt
    reward pair root player
  have hsum := quittingRoot_continueProbability_add_quitProbability root player
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPrefix
  dsimp only
  rw [show quittingRootContinuePayoff reward
      (Function.update pair.1 player (pair.2 player)) root player =
        quittingRootContinuePayoff reward pair.2 root player by
      apply quittingRootExpectedPayoff_continuation_congr
      simp]
  rw [hcontinue, quittingRootSuccessorPayoff_eq_endpointMix]
  change max quitValue (continueValue + liveDebt) -
      ((root player true).toReal * quitValue +
        (root player false).toReal * continueValue) =
    max endpoint liveDebt - (root player true).toReal * endpoint
  have hendpoint : endpoint = quitValue - continueValue := rfl
  have hcontinueWeight : (root player false).toReal =
      1 - (root player true).toReal := by linarith
  by_cases horder : endpoint ≤ liveDebt
  · have hvalueOrder : quitValue ≤ continueValue + liveDebt := by
      rw [hendpoint] at horder
      linarith
    rw [max_eq_right hvalueOrder, max_eq_right horder,
      hcontinueWeight, hendpoint]
    ring
  · have horder' : liveDebt ≤ endpoint := le_of_not_ge horder
    have hvalueOrder : continueValue + liveDebt ≤ quitValue := by
      rw [hendpoint] at horder'
      linarith
    rw [max_eq_left hvalueOrder, max_eq_left horder',
      hcontinueWeight, hendpoint]
    ring

/-- Approximate root Nash makes prefixed debt at most opponent survival times
the input debt, plus the root error. -/
theorem approximateRoot_prefixDebt_le_opponentContinueDebt_add_error
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (player : ι) (error : ℝ)
    (hdebt : 0 ≤ quittingTerminalSemanticDebt pair player)
    (hnash : IsεQuittingRootNash reward pair.1 error root) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) player ≤
      quittingRootOpponentContinueMass root player *
          quittingTerminalSemanticDebt pair player + error := by
  let endpoint := quittingRootEndpointDifference reward pair.1 root player
  let liveDebt := quittingRootOpponentContinueMass root player *
    quittingTerminalSemanticDebt pair player
  let quitWeight := (root player true).toReal
  let continueWeight := (root player false).toReal
  have hliveDebt : 0 ≤ liveDebt := mul_nonneg
    (quittingRootOpponentContinueMass_nonneg root player) hdebt
  have hsum := quittingRoot_continueProbability_add_quitProbability root player
  have hweights : continueWeight = 1 - quitWeight := by
    dsimp only [continueWeight, quitWeight]
    linarith
  have hquit := quittingRootQuitPayoff_le_successor_add_of_isεNash
    reward pair.1 error root player hnash
  have hcontinue := quittingRootContinuePayoff_le_successor_add_of_isεNash
    reward pair.1 error root player hnash
  have hsuccessor := quittingRootSuccessorPayoff_eq_endpointMix
    reward pair.1 root player
  have hquitError : continueWeight * endpoint ≤ error := by
    rw [hsuccessor] at hquit
    rw [show (root player false).toReal = 1 - (root player true).toReal by
      linarith] at hquit
    dsimp only [continueWeight, endpoint, quitWeight]
    unfold quittingRootEndpointDifference
    rw [show (root player false).toReal = 1 - (root player true).toReal by
      linarith]
    nlinarith
  have hcontinueError : quitWeight * (-endpoint) ≤ error := by
    rw [hsuccessor] at hcontinue
    rw [show (root player false).toReal = 1 - (root player true).toReal by
      linarith] at hcontinue
    dsimp only [quitWeight, endpoint]
    unfold quittingRootEndpointDifference
    nlinarith
  rw [quittingTerminalSemanticDebt_prefix_eq_max_endpoint_liveDebt_sub_quitWeight_endpoint]
  change max endpoint liveDebt - quitWeight * endpoint ≤ liveDebt + error
  by_cases hnonneg : 0 ≤ endpoint
  · by_cases horder : liveDebt ≤ endpoint
    · rw [max_eq_left horder]
      rw [hweights] at hquitError
      nlinarith
    · rw [max_eq_right (le_of_not_ge horder)]
      linarith
  · have hendpoint : endpoint ≤ 0 := le_of_not_ge hnonneg
    rw [max_eq_right (hendpoint.trans hliveDebt)]
    linarith

/-- A nonnegative debt coordinate can increase under an approximate root by
at most the root Nash error. -/
theorem approximateRoot_prefixDebt_le_debt_add_error
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (player : ι) (error : ℝ)
    (hdebt : 0 ≤ quittingTerminalSemanticDebt pair player)
    (hnash : IsεQuittingRootNash reward pair.1 error root) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) player ≤
      quittingTerminalSemanticDebt pair player + error := by
  have hsurvival := approximateRoot_prefixDebt_le_opponentContinueDebt_add_error
    reward pair root player error hdebt hnash
  have hmass := quittingRootOpponentContinueMass_le_one root player
  have hscaled : quittingRootOpponentContinueMass root player *
      quittingTerminalSemanticDebt pair player ≤
        quittingTerminalSemanticDebt pair player :=
    mul_le_of_le_one_left hdebt hmass
  linarith

/-- A fixed cap pin forces every approximate product root to spend the same
coordinate-debt amount, up to its Nash error. -/
theorem fixedCapPin_approximateRoot_coordinateDebtDrop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (player : ι) {M gamma error : ℝ}
    (hM : 0 < M) (hgamma : 0 < gamma)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hvalue : |pair.1 player| ≤ M)
    (hdebt : gamma ≤ quittingTerminalSemanticDebt pair player)
    (hcap : |pair.2 player -
        reward (quittingSingletonTerminal player) player| ≤ gamma / 4)
    (hnash : IsεQuittingRootNash reward pair.1 error root) :
    min (gamma / 2) (gamma ^ 2 / (16 * M)) - error ≤
      quittingTerminalSemanticDebt pair player -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root pair) player := by
  let debt := quittingTerminalSemanticDebt pair player
  let opponentAbsorption := quittingRootOpponentAbsorptionMass root player
  let opponentContinue := quittingRootOpponentContinueMass root player
  let endpoint := quittingRootEndpointDifference reward pair.1 root player
  let quitWeight := (root player true).toReal
  let continueWeight := (root player false).toReal
  let singleton := reward (quittingSingletonTerminal player) player
  have hdebtNonneg : 0 ≤ debt := hgamma.le.trans hdebt
  have hopponentNonneg : 0 ≤ opponentAbsorption :=
    quittingRootOpponentAbsorptionMass_nonneg root player
  have hcomplement : opponentContinue = 1 - opponentAbsorption :=
    quittingRootOpponentContinueMass_eq_one_sub_absorptionMass root player
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
  have hprefixLe := approximateRoot_prefixDebt_le_opponentContinueDebt_add_error
    reward pair root player error hdebtNonneg hnash
  by_cases hlarge : gamma / (16 * M) ≤ opponentAbsorption
  · have hproduct :
        (gamma / (16 * M)) * gamma ≤ opponentAbsorption * debt :=
      mul_le_mul hlarge hdebt hgamma.le hopponentNonneg
    have hrewrite :
        (gamma / (16 * M)) * gamma = gamma ^ 2 / (16 * M) := by
      simp only [div_eq_mul_inv, pow_two]
      ring_nf
    rw [hrewrite] at hproduct
    change quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) player ≤
      opponentContinue * debt + error at hprefixLe
    rw [hcomplement] at hprefixLe
    change min (gamma / 2) (gamma ^ 2 / (16 * M)) - error ≤
      debt - quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) player
    exact (sub_le_sub_right (min_le_right (gamma / 2)
      (gamma ^ 2 / (16 * M))) error).trans <| by linarith
  · have hsmall : opponentAbsorption < gamma / (16 * M) :=
      lt_of_not_ge hlarge
    have hscaledSmall : 4 * M * opponentAbsorption < gamma / 4 := by
      have hdenominator : 0 < 16 * M := mul_pos (by norm_num) hM
      have hmul := (lt_div_iff₀ hdenominator).mp hsmall
      nlinarith
    have hendpointLower : gamma / 2 < endpoint := by
      have hlower := (abs_le.mp hendpointClose).1
      linarith
    have hendpointNonneg : 0 ≤ endpoint :=
      (div_nonneg hgamma.le (by norm_num)).trans hendpointLower.le
    have hsum := quittingRoot_continueProbability_add_quitProbability root player
    have hweights : continueWeight = 1 - quitWeight := by
      dsimp only [continueWeight, quitWeight]
      linarith
    have hquitNash := quittingRootQuitPayoff_le_successor_add_of_isεNash
      reward pair.1 error root player hnash
    have hsuccessor := quittingRootSuccessorPayoff_eq_endpointMix
      reward pair.1 root player
    have hquitError : continueWeight * endpoint ≤ error := by
      rw [hsuccessor] at hquitNash
      rw [show (root player false).toReal = 1 - (root player true).toReal by
        linarith] at hquitNash
      dsimp only [continueWeight, endpoint, quitWeight]
      unfold quittingRootEndpointDifference
      rw [show (root player false).toReal = 1 - (root player true).toReal by
        linarith]
      nlinarith
    rw [quittingTerminalSemanticDebt_prefix_eq_max_endpoint_liveDebt_sub_quitWeight_endpoint]
    change min (gamma / 2) (gamma ^ 2 / (16 * M)) - error ≤
      debt - (max endpoint (opponentContinue * debt) - quitWeight * endpoint)
    by_cases horder : opponentContinue * debt ≤ endpoint
    · rw [max_eq_left horder]
      refine (sub_le_sub_right (min_le_left (gamma / 2)
        (gamma ^ 2 / (16 * M))) error).trans ?_
      rw [hweights] at hquitError
      nlinarith
    · rw [max_eq_right (le_of_not_ge horder)]
      refine (sub_le_sub_right (min_le_left (gamma / 2)
        (gamma ^ 2 / (16 * M))) error).trans ?_
      rw [hweights] at hquitError
      nlinarith

end GameTheory
