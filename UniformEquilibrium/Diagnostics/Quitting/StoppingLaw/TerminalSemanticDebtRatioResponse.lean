/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.Topology.OneSidedAffineLimit
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticDebtRatioSeparation

/-!
# Exact-response crossing in the debt-ratio chamber

This module treats one supplied actual profile and one attained complete
behavioral best response. It does not select a carrier source or a paid port.
-/

noncomputable section

namespace GameTheory

open Math.Topology QuittingBoundaryHolonomy

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Exact attained-response debt-ratio crossing for one supplied maximal-debt
player and one complete behavioral best response. -/
theorem quittingTerminal_exactResponse_debtRatioCrossing
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (response : (quittingGame reward).BehaviorStrategy mover)
    (hpositive : 0 < quittingTerminalExploitabilityInf reward)
    (hsourceLower : quittingTerminalExploitabilityInf reward <
      quittingTerminalDebtSum reward profile)
    (hsourceUpper : quittingTerminalDebtSum reward profile <
      2 * quittingTerminalExploitabilityInf reward)
    (hmoverMax : ∀ other,
      quittingTerminalDeviationDebt reward profile other ≤
        quittingTerminalDeviationDebt reward profile mover)
    (hexact : quittingTerminalPayoff reward
        (Function.update profile mover response) mover =
      quittingContinuationBestResponseValue reward profile mover) :
    quittingTerminalExploitabilityInf reward <
        quittingTerminalDeviationDebt reward profile mover ∧
      quittingTerminalPayoff reward (Function.update profile mover response) mover -
          quittingTerminalPayoff reward profile mover =
        quittingTerminalDeviationDebt reward profile mover ∧
      quittingTerminalDeviationDebt reward
          (Function.update profile mover response) mover = 0 ∧
      quittingTerminalDebtSum reward profile *
          (2 * quittingTerminalExploitabilityInf reward -
            quittingTerminalDebtSum reward profile) /
          (quittingTerminalDebtSum reward profile -
            quittingTerminalExploitabilityInf reward) ≤
        quittingTerminalDeviationDebt reward profile mover *
          (2 * quittingTerminalExploitabilityInf reward -
            quittingTerminalDebtSum reward profile) /
          (quittingTerminalDeviationDebt reward profile mover -
            quittingTerminalExploitabilityInf reward) ∧
      quittingTerminalDeviationDebt reward profile mover *
          (2 * quittingTerminalExploitabilityInf reward -
            quittingTerminalDebtSum reward profile) /
          (quittingTerminalDeviationDebt reward profile mover -
            quittingTerminalExploitabilityInf reward) ≤
        quittingTerminalDebtSum reward (Function.update profile mover response) -
          quittingTerminalDebtSum reward profile ∧
      quittingTerminalDebtSum reward profile *
          (2 * quittingTerminalExploitabilityInf reward -
            quittingTerminalDebtSum reward profile) /
          (quittingTerminalDebtSum reward profile -
            quittingTerminalExploitabilityInf reward) ≤
        quittingTerminalDebtSum reward (Function.update profile mover response) -
          quittingTerminalDebtSum reward profile ∧
      0 < quittingTerminalDebtSum reward (Function.update profile mover response) -
        quittingTerminalDebtSum reward profile := by
  let eta := quittingTerminalExploitabilityInf reward
  let sourceTotal := quittingTerminalDebtSum reward profile
  let moverDebt := quittingTerminalDeviationDebt reward profile mover
  let endpoint := Function.update profile mover response
  let endpointTotal := quittingTerminalDebtSum reward endpoint
  have hdebtNonneg : ∀ who,
      0 ≤ quittingTerminalDeviationDebt reward profile who :=
    fun who => quittingTerminalDeviationDebt_nonneg reward profile who
  have hexploitLe : quittingTerminalExploitability reward profile ≤ moverDebt := by
    unfold quittingTerminalExploitability
    apply finitePlayerMax_le
    intro who
    change max 0 (quittingTerminalDeviationDebt reward profile who) ≤ moverDebt
    rw [max_eq_right (hdebtNonneg who)]
    exact hmoverMax who
  have hetaMover : eta ≤ moverDebt := by
    exact (quittingTerminalExploitabilityInf_le reward profile).trans hexploitLe
  have hendpointMover : quittingTerminalDeviationDebt reward endpoint mover = 0 := by
    dsimp only [endpoint]
    unfold quittingTerminalDeviationDebt
    rw [quittingContinuationBestResponseValue_update_self, hexact]
    ring
  have hgain : quittingTerminalPayoff reward endpoint mover -
      quittingTerminalPayoff reward profile mover = moverDebt := by
    dsimp only [endpoint, moverDebt]
    unfold quittingTerminalDeviationDebt
    rw [hexact]
  have hsourceLower' : eta < sourceTotal := hsourceLower
  have hsourceUpper' : sourceTotal < 2 * eta := hsourceUpper
  have hmoverStrict : eta < moverDebt := by
    by_contra hnot
    have hmoverEq : moverDebt = eta := le_antisymm (not_lt.mp hnot) hetaMover
    have hcrossingInequality : ∀ theta,
        0 < theta → theta < 1 →
        eta + (1 - theta) * moverDebt ≤
          (1 - theta) * sourceTotal + theta * endpointTotal := by
      intro theta htheta0 htheta1
      let mixed := Function.update profile mover
        (quittingStoppingLawMixtureBehaviorStrategy reward mover
          (profile mover) response theta htheta0.le htheta1.le)
      have hmoverChord :=
        quittingTerminalSemanticDebt_stoppingLawMixture_eq_self
          reward profile mover (profile mover) response theta
            htheta0.le htheta1.le
      rw [Function.update_eq_self] at hmoverChord
      change quittingTerminalDeviationDebt reward mixed mover =
        (1 - theta) * moverDebt + theta *
          quittingTerminalDeviationDebt reward endpoint mover at hmoverChord
      rw [hendpointMover, mul_zero, add_zero] at hmoverChord
      have hmoverLt : quittingTerminalDeviationDebt reward mixed mover < eta := by
        rw [hmoverChord, hmoverEq]
        nlinarith
      have hlower :=
        quittingTerminalExploitabilityInf_add_debt_le_debtSum_of_debt_lt
          reward mixed mover hmoverLt
      have hupper := quittingTerminalDebtSum_stoppingLawMixture_le
        reward profile mover (profile mover) response theta htheta0.le htheta1.le
      rw [Function.update_eq_self] at hupper
      change quittingTerminalDebtSum reward mixed ≤
        (1 - theta) * sourceTotal + theta * endpointTotal at hupper
      rw [hmoverChord] at hlower
      exact hlower.trans hupper
    have hlimit := affine_le_of_forall_right
      0 eta moverDebt sourceTotal endpointTotal (by norm_num)
      hcrossingInequality
    norm_num [hmoverEq] at hlimit
    linarith
  have hmoverPos : 0 < moverDebt := hpositive.trans hmoverStrict
  let theta0 := (moverDebt - eta) / moverDebt
  have htheta0Pos : 0 < theta0 := by
    dsimp only [theta0]
    positivity
  have htheta0LtOne : theta0 < 1 := by
    dsimp only [theta0]
    rw [div_lt_one hmoverPos]
    linarith
  have hrightInequality : ∀ theta,
      theta0 < theta → theta < 1 →
      eta + (1 - theta) * moverDebt ≤
        (1 - theta) * sourceTotal + theta * endpointTotal := by
    intro theta hthetaLower hthetaUpper
    have hthetaPositive := htheta0Pos.trans hthetaLower
    let mixed := Function.update profile mover
      (quittingStoppingLawMixtureBehaviorStrategy reward mover
        (profile mover) response theta hthetaPositive.le hthetaUpper.le)
    have hmoverChord :=
      quittingTerminalSemanticDebt_stoppingLawMixture_eq_self
        reward profile mover (profile mover) response theta
          hthetaPositive.le hthetaUpper.le
    rw [Function.update_eq_self] at hmoverChord
    change quittingTerminalDeviationDebt reward mixed mover =
      (1 - theta) * moverDebt + theta *
        quittingTerminalDeviationDebt reward endpoint mover at hmoverChord
    rw [hendpointMover, mul_zero, add_zero] at hmoverChord
    have hmoverLt : quittingTerminalDeviationDebt reward mixed mover < eta := by
      rw [hmoverChord]
      dsimp only [theta0] at hthetaLower
      rw [div_lt_iff₀ hmoverPos] at hthetaLower
      nlinarith
    have hlower :=
      quittingTerminalExploitabilityInf_add_debt_le_debtSum_of_debt_lt
        reward mixed mover hmoverLt
    have hupper := quittingTerminalDebtSum_stoppingLawMixture_le
      reward profile mover (profile mover) response theta
        hthetaPositive.le hthetaUpper.le
    rw [Function.update_eq_self] at hupper
    change quittingTerminalDebtSum reward mixed ≤
      (1 - theta) * sourceTotal + theta * endpointTotal at hupper
    rw [hmoverChord] at hlower
    exact hlower.trans hupper
  have hcross := affine_le_of_forall_right
    theta0 eta moverDebt sourceTotal endpointTotal htheta0LtOne hrightInequality
  have hfirstFloor : moverDebt * (2 * eta - sourceTotal) /
      (moverDebt - eta) ≤ endpointTotal - sourceTotal := by
    dsimp only [theta0] at hcross
    have hdenom : 0 < moverDebt - eta := sub_pos.mpr hmoverStrict
    rw [div_le_iff₀ hdenom]
    have hcancel : moverDebt * ((moverDebt - eta) / moverDebt) =
        moverDebt - eta := by field_simp
    have hcancel' : moverDebt * (eta / moverDebt) = eta := by field_simp
    nlinarith
  have hmoverLeTotal : moverDebt ≤ sourceTotal := by
    dsimp only [moverDebt, sourceTotal]
    unfold quittingTerminalDebtSum
    exact Finset.single_le_sum
      (fun who _ => hdebtNonneg who) (Finset.mem_univ mover)
  have hsecondFloor : sourceTotal * (2 * eta - sourceTotal) /
      (sourceTotal - eta) ≤ endpointTotal - sourceTotal := by
    have hsourceDenom : 0 < sourceTotal - eta := sub_pos.mpr hsourceLower'
    have hmoverDenom : 0 < moverDebt - eta := sub_pos.mpr hmoverStrict
    apply le_trans ?_ hfirstFloor
    have hratio : sourceTotal / (sourceTotal - eta) ≤
        moverDebt / (moverDebt - eta) := by
      rw [div_le_div_iff₀ hsourceDenom hmoverDenom]
      nlinarith [hmoverLeTotal]
    have hfactor : 0 < 2 * eta - sourceTotal := sub_pos.mpr hsourceUpper'
    calc
      sourceTotal * (2 * eta - sourceTotal) / (sourceTotal - eta) =
          (2 * eta - sourceTotal) *
            (sourceTotal / (sourceTotal - eta)) := by ring
      _ ≤ (2 * eta - sourceTotal) *
          (moverDebt / (moverDebt - eta)) :=
        mul_le_mul_of_nonneg_left hratio hfactor.le
      _ = moverDebt * (2 * eta - sourceTotal) / (moverDebt - eta) := by ring
  have hmiddleFloor : sourceTotal * (2 * eta - sourceTotal) /
      (sourceTotal - eta) ≤
        moverDebt * (2 * eta - sourceTotal) / (moverDebt - eta) := by
    have hsourceDenom : 0 < sourceTotal - eta := sub_pos.mpr hsourceLower'
    have hmoverDenom : 0 < moverDebt - eta := sub_pos.mpr hmoverStrict
    have hratio : sourceTotal / (sourceTotal - eta) ≤
        moverDebt / (moverDebt - eta) := by
      rw [div_le_div_iff₀ hsourceDenom hmoverDenom]
      nlinarith [hmoverLeTotal]
    have hfactor : 0 ≤ 2 * eta - sourceTotal := (sub_pos.mpr hsourceUpper').le
    calc
      sourceTotal * (2 * eta - sourceTotal) / (sourceTotal - eta) =
          (2 * eta - sourceTotal) *
            (sourceTotal / (sourceTotal - eta)) := by ring
      _ ≤ (2 * eta - sourceTotal) *
          (moverDebt / (moverDebt - eta)) :=
        mul_le_mul_of_nonneg_left hratio hfactor
      _ = moverDebt * (2 * eta - sourceTotal) / (moverDebt - eta) := by ring
  have htargetExcess : 0 < endpointTotal - sourceTotal := by
    have hsourceDenom : 0 < sourceTotal - eta := sub_pos.mpr hsourceLower'
    have hfactor : 0 < 2 * eta - sourceTotal := sub_pos.mpr hsourceUpper'
    have hpositiveFloor : 0 < sourceTotal * (2 * eta - sourceTotal) /
        (sourceTotal - eta) := by
      have hsourcePositive : 0 < sourceTotal := hpositive.trans hsourceLower'
      positivity
    exact hpositiveFloor.trans_le hsecondFloor
  exact ⟨hmoverStrict, hgain, hendpointMover, hmiddleFloor, hfirstFloor,
    hsecondFloor, htargetExcess⟩

end GameTheory
