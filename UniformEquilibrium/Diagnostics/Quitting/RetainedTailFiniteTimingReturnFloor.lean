/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.RetainedTailFiniteTimingNash
import UniformEquilibrium.Quitting.Terminal.ExploitabilityGap

/-!
# A joint-return floor for punishment-separated finite timing Nash grafts

The terminal gap first selects a player whose deleted survival through the
timing word is large.  Replacing the retained tail by that player's fixed
punishment makes the selected host harmless.  Every other player's deleted
survival is controlled by its product with the host survival.  Applying the
terminal gap again gives the exact joint-return floor.

This is a no-go for screened finite timing Nash grafts.  Joint return is not
a marked density or a payoff return, and this module supplies no recurrence
or completion consumer.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A terminal exploitability gap selects a coordinate whose literal
behavioral debt is at least the gap. -/
theorem HasTerminalExploitabilityGap.exists_debt_ge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {gamma : ℝ}
    (gap : HasTerminalExploitabilityGap reward gamma)
    (profile : (quittingGame reward).BehaviorProfile) :
    ∃ who : ι, gamma ≤ quittingTerminalDeviationDebt reward profile who := by
  obtain ⟨who, deviation, hgain⟩ := gap profile
  refine ⟨who, ?_⟩
  have hcap := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward profile who deviation
  unfold quittingTerminalDeviationDebt
  linarith

/-- Reward diameter bounds every coordinate of literal terminal debt. -/
theorem quittingTerminalDeviationDebt_le_two_mul_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (R : ℝ)
    (hreward : ∀ S player, |reward S player| ≤ R) :
    quittingTerminalDeviationDebt reward profile who ≤ 2 * R := by
  have hcap := abs_quittingContinuationBestResponseValue_le
    reward profile who hreward
  have hpayoff := abs_quittingTerminalPayoff_le reward profile who hreward
  unfold quittingTerminalDeviationDebt
  linarith [le_of_abs_le hcap, neg_le_of_abs_le hpayoff]

/-- The gap-selected host has player-deleted return at least
`gamma / (2 * R)`, stated without division for robust downstream use. -/
theorem IsQuittingRetainedTailFiniteTimingNash.exists_host_gap_le_two_mul_bound_mul
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {roots : List (ι → PMF Bool)}
    {tail : (quittingGame reward).BehaviorProfile}
    (nash : IsQuittingRetainedTailFiniteTimingNash reward roots tail)
    {gamma R : ℝ} (gap : HasTerminalExploitabilityGap reward gamma)
    (hreward : ∀ S player, |reward S player| ≤ R) :
    ∃ host : ι, gamma ≤
      2 * R * quittingLiteralRootStackOpponentSurvival roots host := by
  obtain ⟨host, hhost⟩ := gap.exists_debt_ge
    (quittingRetainedTailFiniteTimingGraft reward roots tail)
  refine ⟨host, hhost.trans ?_⟩
  have htransport := nash.debt_le_deletedReturn_mul_tailDebt host
  have htail := quittingTerminalDeviationDebt_le_two_mul_bound
    reward tail host R hreward
  have hscaled := mul_le_mul_of_nonneg_left htail
    (quittingLiteralRootStackOpponentSurvival_nonneg roots host)
  nlinarith

/-- Quantitative no-go for fully screened finite timing Nash grafts.

Suppose one fixed positive terminal gap applies to every behavioral profile,
the reward table is bounded by `R > 0`, and the retained tail lies a positive
coordinatewise margin above fixed actual punishment caps.  Then the joint
probability that the finite timing word returns to that literal tail is at
least `gamma^2 / (2 R (gamma + 2 R))`.

The conclusion is only a return-mass floor.  It does not identify this mass
with any marked density, assert payoff return, or make the block renewable.
-/
theorem terminalGap_retainedTailFiniteTimingNash_jointReturn_ge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile)
    (nash : IsQuittingRetainedTailFiniteTimingNash reward roots tail)
    (punishment : ι → (quittingGame reward).BehaviorProfile)
    (chi : ι → ℝ) {gamma R kappa : ℝ}
    (hgamma : 0 < gamma) (hR : 0 < R) (hkappa : 0 < kappa)
    (gap : HasTerminalExploitabilityGap reward gamma)
    (hreward : ∀ S player, |reward S player| ≤ R)
    (htail : ∀ who, chi who + kappa ≤
      quittingTerminalPayoff reward tail who)
    (hpunishment : ∀ who,
      quittingContinuationBestResponseValue reward (punishment who) who ≤
        chi who + kappa / 2) :
    gamma ^ 2 / (2 * R * (gamma + 2 * R)) ≤
      quittingLiteralRootStackJointSurvival roots := by
  obtain ⟨host, hhost⟩ :=
    nash.exists_host_gap_le_two_mul_bound_mul gap hreward
  have hhostCap : quittingContinuationBestResponseValue reward
      (punishment host) host ≤ quittingTerminalPayoff reward tail host := by
    exact (hpunishment host).trans <| by
      have := htail host
      linarith
  let punished := quittingRetainedTailFiniteTimingGraft
    reward roots (punishment host)
  obtain ⟨who, hwho⟩ := gap.exists_debt_ge punished
  have hM0 := quittingLiteralRootStackJointSurvival_nonneg roots
  have hden : 0 < 2 * R * (gamma + 2 * R) := by positivity
  apply (div_le_iff₀ hden).2
  by_cases hwhoHost : who = host
  · subst who
    have hhostDebt := nash.hostPunishmentDebt_le
      (punishment host) host R hreward hhostCap
    have hgapM : gamma ≤
        2 * R * quittingLiteralRootStackJointSurvival roots := by
      exact hwho.trans hhostDebt
    have hfactor : gamma ≤ gamma + 2 * R := by linarith
    have hmul := mul_le_mul hgapM hfactor (le_of_lt hgamma)
      (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hR)) hM0)
    nlinarith
  · have hwhoDebt := nash.punishmentDebt_le
      (punishment host) who R (le_of_lt hR) hreward
    have hgapOther : gamma ≤ 2 * R *
        (quittingLiteralRootStackOpponentSurvival roots who +
          quittingLiteralRootStackJointSurvival roots) :=
      hwho.trans hwhoDebt
    have hproduct := mul_opponentSurvival_le_jointSurvival_of_ne
      roots hwhoHost
    have hwhoSurvival0 :=
      quittingLiteralRootStackOpponentSurvival_nonneg roots who
    have hgammaWho := mul_le_mul_of_nonneg_left hhost hwhoSurvival0
    have hgammaWho' :
        gamma * quittingLiteralRootStackOpponentSurvival roots who ≤
          2 * R * quittingLiteralRootStackJointSurvival roots := by
      nlinarith
    have hmulGap := mul_le_mul_of_nonneg_left hgapOther (le_of_lt hgamma)
    nlinarith

/-- The universal joint-return floor is strictly positive under the packet's
positive gap and reward-bound hypotheses. -/
theorem terminalGap_retainedTailFiniteTimingNash_jointReturnFloor_pos
    {gamma R : ℝ} (hgamma : 0 < gamma) (hR : 0 < R) :
    0 < gamma ^ 2 / (2 * R * (gamma + 2 * R)) := by
  positivity

end GameTheory
