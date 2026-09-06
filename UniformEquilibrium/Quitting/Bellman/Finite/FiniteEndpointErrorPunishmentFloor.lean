/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.BellmanTelescope
import UniformEquilibrium.Quitting.Classification.AbnormalPlayers
import UniformEquilibrium.Quitting.Paths.QuitEndpointOpponentBound

/-!
# Finite endpoint-error burn-in without an initial punishment floor

The finite backward-growth argument uses endpoint inequalities alone.  It
assumes no Bellman equality, initial punishment floor, or semantic realization
of the continuation annotations.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- If a normal player's next endpoint is more than `τ` below punishment and
both pure endpoints have error at most `ζ`, the punishment debt grows by more
than `τ² / (8M)` when moving one row backward. -/
theorem quittingEndpointError_punishmentDebtDrop_gt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current next : Payoff ι) (root : ι → PMF Bool) (who : ι)
    {M τ ζ : ℝ}
    (hM : 0 < M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hnormal : IsQuittingNormalPlayer reward who)
    (hτ : 0 < τ)
    (hζ : ζ ≤ min (τ / 2) (τ ^ 2 / (8 * M)))
    (hquit : quittingRootQuitPayoff reward current root who ≤ next who + ζ)
    (hcontinue :
      quittingRootContinuePayoff reward current root who ≤ next who + ζ)
    (hbad : τ < quittingPunishmentValue reward who - next who) :
    τ ^ 2 / (8 * M) <
      (quittingPunishmentValue reward who - current who) -
        (quittingPunishmentValue reward who - next who) := by
  let punishment := quittingPunishmentValue reward who
  let singleton := reward (quittingSingletonTerminal who) who
  let alpha := quittingStationaryFixedOpponentsContinueMass root who
  let absorb := quittingRootOpponentAbsorptionMass root who
  let quitValue := quittingStationaryFixedOpponentsQuitValue reward root who
  let continueReward :=
    quittingStationaryFixedOpponentsContinueReward reward root who
  have hτ2 : 0 < τ / 2 := by positivity
  have hκ : 0 < τ ^ 2 / (8 * M) := by positivity
  have hnormal' : punishment ≤ singleton := by
    simpa only [punishment, singleton, IsQuittingNormalPlayer,
      quittingSoloSelfPayoff, quittingSingletonTerminal] using hnormal
  have hquitEq :
      quittingRootQuitPayoff reward current root who = quitValue := by
    simpa [quitValue, quittingStationaryFixedOpponentsQuitValue] using
      quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward
        (fun _ => root) who current 0
  have hcontinueEq :
      quittingRootContinuePayoff reward current root who =
        continueReward + alpha * current who := by
    simpa [continueReward, alpha,
      quittingStationaryFixedOpponentsContinueReward,
      quittingStationaryFixedOpponentsContinueMass] using
      quittingRootContinuePayoff_eq_fixedOpponents reward
        (fun _ => root) who current 0
  have halphaEq :
      alpha = 1 - absorb := by
    simpa only [alpha, absorb, quittingStationaryFixedOpponentsContinueMass,
      quittingFixedOpponentsContinueMass,
      quittingRootOpponentContinueMass] using
      quittingRootOpponentContinueMass_eq_one_sub_absorptionMass root who
  have halpha0 : 0 ≤ alpha := by
    simpa only [alpha, quittingStationaryFixedOpponentsContinueMass,
      quittingFixedOpponentsContinueMass,
      quittingRootOpponentContinueMass] using
      quittingRootOpponentContinueMass_nonneg root who
  have halpha1 : alpha ≤ 1 := by
    simpa only [alpha, quittingStationaryFixedOpponentsContinueMass,
      quittingFixedOpponentsContinueMass,
      quittingRootOpponentContinueMass] using
      quittingRootOpponentContinueMass_le_one root who
  have hquitBound :=
    abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
      reward current root who M hreward
  have hquitLower : singleton - 2 * M * absorb ≤ quitValue := by
    rw [← hquitEq]
    have := neg_le_of_abs_le hquitBound
    linarith
  have hζτ : ζ ≤ τ / 2 := hζ.trans (min_le_left _ _)
  have hζκ : ζ ≤ τ ^ 2 / (8 * M) := hζ.trans (min_le_right _ _)
  have habsGap : τ / (4 * M) < absorb := by
    have hgap : τ / 2 < 2 * M * absorb := by
      rw [hquitEq] at hquit
      linarith
    apply (div_lt_iff₀ (by positivity : 0 < 4 * M)).2
    nlinarith
  have halphaLt : alpha < 1 := by
    rw [halphaEq]
    have habs0 : 0 < absorb := lt_trans (by positivity) habsGap
    linarith
  have hquitLt : quitValue < punishment := by
    rw [hquitEq] at hquit
    linarith
  have hcap := quittingPunishmentValue_le_stationaryUnilateralCap
    reward who root
  rw [quittingStationaryUnilateralCap_eq_max_div] at hcap
  have hride : punishment ≤ continueReward / (1 - alpha) := by
    rcases le_max_iff.mp hcap with hstop | hride
    · exact False.elim ((not_le_of_gt hquitLt) hstop)
    · exact hride
  have hdenom : 0 < 1 - alpha := sub_pos.mpr halphaLt
  have hcontinueReward : (1 - alpha) * punishment ≤ continueReward := by
    simpa [mul_comm] using (le_div_iff₀ hdenom).mp hride
  rw [hcontinueEq] at hcontinue
  have hscaled :
      quittingPunishmentValue reward who - next who - ζ ≤
        alpha * (quittingPunishmentValue reward who - current who) := by
    dsimp only [punishment] at hcontinueReward
    nlinarith
  have halphaPos : 0 < alpha := by
    by_contra hnot
    have : alpha = 0 := le_antisymm (le_of_not_gt hnot) halpha0
    rw [this] at hscaled
    linarith
  have habsTimesGap :
      τ ^ 2 / (4 * M) <
        absorb * (quittingPunishmentValue reward who - next who) := by
    have hscaledAbsorb : τ < 4 * M * absorb :=
      by simpa [mul_comm] using
        (div_lt_iff₀ (by positivity : 0 < 4 * M)).mp habsGap
    have hdebtPos :
        0 < quittingPunishmentValue reward who - next who :=
      lt_trans hτ hbad
    have hproduct : τ * τ <
        (4 * M * absorb) *
          (quittingPunishmentValue reward who - next who) :=
      (mul_lt_mul_of_pos_left hbad hτ).trans
        (mul_lt_mul_of_pos_right hscaledAbsorb hdebtPos)
    apply (div_lt_iff₀ (by positivity : 0 < 4 * M)).2
    calc
      τ ^ 2 = τ * τ := by ring
      _ < (4 * M * absorb) *
          (quittingPunishmentValue reward who - next who) := hproduct
      _ = absorb * (quittingPunishmentValue reward who - next who) *
          (4 * M) := by ring
  have hscaledDrop :
      τ ^ 2 / (8 * M) <
        alpha * ((quittingPunishmentValue reward who - current who) -
          (quittingPunishmentValue reward who - next who)) := by
    have habsEq : absorb = 1 - alpha := by linarith [halphaEq]
    have hdouble : τ ^ 2 / (4 * M) = 2 * (τ ^ 2 / (8 * M)) := by
      field_simp
      ring
    nlinarith
  have hdropPos : 0 <
      (quittingPunishmentValue reward who - current who) -
        (quittingPunishmentValue reward who - next who) := by
    nlinarith [hscaledDrop, hκ, halpha0]
  exact hscaledDrop.trans_le
    (mul_le_of_le_one_left (le_of_lt hdropPos) halpha1)

/-- Finite endpoint inequalities force every endpoint after a fixed burn-in
into the `τ`-punishment box.  Only the displayed finite window is bounded or
constrained; in particular, `value 0` need not satisfy a punishment floor. -/
theorem quittingPunishmentFloor_le_of_finite_endpointErrors_after_burnIn
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    {M B τ ζ : ℝ} {L H : ℕ}
    (hM : 0 < M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hnormal : ∀ who, IsQuittingNormalPlayer reward who)
    (hτ : 0 < τ)
    (hζ : ζ ≤ min (τ / 2) (τ ^ 2 / (8 * M)))
    (hburn : M + B < (L : ℝ) * (τ ^ 2 / (8 * M)))
    (hbound : ∀ time, time ≤ H → ∀ player, |value time player| ≤ B)
    (hquit : ∀ time, time < H → ∀ player,
      quittingRootQuitPayoff reward (value time) (roots time) player ≤
        value (time + 1) player + ζ)
    (hcontinue : ∀ time, time < H → ∀ player,
      quittingRootContinuePayoff reward (value time) (roots time) player ≤
        value (time + 1) player + ζ) :
    ∀ time, L ≤ time → time ≤ H → ∀ player,
      quittingPunishmentValue reward player - τ ≤ value time player := by
  intro time hLtime htimeH player
  let punishment := quittingPunishmentValue reward player
  let κ := τ ^ 2 / (8 * M)
  have hκ : 0 < κ := by
    dsimp only [κ]
    positivity
  have hP : punishment ≤ M := by
    have hnormal' : punishment ≤
        reward (quittingSingletonTerminal player) player := by
      simpa only [punishment, IsQuittingNormalPlayer,
        quittingSoloSelfPayoff, quittingSingletonTerminal] using
        hnormal player
    exact hnormal'.trans
      (le_of_abs_le (hreward (quittingSingletonTerminal player) player))
  have hback : ∀ n, n ≤ H → τ < punishment - value n player →
      punishment - value n player + (n : ℝ) * κ ≤
        punishment - value 0 player := by
    intro n
    induction n with
    | zero =>
        intro _ _
        simp
    | succ n ih =>
        intro hnH hnBad
        have hnLt : n < H := by omega
        have hstep : κ <
            (punishment - value n player) -
              (punishment - value (n + 1) player) := by
          simpa only [punishment, κ] using
            quittingEndpointError_punishmentDebtDrop_gt
              reward (value n) (value (n + 1)) (roots n) player
              hM hreward (hnormal player) hτ hζ
              (hquit n hnLt player) (hcontinue n hnLt player) hnBad
        have hnBadPrev : τ < punishment - value n player := by
          linarith
        have ihPrev := ih (by omega) hnBadPrev
        rw [Nat.cast_succ]
        nlinarith
  by_contra hfloor
  have hbad : τ < punishment - value time player := by
    dsimp only [punishment]
    have := lt_of_not_ge hfloor
    linarith
  have haccumulated := hback time htimeH hbad
  have hvalue0 : -B ≤ value 0 player :=
    neg_le_of_abs_le (hbound 0 (Nat.zero_le H) player)
  have hdebt0 : punishment - value 0 player ≤ M + B := by
    linarith
  have hcast : (L : ℝ) ≤ (time : ℝ) := by exact_mod_cast hLtime
  have hscale : (L : ℝ) * κ ≤ (time : ℝ) * κ :=
    mul_le_mul_of_nonneg_right hcast (le_of_lt hκ)
  dsimp only [κ] at hscale haccumulated
  nlinarith

end GameTheory
