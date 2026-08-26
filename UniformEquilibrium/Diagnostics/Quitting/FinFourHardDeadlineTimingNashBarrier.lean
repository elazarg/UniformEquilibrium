/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.FiniteFubini
import UniformEquilibrium.Diagnostics.Quitting.FiniteDeadlineTimingNashDebt
import UniformEquilibrium.Quitting.Cycles.SoloRootSequenceValues
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-!
# A normalized Fin4 hard-deadline timing-Nash barrier

This file formalizes the concrete rational table used to separate exact Nash
selection in hard finite timing games from unrestricted finite-clock profile
selection.  Players `0` and `1` are active; players `2` and `3` are strict
Continue dummies.
-/

noncomputable section

namespace GameTheory
namespace FinFourHardDeadlineTimingNashBarrier

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

abbrev Player := Fin 4

/-- The rational Fin4 table from the hard-deadline barrier packet. -/
def reward (terminal : {S : Finset Player // S.Nonempty})
    (who : Player) : ℝ :=
  if who = 0 then
    if 0 ∈ terminal.1 then
      if 1 ∈ terminal.1 then 0 else 1 / 2
    else if 1 ∈ terminal.1 then 1 else 0
  else if who = 1 then
    if (0 ∈ terminal.1) = (1 ∈ terminal.1) then 0 else -1
  else if who ∈ terminal.1 then -1 else 0

/-- Every coordinate of the concrete table is normalized. -/
theorem abs_reward_le_one (terminal : {S : Finset Player // S.Nonempty})
    (who : Player) : |reward terminal who| ≤ 1 := by
  fin_cases who <;> simp only [reward] <;> split_ifs <;> norm_num

@[simp] theorem reward_zero (terminal : {S : Finset Player // S.Nonempty}) :
    reward terminal 0 =
      if 0 ∈ terminal.1 then
        if 1 ∈ terminal.1 then 0 else 1 / 2
      else if 1 ∈ terminal.1 then 1 else 0 := by
  simp [reward]

@[simp] theorem reward_one (terminal : {S : Finset Player // S.Nonempty}) :
    reward terminal 1 =
      if (0 ∈ terminal.1) = (1 ∈ terminal.1) then 0 else -1 := by
  simp [reward]

theorem reward_dummy (terminal : {S : Finset Player // S.Nonempty})
    (who : Player) (htwo : 2 ≤ who) :
    reward terminal who = if who ∈ terminal.1 then -1 else 0 := by
  fin_cases who <;> simp_all [reward]

@[simp] theorem solo_reward_zero :
    reward (quittingSingletonTerminal (0 : Player)) 0 = 1 / 2 := by
  norm_num [reward, quittingSingletonTerminal]

@[simp] theorem solo_reward_one :
    reward (quittingSingletonTerminal (1 : Player)) 1 = -1 := by
  norm_num [reward, quittingSingletonTerminal]

@[simp] theorem solo_reward_two :
    reward (quittingSingletonTerminal (2 : Player)) 2 = -1 := by
  simp [reward, quittingSingletonTerminal]

@[simp] theorem solo_reward_three :
    reward (quittingSingletonTerminal (3 : Player)) 3 = -1 := by
  simp [reward, quittingSingletonTerminal]

@[simp] theorem singleton_zero_reward_zero :
    quittingSoloReward reward (0 : Player) 0 = 1 / 2 := by
  exact solo_reward_zero

@[simp] theorem singleton_zero_reward_one :
    quittingSoloReward reward (0 : Player) 1 = -1 := by
  norm_num [reward, quittingSoloReward, quittingSingletonTerminal]

@[simp] theorem singleton_one_reward_zero :
    quittingSoloReward reward (1 : Player) 0 = 1 := by
  norm_num [reward, quittingSoloReward, quittingSingletonTerminal]

@[simp] theorem singleton_one_reward_one :
    quittingSoloReward reward (1 : Player) 1 = -1 := by
  norm_num [reward, quittingSoloReward, quittingSingletonTerminal]

@[simp] theorem collision_zero_one_reward_zero :
    quittingSingletonCollisionReward reward (0 : Player) 1 = 0 := by
  norm_num [quittingSingletonCollisionReward, reward,
    quittingSingletonTerminal]

@[simp] theorem collision_zero_one_reward_one :
    quittingSingletonCollisionReward reward (0 : Player) 1 = 0 := by
  norm_num [quittingSingletonCollisionReward, reward,
    quittingSingletonTerminal]

/-! ## Exact scalar recursion and the nonvanishing debt -/

/-- Active player `0`'s continuation value with `dates` finite dates. -/
def zeroValue (dates : ℕ) : ℝ :=
  1 / 2 * (1 - 1 / ((2 : ℝ) ^ (dates + 1) - 1))

/-- Active player `1`'s continuation value with `dates` finite dates. -/
def oneValue (dates : ℕ) : ℝ := -1 + 1 / ((dates : ℝ) + 1)

/-- Current hazard of active player `0` before a `dates`-date tail. -/
def zeroHazard (dates : ℕ) : ℝ := 1 / ((dates : ℝ) + 2)

/-- Current hazard of active player `1` before a `dates`-date tail. -/
def oneHazard (dates : ℕ) : ℝ := 1 / ((2 : ℝ) ^ (dates + 2) - 1)

@[simp] theorem zeroValue_zero : zeroValue 0 = 0 := by
  norm_num [zeroValue]

@[simp] theorem oneValue_zero : oneValue 0 = 0 := by
  norm_num [oneValue]

theorem zeroValue_lt_half (dates : ℕ) : zeroValue dates < 1 / 2 := by
  unfold zeroValue
  have hpow : (1 : ℝ) < 2 ^ (dates + 1) := by
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hden : 0 < (2 : ℝ) ^ (dates + 1) - 1 := by linarith
  have hinv : 0 < 1 / ((2 : ℝ) ^ (dates + 1) - 1) := by positivity
  nlinarith

theorem oneValue_gt_neg_one (dates : ℕ) : -1 < oneValue dates := by
  unfold oneValue
  have hden : 0 < (dates : ℝ) + 1 := by positivity
  have hinv : 0 < 1 / ((dates : ℝ) + 1) := one_div_pos.mpr hden
  linarith

theorem zeroValue_succ (dates : ℕ) :
    zeroValue (dates + 1) = 1 / (3 - 2 * zeroValue dates) := by
  unfold zeroValue
  let y : ℝ := 2 ^ (dates + 1)
  have hy : (1 : ℝ) < y := by
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hy1 : y - 1 ≠ 0 := by linarith
  have hy2 : 2 * y - 1 ≠ 0 := by nlinarith
  have hpow : (2 : ℝ) ^ (dates + 1 + 1) = 2 * y := by
    rw [pow_succ]
    simp only [y]
    ring
  rw [hpow]
  change 1 / 2 * (1 - 1 / (2 * y - 1)) =
    1 / (3 - 2 * (1 / 2 * (1 - 1 / (y - 1))))
  have hleft : 1 / 2 * (1 - 1 / (2 * y - 1)) =
      (y - 1) / (2 * y - 1) := by
    field_simp [hy2]
    ring
  have hinner : 3 - 2 * (1 / 2 * (1 - 1 / (y - 1))) =
      (2 * y - 1) / (y - 1) := by
    field_simp [hy1]
    ring
  rw [hleft, hinner]
  field_simp [hy1, hy2]

theorem oneValue_succ (dates : ℕ) :
    oneValue (dates + 1) = -1 / (2 + oneValue dates) := by
  unfold oneValue
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hden : (dates : ℝ) + 1 ≠ 0 := by positivity
  have hden' : (dates : ℝ) + 2 ≠ 0 := by positivity
  have hinner : 2 + (-1 + 1 / ((dates : ℝ) + 1)) =
      ((dates : ℝ) + 2) / ((dates : ℝ) + 1) := by
    field_simp [hden]
    ring
  rw [hinner]
  field_simp [hden, hden']
  ring

theorem zeroHazard_eq_indifference (dates : ℕ) :
    zeroHazard dates = (1 + oneValue dates) / (2 + oneValue dates) := by
  unfold zeroHazard oneValue
  have hden : (dates : ℝ) + 1 ≠ 0 := by positivity
  have hden' : (dates : ℝ) + 2 ≠ 0 := by positivity
  have hinner : 2 + (-1 + 1 / ((dates : ℝ) + 1)) =
      ((dates : ℝ) + 2) / ((dates : ℝ) + 1) := by
    field_simp [hden]
    ring
  rw [hinner]
  field_simp [hden, hden']
  ring

theorem oneHazard_eq_indifference (dates : ℕ) :
    oneHazard dates =
      (1 / 2 - zeroValue dates) / (3 / 2 - zeroValue dates) := by
  unfold oneHazard zeroValue
  have hpow : (1 : ℝ) < 2 ^ (dates + 1) :=
    one_lt_pow₀ (by norm_num) (by omega)
  have hden : (2 : ℝ) ^ (dates + 1) - 1 ≠ 0 := by linarith
  field_simp [pow_succ, hden]
  ring_nf

/-- The exact positive-debt coordinate advertised by the packet. -/
def hardDeadlineDebt (deadline : ℕ) : ℝ :=
  (2 : ℝ) ^ (deadline - 1) / ((2 : ℝ) ^ (deadline + 1) - 1)

theorem hardDeadlineDebt_gt_quarter
    (deadline : ℕ) (hdeadline : 0 < deadline) :
    1 / 4 < hardDeadlineDebt deadline := by
  have hpred : deadline - 1 + 2 = deadline + 1 := by omega
  have hpow : (0 : ℝ) < 2 ^ (deadline - 1) := by positivity
  have hden : (0 : ℝ) < (2 : ℝ) ^ (deadline + 1) - 1 := by
    have : (1 : ℝ) < 2 ^ (deadline + 1) :=
      one_lt_pow₀ (by norm_num) (by omega)
    linarith
  unfold hardDeadlineDebt
  apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 4) hden).2
  rw [← hpred, pow_add]
  norm_num

/-- The exact hard-deadline debt strictly decreases when one date is added. -/
theorem hardDeadlineDebt_succ_lt
    (deadline : ℕ) (hdeadline : 0 < deadline) :
    hardDeadlineDebt (deadline + 1) < hardDeadlineDebt deadline := by
  let power : ℝ := 2 ^ (deadline - 1)
  have hpower : 0 < power := by positivity
  have hpred : deadline - 1 + 1 = deadline := by omega
  have hnext : deadline - 1 + 2 = deadline + 1 := by omega
  have hnext' : deadline - 1 + 3 = deadline + 2 := by omega
  have hpow : (2 : ℝ) ^ deadline = 2 * power := by
    rw [← hpred, pow_add]
    norm_num [power]
    ring
  have hpowNext : (2 : ℝ) ^ (deadline + 1) = 4 * power := by
    rw [← hnext, pow_add]
    norm_num [power]
    ring
  have hpowNext' : (2 : ℝ) ^ (deadline + 2) = 8 * power := by
    rw [← hnext', pow_add]
    norm_num [power]
    ring
  have hden : 0 < 4 * power - 1 := by
    rw [← hpowNext]
    have : (1 : ℝ) < 2 ^ (deadline + 1) :=
      one_lt_pow₀ (by norm_num) (by omega)
    linarith
  have hden' : 0 < 8 * power - 1 := by
    rw [← hpowNext']
    have : (1 : ℝ) < 2 ^ (deadline + 2) :=
      one_lt_pow₀ (by norm_num) (by omega)
    linarith
  unfold hardDeadlineDebt
  rw [show deadline + 1 - 1 = deadline by omega, hpow, hpowNext,
    hpowNext']
  apply (div_lt_div_iff₀ hden' hden).2
  nlinarith

/-! ## Explicit backward-induction roots -/

theorem zeroHazard_pos (dates : ℕ) : 0 < zeroHazard dates := by
  unfold zeroHazard
  positivity

theorem zeroHazard_le_one (dates : ℕ) : zeroHazard dates ≤ 1 := by
  unfold zeroHazard
  have hdates : (0 : ℝ) ≤ dates := by positivity
  rw [div_le_one (by positivity : (0 : ℝ) < dates + 2)]
  linarith

theorem oneHazard_pos (dates : ℕ) : 0 < oneHazard dates := by
  unfold oneHazard
  have hpow : (1 : ℝ) < 2 ^ (dates + 2) :=
    one_lt_pow₀ (by norm_num) (by omega)
  positivity

theorem oneHazard_le_one (dates : ℕ) : oneHazard dates ≤ 1 := by
  unfold oneHazard
  have hpow : (2 : ℝ) ≤ 2 ^ (dates + 2) := by
    rw [show dates + 2 = 2 + dates by omega, pow_add]
    have hone : (1 : ℝ) ≤ 2 ^ dates := one_le_pow₀ (by norm_num)
    norm_num
    linarith
  rw [div_le_one (by linarith : (0 : ℝ) < 2 ^ (dates + 2) - 1)]
  linarith

/-- The displayed interior active root before a tail with `dates` live dates;
the two dummy coordinates Continue surely. -/
def rootBefore (dates : ℕ) : Player → PMF Bool := fun who ↦
  if who = 0 then
    bernoulliBool (zeroHazard dates) (zeroHazard_pos dates).le
      (zeroHazard_le_one dates)
  else if who = 1 then
    bernoulliBool (oneHazard dates) (oneHazard_pos dates).le
      (oneHazard_le_one dates)
  else PMF.pure false

/-- Active continuation values after `dates` live dates; dummy values vanish. -/
def valueAfter (dates : ℕ) : Payoff Player := fun who ↦
  if who = 0 then zeroValue dates else if who = 1 then oneValue dates else 0

@[simp] theorem rootBefore_zero_true_toReal (dates : ℕ) :
    (rootBefore dates 0 true).toReal = zeroHazard dates := by
  simp [rootBefore]

@[simp] theorem rootBefore_one_true_toReal (dates : ℕ) :
    (rootBefore dates 1 true).toReal = oneHazard dates := by
  simp [rootBefore]

@[simp] theorem rootBefore_two (dates : ℕ) :
    rootBefore dates 2 = PMF.pure false := by
  simp [rootBefore]

@[simp] theorem rootBefore_three (dates : ℕ) :
    rootBefore dates 3 = PMF.pure false := by
  simp [rootBefore]

theorem rootBefore_endpointDifference_zero (dates : ℕ) :
    quittingRootEndpointDifference reward (valueAfter dates)
        (rootBefore dates) 0 = 0 := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4, expect_pmfPi_fin4]
  simp [rootBefore, valueAfter, reward, quittingRootPayoff,
    quittingQuitters, Math.Probability.expect_eq_sum]
  rw [oneHazard_eq_indifference]
  have hden : 0 < 3 / 2 - zeroValue dates := by
    have := zeroValue_lt_half dates
    linarith
  have hden' : 0 < 3 - 2 * zeroValue dates := by linarith
  field_simp [ne_of_gt hden, ne_of_gt hden']
  ring

theorem rootBefore_endpointDifference_one (dates : ℕ) :
    quittingRootEndpointDifference reward (valueAfter dates)
        (rootBefore dates) 1 = 0 := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4, expect_pmfPi_fin4]
  simp [rootBefore, valueAfter, reward, quittingRootPayoff,
    quittingQuitters, Math.Probability.expect_eq_sum]
  rw [zeroHazard_eq_indifference]
  have hden : 0 < 2 + oneValue dates := by
    have := oneValue_gt_neg_one dates
    linarith
  field_simp [ne_of_gt hden]
  ring

theorem rootBefore_endpointDifference_two (dates : ℕ) :
    quittingRootEndpointDifference reward (valueAfter dates)
        (rootBefore dates) 2 = -1 := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4, expect_pmfPi_fin4]
  simp [rootBefore, valueAfter, reward, quittingRootPayoff,
    quittingQuitters, Math.Probability.expect_eq_sum]

theorem rootBefore_endpointDifference_three (dates : ℕ) :
    quittingRootEndpointDifference reward (valueAfter dates)
        (rootBefore dates) 3 = -1 := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4, expect_pmfPi_fin4]
  simp [rootBefore, valueAfter, reward, quittingRootPayoff,
    quittingQuitters, Math.Probability.expect_eq_sum]

/-- Each displayed root is an exact Nash root against its displayed tail. -/
theorem rootBefore_isZeroNash (dates : ℕ) :
    IsεQuittingRootNash reward (valueAfter dates) 0 (rootBefore dates) := by
  rw [← isεQuittingRootEndpointNash_iff_isεQuittingRootNash]
  intro who
  have hcases : who = 0 ∨ who = 1 ∨ who = 2 ∨ who = 3 := by
    fin_cases who <;> simp
  rcases hcases with rfl | rfl | rfl | rfl
  · simp only [neg_zero]
    rw [rootBefore_endpointDifference_zero]
    simp
  · simp only [neg_zero]
    rw [rootBefore_endpointDifference_one]
    simp
  · simp only [neg_zero]
    rw [rootBefore_endpointDifference_two]
    simp [rootBefore]
  · simp only [neg_zero]
    rw [rootBefore_endpointDifference_three]
    simp [rootBefore]

theorem rootBefore_quitPayoff_zero (dates : ℕ) :
    quittingRootQuitPayoff reward (valueAfter dates) (rootBefore dates) 0 =
      (1 - oneHazard dates) / 2 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [rootBefore, valueAfter, reward, quittingRootPayoff, quittingQuitters,
    Math.Probability.expect_eq_sum]
  ring

theorem rootBefore_quitPayoff_one (dates : ℕ) :
    quittingRootQuitPayoff reward (valueAfter dates) (rootBefore dates) 1 =
      -1 + zeroHazard dates := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [rootBefore, valueAfter, reward, quittingRootPayoff, quittingQuitters,
    Math.Probability.expect_eq_sum]
  ring

theorem rootBefore_continuePayoff_two (dates : ℕ) :
    quittingRootContinuePayoff reward (valueAfter dates) (rootBefore dates) 2 =
      0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [rootBefore, valueAfter, reward, quittingRootPayoff, quittingQuitters,
    Math.Probability.expect_eq_sum]

theorem rootBefore_continuePayoff_three (dates : ℕ) :
    quittingRootContinuePayoff reward (valueAfter dates) (rootBefore dates) 3 =
      0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [rootBefore, valueAfter, reward, quittingRootPayoff, quittingQuitters,
    Math.Probability.expect_eq_sum]

/-- Exact backward Bellman update for the displayed roots. -/
theorem valueAfter_succ_eq_successor (dates : ℕ) :
    valueAfter (dates + 1) =
      quittingRootSuccessorPayoff reward (valueAfter dates)
        (rootBefore dates) := by
  funext who
  have hcases : who = 0 ∨ who = 1 ∨ who = 2 ∨ who = 3 := by
    fin_cases who <;> simp
  rcases hcases with rfl | rfl | rfl | rfl
  · rw [quittingRootSuccessorPayoff_eq_max_of_isZeroNash reward
      (valueAfter dates) (rootBefore dates) 0 (rootBefore_isZeroNash dates)]
    have hdiff := rootBefore_endpointDifference_zero dates
    unfold quittingRootEndpointDifference at hdiff
    rw [show quittingRootContinuePayoff reward (valueAfter dates)
        (rootBefore dates) 0 =
          quittingRootQuitPayoff reward (valueAfter dates)
            (rootBefore dates) 0 by linarith]
    rw [max_self, rootBefore_quitPayoff_zero]
    simp only [valueAfter, if_pos]
    rw [oneHazard_eq_indifference, zeroValue_succ]
    have hden : 0 < 3 / 2 - zeroValue dates := by
      have := zeroValue_lt_half dates
      linarith
    have hden' : 0 < 3 - 2 * zeroValue dates := by linarith
    field_simp [ne_of_gt hden, ne_of_gt hden']
    ring
  · rw [quittingRootSuccessorPayoff_eq_max_of_isZeroNash reward
      (valueAfter dates) (rootBefore dates) 1 (rootBefore_isZeroNash dates)]
    have hdiff := rootBefore_endpointDifference_one dates
    unfold quittingRootEndpointDifference at hdiff
    rw [show quittingRootContinuePayoff reward (valueAfter dates)
        (rootBefore dates) 1 =
          quittingRootQuitPayoff reward (valueAfter dates)
            (rootBefore dates) 1 by linarith]
    rw [max_self, rootBefore_quitPayoff_one]
    simp [valueAfter]
    rw [zeroHazard_eq_indifference, oneValue_succ]
    have hden : 0 < 2 + oneValue dates := by
      have := oneValue_gt_neg_one dates
      linarith
    field_simp [ne_of_gt hden]
    ring
  · rw [quittingRootSuccessorPayoff_eq_max_of_isZeroNash reward
      (valueAfter dates) (rootBefore dates) 2 (rootBefore_isZeroNash dates),
      rootBefore_continuePayoff_two]
    have hdiff := rootBefore_endpointDifference_two dates
    unfold quittingRootEndpointDifference at hdiff
    rw [rootBefore_continuePayoff_two] at hdiff
    rw [show quittingRootQuitPayoff reward (valueAfter dates)
        (rootBefore dates) 2 = -1 by linarith]
    simp [valueAfter]
  · rw [quittingRootSuccessorPayoff_eq_max_of_isZeroNash reward
      (valueAfter dates) (rootBefore dates) 3 (rootBefore_isZeroNash dates),
      rootBefore_continuePayoff_three]
    have hdiff := rootBefore_endpointDifference_three dates
    unfold quittingRootEndpointDifference at hdiff
    rw [rootBefore_continuePayoff_three] at hdiff
    rw [show quittingRootQuitPayoff reward (valueAfter dates)
        (rootBefore dates) 3 = -1 by linarith]
    simp [valueAfter]

/-! ## The explicit finite hard-tail chain -/

/-- Chronological roots for a fixed positive hard deadline. -/
def hardDeadlineRoots (deadline time : ℕ) : Player → PMF Bool :=
  if time < deadline then rootBefore (deadline - time - 1)
  else quittingAllContinueRoot

/-- Backward value attached to each chronological date. -/
def hardDeadlineValue (deadline time : ℕ) : Payoff Player :=
  if time ≤ deadline then valueAfter (deadline - time) else 0

@[simp] theorem valueAfter_zero : valueAfter 0 = 0 := by
  funext who
  have hcases : who = 0 ∨ who = 1 ∨ who = 2 ∨ who = 3 := by
    fin_cases who <;> simp
  rcases hcases with rfl | rfl | rfl | rfl <;>
    simp [valueAfter]

theorem hardDeadlineRoots_eq_allContinue_of_le
    (deadline time : ℕ) (htime : deadline ≤ time) :
    hardDeadlineRoots deadline time = quittingAllContinueRoot := by
  simp [hardDeadlineRoots, Nat.not_lt.mpr htime]

@[simp] theorem hardDeadlineValue_at_deadline (deadline : ℕ) :
    hardDeadlineValue deadline deadline = 0 := by
  simp [hardDeadlineValue]

theorem hardDeadlineValue_policy (deadline time : ℕ)
    (htime : time < deadline) :
    hardDeadlineValue deadline time =
      quittingRootSuccessorPayoff reward
        (hardDeadlineValue deadline (time + 1))
        (hardDeadlineRoots deadline time) := by
  have hnext : time + 1 ≤ deadline := by omega
  have hsub : deadline - time = (deadline - time - 1) + 1 := by omega
  have hnextSub : deadline - (time + 1) = deadline - time - 1 := by omega
  simp only [hardDeadlineValue, if_pos htime.le, if_pos hnext,
    hardDeadlineRoots, if_pos htime]
  rw [hsub, hnextSub]
  exact valueAfter_succ_eq_successor (deadline - time - 1)

theorem hardDeadlineRoots_isZeroNash (deadline time : ℕ)
    (htime : time < deadline) :
    IsεQuittingRootNash reward (hardDeadlineValue deadline (time + 1)) 0
      (hardDeadlineRoots deadline time) := by
  have hnext : time + 1 ≤ deadline := by omega
  have hnextSub : deadline - (time + 1) = deadline - time - 1 := by omega
  simp only [hardDeadlineValue, if_pos hnext, hardDeadlineRoots, if_pos htime]
  rw [hnextSub]
  exact rootBefore_isZeroNash (deadline - time - 1)

/-- The literal behavioral realization of the explicit finite chain. -/
def hardDeadlineProfile (deadline : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingInfinitePathProfile reward (hardDeadlineRoots deadline)

theorem hardDeadlineProfile_payoff (deadline : ℕ) :
    quittingTerminalPayoff reward (hardDeadlineProfile deadline) =
      valueAfter deadline := by
  have hpayoff := quittingTerminalPayoff_finiteExactChainProfile
    reward (hardDeadlineRoots deadline) (hardDeadlineValue deadline) deadline
      (hardDeadlineRoots_eq_allContinue_of_le deadline)
      (hardDeadlineValue_at_deadline deadline)
      (hardDeadlineValue_policy deadline)
  simpa [hardDeadlineProfile, hardDeadlineValue] using hpayoff

private theorem finiteExactNash_some_le_value
    {roots : ℕ → Player → PMF Bool} {value : ℕ → Payoff Player}
    {cutoff : ℕ}
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hnash : ∀ time, time < cutoff →
      IsεQuittingRootNash reward (value (time + 1)) 0 (roots time))
    (who : Player) (start fuel : ℕ) (hstop : start + fuel < cutoff) :
    quittingRootSequencePureTimeTerminalValue reward roots who
        (some (start + fuel)) start ≤ value start who := by
  induction fuel generalizing start with
  | zero =>
      rw [Nat.add_zero,
        quittingRootSequencePureTimeTerminalValue_some_self]
      have hquit := quittingRootQuitPayoff_le_successor_of_isZeroNash
        reward (value (start + 1)) (roots start) who
          (hnash start (by simpa using hstop))
      rw [quittingRootQuitPayoff_eq_fixedOpponentsQuitValue,
        ← congrFun (hpolicy start (by simpa using hstop)) who] at hquit
      exact hquit
  | succ fuel ih =>
      have hne : start ≠ start + (fuel + 1) := by omega
      unfold quittingRootSequencePureTimeTerminalValue
      rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman,
        quittingPureTimeHazard_some_of_ne hne]
      simp only [PMF.pure_apply, if_neg (by decide : (true : Bool) ≠ false),
        ENNReal.toReal_zero, if_true, ENNReal.toReal_one, zero_mul, one_mul]
      have htail := ih (start + 1) (by omega)
      have hidx : start + (fuel + 1) = start + 1 + fuel := by omega
      have htail' : quittingRootSequenceHazardTerminalValue reward roots who
          (quittingPureTimeHazard (some (start + (fuel + 1)))) (start + 1) ≤
          value (start + 1) who := by
        simpa only [quittingRootSequencePureTimeTerminalValue, hidx] using htail
      have hmass : 0 ≤ quittingFixedOpponentsContinueMass roots who start :=
        quittingStationaryContinueMass_nonneg
          (Function.update (roots start) who (PMF.pure false))
      have hcontinue := quittingRootContinuePayoff_le_successor_of_isZeroNash
        reward (value (start + 1)) (roots start) who
          (hnash start (by omega))
      rw [quittingRootContinuePayoff_eq_fixedOpponents,
        ← congrFun (hpolicy start (by omega)) who] at hcontinue
      have hscaled := mul_le_mul_of_nonneg_left htail' hmass
      linarith

private theorem finiteExactNash_none_le_value
    {roots : ℕ → Player → PMF Bool} {value : ℕ → Payoff Player}
    {cutoff : ℕ}
    (htail : ∀ time, cutoff ≤ time →
      roots time = (quittingAllContinueRoot : Player → PMF Bool))
    (hterminal : value cutoff = 0)
    (hpolicy : ∀ time, time < cutoff →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hnash : ∀ time, time < cutoff →
      IsεQuittingRootNash reward (value (time + 1)) 0 (roots time))
    (who : Player) (start : ℕ) (hstart : start ≤ cutoff) :
    quittingRootSequencePureTimeTerminalValue reward roots who none start ≤
      value start who := by
  exact Nat.decreasingInduction (n := cutoff) (motive := fun time _ ↦
      quittingRootSequencePureTimeTerminalValue reward roots who none time ≤
        value time who)
    (fun liveTime hlive ih ↦ by
      rw [quittingRootSequencePureTimeTerminalValue_none_succ_eq_fixedOpponents]
      have hmass : 0 ≤
          quittingFixedOpponentsContinueMass roots who liveTime :=
        quittingStationaryContinueMass_nonneg
          (Function.update (roots liveTime) who (PMF.pure false))
      have hcontinue := quittingRootContinuePayoff_le_successor_of_isZeroNash
        reward (value (liveTime + 1)) (roots liveTime) who
          (hnash liveTime hlive)
      rw [quittingRootContinuePayoff_eq_fixedOpponents,
        ← congrFun (hpolicy liveTime hlive) who] at hcontinue
      have hscaled := mul_le_mul_of_nonneg_left ih hmass
      linarith)
    (by
      rw [quittingRootSequencePureTimeTerminalValue_none_eq_zero_of_allContinue_from
        reward roots who cutoff htail, congrFun hterminal who]
      simp)
    hstart

/-- The explicit chain is a Nash profile of the declared finite timing menu. -/
theorem hardDeadlineProfile_isFiniteDeadline (deadline : ℕ) :
    QuittingFiniteDeadlineNashProfile reward
      (hardDeadlineProfile deadline) deadline := by
  constructor
  · intro time htime
    simp only [hardDeadlineProfile,
      quittingProfileLiveRoot_infinitePathProfile]
    exact hardDeadlineRoots_eq_allContinue_of_le deadline time htime
  · intro who quitTime hmenu
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
      hardDeadlineProfile, quittingProfileLiveRoot_infinitePathProfile]
    have hprofilePayoff := congrFun (hardDeadlineProfile_payoff deadline) who
    rw [hardDeadlineProfile] at hprofilePayoff
    rw [quittingTerminalPayoff_infinitePathProfile] at hprofilePayoff
    rw [quittingTerminalPayoff_infinitePathProfile]
    rw [hprofilePayoff]
    rcases hmenu with rfl | ⟨time, htime, rfl⟩
    · exact finiteExactNash_none_le_value
        (hardDeadlineRoots_eq_allContinue_of_le deadline)
        (hardDeadlineValue_at_deadline deadline)
        (hardDeadlineValue_policy deadline)
        (hardDeadlineRoots_isZeroNash deadline) who 0 (Nat.zero_le deadline)
    · simpa [hardDeadlineValue] using finiteExactNash_some_le_value
        (hardDeadlineValue_policy deadline)
        (hardDeadlineRoots_isZeroNash deadline) who 0 time (by simpa using htime)

/-! ## Exact opponent survival and unrestricted debt -/

/-- Active player `1`'s Never mass in the displayed `dates`-date profile. -/
def oneNeverMass (dates : ℕ) : ℝ :=
  (2 : ℝ) ^ dates / ((2 : ℝ) ^ (dates + 1) - 1)

@[simp] theorem oneNeverMass_zero : oneNeverMass 0 = 1 := by
  norm_num [oneNeverMass]

theorem oneNeverMass_succ (dates : ℕ) :
    oneNeverMass (dates + 1) =
      (1 - oneHazard dates) * oneNeverMass dates := by
  unfold oneNeverMass oneHazard
  have hpow0 : (0 : ℝ) < 2 ^ dates := by positivity
  have hden : (2 : ℝ) ^ (dates + 1) - 1 ≠ 0 := by
    have : (1 : ℝ) < 2 ^ (dates + 1) :=
      one_lt_pow₀ (by norm_num) (by omega)
    linarith
  have hden' : (2 : ℝ) ^ (dates + 2) - 1 ≠ 0 := by
    have : (1 : ℝ) < 2 ^ (dates + 2) :=
      one_lt_pow₀ (by norm_num) (by omega)
    linarith
  field_simp [hden, hden']
  ring

theorem rootBefore_fixedOpponentsContinueMass_zero (dates : ℕ) :
    quittingStationaryContinueMass
        (Function.update (rootBefore dates) 0 (PMF.pure false)) =
      1 - oneHazard dates := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [rootBefore, Fin.prod_univ_succ]

theorem hardDeadlineRoots_succ_shift (deadline time : ℕ) :
    hardDeadlineRoots (deadline + 1) (time + 1) =
      hardDeadlineRoots deadline time := by
  unfold hardDeadlineRoots
  by_cases htime : time < deadline
  · simp only [if_pos (by omega : time + 1 < deadline + 1), if_pos htime]
    apply congrArg rootBefore
    omega
  · have hle : deadline ≤ time := Nat.le_of_not_gt htime
    simp only [if_neg (by omega : ¬ time + 1 < deadline + 1), if_neg htime]

theorem hardDeadlineOpponentSurvival_zero (deadline : ℕ) :
    quittingOpponentSurvivalWeight (hardDeadlineRoots deadline) 0 0 deadline =
      oneNeverMass deadline := by
  induction deadline with
  | zero => simp [quittingOpponentSurvivalWeight]
  | succ deadline ih =>
      rw [show deadline + 1 = deadline + 1 by rfl,
        quittingOpponentSurvivalWeight_succ_left]
      have hfirst : quittingFixedOpponentsContinueMass
          (hardDeadlineRoots (deadline + 1)) 0 0 = 1 - oneHazard deadline := by
        unfold quittingFixedOpponentsContinueMass
        rw [show hardDeadlineRoots (deadline + 1) 0 = rootBefore deadline by
          simp [hardDeadlineRoots]]
        exact rootBefore_fixedOpponentsContinueMass_zero deadline
      have htail : quittingOpponentSurvivalWeight
          (hardDeadlineRoots (deadline + 1)) 0 1 deadline =
            quittingOpponentSurvivalWeight
              (hardDeadlineRoots deadline) 0 0 deadline := by
        unfold quittingOpponentSurvivalWeight
        apply Finset.prod_congr rfl
        intro offset _hoffset
        simp only [Nat.zero_add]
        unfold quittingFixedOpponentsContinueMass
        rw [show 1 + offset = offset + 1 by omega,
          hardDeadlineRoots_succ_shift]
      rw [hfirst, htail, ih, oneNeverMass_succ]

theorem hardDeadlineEscapeCharge_zero
    (deadline : ℕ) :
    quittingFiniteDeadlineEscapeCharge reward (hardDeadlineProfile deadline)
        deadline 0 = oneNeverMass deadline / 2 := by
  unfold quittingFiniteDeadlineEscapeCharge
    quittingFiniteDeadlineOpponentSurvival hardDeadlineProfile
  rw [quittingProfileLiveRoot_infinitePathProfile,
    hardDeadlineOpponentSurvival_zero]
  simp [reward, quittingSingletonTerminal]
  ring

theorem hardDeadlineRoot_continuePayoff_zero_eq_value
    (deadline time : ℕ) (htime : time < deadline) :
    quittingRootContinuePayoff reward
        (hardDeadlineValue deadline (time + 1))
        (hardDeadlineRoots deadline time) 0 =
      hardDeadlineValue deadline time 0 := by
  have hnext : time + 1 ≤ deadline := by omega
  have hsub : deadline - time = (deadline - time - 1) + 1 := by omega
  have hnextSub : deadline - (time + 1) = deadline - time - 1 := by omega
  simp only [hardDeadlineValue, if_pos hnext, if_pos htime.le,
    hardDeadlineRoots, if_pos htime]
  rw [hnextSub]
  conv_rhs => rw [hsub]
  have hdiff := rootBefore_endpointDifference_zero (deadline - time - 1)
  unfold quittingRootEndpointDifference at hdiff
  rw [valueAfter_succ_eq_successor]
  rw [quittingRootSuccessorPayoff_eq_max_of_isZeroNash reward
    (valueAfter (deadline - time - 1)) (rootBefore (deadline - time - 1)) 0
    (rootBefore_isZeroNash (deadline - time - 1))]
  rw [show quittingRootQuitPayoff reward (valueAfter (deadline - time - 1))
      (rootBefore (deadline - time - 1)) 0 =
        quittingRootContinuePayoff reward (valueAfter (deadline - time - 1))
          (rootBefore (deadline - time - 1)) 0 by linarith, max_self]

theorem hardDeadlineNeverValue_zero (deadline : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward
        (hardDeadlineRoots deadline) 0 none 0 = valueAfter deadline 0 := by
  have hbackward : ∀ time, time ≤ deadline →
      quittingRootSequencePureTimeTerminalValue reward
          (hardDeadlineRoots deadline) 0 none time =
        hardDeadlineValue deadline time 0 := by
    intro time htime
    exact Nat.decreasingInduction (n := deadline) (motive := fun stage _ ↦
        quittingRootSequencePureTimeTerminalValue reward
            (hardDeadlineRoots deadline) 0 none stage =
          hardDeadlineValue deadline stage 0)
      (fun liveTime hlive ih ↦ by
        rw [quittingRootSequencePureTimeTerminalValue_none_succ_eq_fixedOpponents]
        rw [ih]
        rw [← quittingRootContinuePayoff_eq_fixedOpponents]
        exact hardDeadlineRoot_continuePayoff_zero_eq_value
          deadline liveTime hlive)
      (by
        rw [quittingRootSequencePureTimeTerminalValue_none_eq_zero_of_allContinue_from
          reward (hardDeadlineRoots deadline) 0 deadline
          (hardDeadlineRoots_eq_allContinue_of_le deadline)]
        simp)
      htime
  simpa [hardDeadlineValue] using hbackward 0 (Nat.zero_le deadline)

/-- Player `0` has exactly the packet's unrestricted behavioral debt. -/
theorem hardDeadlineProfile_debt_zero_eq (deadline : ℕ) :
    quittingTerminalDeviationDebt reward (hardDeadlineProfile deadline) 0 =
      oneNeverMass deadline / 2 := by
  apply le_antisymm
  · rw [← hardDeadlineEscapeCharge_zero deadline]
    exact (hardDeadlineProfile_isFiniteDeadline deadline).semanticDebt_le_escapeCharge 0
  · let late := quittingPureTimeBehaviorStrategy reward (0 : Player)
      (some deadline)
    have hbest := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward (hardDeadlineProfile deadline) 0 late
    have hlate := quittingRootSequencePureTimeTerminalValue_late_sub_none_eq
      reward (hardDeadlineRoots deadline) 0 deadline deadline le_rfl
      (hardDeadlineRoots_eq_allContinue_of_le deadline)
    rw [hardDeadlineOpponentSurvival_zero] at hlate
    have hlatePayoff := quittingTerminalPayoff_update_pureTimeBehaviorStrategy
      reward (hardDeadlineProfile deadline) 0 (some deadline)
    rw [hardDeadlineProfile, quittingProfileLiveRoot_infinitePathProfile]
      at hlatePayoff
    have hlatePayoff' : quittingTerminalPayoff reward
        (Function.update (hardDeadlineProfile deadline) 0
          (quittingPureTimeBehaviorStrategy reward 0 (some deadline))) 0 =
        quittingRootSequencePureTimeTerminalValue reward
          (hardDeadlineRoots deadline) 0 (some deadline) := by
      exact hlatePayoff
    have hprescribed := congrFun (hardDeadlineProfile_payoff deadline) 0
    have hnever := hardDeadlineNeverValue_zero deadline
    have hsolo : reward (quittingSingletonTerminal (0 : Player)) 0 = 1 / 2 :=
      solo_reward_zero
    dsimp only [late] at hbest
    rw [hlatePayoff'] at hbest
    unfold quittingTerminalDeviationDebt
    rw [hsolo] at hlate
    linarith

theorem oneNeverMass_div_two_eq_hardDeadlineDebt
    (deadline : ℕ) (hdeadline : 0 < deadline) :
    oneNeverMass deadline / 2 = hardDeadlineDebt deadline := by
  unfold oneNeverMass hardDeadlineDebt
  have hpred : deadline - 1 + 1 = deadline := by omega
  have hpow : (2 : ℝ) ^ deadline = 2 * 2 ^ (deadline - 1) := by
    calc
      (2 : ℝ) ^ deadline = 2 ^ (deadline - 1 + 1) := by
        exact congrArg (fun exponent : ℕ ↦ (2 : ℝ) ^ exponent) hpred.symm
      _ = 2 * 2 ^ (deadline - 1) := by
        rw [pow_succ]
        ring
  rw [hpow]
  ring

/-- Exact semantic nonvanishing for every positive hard deadline. -/
theorem hardDeadlineProfile_debt_zero_gt_quarter
    (deadline : ℕ) (hdeadline : 0 < deadline) :
    1 / 4 <
      quittingTerminalDeviationDebt reward (hardDeadlineProfile deadline) 0 := by
  rw [hardDeadlineProfile_debt_zero_eq,
    oneNeverMass_div_two_eq_hardDeadlineDebt deadline hdeadline]
  exact hardDeadlineDebt_gt_quarter deadline hdeadline

theorem hardDeadlineProfile_debt_eq_zero_of_ne_zero
    (deadline : ℕ) (who : Player) (hne : who ≠ 0) :
    quittingTerminalDeviationDebt reward (hardDeadlineProfile deadline) who =
      0 := by
  have hup :=
    (hardDeadlineProfile_isFiniteDeadline deadline).semanticDebt_le_escapeCharge who
  have hlow := quittingTerminalDeviationDebt_nonneg
    reward (hardDeadlineProfile deadline) who
  have hsolo : reward (quittingSingletonTerminal who) who = -1 := by
    have hcases : who = 1 ∨ who = 2 ∨ who = 3 := by
      fin_cases who <;> simp_all
    rcases hcases with rfl | rfl | rfl
    · exact solo_reward_one
    · exact solo_reward_two
    · exact solo_reward_three
  unfold quittingFiniteDeadlineEscapeCharge at hup
  rw [hsolo] at hup
  norm_num at hup
  change quittingTerminalDeviationDebt reward
      (hardDeadlineProfile deadline) who ≤ 0 at hup
  linarith

theorem semanticDebt_hardDeadlineProfile (deadline : ℕ) (who : Player) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (hardDeadlineProfile deadline)) who =
      quittingTerminalDeviationDebt reward (hardDeadlineProfile deadline) who := by
  rfl

/-- The maximum positive semantic debt is exactly the displayed coordinate. -/
theorem hardDeadlineProfile_exploitability_eq (deadline : ℕ) :
    quittingTerminalSemanticExploitability
        (quittingTerminalSemanticPair reward (hardDeadlineProfile deadline)) =
      oneNeverMass deadline / 2 := by
  let debt := oneNeverMass deadline / 2
  have hdebt0 : 0 ≤ debt := by
    dsimp only [debt, oneNeverMass]
    have hden : 0 < (2 : ℝ) ^ (deadline + 1) - 1 := by
      have : (1 : ℝ) < 2 ^ (deadline + 1) :=
        one_lt_pow₀ (by norm_num) (by omega)
      linarith
    positivity
  apply le_antisymm
  · unfold quittingTerminalSemanticExploitability
    apply QuittingBoundaryHolonomy.finitePlayerMax_le
    intro who
    by_cases hwho : who = 0
    · subst who
      rw [semanticDebt_hardDeadlineProfile,
        hardDeadlineProfile_debt_zero_eq, max_eq_right hdebt0]
    · rw [semanticDebt_hardDeadlineProfile,
        hardDeadlineProfile_debt_eq_zero_of_ne_zero deadline who hwho]
      simpa using hdebt0
  · have hmax := QuittingBoundaryHolonomy.le_finitePlayerMax
      (fun who : Player ↦ max 0 (quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (hardDeadlineProfile deadline)) who))
      (0 : Player)
    rw [semanticDebt_hardDeadlineProfile,
      hardDeadlineProfile_debt_zero_eq, max_eq_right hdebt0] at hmax
    exact hmax

/-- For every positive deadline, exact exploitability is the packet's
rational `D_N`. -/
theorem hardDeadlineProfile_exploitability_eq_hardDeadlineDebt
    (deadline : ℕ) (hdeadline : 0 < deadline) :
    quittingTerminalSemanticExploitability
        (quittingTerminalSemanticPair reward (hardDeadlineProfile deadline)) =
      hardDeadlineDebt deadline := by
  rw [hardDeadlineProfile_exploitability_eq,
    oneNeverMass_div_two_eq_hardDeadlineDebt deadline hdeadline]

theorem hardDeadlineDebt_eq_normalizedGeometric
    (deadline : ℕ) (hdeadline : 0 < deadline) :
    hardDeadlineDebt deadline =
      (1 / 4) / (1 - (1 / 2 : ℝ) ^ (deadline + 1)) := by
  have hindex : deadline - 1 + 2 = deadline + 1 := by omega
  have hpow : (2 : ℝ) ^ (deadline + 1) =
      4 * 2 ^ (deadline - 1) := by
    calc
      (2 : ℝ) ^ (deadline + 1) = 2 ^ (deadline - 1 + 2) := by
        exact congrArg (fun exponent : ℕ ↦ (2 : ℝ) ^ exponent)
          hindex.symm
      _ = 4 * 2 ^ (deadline - 1) := by
        rw [pow_add]
        norm_num
        ring
  have hx : (2 : ℝ) ^ (deadline - 1) ≠ 0 := by positivity
  have hden : (2 : ℝ) ^ (deadline + 1) - 1 ≠ 0 := by
    have : (1 : ℝ) < 2 ^ (deadline + 1) :=
      one_lt_pow₀ (by norm_num) (by omega)
    linarith
  unfold hardDeadlineDebt
  rw [one_div_pow, hpow]
  field_simp [hx, hden]

/-- The exact hard-tail exploitability sequence converges to `1/4`. -/
theorem tendsto_hardDeadlineDebt_succ_quarter :
    Filter.Tendsto (fun deadline : ℕ ↦ hardDeadlineDebt (deadline + 1))
      Filter.atTop (nhds (1 / 4 : ℝ)) := by
  have hreformula : (fun deadline : ℕ ↦ hardDeadlineDebt (deadline + 1)) =
      fun deadline : ℕ ↦
        (1 / 4) / (1 - (1 / 2 : ℝ) ^ (deadline + 2)) := by
    funext deadline
    rw [hardDeadlineDebt_eq_normalizedGeometric (deadline + 1) (by omega)]
  rw [hreformula]
  have hpow : Filter.Tendsto (fun deadline : ℕ ↦
      (1 / 2 : ℝ) ^ (deadline + 2)) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (Filter.tendsto_add_atTop_nat 2)
  have hden : Filter.Tendsto (fun deadline : ℕ ↦
      1 - (1 / 2 : ℝ) ^ (deadline + 2)) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hpow
  have hconst : Filter.Tendsto (fun _deadline : ℕ ↦ (1 / 4 : ℝ))
      Filter.atTop (nhds (1 / 4 : ℝ)) := tendsto_const_nhds
  have hlimit := hconst.div hden (by norm_num : (1 : ℝ) ≠ 0)
  convert hlimit using 1
  · rfl
  · norm_num

/-- Consequently the semantic exploitability of the explicit Nash family
converges to `1/4`. -/
theorem tendsto_hardDeadlineProfile_exploitability_quarter :
    Filter.Tendsto (fun deadline : ℕ ↦
      quittingTerminalSemanticExploitability
        (quittingTerminalSemanticPair reward
          (hardDeadlineProfile (deadline + 1))))
      Filter.atTop (nhds (1 / 4 : ℝ)) := by
  apply tendsto_hardDeadlineDebt_succ_quarter.congr'
  filter_upwards [] with deadline
  exact (hardDeadlineProfile_exploitability_eq_hardDeadlineDebt
    (deadline + 1) (by omega)).symm

/-! ## A vanishing-error comparison family -/

/-- The hazard which realizes a uniform stopping date among the first
`length` dates. -/
def uniformFiniteHazard (length time : ℕ) : ℝ :=
  if time < length then 1 / ((length - time : ℕ) : ℝ) else 0

theorem uniformFiniteHazard_nonneg (length time : ℕ) :
    0 ≤ uniformFiniteHazard length time := by
  unfold uniformFiniteHazard
  split_ifs
  · positivity
  · exact le_rfl

theorem uniformFiniteHazard_le_one (length time : ℕ) :
    uniformFiniteHazard length time ≤ 1 := by
  unfold uniformFiniteHazard
  split_ifs with htime
  · have hpos : 0 < length - time := by omega
    rw [div_le_one (by positivity : (0 : ℝ) < (length - time : ℕ))]
    exact_mod_cast hpos
  · norm_num

/-- A solo tail in which player `0` stops uniformly on dates
`0, ..., length - 1`. -/
def uniformSoloTailRoots (length : ℕ) : ℕ → Player → PMF Bool :=
  fun time who ↦
    if who = 0 then
      bernoulliBool (uniformFiniteHazard length time)
        (uniformFiniteHazard_nonneg length time)
        (uniformFiniteHazard_le_one length time)
    else PMF.pure false

@[simp] theorem uniformSoloTailRoots_zero_true_toReal
    (length time : ℕ) :
    (uniformSoloTailRoots length time 0 true).toReal =
      uniformFiniteHazard length time := by
  simp [uniformSoloTailRoots]

@[simp] theorem uniformSoloTailRoots_zero_false_toReal
    (length time : ℕ) :
    (uniformSoloTailRoots length time 0 false).toReal =
      1 - uniformFiniteHazard length time := by
  simp [uniformSoloTailRoots]

theorem uniformSoloTailRoots_solo (length time : ℕ) :
    ∀ who, who ≠ (0 : Player) →
      uniformSoloTailRoots length time who = PMF.pure false := by
  intro who hwho
  simp [uniformSoloTailRoots, hwho]

theorem uniformSoloTailRoots_opponentSurvival_one
    (length phase : ℕ) (hlength : 0 < length) (hphase : phase ≤ length) :
    quittingOpponentSurvivalWeight (uniformSoloTailRoots length) 1 0 phase =
      ((length - phase : ℕ) : ℝ) / length := by
  induction phase with
  | zero =>
      simp [quittingOpponentSurvivalWeight,
        show (length : ℝ) ≠ 0 by exact_mod_cast ne_of_gt hlength]
  | succ phase ih =>
      have hphaseLt : phase < length := by omega
      have hsubPos : 0 < length - phase := by omega
      have hcastSub : ((length - phase : ℕ) : ℝ) =
          (length : ℝ) - phase := by
        exact_mod_cast Nat.cast_sub hphaseLt.le
      have hsubSucc : length - (phase + 1) = length - phase - 1 := by omega
      have hsubCastPos : (0 : ℝ) < (length - phase : ℕ) := by
        exact_mod_cast hsubPos
      have hdenNe : (length : ℝ) - phase ≠ 0 := by
        rw [← hcastSub]
        exact ne_of_gt hsubCastPos
      rw [show phase + 1 = phase.succ by rfl,
        quittingOpponentSurvivalWeight_succ]
      simp only [Nat.zero_add]
      rw [ih hphaseLt.le]
      rw [quittingFixedOpponentsContinueMass_eq_of_soloRoot
        (uniformSoloTailRoots length)
        (uniformSoloTailRoots_solo length phase) (by norm_num : (1 : Player) ≠ 0)]
      rw [uniformSoloTailRoots_zero_false_toReal]
      simp only [uniformFiniteHazard, if_pos hphaseLt]
      rw [hsubSucc, Nat.cast_sub (by omega : 1 ≤ length - phase), Nat.cast_one,
        hcastSub]
      field_simp [show (length : ℝ) ≠ 0 by exact_mod_cast ne_of_gt hlength,
        hdenNe]

theorem uniformSoloTailRoots_opponentSurvival_one_eq_zero_of_le
    (length phase : ℕ) (hlength : 0 < length) (hphase : length ≤ phase) :
    quittingOpponentSurvivalWeight (uniformSoloTailRoots length) 1 0 phase = 0 := by
  have hsum : length + (phase - length) = phase := by omega
  rw [← hsum, quittingOpponentSurvivalWeight_add,
    uniformSoloTailRoots_opponentSurvival_one length length hlength le_rfl]
  simp

theorem uniformSoloTailRoots_jointSurvivalLimit_eq_zero
    (length : ℕ) (hlength : 0 < length) :
    quittingJointSurvivalLimit (uniformSoloTailRoots length) 0 = 0 := by
  have hopponent : quittingOpponentSurvivalWeight
      (uniformSoloTailRoots length) 1 0 length = 0 :=
    uniformSoloTailRoots_opponentSurvival_one_eq_zero_of_le
      length length hlength le_rfl
  have hjoint : quittingJointSurvivalWeight
      (uniformSoloTailRoots length) 0 length ≤ 0 := by
    simpa [hopponent] using
      (quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight
        (uniformSoloTailRoots length) 1 0 length)
  apply le_antisymm
  · have hlimit : quittingJointSurvivalLimit
        (uniformSoloTailRoots length) 0 ≤
          quittingJointSurvivalWeight (uniformSoloTailRoots length) 0 length := by
      unfold quittingJointSurvivalLimit
      apply ciInf_le
      refine ⟨0, ?_⟩
      rintro _ ⟨fuel, rfl⟩
      exact quittingJointSurvivalWeight_nonneg
        (uniformSoloTailRoots length) 0 fuel
    exact hlimit.trans hjoint
  · exact quittingJointSurvivalLimit_nonneg (uniformSoloTailRoots length) 0

/-- The executable solo tail whose owner stops uniformly on its first
`length` dates. -/
def uniformSoloTailProfile (length : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootSequenceProfile reward (uniformSoloTailRoots length) 0

@[simp] theorem uniformSoloTailProfile_liveRoot (length time : ℕ) :
    quittingProfileLiveRoot reward (uniformSoloTailProfile length) time =
      uniformSoloTailRoots length time := by
  simp [uniformSoloTailProfile]

theorem uniformSoloTailProfile_liveRoots (length : ℕ) :
    quittingProfileLiveRoot reward (uniformSoloTailProfile length) =
      uniformSoloTailRoots length := by
  funext time
  exact uniformSoloTailProfile_liveRoot length time

theorem uniformSoloTailProfile_payoff
    (length : ℕ) (hlength : 0 < length) (who : Player) :
    quittingTerminalPayoff reward (uniformSoloTailProfile length) who =
      quittingSoloReward reward 0 who := by
  exact quittingRootSequenceTerminalValue_eq_soloReward_of_absorbing
    reward (uniformSoloTailRoots length) 0 0
    (fun time ↦ uniformSoloTailRoots_solo length time)
    (by
      rw [quittingLiveMassLimit_rootSequence_eq_jointSurvivalLimit]
      exact uniformSoloTailRoots_jointSurvivalLimit_eq_zero length hlength)
    who

theorem uniformSoloTailPureTimeValue_one_eq
    (length phase : ℕ) (hlength : 0 < length) (hphase : phase < length) :
    quittingRootSequencePureTimeTerminalValue reward
        (uniformSoloTailRoots length) 1 (some phase) 0 =
      -1 + 1 / length := by
  rw [show phase = 0 + phase by omega,
    quittingRootSequencePureTimeTerminalValue_some_eq_of_soloRoots
      reward (uniformSoloTailRoots length) (by norm_num : (1 : Player) ≠ 0)
      (fun time ↦ uniformSoloTailRoots_solo length time) 0 phase]
  simp only [Nat.zero_add]
  rw [uniformSoloTailRoots_opponentSurvival_one length phase hlength hphase.le,
    uniformSoloTailRoots_zero_false_toReal,
    uniformSoloTailRoots_zero_true_toReal]
  simp only [uniformFiniteHazard, if_pos hphase]
  simp [quittingSoloReward, quittingSingletonCollisionReward, reward]
  have hlengthNe : (length : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hlength
  have hsubPos : 0 < length - phase := by omega
  have hsubNe : ((length - phase : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hsubPos
  field_simp [hlengthNe, hsubNe]
  ring

theorem uniformSoloTailPureTimeValue_one_eq_neg_one_of_le
    (length phase : ℕ) (hlength : 0 < length) (hphase : length ≤ phase) :
    quittingRootSequencePureTimeTerminalValue reward
        (uniformSoloTailRoots length) 1 (some phase) 0 = -1 := by
  rw [show phase = 0 + phase by omega,
    quittingRootSequencePureTimeTerminalValue_some_eq_of_soloRoots
      reward (uniformSoloTailRoots length) (by norm_num : (1 : Player) ≠ 0)
      (fun time ↦ uniformSoloTailRoots_solo length time) 0 phase]
  simp only [Nat.zero_add]
  rw [uniformSoloTailRoots_opponentSurvival_one_eq_zero_of_le
    length phase hlength hphase]
  simp [quittingSoloReward, reward]

theorem uniformSoloTailPureTimeValue_one_none
    (length : ℕ) (hlength : 0 < length) :
    quittingRootSequencePureTimeTerminalValue reward
        (uniformSoloTailRoots length) 1 none 0 = -1 := by
  have hupdate : quittingRootSequenceUpdate
      (uniformSoloTailRoots length) 1 (fun _ ↦ PMF.pure false) =
        uniformSoloTailRoots length := by
    funext time who
    by_cases hwho : who = (1 : Player)
    · subst who
      simp [quittingRootSequenceUpdate, uniformSoloTailRoots]
    · simp [quittingRootSequenceUpdate, Function.update_of_ne hwho]
  unfold quittingRootSequencePureTimeTerminalValue
    quittingRootSequenceHazardTerminalValue
  rw [show quittingPureTimeHazard none = fun _ ↦ PMF.pure false by rfl,
    hupdate]
  exact (uniformSoloTailProfile_payoff length hlength 1).trans (by
    simp [quittingSoloReward, reward])

/-- Player `1`'s unrestricted behavioral cap against the uniform solo tail
is exactly one tie atom above `-1`. -/
theorem uniformSoloTailProfile_bestResponse_one
    (length : ℕ) (hlength : 0 < length) :
    quittingContinuationBestResponseValue reward
        (uniformSoloTailProfile length) 1 =
      -1 + 1 / length := by
  unfold quittingContinuationBestResponseValue
  rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime]
  apply le_antisymm
  · apply csSup_le
    · exact Set.range_nonempty _
    · rintro value ⟨choice, rfl⟩
      dsimp only
      rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
      rw [uniformSoloTailProfile_liveRoots]
      change quittingRootSequencePureTimeTerminalValue reward
        (uniformSoloTailRoots length) 1 choice 0 ≤ -1 + 1 / length
      cases choice with
      | none =>
          rw [uniformSoloTailPureTimeValue_one_none length hlength]
          have : (0 : ℝ) ≤ 1 / length := by positivity
          linarith
      | some phase =>
          by_cases hphase : phase < length
          · rw [uniformSoloTailPureTimeValue_one_eq length phase hlength hphase]
          · rw [uniformSoloTailPureTimeValue_one_eq_neg_one_of_le
              length phase hlength (Nat.le_of_not_gt hphase)]
            have : (0 : ℝ) ≤ 1 / length := by positivity
            linarith
  · apply le_csSup
    · refine ⟨quittingRewardBound reward, ?_⟩
      rintro value ⟨choice, rfl⟩
      exact (le_abs_self _).trans
        (abs_quittingTerminalPayoff_le_quittingRewardBound reward _ 1)
    · refine ⟨some 0, ?_⟩
      dsimp only
      rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
      rw [uniformSoloTailProfile_liveRoots]
      exact uniformSoloTailPureTimeValue_one_eq length 0 hlength hlength

/-- The comparison prefix: player `1` Quits surely and everyone else
Continues. -/
def comparisonRoot : Player → PMF Bool := fun who ↦
  if who = 1 then PMF.pure true else PMF.pure false

/-- The fixed payoff delivered by every comparison profile. -/
def comparisonTarget : Payoff Player := fun who ↦
  if who = 0 then 1 else if who = 1 then -1 else 0

/-- Player `1` Quits at date zero; after refusal, player `0` uses the uniform
solo tail. -/
def comparisonProfile (length : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward comparisonRoot
    (uniformSoloTailProfile length)

/-- Every comparison profile delivers the same terminal payoff vector. -/
theorem comparisonProfile_payoff (length : ℕ) :
    quittingTerminalPayoff reward (comparisonProfile length) =
      comparisonTarget := by
  funext who
  rw [comparisonProfile, quittingTerminalPayoff_rootThenContinuation_eq]
  unfold quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  fin_cases who <;>
    simp [comparisonRoot, comparisonTarget, reward, quittingRootPayoff,
      quittingQuitters, Math.Probability.expect_eq_sum]

theorem comparisonRoot_quitPayoff_zero (tail : Payoff Player) :
    quittingRootQuitPayoff reward tail comparisonRoot 0 = 0 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [comparisonRoot, reward, quittingRootPayoff, quittingQuitters,
    Math.Probability.expect_eq_sum]

theorem comparisonRoot_quitPayoff_one (tail : Payoff Player) :
    quittingRootQuitPayoff reward tail comparisonRoot 1 = -1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [comparisonRoot, reward, quittingRootPayoff, quittingQuitters,
    Math.Probability.expect_eq_sum]

theorem comparisonRoot_quitPayoff_two (tail : Payoff Player) :
    quittingRootQuitPayoff reward tail comparisonRoot 2 = -1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [comparisonRoot, reward, quittingRootPayoff, quittingQuitters,
    Math.Probability.expect_eq_sum]

theorem comparisonRoot_quitPayoff_three (tail : Payoff Player) :
    quittingRootQuitPayoff reward tail comparisonRoot 3 = -1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [comparisonRoot, reward, quittingRootPayoff, quittingQuitters,
    Math.Probability.expect_eq_sum]

theorem comparisonRoot_continuePayoff_zero (tail : Payoff Player) :
    quittingRootContinuePayoff reward tail comparisonRoot 0 = 1 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [comparisonRoot, reward, quittingRootPayoff, quittingQuitters,
    Math.Probability.expect_eq_sum]

theorem comparisonRoot_continuePayoff_one (tail : Payoff Player) :
    quittingRootContinuePayoff reward tail comparisonRoot 1 = tail 1 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [comparisonRoot, reward, quittingRootPayoff, quittingQuitters,
    Math.Probability.expect_eq_sum]

theorem comparisonRoot_continuePayoff_two (tail : Payoff Player) :
    quittingRootContinuePayoff reward tail comparisonRoot 2 = 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [comparisonRoot, reward, quittingRootPayoff, quittingQuitters,
    Math.Probability.expect_eq_sum]

theorem comparisonRoot_continuePayoff_three (tail : Payoff Player) :
    quittingRootContinuePayoff reward tail comparisonRoot 3 = 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [comparisonRoot, reward, quittingRootPayoff, quittingQuitters,
    Math.Probability.expect_eq_sum]

/-- Exact all-behavior cap of the comparison profile. Only player `1` can
gain, by refusing the prefix and choosing one atom of the uniform tail. -/
theorem comparisonProfile_bestResponse
    (length : ℕ) (hlength : 0 < length) (who : Player) :
    quittingContinuationBestResponseValue reward (comparisonProfile length) who =
      if who = 1 then -1 + (1 : ℝ) / length else comparisonTarget who := by
  rw [comparisonProfile,
    quittingContinuationBestResponseValue_rootThenContinuation_eq_max]
  have hcases : who = 0 ∨ who = 1 ∨ who = 2 ∨ who = 3 := by
    fin_cases who <;> simp
  rcases hcases with rfl | rfl | rfl | rfl
  · rw [comparisonRoot_quitPayoff_zero,
      comparisonRoot_continuePayoff_zero]
    norm_num [comparisonTarget]
  · rw [comparisonRoot_quitPayoff_one,
      comparisonRoot_continuePayoff_one]
    simp only [Function.update_self,
      uniformSoloTailProfile_bestResponse_one length hlength,
      if_pos]
    have herror : (0 : ℝ) ≤ 1 / length := by positivity
    rw [max_eq_right]
    linarith
  · rw [comparisonRoot_quitPayoff_two,
      comparisonRoot_continuePayoff_two]
    simp [comparisonTarget]
  · rw [comparisonRoot_quitPayoff_three,
      comparisonRoot_continuePayoff_three]
    simp [comparisonTarget]

/-- Coordinatewise terminal debt of the comparison profile. -/
theorem comparisonProfile_debt
    (length : ℕ) (hlength : 0 < length) (who : Player) :
    quittingTerminalDeviationDebt reward (comparisonProfile length) who =
      if who = 1 then (1 : ℝ) / length else 0 := by
  unfold quittingTerminalDeviationDebt
  rw [comparisonProfile_bestResponse length hlength who,
    congrFun (comparisonProfile_payoff length) who]
  have hcases : who = 0 ∨ who = 1 ∨ who = 2 ∨ who = 3 := by
    fin_cases who <;> simp
  rcases hcases with rfl | rfl | rfl | rfl <;>
    simp [comparisonTarget]

/-- The comparison family has exact unrestricted semantic exploitability
`1 / length`. -/
theorem comparisonProfile_exploitability
    (length : ℕ) (hlength : 0 < length) :
    quittingTerminalSemanticExploitability
        (quittingTerminalSemanticPair reward (comparisonProfile length)) =
      (1 : ℝ) / length := by
  have herror : (0 : ℝ) ≤ 1 / length := by positivity
  apply le_antisymm
  · unfold quittingTerminalSemanticExploitability
    apply QuittingBoundaryHolonomy.finitePlayerMax_le
    intro who
    change max 0
      (quittingTerminalDeviationDebt reward (comparisonProfile length) who) ≤
        (1 : ℝ) / length
    rw [comparisonProfile_debt length hlength who]
    by_cases hwho : who = 1
    · rw [if_pos hwho, max_eq_right herror]
    · rw [if_neg hwho]
      simpa only [max_self] using herror
  · have hmax := QuittingBoundaryHolonomy.le_finitePlayerMax
      (fun who : Player ↦ max 0 (quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (comparisonProfile length)) who))
      (1 : Player)
    change (1 : ℝ) / length ≤
      quittingTerminalSemanticExploitability
        (quittingTerminalSemanticPair reward (comparisonProfile length))
    rw [show quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (comparisonProfile length)) 1 =
          quittingTerminalDeviationDebt reward (comparisonProfile length) 1 by rfl,
      comparisonProfile_debt length hlength 1, if_pos rfl,
      max_eq_right herror] at hmax
    exact hmax

/-- The true executable terminal exploitability infimum of the concrete
table is zero, despite the hard-deadline Nash barrier. -/
theorem terminalExploitabilityInf_eq_zero :
    quittingTerminalExploitabilityInf reward = 0 := by
  apply le_antisymm
  · have hbound : ∀ index : ℕ,
        quittingTerminalExploitabilityInf reward ≤
          (1 : ℝ) / (index + 1) := by
      intro index
      have hinf := quittingTerminalExploitabilityInf_le
        reward (comparisonProfile (index + 1))
      rw [← quittingTerminalSemanticExploitability_pair] at hinf
      rw [comparisonProfile_exploitability (index + 1) (by omega)] at hinf
      simpa only [Nat.cast_add, Nat.cast_one] using hinf
    have hlimit : Filter.Tendsto (fun index : ℕ ↦
        (1 : ℝ) / (index + 1)) Filter.atTop (nhds 0) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact ge_of_tendsto' hlimit hbound
  · unfold quittingTerminalExploitabilityInf
    have hprofiles : Set.Nonempty
        (Set.range fun profile : (quittingGame reward).BehaviorProfile ↦
          quittingTerminalExploitability reward profile) :=
      ⟨_, comparisonProfile 1, rfl⟩
    apply le_csInf hprofiles
    rintro value ⟨profile, rfl⟩
    exact quittingTerminalExploitability_nonneg reward profile

/-- Every comparison profile is a terminal `1 / length`-Nash profile against
all behavioral deviations. -/
theorem comparisonProfile_isTerminalNash
    (length : ℕ) (hlength : 0 < length) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ((1 : ℝ) / length)
      (comparisonProfile length) := by
  intro who deviation
  have hbest := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward (comparisonProfile length) who deviation
  have hdebt := comparisonProfile_debt length hlength who
  unfold quittingTerminalDeviationDebt at hdebt
  by_cases hwho : who = 1
  · rw [if_pos hwho] at hdebt
    linarith
  · rw [if_neg hwho] at hdebt
    have herror : (0 : ℝ) ≤ 1 / length := by positivity
    linarith

/-- The fixed vector `(1, -1, 0, 0)` is a uniform-equilibrium payoff of the
same table whose hard-deadline Nash family has a nonvanishing `1/4` debt
barrier. -/
theorem comparisonTarget_isUniformEquilibriumPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none comparisonTarget := by
  let error : ℕ → ℝ := fun index ↦ 1 / ((index : ℝ) + 1)
  let profiles : ℕ → (quittingGame reward).BehaviorProfile :=
    fun index ↦ comparisonProfile (index + 1)
  have herror : Filter.Tendsto error Filter.atTop (nhds 0) := by
    simpa [error] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hnash : ∀ index,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (error index) (profiles index) := by
    intro index
    simpa [error, profiles, Nat.cast_add, Nat.cast_one] using
      comparisonProfile_isTerminalNash (index + 1) (by omega)
  have htarget : Filter.Tendsto
      (fun index ↦ quittingTerminalPayoff reward (profiles index))
      Filter.atTop (nhds comparisonTarget) := by
    simp only [profiles, comparisonProfile_payoff]
    exact tendsto_const_nhds
  exact quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto
    reward comparisonTarget error profiles herror
      (Filter.Frequently.of_forall hnash) htarget

end FinFourHardDeadlineTimingNashBarrier
end GameTheory
