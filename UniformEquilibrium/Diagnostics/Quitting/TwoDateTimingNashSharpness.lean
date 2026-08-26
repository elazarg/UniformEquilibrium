/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.FiniteFubini
import UniformEquilibrium.Diagnostics.Quitting.TwoDateTimingNashDebt

/-!
# Sharpness of the two-date timing-Nash debt bound

This module gives the exact normalized rational four-player regression for the
universal two-date timing-Nash theorem.  Its finite timing game has one unique
mixed Nash profile: both active players use planned-time masses
`(1 / 4, 1 / 4, 1 / 2)` on date zero, date one, and Never, while both dummy
players choose Never.  The literal stopping-law realization has unrestricted
behavioral terminal debt exactly `1 / 2` for player zero.

The active reward coordinates are zero on dummy-only coalitions.  Thus this
table is not definitionally the later fixed-prefix table, whose active rewards
on such coalitions are `(1, -1)`.  No literal same-table identification with
that regression is claimed here.
-/

noncomputable section

namespace GameTheory
namespace TwoDateTimingNashSharpness

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

abbrev Player := Fin 4
abbrev Action := QuittingTwoDateTimingAction

def now : Action := some ⟨0, by omega⟩
def next : Action := some ⟨1, by omega⟩
def never : Action := none

def reward (terminal : {S : Finset Player // S.Nonempty})
    (who : Player) : ℝ :=
  if who = 0 then
    if 0 ∈ terminal.1 then
      if 1 ∈ terminal.1 then -1 else 1
    else if 1 ∈ terminal.1 then 1 else 0
  else if who = 1 then
    if 0 ∈ terminal.1 then
      if 1 ∈ terminal.1 then 1 else -1
    else if 1 ∈ terminal.1 then -1 else 0
  else if who ∈ terminal.1 then -1 else 0

theorem reward_one_eq_neg_zero
    (terminal : {S : Finset Player // S.Nonempty}) :
    reward terminal 1 = -reward terminal 0 := by
  simp only [reward]
  by_cases hzero : 0 ∈ terminal.1 <;>
    by_cases hone : 1 ∈ terminal.1 <;> simp [hzero, hone]

theorem abs_reward_le_one
    (terminal : {S : Finset Player // S.Nonempty}) (who : Player) :
    |reward terminal who| ≤ 1 := by
  fin_cases who <;> simp only [reward] <;> split_ifs <;> norm_num

theorem terminalPayoff_one_eq_neg_zero
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward profile 1 =
      -quittingTerminalPayoff reward profile 0 := by
  unfold quittingTerminalPayoff
  simp_rw [reward_one_eq_neg_zero]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro terminal _
  ring

def activeProfile (row column : PMF Action) : Player → PMF Action
  | 0 => row
  | 1 => column
  | _ => PMF.pure never

def mass (law : PMF Action) (action : Action) : ℝ := (law action).toReal

def actionTime {dates : ℕ} : Option (Fin dates) →
    Math.Probability.CompactStoppingTime
  | none => (⊤ : WithTop ℕ)
  | some time => WithTop.some time.val

theorem actionTime_two (action : Action) :
    actionTime action = quittingTwoDateTimingActionTime action := by
  cases action <;> rfl

def actionCurrent {dates : ℕ} : Option (Fin (dates + 1)) → Bool
  | none => false
  | some time => Fin.cases true (fun _ => false) time

def actionTail {dates : ℕ} :
    Option (Fin (dates + 1)) → Option (Fin dates)
  | none => none
  | some time => Fin.cases none (fun tail => some tail) time

def choicesRoot {dates : ℕ}
    (choices : Player → Option (Fin (dates + 1))) :
    Player → PMF Bool := fun who => PMF.pure (actionCurrent (choices who))

def choicesTail {dates : ℕ}
    (choices : Player → Option (Fin (dates + 1))) :
    Player → Option (Fin dates) :=
  fun who => actionTail (choices who)

theorem pureProfile_succ_eq_rootThen
    (localReward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (dates : ℕ)
    (choices : Player → Option (Fin (dates + 1))) :
    quittingPureStoppingTimeProfile localReward (fun who =>
        actionTime (choices who)) =
      quittingRootThenContinuationProfile localReward
        (choicesRoot choices)
        (quittingPureStoppingTimeProfile localReward (fun who =>
          actionTime (choicesTail choices who))) := by
  funext who time history
  cases time with
  | zero =>
      unfold quittingPureStoppingTimeProfile
        quittingPureTimeBehaviorStrategy choicesRoot
        quittingRootThenContinuationProfile
      cases hchoice : choices who with
      | none => simp [hchoice, actionTime,
          actionCurrent, quittingPureTimeHazard]
      | some finiteTime =>
          cases finiteTime using Fin.cases with
          | zero => simp [hchoice, actionTime,
              actionCurrent, quittingPureTimeHazard]
          | succ tailTime =>
              simp [hchoice, actionTime,
                actionCurrent, quittingPureTimeHazard]
              change (if 0 = tailTime.val + 1 then PMF.pure true
                else PMF.pure false) = PMF.pure false
              simp
  | succ time =>
      unfold quittingPureStoppingTimeProfile
        quittingPureTimeBehaviorStrategy choicesTail
        quittingRootThenContinuationProfile
      cases hchoice : choices who with
      | none => simp [hchoice, actionTime,
          actionTail, quittingPureTimeHazard]
      | some finiteTime =>
          cases finiteTime using Fin.cases with
          | zero =>
              simp [hchoice, actionTime,
                actionTail, quittingPureTimeHazard]
          | succ tailTime =>
              simp [hchoice, actionTime,
                actionTail, quittingPureTimeHazard]
              change (if time + 1 = tailTime.val + 1 then PMF.pure true
                else PMF.pure false) =
                  if time = tailTime.val then PMF.pure true else PMF.pure false
              simp only [Nat.add_right_cancel_iff]

def purePayoff
    (localReward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (dates : ℕ)
    (choices : Player → Option (Fin dates))
    (who : Player) : ℝ :=
  quittingTerminalPayoff localReward
    (quittingPureStoppingTimeProfile localReward fun player =>
      actionTime (choices player)) who

theorem purePayoff_succ
    (localReward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (dates : ℕ)
    (choices : Player → Option (Fin (dates + 1)))
    (who : Player) :
    purePayoff localReward (dates + 1) choices who =
      quittingRootPayoff localReward
        (fun player => purePayoff localReward dates
          (choicesTail choices) player)
        (fun player => actionCurrent (choices player)) who := by
  unfold purePayoff
  rw [pureProfile_succ_eq_rootThen,
    quittingTerminalPayoff_rootThenContinuation_eq]
  unfold quittingRootExpectedPayoff choicesRoot
  rw [pmfPi_pure]
  simp [Math.Probability.expect_pure]

theorem purePayoff_succ_of_current_nonempty
    (localReward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (dates : ℕ)
    (choices : Player → Option (Fin (dates + 1)))
    (who : Player)
    (hcurrent : (quittingQuitters fun player =>
      actionCurrent (choices player)).Nonempty) :
    purePayoff localReward (dates + 1) choices who =
      localReward
        ⟨quittingQuitters (fun player => actionCurrent (choices player)),
          hcurrent⟩ who := by
  rw [purePayoff_succ, quittingRootPayoff, dif_pos hcurrent]

theorem purePayoff_succ_of_current_empty
    (localReward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (dates : ℕ)
    (choices : Player → Option (Fin (dates + 1)))
    (who : Player)
    (hcurrent : ¬(quittingQuitters fun player =>
      actionCurrent (choices player)).Nonempty) :
    purePayoff localReward (dates + 1) choices who =
      purePayoff localReward dates (choicesTail choices) who := by
  rw [purePayoff_succ, quittingRootPayoff, dif_neg hcurrent]

theorem purePayoff_zero
    (localReward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (choices : Player → Option (Fin 0))
    (who : Player) : purePayoff localReward 0 choices who = 0 := by
  have hchoices : choices = fun _ => none := by
    funext player
    cases h : choices player with
    | none => rfl
    | some time => exact Fin.elim0 time
  rw [hchoices]
  have hprofile :
      (quittingPureStoppingTimeProfile localReward fun _ : Player =>
        actionTime (none : Option (Fin 0))) =
        quittingAlwaysContinueProfile localReward := by
    funext player time history
    simp [quittingAlwaysContinueProfile, quittingPureStoppingTimeProfile,
      StochasticGame.stationaryBehaviorProfile,
      quittingPureTimeBehaviorStrategy,
      actionTime, quittingPureTimeHazard]
    rfl
  unfold purePayoff
  rw [hprofile, quittingTerminalPayoff_quittingAlwaysContinue]

theorem pure_row_now_value (columnAction : Action) :
    purePayoff reward 2 ![now, columnAction, never, never] 0 =
      if columnAction = now then -1 else 1 := by
  cases columnAction with
  | none =>
      change purePayoff reward 2 ![now, never, never, never] 0 = 1
      rw [purePayoff_succ]
      rw [quittingRootPayoff, dif_pos]
      · simp [now, never, actionCurrent, reward, quittingQuitters]
      · exact ⟨0, by simp [now, actionCurrent, quittingQuitters]⟩
  | some time =>
      fin_cases time
      · change purePayoff reward 2 ![now, now, never, never] 0 = -1
        rw [purePayoff_succ]
        rw [quittingRootPayoff, dif_pos]
        · simp [now, actionCurrent, reward, quittingQuitters]
        · exact ⟨0, by simp [now, actionCurrent, quittingQuitters]⟩
      · change purePayoff reward 2 ![now, next, never, never] 0 = 1
        rw [purePayoff_succ]
        let current : Player → Bool := fun player =>
          actionCurrent (![now, next, never, never] player)
        have hzero : 0 ∈ quittingQuitters current := by decide
        have hone : 1 ∉ quittingQuitters current := by decide
        rw [quittingRootPayoff, dif_pos ⟨0, hzero⟩]
        change reward ⟨quittingQuitters current, _⟩ 0 = 1
        simp only [reward, if_pos hzero, if_neg hone]
        simp

theorem pure_row_next_value (columnAction : Action) :
    purePayoff reward 2 ![next, columnAction, never, never] 0 =
      if columnAction = next then -1 else 1 := by
  cases columnAction with
  | none =>
      change purePayoff reward 2 ![next, never, never, never] 0 = 1
      rw [purePayoff_succ_of_current_empty]
      · rw [purePayoff_succ_of_current_nonempty]
        · let current : Player → Bool := fun player =>
            actionCurrent (choicesTail ![next, never, never, never] player)
          have hzero : 0 ∈ quittingQuitters current := by decide
          have hone : 1 ∉ quittingQuitters current := by decide
          change reward ⟨quittingQuitters current, _⟩ 0 = 1
          simp only [reward, if_pos hzero, if_neg hone]
          simp
        · exact ⟨0, by decide⟩
      · decide
  | some time =>
      fin_cases time
      · change purePayoff reward 2 ![next, now, never, never] 0 = 1
        rw [purePayoff_succ_of_current_nonempty]
        · let current : Player → Bool := fun player =>
            actionCurrent (![next, now, never, never] player)
          have hzero : 0 ∉ quittingQuitters current := by decide
          have hone : 1 ∈ quittingQuitters current := by decide
          change reward ⟨quittingQuitters current, _⟩ 0 = 1
          simp only [reward, if_neg hzero, if_pos hone]
          simp
        · exact ⟨1, by decide⟩
      · change purePayoff reward 2 ![next, next, never, never] 0 = -1
        rw [purePayoff_succ_of_current_empty]
        · rw [purePayoff_succ_of_current_nonempty]
          · let current : Player → Bool := fun player =>
              actionCurrent (choicesTail ![next, next, never, never] player)
            have hzero : 0 ∈ quittingQuitters current := by decide
            have hone : 1 ∈ quittingQuitters current := by decide
            change reward ⟨quittingQuitters current, _⟩ 0 = -1
            simp only [reward, if_pos hzero, if_pos hone]
            simp
          · exact ⟨0, by decide⟩
        · decide

theorem pure_row_never_value (columnAction : Action) :
    purePayoff reward 2 ![never, columnAction, never, never] 0 =
      if columnAction = never then 0 else 1 := by
  cases columnAction with
  | none =>
      change purePayoff reward 2 ![never, never, never, never] 0 = 0
      rw [purePayoff_succ_of_current_empty]
      · rw [purePayoff_succ_of_current_empty]
        · exact purePayoff_zero reward _ 0
        · decide
      · decide
  | some time =>
      fin_cases time
      · change purePayoff reward 2 ![never, now, never, never] 0 = 1
        rw [purePayoff_succ_of_current_nonempty]
        · let current : Player → Bool := fun player =>
            actionCurrent (![never, now, never, never] player)
          have hzero : 0 ∉ quittingQuitters current := by decide
          have hone : 1 ∈ quittingQuitters current := by decide
          change reward ⟨quittingQuitters current, _⟩ 0 = 1
          simp only [reward, if_neg hzero, if_pos hone]
          simp
        · exact ⟨1, by decide⟩
      · change purePayoff reward 2 ![never, next, never, never] 0 = 1
        rw [purePayoff_succ_of_current_empty]
        · rw [purePayoff_succ_of_current_nonempty]
          · let current : Player → Bool := fun player =>
              actionCurrent (choicesTail ![never, next, never, never] player)
            have hzero : 0 ∉ quittingQuitters current := by decide
            have hone : 1 ∈ quittingQuitters current := by decide
            change reward ⟨quittingQuitters current, _⟩ 0 = 1
            simp only [reward, if_neg hzero, if_pos hone]
            simp
          · exact ⟨1, by decide⟩
        · decide

theorem row_now_value (row column : PMF Action) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update (activeProfile row column) 0 (PMF.pure now)) 0 =
      1 - 2 * mass column now := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [← actionTime_two]
  change Math.Probability.expect
      (pmfPi (Function.update (activeProfile row column) 0 (PMF.pure now)))
      (fun choices => purePayoff reward 2 choices 0) = _
  rw [expect_pmfPi_fin4]
  simp only [activeProfile, Function.update_self,
    Math.Probability.expect_pure, Fin.isValue,
    Function.update_of_ne (by decide : (1 : Player) ≠ 0),
    Function.update_of_ne (by decide : (2 : Player) ≠ 0),
    Function.update_of_ne (by decide : (3 : Player) ≠ 0)]
  simp [Math.Probability.expect_eq_sum]
  rw [show (some (0 : Fin 2) : Action) = now by rfl,
    show (some (1 : Fin 2) : Action) = next by rfl]
  rw [pure_row_now_value none, pure_row_now_value now,
    pure_row_now_value next]
  have hsum := Math.Probability.pmf_toReal_sum_one column
  rw [Fintype.sum_option, Fin.sum_univ_two] at hsum
  dsimp only [mass]
  norm_num [now, next] at hsum ⊢
  rw [if_neg (by decide : (none : Action) ≠ some (0 : Fin 2))]
  linarith

theorem row_next_value (row column : PMF Action) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update (activeProfile row column) 0 (PMF.pure next)) 0 =
      1 - 2 * mass column next := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [← actionTime_two]
  change Math.Probability.expect
      (pmfPi (Function.update (activeProfile row column) 0 (PMF.pure next)))
      (fun choices => purePayoff reward 2 choices 0) = _
  rw [expect_pmfPi_fin4]
  simp only [activeProfile, Function.update_self,
    Math.Probability.expect_pure, Fin.isValue,
    Function.update_of_ne (by decide : (1 : Player) ≠ 0),
    Function.update_of_ne (by decide : (2 : Player) ≠ 0),
    Function.update_of_ne (by decide : (3 : Player) ≠ 0)]
  simp [Math.Probability.expect_eq_sum]
  rw [show (some (0 : Fin 2) : Action) = now by rfl,
    show (some (1 : Fin 2) : Action) = next by rfl]
  rw [pure_row_next_value none, pure_row_next_value now,
    pure_row_next_value next]
  have hsum := Math.Probability.pmf_toReal_sum_one column
  rw [Fintype.sum_option, Fin.sum_univ_two] at hsum
  dsimp only [mass]
  norm_num [now, next] at hsum ⊢
  rw [if_neg (by decide : (none : Action) ≠ some (1 : Fin 2))]
  linarith

theorem row_never_value (row column : PMF Action) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update (activeProfile row column) 0 (PMF.pure never)) 0 =
      1 - mass column never := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [← actionTime_two]
  change Math.Probability.expect
      (pmfPi (Function.update (activeProfile row column) 0 (PMF.pure never)))
      (fun choices => purePayoff reward 2 choices 0) = _
  rw [expect_pmfPi_fin4]
  simp only [activeProfile, Function.update_self,
    Math.Probability.expect_pure, Fin.isValue,
    Function.update_of_ne (by decide : (1 : Player) ≠ 0),
    Function.update_of_ne (by decide : (2 : Player) ≠ 0),
    Function.update_of_ne (by decide : (3 : Player) ≠ 0)]
  simp [Math.Probability.expect_eq_sum]
  rw [show (some (0 : Fin 2) : Action) = now by rfl,
    show (some (1 : Fin 2) : Action) = next by rfl]
  rw [pure_row_never_value none, pure_row_never_value now,
    pure_row_never_value next]
  have hsum := Math.Probability.pmf_toReal_sum_one column
  rw [Fintype.sum_option, Fin.sum_univ_two] at hsum
  dsimp only [mass]
  simp [never, now, next] at hsum ⊢
  linarith

private theorem expect_pure_row_now (column : PMF Action) :
    Math.Probability.expect column (fun action =>
      purePayoff reward 2 ![now, action, never, never] 0) =
      1 - 2 * mass column now := by
  rw [Math.Probability.expect_eq_sum, Fintype.sum_option,
    Fin.sum_univ_two]
  rw [show (some (0 : Fin 2) : Action) = now by rfl,
    show (some (1 : Fin 2) : Action) = next by rfl]
  rw [pure_row_now_value none, pure_row_now_value now,
    pure_row_now_value next]
  have hsum := Math.Probability.pmf_toReal_sum_one column
  rw [Fintype.sum_option, Fin.sum_univ_two] at hsum
  dsimp only [mass]
  norm_num [now, next] at hsum ⊢
  rw [if_neg (by decide : (none : Action) ≠ some (0 : Fin 2))]
  linarith

private theorem expect_pure_row_next (column : PMF Action) :
    Math.Probability.expect column (fun action =>
      purePayoff reward 2 ![next, action, never, never] 0) =
      1 - 2 * mass column next := by
  rw [Math.Probability.expect_eq_sum, Fintype.sum_option,
    Fin.sum_univ_two]
  rw [show (some (0 : Fin 2) : Action) = now by rfl,
    show (some (1 : Fin 2) : Action) = next by rfl]
  rw [pure_row_next_value none, pure_row_next_value now,
    pure_row_next_value next]
  have hsum := Math.Probability.pmf_toReal_sum_one column
  rw [Fintype.sum_option, Fin.sum_univ_two] at hsum
  dsimp only [mass]
  norm_num [now, next] at hsum ⊢
  rw [if_neg (by decide : (none : Action) ≠ some (1 : Fin 2))]
  linarith

private theorem expect_pure_row_never (column : PMF Action) :
    Math.Probability.expect column (fun action =>
      purePayoff reward 2 ![never, action, never, never] 0) =
      1 - mass column never := by
  rw [Math.Probability.expect_eq_sum, Fintype.sum_option,
    Fin.sum_univ_two]
  rw [show (some (0 : Fin 2) : Action) = now by rfl,
    show (some (1 : Fin 2) : Action) = next by rfl]
  rw [pure_row_never_value none, pure_row_never_value now,
    pure_row_never_value next]
  have hsum := Math.Probability.pmf_toReal_sum_one column
  rw [Fintype.sum_option, Fin.sum_univ_two] at hsum
  dsimp only [mass]
  simp [never, now, next] at hsum ⊢
  linarith

theorem active_row_payoff_eq (row column : PMF Action) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (activeProfile row column) 0 =
      mass row now * (1 - 2 * mass column now) +
        mass row next * (1 - 2 * mass column next) +
          mass row never * (1 - mass column never) := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [← actionTime_two]
  change Math.Probability.expect (pmfPi (activeProfile row column))
      (fun choices => purePayoff reward 2 choices 0) = _
  rw [expect_pmfPi_fin4]
  simp only [activeProfile, Math.Probability.expect_pure]
  rw [Math.Probability.expect_eq_sum, Fintype.sum_option,
    Fin.sum_univ_two]
  rw [show (some (0 : Fin 2) : Action) = now by rfl,
    show (some (1 : Fin 2) : Action) = next by rfl]
  rw [expect_pure_row_now, expect_pure_row_next]
  change mass row never *
      Math.Probability.expect column (fun b =>
        purePayoff reward 2 ![never, b, never, never] 0) +
      (mass row now * (1 - 2 * mass column now) +
        mass row next * (1 - 2 * mass column next)) = _
  rw [expect_pure_row_never]
  ring

theorem mixedPayoff_one_eq_neg_zero (mixed : Player → PMF Action) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu mixed 1 =
      -(quittingTwoDateTimingGame reward).mixedExtension.eu mixed 0 := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu,
    (quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [terminalPayoff_one_eq_neg_zero]
  exact Math.Probability.expect_neg _ _

theorem column_now_value (row column : PMF Action) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update (activeProfile row column) 1 (PMF.pure now)) 1 =
      2 * mass row now - 1 := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [terminalPayoff_one_eq_neg_zero, ← actionTime_two]
  change Math.Probability.expect
      (pmfPi (Function.update (activeProfile row column) 1 (PMF.pure now)))
      (fun choices => -purePayoff reward 2 choices 0) = _
  rw [expect_pmfPi_fin4]
  simp only [activeProfile,
    Function.update_of_ne (by decide : (0 : Player) ≠ 1),
    Function.update_self, Math.Probability.expect_pure,
    Fin.isValue,
    Function.update_of_ne (by decide : (2 : Player) ≠ 1),
    Function.update_of_ne (by decide : (3 : Player) ≠ 1)]
  rw [Math.Probability.expect_eq_sum, Fintype.sum_option,
    Fin.sum_univ_two]
  rw [show (some (0 : Fin 2) : Action) = now by rfl,
    show (some (1 : Fin 2) : Action) = next by rfl,
    show (none : Action) = never by rfl]
  rw [pure_row_never_value now, pure_row_now_value now,
    pure_row_next_value now]
  have hsum := Math.Probability.pmf_toReal_sum_one row
  rw [Fintype.sum_option, Fin.sum_univ_two] at hsum
  dsimp only [mass]
  simp [now, next, never] at ⊢
  linarith

theorem column_next_value (row column : PMF Action) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update (activeProfile row column) 1 (PMF.pure next)) 1 =
      2 * mass row next - 1 := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [terminalPayoff_one_eq_neg_zero, ← actionTime_two]
  change Math.Probability.expect
      (pmfPi (Function.update (activeProfile row column) 1 (PMF.pure next)))
      (fun choices => -purePayoff reward 2 choices 0) = _
  rw [expect_pmfPi_fin4]
  simp only [activeProfile,
    Function.update_of_ne (by decide : (0 : Player) ≠ 1),
    Function.update_self, Math.Probability.expect_pure,
    Fin.isValue,
    Function.update_of_ne (by decide : (2 : Player) ≠ 1),
    Function.update_of_ne (by decide : (3 : Player) ≠ 1)]
  rw [Math.Probability.expect_eq_sum, Fintype.sum_option,
    Fin.sum_univ_two]
  rw [show (some (0 : Fin 2) : Action) = now by rfl,
    show (some (1 : Fin 2) : Action) = next by rfl,
    show (none : Action) = never by rfl]
  rw [pure_row_never_value next, pure_row_now_value next,
    pure_row_next_value next]
  have hsum := Math.Probability.pmf_toReal_sum_one row
  rw [Fintype.sum_option, Fin.sum_univ_two] at hsum
  dsimp only [mass]
  simp [now, next, never] at ⊢
  linarith

theorem column_never_value (row column : PMF Action) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update (activeProfile row column) 1 (PMF.pure never)) 1 =
      mass row never - 1 := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [terminalPayoff_one_eq_neg_zero, ← actionTime_two]
  change Math.Probability.expect
      (pmfPi (Function.update (activeProfile row column) 1 (PMF.pure never)))
      (fun choices => -purePayoff reward 2 choices 0) = _
  rw [expect_pmfPi_fin4]
  simp only [activeProfile,
    Function.update_of_ne (by decide : (0 : Player) ≠ 1),
    Function.update_self, Math.Probability.expect_pure,
    Fin.isValue,
    Function.update_of_ne (by decide : (2 : Player) ≠ 1),
    Function.update_of_ne (by decide : (3 : Player) ≠ 1)]
  rw [Math.Probability.expect_eq_sum, Fintype.sum_option,
    Fin.sum_univ_two]
  rw [show (some (0 : Fin 2) : Action) = now by rfl,
    show (some (1 : Fin 2) : Action) = next by rfl,
    show (none : Action) = never by rfl]
  rw [pure_row_never_value never, pure_row_now_value never,
    pure_row_next_value never]
  have hsum := Math.Probability.pmf_toReal_sum_one row
  rw [Fintype.sum_option, Fin.sum_univ_two] at hsum
  dsimp only [mass]
  simp [now, next, never] at ⊢
  linarith

def equilibriumWeight : Action → ℝ
  | none => 1 / 2
  | some _ => 1 / 4

theorem equilibriumWeight_nonneg (action : Action) :
    0 ≤ equilibriumWeight action := by
  cases action <;> simp [equilibriumWeight]

theorem equilibriumWeight_sum : ∑ action, equilibriumWeight action = 1 := by
  rw [Fintype.sum_option, Fin.sum_univ_two]
  norm_num [equilibriumWeight]

def equilibriumLaw : PMF Action :=
  PMF.ofFintype (fun action => ENNReal.ofReal (equilibriumWeight action)) (by
    rw [← ENNReal.ofReal_one, ← equilibriumWeight_sum]
    exact (ENNReal.ofReal_sum_of_nonneg fun action _ =>
      equilibriumWeight_nonneg action).symm)

theorem equilibriumLaw_apply (action : Action) :
    mass equilibriumLaw action = equilibriumWeight action := by
  unfold mass equilibriumLaw
  rw [PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (equilibriumWeight_nonneg action)

@[simp] theorem equilibriumLaw_now : mass equilibriumLaw now = 1 / 4 := by
  rw [equilibriumLaw_apply]
  rfl

@[simp] theorem equilibriumLaw_next : mass equilibriumLaw next = 1 / 4 := by
  rw [equilibriumLaw_apply]
  rfl

@[simp] theorem equilibriumLaw_never : mass equilibriumLaw never = 1 / 2 := by
  rw [equilibriumLaw_apply]
  rfl

def equilibriumProfile : Player → PMF Action :=
  activeProfile equilibriumLaw equilibriumLaw

theorem equilibrium_row_payoff :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        equilibriumProfile 0 = 1 / 2 := by
  rw [equilibriumProfile, active_row_payoff_eq]
  norm_num

theorem equilibrium_column_payoff :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        equilibriumProfile 1 = -1 / 2 := by
  rw [mixedPayoff_one_eq_neg_zero, equilibrium_row_payoff]
  norm_num

private theorem equilibrium_row_now_deviation :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update equilibriumProfile 0 (PMF.pure now)) 0 =
      1 / 2 := by
  calc
    _ = 1 - 2 * mass equilibriumLaw now := by
      simpa only [equilibriumProfile] using
        row_now_value equilibriumLaw equilibriumLaw
    _ = _ := by norm_num

private theorem equilibrium_row_next_deviation :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update equilibriumProfile 0 (PMF.pure next)) 0 =
      1 / 2 := by
  calc
    _ = 1 - 2 * mass equilibriumLaw next := by
      simpa only [equilibriumProfile] using
        row_next_value equilibriumLaw equilibriumLaw
    _ = _ := by norm_num

private theorem equilibrium_row_never_deviation :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update equilibriumProfile 0 (PMF.pure never)) 0 =
      1 / 2 := by
  calc
    _ = 1 - mass equilibriumLaw never := by
      simpa only [equilibriumProfile] using
        row_never_value equilibriumLaw equilibriumLaw
    _ = _ := by norm_num

theorem equilibrium_row_deviation_value (action : Action) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update equilibriumProfile 0 (PMF.pure action)) 0 =
      1 / 2 := by
  cases action with
  | none => exact equilibrium_row_never_deviation
  | some time =>
      fin_cases time
      · exact equilibrium_row_now_deviation
      · exact equilibrium_row_next_deviation

private theorem equilibrium_column_now_deviation :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update equilibriumProfile 1 (PMF.pure now)) 1 =
      -1 / 2 := by
  calc
    _ = 2 * mass equilibriumLaw now - 1 := by
      simpa only [equilibriumProfile] using
        column_now_value equilibriumLaw equilibriumLaw
    _ = _ := by norm_num

private theorem equilibrium_column_next_deviation :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update equilibriumProfile 1 (PMF.pure next)) 1 =
      -1 / 2 := by
  calc
    _ = 2 * mass equilibriumLaw next - 1 := by
      simpa only [equilibriumProfile] using
        column_next_value equilibriumLaw equilibriumLaw
    _ = _ := by norm_num

private theorem equilibrium_column_never_deviation :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update equilibriumProfile 1 (PMF.pure never)) 1 =
      -1 / 2 := by
  calc
    _ = mass equilibriumLaw never - 1 := by
      simpa only [equilibriumProfile] using
        column_never_value equilibriumLaw equilibriumLaw
    _ = _ := by norm_num

theorem equilibrium_column_deviation_value (action : Action) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update equilibriumProfile 1 (PMF.pure action)) 1 =
      -1 / 2 := by
  cases action with
  | none => exact equilibrium_column_never_deviation
  | some time =>
      fin_cases time
      · exact equilibrium_column_now_deviation
      · exact equilibrium_column_next_deviation

private theorem pure_dummy_two_now_value
    (rowAction columnAction : Action) :
    purePayoff reward 2 ![rowAction, columnAction, now, never] 2 = -1 := by
  have hcurrent : (quittingQuitters fun player =>
      actionCurrent (![rowAction, columnAction, now, never] player)).Nonempty :=
    ⟨2, by simp [quittingQuitters, actionCurrent, now]⟩
  rw [purePayoff_succ_of_current_nonempty reward 1 _ 2 hcurrent]
  simp only [reward, if_neg (by decide : (2 : Player) ≠ 0),
    if_neg (by decide : (2 : Player) ≠ 1)]
  simp [quittingQuitters, actionCurrent, now]

private theorem pure_dummy_two_never_value
    (rowAction columnAction : Action) :
    purePayoff reward 2 ![rowAction, columnAction, never, never] 2 = 0 := by
  rw [purePayoff_succ]
  unfold quittingRootPayoff
  split
  case isTrue hcurrent =>
    simp only [reward, if_neg (by decide : (2 : Player) ≠ 0),
      if_neg (by decide : (2 : Player) ≠ 1)]
    simp [quittingQuitters, actionCurrent, never]
  case isFalse hcurrent =>
    change purePayoff reward 1
      (choicesTail ![rowAction, columnAction, never, never]) 2 = 0
    rw [purePayoff_succ]
    unfold quittingRootPayoff
    split
    case isTrue htail =>
      simp only [reward, if_neg (by decide : (2 : Player) ≠ 0),
        if_neg (by decide : (2 : Player) ≠ 1)]
      simp [quittingQuitters, actionCurrent, choicesTail, actionTail, never]
    case isFalse htail => exact purePayoff_zero reward _ 2

private theorem actionCurrent_eq_true_iff (action : Action) :
    actionCurrent action = true ↔ action = now := by
  cases action with
  | none => simp [actionCurrent, now]
  | some time =>
      fin_cases time
      · simp [actionCurrent, now]
      · decide

@[simp] private theorem quittingQuitters_vec4 (a b c d : Bool) :
    quittingQuitters ![a, b, c, d] =
      (if a then {0} else ∅) ∪ (if b then {1} else ∅) ∪
        (if c then {2} else ∅) ∪ (if d then {3} else ∅) := by
  ext who
  fin_cases who <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp [quittingQuitters]

private theorem dummy_two_current_nonempty_iff
    (rowAction columnAction : Action) :
    (quittingQuitters fun player =>
        actionCurrent (![rowAction, columnAction, next, never] player)).Nonempty ↔
      rowAction = now ∨ columnAction = now := by
  rw [quittingQuitters_nonempty_iff]
  constructor
  · rintro ⟨player, hplayer⟩
    fin_cases player
    · exact Or.inl ((actionCurrent_eq_true_iff rowAction).mp hplayer)
    · exact Or.inr ((actionCurrent_eq_true_iff columnAction).mp hplayer)
    · exact False.elim ((by decide : actionCurrent next ≠ true) hplayer)
    · exact False.elim ((by decide : actionCurrent never ≠ true) hplayer)
  · rintro (hrow | hcolumn)
    · exact ⟨0, by simp [hrow, actionCurrent, now]⟩
    · exact ⟨1, by simp [hcolumn, actionCurrent, now]⟩

private theorem pure_dummy_two_next_value
    (rowAction columnAction : Action) :
    purePayoff reward 2 ![rowAction, columnAction, next, never] 2 =
      if rowAction = now ∨ columnAction = now then 0 else -1 := by
  rw [purePayoff_succ]
  unfold quittingRootPayoff
  split
  case isTrue hcurrent =>
    rw [if_pos ((dummy_two_current_nonempty_iff rowAction columnAction).mp
      hcurrent)]
    simp only [reward, if_neg (by decide : (2 : Player) ≠ 0),
      if_neg (by decide : (2 : Player) ≠ 1)]
    rw [if_neg]
    have hfun : (fun player =>
        actionCurrent (![rowAction, columnAction, next, never] player)) =
        ![actionCurrent rowAction, actionCurrent columnAction,
          actionCurrent next, actionCurrent never] := by
      funext player
      fin_cases player <;> rfl
    rw [hfun]
    have hnext : actionCurrent next = false := by decide
    rw [hnext]
    cases hrow : actionCurrent rowAction <;>
      cases hcolumn : actionCurrent columnAction <;>
        simp [quittingQuitters_vec4, actionCurrent, never]
  case isFalse hcurrent =>
    rw [if_neg (not_congr (dummy_two_current_nonempty_iff
      rowAction columnAction) |>.mp hcurrent)]
    change purePayoff reward 1
      (choicesTail ![rowAction, columnAction, next, never]) 2 = -1
    have htwo : 2 ∈ quittingQuitters (fun player => actionCurrent
        (choicesTail ![rowAction, columnAction, next, never] player)) := by
      simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
        true_and]
      change actionCurrent (actionTail next) = true
      decide
    have htail : (quittingQuitters fun player => actionCurrent
        (choicesTail ![rowAction, columnAction, next, never] player)).Nonempty :=
      ⟨2, htwo⟩
    rw [purePayoff_succ_of_current_nonempty reward 0 _ 2 htail]
    simp only [reward, if_neg (by decide : (2 : Player) ≠ 0),
      if_neg (by decide : (2 : Player) ≠ 1)]
    rw [if_pos htwo]

private theorem equilibrium_dummy_two_now_deviation :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update equilibriumProfile 2 (PMF.pure now)) 2 = -1 := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [← actionTime_two]
  change Math.Probability.expect
      (pmfPi (Function.update equilibriumProfile 2 (PMF.pure now)))
      (fun choices => purePayoff reward 2 choices 2) = -1
  rw [expect_pmfPi_fin4]
  simp only [equilibriumProfile, activeProfile,
    Function.update_of_ne (by decide : (0 : Player) ≠ 2),
    Function.update_of_ne (by decide : (1 : Player) ≠ 2),
    Function.update_self,
    Function.update_of_ne (by decide : (3 : Player) ≠ 2),
    Math.Probability.expect_pure, Fin.isValue]
  simp_rw [pure_dummy_two_now_value]
  simp

private theorem equilibrium_dummy_two_never_deviation :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update equilibriumProfile 2 (PMF.pure never)) 2 = 0 := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [← actionTime_two]
  change Math.Probability.expect
      (pmfPi (Function.update equilibriumProfile 2 (PMF.pure never)))
      (fun choices => purePayoff reward 2 choices 2) = 0
  rw [expect_pmfPi_fin4]
  simp only [equilibriumProfile, activeProfile,
    Function.update_of_ne (by decide : (0 : Player) ≠ 2),
    Function.update_of_ne (by decide : (1 : Player) ≠ 2),
    Function.update_self,
    Function.update_of_ne (by decide : (3 : Player) ≠ 2),
    Math.Probability.expect_pure, Fin.isValue]
  simp_rw [pure_dummy_two_never_value]
  simp

private theorem equilibrium_dummy_two_next_deviation :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update equilibriumProfile 2 (PMF.pure next)) 2 =
      -9 / 16 := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [← actionTime_two]
  change Math.Probability.expect
      (pmfPi (Function.update equilibriumProfile 2 (PMF.pure next)))
      (fun choices => purePayoff reward 2 choices 2) = -9 / 16
  rw [expect_pmfPi_fin4]
  simp only [equilibriumProfile, activeProfile,
    Function.update_of_ne (by decide : (0 : Player) ≠ 2),
    Function.update_of_ne (by decide : (1 : Player) ≠ 2),
    Function.update_self,
    Function.update_of_ne (by decide : (3 : Player) ≠ 2),
    Math.Probability.expect_pure, Fin.isValue]
  simp_rw [pure_dummy_two_next_value]
  simp [Math.Probability.expect_eq_sum, Fintype.sum_option,
    Fin.sum_univ_two, equilibriumLaw, PMF.ofFintype_apply,
    equilibriumWeight, now]
  norm_num

private theorem pure_dummy_three_now_value
    (rowAction columnAction : Action) :
    purePayoff reward 2 ![rowAction, columnAction, never, now] 3 = -1 := by
  have hcurrent : (quittingQuitters fun player =>
      actionCurrent (![rowAction, columnAction, never, now] player)).Nonempty :=
    ⟨3, by simp [quittingQuitters, actionCurrent, now]⟩
  rw [purePayoff_succ_of_current_nonempty reward 1 _ 3 hcurrent]
  simp only [reward, if_neg (by decide : (3 : Player) ≠ 0),
    if_neg (by decide : (3 : Player) ≠ 1)]
  simp [quittingQuitters, actionCurrent, now]

private theorem pure_dummy_three_never_value
    (rowAction columnAction : Action) :
    purePayoff reward 2 ![rowAction, columnAction, never, never] 3 = 0 := by
  rw [purePayoff_succ]
  unfold quittingRootPayoff
  split
  case isTrue hcurrent =>
    simp only [reward, if_neg (by decide : (3 : Player) ≠ 0),
      if_neg (by decide : (3 : Player) ≠ 1)]
    simp [quittingQuitters, actionCurrent, never]
  case isFalse hcurrent =>
    change purePayoff reward 1
      (choicesTail ![rowAction, columnAction, never, never]) 3 = 0
    rw [purePayoff_succ]
    unfold quittingRootPayoff
    split
    case isTrue htail =>
      simp only [reward, if_neg (by decide : (3 : Player) ≠ 0),
        if_neg (by decide : (3 : Player) ≠ 1)]
      simp [quittingQuitters, actionCurrent, choicesTail, actionTail, never]
    case isFalse htail => exact purePayoff_zero reward _ 3

private theorem dummy_three_current_nonempty_iff
    (rowAction columnAction : Action) :
    (quittingQuitters fun player =>
        actionCurrent (![rowAction, columnAction, never, next] player)).Nonempty ↔
      rowAction = now ∨ columnAction = now := by
  rw [quittingQuitters_nonempty_iff]
  constructor
  · rintro ⟨player, hplayer⟩
    fin_cases player
    · exact Or.inl ((actionCurrent_eq_true_iff rowAction).mp hplayer)
    · exact Or.inr ((actionCurrent_eq_true_iff columnAction).mp hplayer)
    · exact False.elim ((by decide : actionCurrent never ≠ true) hplayer)
    · exact False.elim ((by decide : actionCurrent next ≠ true) hplayer)
  · rintro (hrow | hcolumn)
    · exact ⟨0, by simp [hrow, actionCurrent, now]⟩
    · exact ⟨1, by simp [hcolumn, actionCurrent, now]⟩

private theorem pure_dummy_three_next_value
    (rowAction columnAction : Action) :
    purePayoff reward 2 ![rowAction, columnAction, never, next] 3 =
      if rowAction = now ∨ columnAction = now then 0 else -1 := by
  rw [purePayoff_succ]
  unfold quittingRootPayoff
  split
  case isTrue hcurrent =>
    rw [if_pos ((dummy_three_current_nonempty_iff rowAction columnAction).mp
      hcurrent)]
    simp only [reward, if_neg (by decide : (3 : Player) ≠ 0),
      if_neg (by decide : (3 : Player) ≠ 1)]
    rw [if_neg]
    have hfun : (fun player =>
        actionCurrent (![rowAction, columnAction, never, next] player)) =
        ![actionCurrent rowAction, actionCurrent columnAction,
          actionCurrent never, actionCurrent next] := by
      funext player
      fin_cases player <;> rfl
    rw [hfun]
    have hnext : actionCurrent next = false := by decide
    rw [hnext]
    cases hrow : actionCurrent rowAction <;>
      cases hcolumn : actionCurrent columnAction <;>
        simp [quittingQuitters_vec4, actionCurrent, never]
  case isFalse hcurrent =>
    rw [if_neg (not_congr (dummy_three_current_nonempty_iff
      rowAction columnAction) |>.mp hcurrent)]
    change purePayoff reward 1
      (choicesTail ![rowAction, columnAction, never, next]) 3 = -1
    have hthree : 3 ∈ quittingQuitters (fun player => actionCurrent
        (choicesTail ![rowAction, columnAction, never, next] player)) := by
      simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
        true_and]
      change actionCurrent (actionTail next) = true
      decide
    have htail : (quittingQuitters fun player => actionCurrent
        (choicesTail ![rowAction, columnAction, never, next] player)).Nonempty :=
      ⟨3, hthree⟩
    rw [purePayoff_succ_of_current_nonempty reward 0 _ 3 htail]
    simp only [reward, if_neg (by decide : (3 : Player) ≠ 0),
      if_neg (by decide : (3 : Player) ≠ 1)]
    rw [if_pos hthree]

private theorem equilibrium_dummy_three_now_deviation :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update equilibriumProfile 3 (PMF.pure now)) 3 = -1 := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [← actionTime_two]
  change Math.Probability.expect
      (pmfPi (Function.update equilibriumProfile 3 (PMF.pure now)))
      (fun choices => purePayoff reward 2 choices 3) = -1
  rw [expect_pmfPi_fin4]
  simp only [equilibriumProfile, activeProfile,
    Function.update_of_ne (by decide : (0 : Player) ≠ 3),
    Function.update_of_ne (by decide : (1 : Player) ≠ 3),
    Function.update_of_ne (by decide : (2 : Player) ≠ 3),
    Function.update_self, Math.Probability.expect_pure, Fin.isValue]
  simp_rw [pure_dummy_three_now_value]
  simp

private theorem equilibrium_dummy_three_never_deviation :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update equilibriumProfile 3 (PMF.pure never)) 3 = 0 := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [← actionTime_two]
  change Math.Probability.expect
      (pmfPi (Function.update equilibriumProfile 3 (PMF.pure never)))
      (fun choices => purePayoff reward 2 choices 3) = 0
  rw [expect_pmfPi_fin4]
  simp only [equilibriumProfile, activeProfile,
    Function.update_of_ne (by decide : (0 : Player) ≠ 3),
    Function.update_of_ne (by decide : (1 : Player) ≠ 3),
    Function.update_of_ne (by decide : (2 : Player) ≠ 3),
    Function.update_self, Math.Probability.expect_pure, Fin.isValue]
  simp_rw [pure_dummy_three_never_value]
  simp

private theorem equilibrium_dummy_three_next_deviation :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update equilibriumProfile 3 (PMF.pure next)) 3 =
      -9 / 16 := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [← actionTime_two]
  change Math.Probability.expect
      (pmfPi (Function.update equilibriumProfile 3 (PMF.pure next)))
      (fun choices => purePayoff reward 2 choices 3) = -9 / 16
  rw [expect_pmfPi_fin4]
  simp only [equilibriumProfile, activeProfile,
    Function.update_of_ne (by decide : (0 : Player) ≠ 3),
    Function.update_of_ne (by decide : (1 : Player) ≠ 3),
    Function.update_of_ne (by decide : (2 : Player) ≠ 3),
    Function.update_self, Math.Probability.expect_pure, Fin.isValue]
  simp_rw [pure_dummy_three_next_value]
  simp [Math.Probability.expect_eq_sum, Fintype.sum_option,
    Fin.sum_univ_two, equilibriumLaw, PMF.ofFintype_apply,
    equilibriumWeight, now]
  norm_num

theorem equilibrium_dummy_two_payoff :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        equilibriumProfile 2 = 0 := by
  have hupdate :
      Function.update equilibriumProfile 2 (PMF.pure never) =
        equilibriumProfile := by
    funext who
    fin_cases who <;> simp [equilibriumProfile, activeProfile, never]
  have heq := congrArg (fun profile : Player → PMF Action =>
    (quittingTwoDateTimingGame reward).mixedExtension.eu profile 2) hupdate
  exact heq.symm.trans equilibrium_dummy_two_never_deviation

theorem equilibrium_dummy_three_payoff :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        equilibriumProfile 3 = 0 := by
  have hupdate :
      Function.update equilibriumProfile 3 (PMF.pure never) =
        equilibriumProfile := by
    funext who
    fin_cases who <;> simp [equilibriumProfile, activeProfile, never]
  have heq := congrArg (fun profile : Player → PMF Action =>
    (quittingTwoDateTimingGame reward).mixedExtension.eu profile 3) hupdate
  exact heq.symm.trans equilibrium_dummy_three_never_deviation

theorem equilibrium_dummy_two_deviation_le (action : Action) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
      (Function.update equilibriumProfile 2 (PMF.pure action)) 2 ≤ 0 := by
  cases action with
  | none => exact equilibrium_dummy_two_never_deviation.le
  | some time =>
      fin_cases time
      · exact equilibrium_dummy_two_now_deviation.le.trans (by norm_num)
      · exact equilibrium_dummy_two_next_deviation.le.trans (by norm_num)

theorem equilibrium_dummy_three_deviation_le (action : Action) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
      (Function.update equilibriumProfile 3 (PMF.pure action)) 3 ≤ 0 := by
  cases action with
  | none => exact equilibrium_dummy_three_never_deviation.le
  | some time =>
      fin_cases time
      · exact equilibrium_dummy_three_now_deviation.le.trans (by norm_num)
      · exact equilibrium_dummy_three_next_deviation.le.trans (by norm_num)

theorem equilibriumProfile_isNash :
    (quittingTwoDateTimingGame reward).mixedExtension.IsNash
      equilibriumProfile := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  apply ((quittingTwoDateTimingGame reward).isNash_iff_gains_nonpos
    equilibriumProfile).mpr
  intro who action
  unfold KernelGame.mixedGain
  have hval : who.val = 0 ∨ who.val = 1 ∨
      who.val = 2 ∨ who.val = 3 := by
    have hlt := who.isLt
    omega
  rcases hval with hzero | hone | htwo | hthree
  · have : who = 0 := Fin.ext hzero
    subst who
    rw [equilibrium_row_deviation_value, equilibrium_row_payoff]
    norm_num
  · have : who = 1 := Fin.ext hone
    subst who
    rw [equilibrium_column_deviation_value, equilibrium_column_payoff]
    norm_num
  · have : who = 2 := Fin.ext htwo
    subst who
    rw [equilibrium_dummy_two_payoff, sub_zero]
    exact equilibrium_dummy_two_deviation_le action
  · have : who = 3 := Fin.ext hthree
    subst who
    rw [equilibrium_dummy_three_payoff, sub_zero]
    exact equilibrium_dummy_three_deviation_le action

private theorem pure_dummy_now_general (choices : Player → Action)
    (dummy : Player) (hzero : dummy ≠ 0) (hone : dummy ≠ 1) :
    purePayoff reward 2 (Function.update choices dummy now) dummy = -1 := by
  have hcurrent : (quittingQuitters fun player => actionCurrent
      (Function.update choices dummy now player)).Nonempty :=
    ⟨dummy, by simp [quittingQuitters, actionCurrent, now]⟩
  rw [purePayoff_succ_of_current_nonempty reward 1 _ dummy hcurrent]
  simp only [reward, if_neg hzero, if_neg hone]
  rw [if_pos]
  simp [quittingQuitters, actionCurrent, now]

private theorem pure_dummy_never_general (choices : Player → Action)
    (dummy : Player) (hzero : dummy ≠ 0) (hone : dummy ≠ 1) :
    purePayoff reward 2 (Function.update choices dummy never) dummy = 0 := by
  rw [purePayoff_succ]
  unfold quittingRootPayoff
  split
  case isTrue hcurrent =>
    simp only [reward, if_neg hzero, if_neg hone]
    rw [if_neg]
    simp [quittingQuitters, actionCurrent, never]
  case isFalse hcurrent =>
    change purePayoff reward 1
      (choicesTail (Function.update choices dummy never)) dummy = 0
    rw [purePayoff_succ]
    unfold quittingRootPayoff
    split
    case isTrue htail =>
      simp only [reward, if_neg hzero, if_neg hone]
      rw [if_neg]
      simp [quittingQuitters, choicesTail, actionTail,
        actionCurrent, never]
    case isFalse htail => exact purePayoff_zero reward _ dummy

theorem dummy_now_payoff (mixed : Player → PMF Action)
    (dummy : Player) (hzero : dummy ≠ 0) (hone : dummy ≠ 1) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update mixed dummy (PMF.pure now)) dummy = -1 := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [← actionTime_two]
  change Math.Probability.expect
      (pmfPi (Function.update mixed dummy (PMF.pure now)))
      (fun choices => purePayoff reward 2 choices dummy) = -1
  calc
    _ = Math.Probability.expect
        (pmfPi (Function.update mixed dummy (PMF.pure now)))
        (fun _ => -1) := by
      apply Math.ProbabilityMassFunction.expect_congr_on_support
      intro choices hchoices
      have hcoordinate := eq_of_mem_support_pmfPi_update_pure
        mixed dummy now hchoices
      have heq : choices = Function.update choices dummy now := by
        funext player
        by_cases hplayer : player = dummy
        · subst player
          simp [hcoordinate]
        · rw [Function.update_of_ne hplayer]
      rw [heq]
      exact pure_dummy_now_general choices dummy hzero hone
    _ = -1 := Math.Probability.expect_const _ _

theorem dummy_never_payoff (mixed : Player → PMF Action)
    (dummy : Player) (hzero : dummy ≠ 0) (hone : dummy ≠ 1) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update mixed dummy (PMF.pure never)) dummy = 0 := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [← actionTime_two]
  change Math.Probability.expect
      (pmfPi (Function.update mixed dummy (PMF.pure never)))
      (fun choices => purePayoff reward 2 choices dummy) = 0
  calc
    _ = Math.Probability.expect
        (pmfPi (Function.update mixed dummy (PMF.pure never)))
        (fun _ => 0) := by
      apply Math.ProbabilityMassFunction.expect_congr_on_support
      intro choices hchoices
      have hcoordinate := eq_of_mem_support_pmfPi_update_pure
        mixed dummy never hchoices
      have heq : choices = Function.update choices dummy never := by
        funext player
        by_cases hplayer : player = dummy
        · subst player
          simp [hcoordinate]
        · rw [Function.update_of_ne hplayer]
      rw [heq]
      exact pure_dummy_never_general choices dummy hzero hone
    _ = 0 := Math.Probability.expect_const _ _

private theorem mixedGain_eq_zero_of_mem_support
    {I : Type} [Fintype I] [DecidableEq I]
    (G : KernelGame I) [Finite G.Outcome]
    [∀ who, Finite (G.Strategy who)]
    (mixed : ∀ who, PMF (G.Strategy who))
    (hnash : G.mixedExtension.IsNash mixed)
    (who : I) (action : G.Strategy who)
    (haction : mixed who action ≠ 0) :
    G.mixedGain mixed who action = 0 := by
  letI : Fintype (G.Strategy who) := Fintype.ofFinite _
  have hgain : ∀ choice : G.Strategy who,
      G.mixedGain mixed who choice ≤ 0 :=
    fun choice => (G.isNash_iff_gains_nonpos mixed).mp hnash who choice
  have hweighted := G.weighted_gain_sum_zero mixed who
  unfold Math.Probability.expect at hweighted
  rw [tsum_fintype] at hweighted
  have hterm :
      (mixed who action).toReal * G.mixedGain mixed who action = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos (fun choice _ =>
      mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg
        (hgain choice))).mp hweighted action (Finset.mem_univ action)
  have hmass : 0 < (mixed who action).toReal :=
    ENNReal.toReal_pos haction (PMF.apply_ne_top _ _)
  exact (mul_eq_zero.mp hterm).resolve_left hmass.ne'

theorem dummy_now_mass_eq_zero (mixed : Player → PMF Action)
    (hnash : (quittingTwoDateTimingGame reward).mixedExtension.IsNash mixed)
    (dummy : Player) (hzero : dummy ≠ 0) (hone : dummy ≠ 1) :
    mixed dummy now = 0 := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  letI : ∀ who, Finite ((quittingTwoDateTimingGame reward).Strategy who) :=
    fun _ => by
      unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
      infer_instance
  by_contra hmass
  have hsupport := mixedGain_eq_zero_of_mem_support
    (quittingTwoDateTimingGame reward) mixed hnash dummy now hmass
  have hnever := ((quittingTwoDateTimingGame reward).isNash_iff_gains_nonpos
    mixed).mp hnash dummy never
  unfold KernelGame.mixedGain at hsupport hnever
  rw [dummy_now_payoff mixed dummy hzero hone] at hsupport
  rw [dummy_never_payoff mixed dummy hzero hone] at hnever
  linarith

private theorem ne_of_mem_support_pmfPi_of_marginal_eq_zero
    (mixed : Player → PMF Action) (choices : Player → Action)
    (hchoices : choices ∈ (pmfPi mixed).support)
    (who : Player) (action : Action) (hmass : mixed who action = 0) :
    choices who ≠ action := by
  intro heq
  have hzero : pmfPi mixed choices = 0 := by
    rw [pmfPi_apply]
    apply Finset.prod_eq_zero (Finset.mem_univ who)
    rw [heq, hmass]
  exact (PMF.mem_support_iff _ _).mp hchoices hzero

private theorem actionCurrent_eq_false_of_ne_now (action : Action)
    (hne : action ≠ now) : actionCurrent action = false := by
  cases hcurrent : actionCurrent action
  · rfl
  · exact False.elim (hne ((actionCurrent_eq_true_iff action).mp hcurrent))

private theorem pure_column_value_of_row_now
    (choices : Player → Action)
    (hrow : choices 0 = now) :
    purePayoff reward 2 choices 1 =
      if choices 1 = now then 1 else -1 := by
  have hnonempty : (quittingQuitters fun player =>
      actionCurrent (choices player)).Nonempty :=
    ⟨0, by simp [quittingQuitters, hrow, actionCurrent, now]⟩
  rw [purePayoff_succ_of_current_nonempty reward 1 _ 1 hnonempty]
  have hrowCurrent : actionCurrent (choices 0) = true := by
    rw [hrow]
    rfl
  by_cases hcolumn : choices 1 = now
  · rw [if_pos hcolumn]
    have hcolumnCurrent : actionCurrent (choices 1) = true := by
      rw [hcolumn]
      rfl
    have hzeroMem : 0 ∈ quittingQuitters (fun player =>
        actionCurrent (choices player)) := by
      simpa [quittingQuitters] using hrowCurrent
    have honeMem : 1 ∈ quittingQuitters (fun player =>
        actionCurrent (choices player)) := by
      simpa [quittingQuitters] using hcolumnCurrent
    simp [reward, hzeroMem, honeMem]
  · rw [if_neg hcolumn]
    have hcolumnCurrent : actionCurrent (choices 1) = false :=
      actionCurrent_eq_false_of_ne_now _ hcolumn
    have hzeroMem : 0 ∈ quittingQuitters (fun player =>
        actionCurrent (choices player)) := by
      simpa [quittingQuitters] using hrowCurrent
    have honeMem : 1 ∉ quittingQuitters (fun player =>
        actionCurrent (choices player)) := by
      simpa [quittingQuitters] using hcolumnCurrent
    simp [reward, hzeroMem, honeMem]

private theorem eq_of_mem_support_pmfPi_of_marginal_eq_pure
    (mixed : Player → PMF Action) (choices : Player → Action)
    (hchoices : choices ∈ (pmfPi mixed).support)
    (who : Player) (action : Action)
    (hmarginal : mixed who = PMF.pure action) :
    choices who = action := by
  have hfamily : mixed = Function.update mixed who (PMF.pure action) := by
    funext player
    by_cases hplayer : player = who
    · subst player
      rw [Function.update_self, hmarginal]
    · rw [Function.update_of_ne hplayer]
  rw [hfamily] at hchoices
  exact eq_of_mem_support_pmfPi_update_pure mixed who action hchoices

theorem column_deviation_value_of_row_pure_now
    (mixed : Player → PMF Action)
    (hrow : mixed 0 = PMF.pure now) (action : Action) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update mixed 1 (PMF.pure action)) 1 =
      if action = now then 1 else -1 := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [← actionTime_two]
  let deviated := Function.update mixed 1 (PMF.pure action)
  change Math.Probability.expect (pmfPi deviated)
      (fun choices => purePayoff reward 2 choices 1) = _
  calc
    _ = Math.Probability.expect (pmfPi deviated)
        (fun _ => if action = now then 1 else -1) := by
      apply Math.ProbabilityMassFunction.expect_congr_on_support
      intro choices hchoices
      have hrowMarginal : deviated 0 = PMF.pure now := by
        simp only [deviated,
          Function.update_of_ne (by decide : (0 : Player) ≠ 1), hrow]
      have hrowChoice := eq_of_mem_support_pmfPi_of_marginal_eq_pure
        deviated choices hchoices 0 now hrowMarginal
      have hcolumnMarginal : deviated 1 = PMF.pure action := by
        simp only [deviated, Function.update_self]
      have hcolumnChoice := eq_of_mem_support_pmfPi_of_marginal_eq_pure
        deviated choices hchoices 1 action hcolumnMarginal
      rw [pure_column_value_of_row_now choices hrowChoice, hcolumnChoice]
    _ = _ := Math.Probability.expect_const _ _

private theorem pure_row_value_of_column_now
    (choices : Player → Action) (hcolumn : choices 1 = now) :
    purePayoff reward 2 choices 0 =
      if choices 0 = now then -1 else 1 := by
  have hnonempty : (quittingQuitters fun player =>
      actionCurrent (choices player)).Nonempty :=
    ⟨1, by simp [quittingQuitters, hcolumn, actionCurrent, now]⟩
  rw [purePayoff_succ_of_current_nonempty reward 1 _ 0 hnonempty]
  have hcolumnCurrent : actionCurrent (choices 1) = true := by
    rw [hcolumn]
    rfl
  by_cases hrow : choices 0 = now
  · rw [if_pos hrow]
    have hrowCurrent : actionCurrent (choices 0) = true := by
      rw [hrow]
      rfl
    have hzeroMem : 0 ∈ quittingQuitters (fun player =>
        actionCurrent (choices player)) := by
      simpa [quittingQuitters] using hrowCurrent
    have honeMem : 1 ∈ quittingQuitters (fun player =>
        actionCurrent (choices player)) := by
      simpa [quittingQuitters] using hcolumnCurrent
    simp [reward, hzeroMem, honeMem]
  · rw [if_neg hrow]
    have hrowCurrent : actionCurrent (choices 0) = false :=
      actionCurrent_eq_false_of_ne_now _ hrow
    have hzeroMem : 0 ∉ quittingQuitters (fun player =>
        actionCurrent (choices player)) := by
      simpa [quittingQuitters] using hrowCurrent
    have honeMem : 1 ∈ quittingQuitters (fun player =>
        actionCurrent (choices player)) := by
      simpa [quittingQuitters] using hcolumnCurrent
    simp [reward, hzeroMem, honeMem]

theorem row_deviation_value_of_column_pure_now
    (mixed : Player → PMF Action)
    (hcolumn : mixed 1 = PMF.pure now) (action : Action) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update mixed 0 (PMF.pure action)) 0 =
      if action = now then -1 else 1 := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [← actionTime_two]
  let deviated := Function.update mixed 0 (PMF.pure action)
  change Math.Probability.expect (pmfPi deviated)
      (fun choices => purePayoff reward 2 choices 0) = _
  calc
    _ = Math.Probability.expect (pmfPi deviated)
        (fun _ => if action = now then -1 else 1) := by
      apply Math.ProbabilityMassFunction.expect_congr_on_support
      intro choices hchoices
      have hrowMarginal : deviated 0 = PMF.pure action := by
        simp only [deviated, Function.update_self]
      have hrowChoice := eq_of_mem_support_pmfPi_of_marginal_eq_pure
        deviated choices hchoices 0 action hrowMarginal
      have hcolumnMarginal : deviated 1 = PMF.pure now := by
        simp only [deviated,
          Function.update_of_ne (by decide : (1 : Player) ≠ 0), hcolumn]
      have hcolumnChoice := eq_of_mem_support_pmfPi_of_marginal_eq_pure
        deviated choices hchoices 1 now hcolumnMarginal
      rw [pure_row_value_of_column_now choices hcolumnChoice, hrowChoice]
    _ = _ := Math.Probability.expect_const _ _

theorem reward_bound (terminal : {S : Finset Player // S.Nonempty})
    (who : Player) : |reward terminal who| ≤ 1 := by
  fin_cases who <;> simp only [reward] <;> split_ifs <;> norm_num

theorem mixed_payoff_le_one (mixed : Player → PMF Action)
    (who : Player) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu mixed who ≤ 1 := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  letI : ∀ player, Finite
      ((quittingTwoDateTimingGame reward).Strategy player) := fun _ => by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  apply Math.ProbabilityMassFunction.expect_le_of_le_on_support
  intro choices _
  exact (le_abs_self _).trans (abs_quittingTerminalPayoff_le reward
    (quittingPureStoppingTimeProfile reward fun player =>
      quittingTwoDateTimingActionTime (choices player)) who reward_bound)

theorem column_eq_pure_now_of_row_pure_now
    (mixed : Player → PMF Action)
    (hnash : (quittingTwoDateTimingGame reward).mixedExtension.IsNash mixed)
    (hrow : mixed 0 = PMF.pure now) : mixed 1 = PMF.pure now := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  letI : ∀ player, Finite
      ((quittingTwoDateTimingGame reward).Strategy player) := fun _ => by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  have hgainNow := ((quittingTwoDateTimingGame reward).isNash_iff_gains_nonpos
    mixed).mp hnash 1 now
  unfold KernelGame.mixedGain at hgainNow
  rw [column_deviation_value_of_row_pure_now mixed hrow now,
    if_pos rfl] at hgainNow
  have hpayoffLe := mixed_payoff_le_one mixed 1
  have hpayoff :
      (quittingTwoDateTimingGame reward).mixedExtension.eu mixed 1 = 1 := by
    linarith
  have hsupportSet : (mixed 1).support = {now} := by
    apply Set.Subset.antisymm
    · intro action haction
      by_contra hne
      have hneNow : action ≠ now := by simpa using hne
      have hmass : mixed 1 action ≠ 0 :=
        (PMF.mem_support_iff _ _).mp haction
      have hsupport := mixedGain_eq_zero_of_mem_support
        (quittingTwoDateTimingGame reward) mixed hnash 1 action hmass
      unfold KernelGame.mixedGain at hsupport
      rw [column_deviation_value_of_row_pure_now mixed hrow action,
        if_neg hneNow, hpayoff] at hsupport
      norm_num at hsupport
    · intro action haction
      rw [Set.mem_singleton_iff.mp haction]
      obtain ⟨supported, hsupported⟩ := (mixed 1).support_nonempty
      have hsupportedNow : supported = now := by
        by_contra hne
        have hmass : mixed 1 supported ≠ 0 :=
          (PMF.mem_support_iff _ _).mp hsupported
        have hsupport := mixedGain_eq_zero_of_mem_support
          (quittingTwoDateTimingGame reward) mixed hnash 1 supported hmass
        unfold KernelGame.mixedGain at hsupport
        rw [column_deviation_value_of_row_pure_now mixed hrow supported,
          if_neg hne, hpayoff] at hsupport
        norm_num at hsupport
      simpa [hsupportedNow] using hsupported
  have hmassOne : mixed 1 now = 1 :=
    (PMF.apply_eq_one_iff (mixed 1) now).mpr hsupportSet
  apply PMF.ext
  intro action
  by_cases haction : action = now
  · subst action
    rw [hmassOne, PMF.pure_apply_self]
  · have hzero : mixed 1 action = 0 :=
      (PMF.apply_eq_zero_iff (mixed 1) action).mpr (by
        rw [hsupportSet]
        simpa using haction)
    rw [hzero, PMF.pure_apply, if_neg haction]

theorem row_not_pure_now
    (mixed : Player → PMF Action)
    (hnash : (quittingTwoDateTimingGame reward).mixedExtension.IsNash mixed) :
    mixed 0 ≠ PMF.pure now := by
  intro hrow
  have hcolumn := column_eq_pure_now_of_row_pure_now mixed hnash hrow
  have hupdate : Function.update mixed 0 (PMF.pure now) = mixed := by
    funext player
    by_cases hplayer : player = 0
    · subst player
      rw [Function.update_self, hrow]
    · rw [Function.update_of_ne hplayer]
  have hprescribed :
      (quittingTwoDateTimingGame reward).mixedExtension.eu mixed 0 = -1 := by
    have hdeviation := row_deviation_value_of_column_pure_now mixed hcolumn now
    rw [if_pos rfl] at hdeviation
    have heq := congrArg (fun profile : Player → PMF Action =>
      (quittingTwoDateTimingGame reward).mixedExtension.eu profile 0) hupdate
    exact heq.symm.trans hdeviation
  have hgain := hnash 0 (PMF.pure next)
  rw [row_deviation_value_of_column_pure_now mixed hcolumn next,
    if_neg (by decide : next ≠ now), hprescribed] at hgain
  norm_num at hgain

private theorem pure_column_now_value (choices : Player → Action)
    (hcolumn : choices 1 = now) :
    purePayoff reward 2 choices 1 =
      if choices 0 = now then 1 else -1 := by
  have hnonempty : (quittingQuitters fun player =>
      actionCurrent (choices player)).Nonempty :=
    ⟨1, by simp [quittingQuitters, hcolumn, actionCurrent, now]⟩
  rw [purePayoff_succ_of_current_nonempty reward 1 _ 1 hnonempty]
  have honeMem : 1 ∈ quittingQuitters (fun player =>
      actionCurrent (choices player)) := by
    simp [quittingQuitters, hcolumn, actionCurrent, now]
  by_cases hrow : choices 0 = now
  · rw [if_pos hrow]
    have hzeroMem : 0 ∈ quittingQuitters (fun player =>
        actionCurrent (choices player)) := by
      simp [quittingQuitters, hrow, actionCurrent, now]
    simp [reward, hzeroMem, honeMem]
  · rw [if_neg hrow]
    have hzeroCurrent := actionCurrent_eq_false_of_ne_now _ hrow
    have hzeroMem : 0 ∉ quittingQuitters (fun player =>
        actionCurrent (choices player)) := by
      simpa [quittingQuitters] using hzeroCurrent
    simp [reward, hzeroMem, honeMem]

theorem column_now_value_of_row_now_mass_zero
    (mixed : Player → PMF Action) (hrow : mixed 0 now = 0) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update mixed 1 (PMF.pure now)) 1 = -1 := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [← actionTime_two]
  let deviated := Function.update mixed 1 (PMF.pure now)
  change Math.Probability.expect (pmfPi deviated)
      (fun choices => purePayoff reward 2 choices 1) = -1
  calc
    _ = Math.Probability.expect (pmfPi deviated) (fun _ => -1) := by
      apply Math.ProbabilityMassFunction.expect_congr_on_support
      intro choices hchoices
      have hcolumnMarginal : deviated 1 = PMF.pure now := by
        simp only [deviated, Function.update_self]
      have hcolumnChoice := eq_of_mem_support_pmfPi_of_marginal_eq_pure
        deviated choices hchoices 1 now hcolumnMarginal
      have hrowMass : deviated 0 now = 0 := by
        simp only [deviated,
          Function.update_of_ne (by decide : (0 : Player) ≠ 1), hrow]
      have hrowChoice := ne_of_mem_support_pmfPi_of_marginal_eq_zero
        deviated choices hchoices 0 now hrowMass
      rw [pure_column_now_value choices hcolumnChoice, if_neg hrowChoice]
    _ = -1 := Math.Probability.expect_const _ _

theorem row_now_mass_eq_zero_of_column_pure_now
    (mixed : Player → PMF Action)
    (hnash : (quittingTwoDateTimingGame reward).mixedExtension.IsNash mixed)
    (hcolumn : mixed 1 = PMF.pure now) : mixed 0 now = 0 := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  letI : ∀ player, Finite
      ((quittingTwoDateTimingGame reward).Strategy player) := fun _ => by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  have hgainNext := ((quittingTwoDateTimingGame reward).isNash_iff_gains_nonpos
    mixed).mp hnash 0 next
  unfold KernelGame.mixedGain at hgainNext
  rw [row_deviation_value_of_column_pure_now mixed hcolumn next,
    if_neg (by decide : next ≠ now)] at hgainNext
  have hpayoffLe := mixed_payoff_le_one mixed 0
  have hpayoff :
      (quittingTwoDateTimingGame reward).mixedExtension.eu mixed 0 = 1 := by
    linarith
  by_contra hmass
  have hsupport := mixedGain_eq_zero_of_mem_support
    (quittingTwoDateTimingGame reward) mixed hnash 0 now hmass
  unfold KernelGame.mixedGain at hsupport
  rw [row_deviation_value_of_column_pure_now mixed hcolumn now,
    if_pos rfl, hpayoff] at hsupport
  norm_num at hsupport

theorem column_payoff_eq_neg_one_of_column_pure_now
    (mixed : Player → PMF Action) (hcolumn : mixed 1 = PMF.pure now)
    (hrow : mixed 0 now = 0) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu mixed 1 = -1 := by
  have hupdate : Function.update mixed 1 (PMF.pure now) = mixed := by
    funext player
    by_cases hplayer : player = 1
    · subst player
      rw [Function.update_self, hcolumn]
    · rw [Function.update_of_ne hplayer]
  have hvalue := column_now_value_of_row_now_mass_zero mixed hrow
  have heq := congrArg (fun profile : Player → PMF Action =>
    (quittingTwoDateTimingGame reward).mixedExtension.eu profile 1) hupdate
  exact heq.symm.trans hvalue

private theorem current_empty_of_all_ne_now (choices : Player → Action)
    (hall : ∀ player, choices player ≠ now) :
    ¬(quittingQuitters fun player =>
      actionCurrent (choices player)).Nonempty := by
  rw [quittingQuitters_nonempty_iff]
  rintro ⟨player, hcurrent⟩
  exact hall player ((actionCurrent_eq_true_iff _).mp hcurrent)

private theorem pure_column_next_value_of_no_dummy_now
    (rowAction dummyTwo dummyThree : Action)
    (htwo : dummyTwo ≠ now) (hthree : dummyThree ≠ now) :
    purePayoff reward 2 ![rowAction, next, dummyTwo, dummyThree] 1 =
      if rowAction = next then 1 else -1 := by
  cases rowAction with
  | none =>
      change purePayoff reward 2 ![never, next, dummyTwo, dummyThree] 1 =
        (if never = next then 1 else -1)
      rw [if_neg (by decide : never ≠ next)]
      have hcurrent := current_empty_of_all_ne_now
        ![never, next, dummyTwo, dummyThree] (by
          intro player
          fin_cases player
          · change never ≠ now
            decide
          · change next ≠ now
            decide
          · exact htwo
          · exact hthree)
      rw [purePayoff_succ_of_current_empty reward 1 _ 1 hcurrent]
      have hone : 1 ∈ quittingQuitters (fun player => actionCurrent
          (choicesTail ![never, next, dummyTwo, dummyThree] player)) := by
        simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
          true_and]
        change actionCurrent (actionTail next) = true
        decide
      rw [purePayoff_succ_of_current_nonempty reward 0 _ 1 ⟨1, hone⟩]
      have hzero : 0 ∉ quittingQuitters (fun player => actionCurrent
          (choicesTail ![never, next, dummyTwo, dummyThree] player)) := by
        simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
          true_and]
        change actionCurrent (actionTail never) ≠ true
        decide
      simp [reward, hzero, hone]
  | some rowTime =>
      fin_cases rowTime
      · change purePayoff reward 2 ![now, next, dummyTwo, dummyThree] 1 =
          (if now = next then 1 else -1)
        rw [if_neg (by decide : now ≠ next)]
        have hcurrent : (quittingQuitters fun player =>
            actionCurrent (![now, next, dummyTwo, dummyThree] player)).Nonempty :=
          ⟨0, by simp [quittingQuitters, actionCurrent, now]⟩
        rw [purePayoff_succ_of_current_nonempty reward 1 _ 1 hcurrent]
        have hzero : 0 ∈ quittingQuitters (fun player =>
            actionCurrent (![now, next, dummyTwo, dummyThree] player)) := by
          simp [quittingQuitters, actionCurrent, now]
        have hone : 1 ∉ quittingQuitters (fun player =>
            actionCurrent (![now, next, dummyTwo, dummyThree] player)) := by
          simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
            true_and]
          change actionCurrent next ≠ true
          decide
        simp [reward, hzero, hone]
      · change purePayoff reward 2 ![next, next, dummyTwo, dummyThree] 1 =
          (if next = next then 1 else -1)
        rw [if_pos rfl]
        have hcurrent := current_empty_of_all_ne_now
          ![next, next, dummyTwo, dummyThree] (by
            intro player
            fin_cases player
            · change next ≠ now
              decide
            · change next ≠ now
              decide
            · exact htwo
            · exact hthree)
        rw [purePayoff_succ_of_current_empty reward 1 _ 1 hcurrent]
        have hzero : 0 ∈ quittingQuitters (fun player => actionCurrent
            (choicesTail ![next, next, dummyTwo, dummyThree] player)) := by
          simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
            true_and]
          change actionCurrent (actionTail next) = true
          decide
        have hone : 1 ∈ quittingQuitters (fun player => actionCurrent
            (choicesTail ![next, next, dummyTwo, dummyThree] player)) := by
          simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
            true_and]
          change actionCurrent (actionTail next) = true
          decide
        rw [purePayoff_succ_of_current_nonempty reward 0 _ 1 ⟨1, hone⟩]
        simp [reward, hzero, hone]

private theorem pure_column_never_value_of_no_dummy_now
    (rowAction dummyTwo dummyThree : Action)
    (htwo : dummyTwo ≠ now) (hthree : dummyThree ≠ now) :
    purePayoff reward 2 ![rowAction, never, dummyTwo, dummyThree] 1 =
      if rowAction = never then 0 else -1 := by
  cases rowAction with
  | none =>
      change purePayoff reward 2 ![never, never, dummyTwo, dummyThree] 1 =
        (if never = never then 0 else -1)
      rw [if_pos rfl]
      have hcurrent := current_empty_of_all_ne_now
        ![never, never, dummyTwo, dummyThree] (by
          intro player
          fin_cases player
          · change never ≠ now
            decide
          · change never ≠ now
            decide
          · exact htwo
          · exact hthree)
      rw [purePayoff_succ_of_current_empty reward 1 _ 1 hcurrent]
      rw [purePayoff_succ]
      unfold quittingRootPayoff
      split
      case isTrue htail =>
        have hzero : 0 ∉ quittingQuitters (fun player => actionCurrent
            (choicesTail ![never, never, dummyTwo, dummyThree] player)) := by
          simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
            true_and]
          change actionCurrent (actionTail never) ≠ true
          decide
        have hone : 1 ∉ quittingQuitters (fun player => actionCurrent
            (choicesTail ![never, never, dummyTwo, dummyThree] player)) := by
          simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
            true_and]
          change actionCurrent (actionTail never) ≠ true
          decide
        simp [reward, hzero, hone]
      case isFalse htail => exact purePayoff_zero reward _ 1
  | some rowTime =>
      fin_cases rowTime
      · change purePayoff reward 2 ![now, never, dummyTwo, dummyThree] 1 =
          (if now = never then 0 else -1)
        rw [if_neg (by decide : now ≠ never)]
        have hcurrent : (quittingQuitters fun player =>
            actionCurrent (![now, never, dummyTwo, dummyThree] player)).Nonempty :=
          ⟨0, by simp [quittingQuitters, actionCurrent, now]⟩
        rw [purePayoff_succ_of_current_nonempty reward 1 _ 1 hcurrent]
        have hzero : 0 ∈ quittingQuitters (fun player =>
            actionCurrent (![now, never, dummyTwo, dummyThree] player)) := by
          simp [quittingQuitters, actionCurrent, now]
        have hone : 1 ∉ quittingQuitters (fun player =>
            actionCurrent (![now, never, dummyTwo, dummyThree] player)) := by
          simp [quittingQuitters, actionCurrent, never]
        simp [reward, hzero, hone]
      · change purePayoff reward 2 ![next, never, dummyTwo, dummyThree] 1 =
          (if next = never then 0 else -1)
        rw [if_neg (by decide : next ≠ never)]
        have hcurrent := current_empty_of_all_ne_now
          ![next, never, dummyTwo, dummyThree] (by
            intro player
            fin_cases player
            · change next ≠ now
              decide
            · change never ≠ now
              decide
            · exact htwo
            · exact hthree)
        rw [purePayoff_succ_of_current_empty reward 1 _ 1 hcurrent]
        have hzero : 0 ∈ quittingQuitters (fun player => actionCurrent
            (choicesTail ![next, never, dummyTwo, dummyThree] player)) := by
          simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
            true_and]
          change actionCurrent (actionTail next) = true
          decide
        have hone : 1 ∉ quittingQuitters (fun player => actionCurrent
            (choicesTail ![next, never, dummyTwo, dummyThree] player)) := by
          simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
            true_and]
          change actionCurrent (actionTail never) ≠ true
          decide
        rw [purePayoff_succ_of_current_nonempty reward 0 _ 1 ⟨0, hzero⟩]
        simp [reward, hzero, hone]

theorem column_next_value_of_no_current_mass
    (mixed : Player → PMF Action)
    (htwo : mixed 2 now = 0)
    (hthree : mixed 3 now = 0) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update mixed 1 (PMF.pure next)) 1 =
      2 * mass (mixed 0) next - 1 := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [← actionTime_two]
  let deviated := Function.update mixed 1 (PMF.pure next)
  change Math.Probability.expect (pmfPi deviated)
      (fun choices => purePayoff reward 2 choices 1) = _
  have hintegrand : Math.Probability.expect (pmfPi deviated)
      (fun choices => purePayoff reward 2 choices 1) =
      Math.Probability.expect (pmfPi deviated)
        (fun choices => if choices 0 = next then 1 else -1) := by
    apply Math.ProbabilityMassFunction.expect_congr_on_support
    intro choices hchoices
    have hcolumnMarginal : deviated 1 = PMF.pure next := by
      simp only [deviated, Function.update_self]
    have hcolumnChoice := eq_of_mem_support_pmfPi_of_marginal_eq_pure
      deviated choices hchoices 1 next hcolumnMarginal
    have htwoMass : deviated 2 now = 0 := by
      simp only [deviated,
        Function.update_of_ne (by decide : (2 : Player) ≠ 1), htwo]
    have htwoChoice := ne_of_mem_support_pmfPi_of_marginal_eq_zero
      deviated choices hchoices 2 now htwoMass
    have hthreeMass : deviated 3 now = 0 := by
      simp only [deviated,
        Function.update_of_ne (by decide : (3 : Player) ≠ 1), hthree]
    have hthreeChoice := ne_of_mem_support_pmfPi_of_marginal_eq_zero
      deviated choices hchoices 3 now hthreeMass
    have hchoicesEq : choices =
        ![choices 0, next, choices 2, choices 3] := by
      funext player
      fin_cases player <;> simp [hcolumnChoice]
    rw [hchoicesEq]
    exact pure_column_next_value_of_no_dummy_now
      (choices 0) (choices 2) (choices 3) htwoChoice hthreeChoice
  rw [hintegrand, expect_pmfPi_fin4]
  simp only [deviated,
    Function.update_of_ne (by decide : (0 : Player) ≠ 1)]
  rw [Math.Probability.expect_eq_sum, Fintype.sum_option,
    Fin.sum_univ_two]
  rw [show (some (0 : Fin 2) : Action) = now by rfl,
    show (some (1 : Fin 2) : Action) = next by rfl]
  have hsum := Math.Probability.pmf_toReal_sum_one (mixed 0)
  rw [Fintype.sum_option, Fin.sum_univ_two] at hsum
  dsimp only [mass]
  simp [now, next] at ⊢
  linarith

theorem column_never_value_of_no_current_mass
    (mixed : Player → PMF Action)
    (htwo : mixed 2 now = 0)
    (hthree : mixed 3 now = 0) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update mixed 1 (PMF.pure never)) 1 =
      mass (mixed 0) never - 1 := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [← actionTime_two]
  let deviated := Function.update mixed 1 (PMF.pure never)
  change Math.Probability.expect (pmfPi deviated)
      (fun choices => purePayoff reward 2 choices 1) = _
  have hintegrand : Math.Probability.expect (pmfPi deviated)
      (fun choices => purePayoff reward 2 choices 1) =
      Math.Probability.expect (pmfPi deviated)
        (fun choices => if choices 0 = never then 0 else -1) := by
    apply Math.ProbabilityMassFunction.expect_congr_on_support
    intro choices hchoices
    have hcolumnMarginal : deviated 1 = PMF.pure never := by
      simp only [deviated, Function.update_self]
    have hcolumnChoice := eq_of_mem_support_pmfPi_of_marginal_eq_pure
      deviated choices hchoices 1 never hcolumnMarginal
    have htwoMass : deviated 2 now = 0 := by
      simp only [deviated,
        Function.update_of_ne (by decide : (2 : Player) ≠ 1), htwo]
    have htwoChoice := ne_of_mem_support_pmfPi_of_marginal_eq_zero
      deviated choices hchoices 2 now htwoMass
    have hthreeMass : deviated 3 now = 0 := by
      simp only [deviated,
        Function.update_of_ne (by decide : (3 : Player) ≠ 1), hthree]
    have hthreeChoice := ne_of_mem_support_pmfPi_of_marginal_eq_zero
      deviated choices hchoices 3 now hthreeMass
    have hchoicesEq : choices =
        ![choices 0, never, choices 2, choices 3] := by
      funext player
      fin_cases player <;> simp [hcolumnChoice]
    rw [hchoicesEq]
    exact pure_column_never_value_of_no_dummy_now
      (choices 0) (choices 2) (choices 3) htwoChoice hthreeChoice
  rw [hintegrand, expect_pmfPi_fin4]
  simp only [deviated,
    Function.update_of_ne (by decide : (0 : Player) ≠ 1)]
  rw [Math.Probability.expect_eq_sum, Fintype.sum_option,
    Fin.sum_univ_two]
  rw [show (some (0 : Fin 2) : Action) = now by rfl,
    show (some (1 : Fin 2) : Action) = next by rfl]
  have hsum := Math.Probability.pmf_toReal_sum_one (mixed 0)
  rw [Fintype.sum_option, Fin.sum_univ_two] at hsum
  dsimp only [mass]
  simp [never, now, next] at ⊢
  linarith

theorem column_not_pure_now
    (mixed : Player → PMF Action)
    (hnash : (quittingTwoDateTimingGame reward).mixedExtension.IsNash mixed) :
    mixed 1 ≠ PMF.pure now := by
  intro hcolumn
  have hrow := row_now_mass_eq_zero_of_column_pure_now mixed hnash hcolumn
  have htwo := dummy_now_mass_eq_zero mixed hnash 2 (by decide) (by decide)
  have hthree := dummy_now_mass_eq_zero mixed hnash 3 (by decide) (by decide)
  have hpayoff :=
    column_payoff_eq_neg_one_of_column_pure_now mixed hcolumn hrow
  have hgainNext := hnash 1 (PMF.pure next)
  rw [column_next_value_of_no_current_mass mixed htwo hthree,
    hpayoff] at hgainNext
  have hnextNonneg : 0 ≤ mass (mixed 0) next := ENNReal.toReal_nonneg
  have hnext : mass (mixed 0) next = 0 := by linarith
  have hgainNever := hnash 1 (PMF.pure never)
  rw [column_never_value_of_no_current_mass mixed htwo hthree,
    hpayoff] at hgainNever
  have hneverNonneg : 0 ≤ mass (mixed 0) never := ENNReal.toReal_nonneg
  have hnever : mass (mixed 0) never = 0 := by linarith
  have hsum := Math.Probability.pmf_toReal_sum_one (mixed 0)
  rw [Fintype.sum_option, Fin.sum_univ_two] at hsum
  rw [show (none : Action) = never by rfl,
    show (some (0 : Fin 2) : Action) = now by rfl,
    show (some (1 : Fin 2) : Action) = next by rfl] at hsum
  dsimp only [mass] at hnext hnever
  rw [hrow, hnext, hnever] at hsum
  simp at hsum

private theorem dummy_two_current_nonempty_iff_of_other_ne_now
    (rowAction columnAction otherAction : Action)
    (hother : otherAction ≠ now) :
    (quittingQuitters fun player => actionCurrent
        (![rowAction, columnAction, next, otherAction] player)).Nonempty ↔
      rowAction = now ∨ columnAction = now := by
  rw [quittingQuitters_nonempty_iff]
  constructor
  · rintro ⟨player, hplayer⟩
    fin_cases player
    · exact Or.inl ((actionCurrent_eq_true_iff rowAction).mp hplayer)
    · exact Or.inr ((actionCurrent_eq_true_iff columnAction).mp hplayer)
    · exact False.elim ((by decide : actionCurrent next ≠ true) hplayer)
    · exact False.elim (hother ((actionCurrent_eq_true_iff _).mp hplayer))
  · rintro (hrow | hcolumn)
    · exact ⟨0, by simp [hrow, actionCurrent, now]⟩
    · exact ⟨1, by simp [hcolumn, actionCurrent, now]⟩

private theorem pure_dummy_two_next_value_of_other_ne_now
    (rowAction columnAction otherAction : Action)
    (hother : otherAction ≠ now) :
    purePayoff reward 2 ![rowAction, columnAction, next, otherAction] 2 =
      if rowAction = now ∨ columnAction = now then 0 else -1 := by
  rw [purePayoff_succ]
  unfold quittingRootPayoff
  split
  case isTrue hcurrent =>
    rw [if_pos ((dummy_two_current_nonempty_iff_of_other_ne_now
      rowAction columnAction otherAction hother).mp hcurrent)]
    simp only [reward, if_neg (by decide : (2 : Player) ≠ 0),
      if_neg (by decide : (2 : Player) ≠ 1)]
    rw [if_neg]
    have hfun : (fun player => actionCurrent
        (![rowAction, columnAction, next, otherAction] player)) =
        ![actionCurrent rowAction, actionCurrent columnAction,
          actionCurrent next, actionCurrent otherAction] := by
      funext player
      fin_cases player <;> rfl
    rw [hfun]
    have hnext : actionCurrent next = false := by decide
    have hotherCurrent := actionCurrent_eq_false_of_ne_now _ hother
    rw [hnext, hotherCurrent]
    cases hrow : actionCurrent rowAction <;>
      cases hcolumn : actionCurrent columnAction <;>
        simp [quittingQuitters_vec4]
  case isFalse hcurrent =>
    rw [if_neg (not_congr (dummy_two_current_nonempty_iff_of_other_ne_now
      rowAction columnAction otherAction hother) |>.mp hcurrent)]
    change purePayoff reward 1
      (choicesTail ![rowAction, columnAction, next, otherAction]) 2 = -1
    have htwo : 2 ∈ quittingQuitters (fun player => actionCurrent
        (choicesTail ![rowAction, columnAction, next, otherAction] player)) := by
      simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
        true_and]
      change actionCurrent (actionTail next) = true
      decide
    rw [purePayoff_succ_of_current_nonempty reward 0 _ 2 ⟨2, htwo⟩]
    simp only [reward, if_neg (by decide : (2 : Player) ≠ 0),
      if_neg (by decide : (2 : Player) ≠ 1), if_pos htwo]

theorem dummy_two_next_payoff
    (mixed : Player → PMF Action) (hother : mixed 3 now = 0) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update mixed 2 (PMF.pure next)) 2 =
      -(1 - mass (mixed 0) now) * (1 - mass (mixed 1) now) := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [← actionTime_two]
  let deviated := Function.update mixed 2 (PMF.pure next)
  change Math.Probability.expect (pmfPi deviated)
      (fun choices => purePayoff reward 2 choices 2) = _
  have hintegrand : Math.Probability.expect (pmfPi deviated)
      (fun choices => purePayoff reward 2 choices 2) =
      Math.Probability.expect (pmfPi deviated) (fun choices =>
        if choices 0 = now ∨ choices 1 = now then 0 else -1) := by
    apply Math.ProbabilityMassFunction.expect_congr_on_support
    intro choices hchoices
    have hdummyMarginal : deviated 2 = PMF.pure next := by
      simp only [deviated, Function.update_self]
    have hdummyChoice := eq_of_mem_support_pmfPi_of_marginal_eq_pure
      deviated choices hchoices 2 next hdummyMarginal
    have hotherMass : deviated 3 now = 0 := by
      simp only [deviated,
        Function.update_of_ne (by decide : (3 : Player) ≠ 2), hother]
    have hotherChoice := ne_of_mem_support_pmfPi_of_marginal_eq_zero
      deviated choices hchoices 3 now hotherMass
    have hchoicesEq : choices =
        ![choices 0, choices 1, next, choices 3] := by
      funext player
      fin_cases player <;> simp [hdummyChoice]
    rw [hchoicesEq]
    exact pure_dummy_two_next_value_of_other_ne_now
      (choices 0) (choices 1) (choices 3) hotherChoice
  rw [hintegrand, expect_pmfPi_fin4]
  simp only [deviated,
    Function.update_of_ne (by decide : (0 : Player) ≠ 2),
    Function.update_of_ne (by decide : (1 : Player) ≠ 2),
    Function.update_self, Math.Probability.expect_pure,
    Function.update_of_ne (by decide : (3 : Player) ≠ 2)]
  simp [Math.Probability.expect_eq_sum, Fintype.sum_option,
    Fin.sum_univ_two, now]
  have hrowSum := Math.Probability.pmf_toReal_sum_one (mixed 0)
  have hcolumnSum := Math.Probability.pmf_toReal_sum_one (mixed 1)
  have hotherSum := Math.Probability.pmf_toReal_sum_one (mixed 3)
  rw [Fintype.sum_option, Fin.sum_univ_two] at hrowSum hcolumnSum hotherSum
  dsimp only [mass]
  have hrowNone : ((mixed 0) none).toReal =
      1 - ((mixed 0) (some 0)).toReal - ((mixed 0) (some 1)).toReal := by
    linarith
  have hcolumnNone : ((mixed 1) none).toReal =
      1 - ((mixed 1) (some 0)).toReal - ((mixed 1) (some 1)).toReal := by
    linarith
  have hotherNone : ((mixed 3) none).toReal =
      1 - ((mixed 3) (some 0)).toReal - ((mixed 3) (some 1)).toReal := by
    linarith
  rw [hrowNone, hcolumnNone, hotherNone]
  ring

private theorem dummy_three_current_nonempty_iff_of_other_ne_now
    (rowAction columnAction otherAction : Action)
    (hother : otherAction ≠ now) :
    (quittingQuitters fun player => actionCurrent
        (![rowAction, columnAction, otherAction, next] player)).Nonempty ↔
      rowAction = now ∨ columnAction = now := by
  rw [quittingQuitters_nonempty_iff]
  constructor
  · rintro ⟨player, hplayer⟩
    fin_cases player
    · exact Or.inl ((actionCurrent_eq_true_iff rowAction).mp hplayer)
    · exact Or.inr ((actionCurrent_eq_true_iff columnAction).mp hplayer)
    · exact False.elim (hother ((actionCurrent_eq_true_iff _).mp hplayer))
    · exact False.elim ((by decide : actionCurrent next ≠ true) hplayer)
  · rintro (hrow | hcolumn)
    · exact ⟨0, by simp [hrow, actionCurrent, now]⟩
    · exact ⟨1, by simp [hcolumn, actionCurrent, now]⟩

private theorem pure_dummy_three_next_value_of_other_ne_now
    (rowAction columnAction otherAction : Action)
    (hother : otherAction ≠ now) :
    purePayoff reward 2 ![rowAction, columnAction, otherAction, next] 3 =
      if rowAction = now ∨ columnAction = now then 0 else -1 := by
  rw [purePayoff_succ]
  unfold quittingRootPayoff
  split
  case isTrue hcurrent =>
    rw [if_pos ((dummy_three_current_nonempty_iff_of_other_ne_now
      rowAction columnAction otherAction hother).mp hcurrent)]
    simp only [reward, if_neg (by decide : (3 : Player) ≠ 0),
      if_neg (by decide : (3 : Player) ≠ 1)]
    rw [if_neg]
    have hfun : (fun player => actionCurrent
        (![rowAction, columnAction, otherAction, next] player)) =
        ![actionCurrent rowAction, actionCurrent columnAction,
          actionCurrent otherAction, actionCurrent next] := by
      funext player
      fin_cases player <;> rfl
    rw [hfun]
    have hnext : actionCurrent next = false := by decide
    have hotherCurrent := actionCurrent_eq_false_of_ne_now _ hother
    rw [hnext, hotherCurrent]
    cases hrow : actionCurrent rowAction <;>
      cases hcolumn : actionCurrent columnAction <;>
        simp [quittingQuitters_vec4]
  case isFalse hcurrent =>
    rw [if_neg (not_congr (dummy_three_current_nonempty_iff_of_other_ne_now
      rowAction columnAction otherAction hother) |>.mp hcurrent)]
    change purePayoff reward 1
      (choicesTail ![rowAction, columnAction, otherAction, next]) 3 = -1
    have hthree : 3 ∈ quittingQuitters (fun player => actionCurrent
        (choicesTail ![rowAction, columnAction, otherAction, next] player)) := by
      simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
        true_and]
      change actionCurrent (actionTail next) = true
      decide
    rw [purePayoff_succ_of_current_nonempty reward 0 _ 3 ⟨3, hthree⟩]
    simp only [reward, if_neg (by decide : (3 : Player) ≠ 0),
      if_neg (by decide : (3 : Player) ≠ 1), if_pos hthree]

theorem dummy_three_next_payoff
    (mixed : Player → PMF Action) (hother : mixed 2 now = 0) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update mixed 3 (PMF.pure next)) 3 =
      -(1 - mass (mixed 0) now) * (1 - mass (mixed 1) now) := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [← actionTime_two]
  let deviated := Function.update mixed 3 (PMF.pure next)
  change Math.Probability.expect (pmfPi deviated)
      (fun choices => purePayoff reward 2 choices 3) = _
  have hintegrand : Math.Probability.expect (pmfPi deviated)
      (fun choices => purePayoff reward 2 choices 3) =
      Math.Probability.expect (pmfPi deviated) (fun choices =>
        if choices 0 = now ∨ choices 1 = now then 0 else -1) := by
    apply Math.ProbabilityMassFunction.expect_congr_on_support
    intro choices hchoices
    have hdummyMarginal : deviated 3 = PMF.pure next := by
      simp only [deviated, Function.update_self]
    have hdummyChoice := eq_of_mem_support_pmfPi_of_marginal_eq_pure
      deviated choices hchoices 3 next hdummyMarginal
    have hotherMass : deviated 2 now = 0 := by
      simp only [deviated,
        Function.update_of_ne (by decide : (2 : Player) ≠ 3), hother]
    have hotherChoice := ne_of_mem_support_pmfPi_of_marginal_eq_zero
      deviated choices hchoices 2 now hotherMass
    have hchoicesEq : choices =
        ![choices 0, choices 1, choices 2, next] := by
      funext player
      fin_cases player <;> simp [hdummyChoice]
    rw [hchoicesEq]
    exact pure_dummy_three_next_value_of_other_ne_now
      (choices 0) (choices 1) (choices 2) hotherChoice
  rw [hintegrand, expect_pmfPi_fin4]
  simp only [deviated,
    Function.update_of_ne (by decide : (0 : Player) ≠ 3),
    Function.update_of_ne (by decide : (1 : Player) ≠ 3),
    Function.update_of_ne (by decide : (2 : Player) ≠ 3),
    Function.update_self, Math.Probability.expect_pure]
  simp [Math.Probability.expect_eq_sum, Fintype.sum_option,
    Fin.sum_univ_two, now]
  have hrowSum := Math.Probability.pmf_toReal_sum_one (mixed 0)
  have hcolumnSum := Math.Probability.pmf_toReal_sum_one (mixed 1)
  have hotherSum := Math.Probability.pmf_toReal_sum_one (mixed 2)
  rw [Fintype.sum_option, Fin.sum_univ_two] at hrowSum hcolumnSum hotherSum
  dsimp only [mass]
  have hrowNone : ((mixed 0) none).toReal =
      1 - ((mixed 0) (some 0)).toReal - ((mixed 0) (some 1)).toReal := by
    linarith
  have hcolumnNone : ((mixed 1) none).toReal =
      1 - ((mixed 1) (some 0)).toReal - ((mixed 1) (some 1)).toReal := by
    linarith
  have hotherNone : ((mixed 2) none).toReal =
      1 - ((mixed 2) (some 0)).toReal - ((mixed 2) (some 1)).toReal := by
    linarith
  rw [hrowNone, hcolumnNone, hotherNone]
  ring

private theorem pmf_eq_pure_of_apply_eq_one (law : PMF Action)
    (action : Action) (hmass : law action = 1) :
    law = PMF.pure action := by
  have hsupport : law.support = {action} :=
    (PMF.apply_eq_one_iff law action).mp hmass
  apply PMF.ext
  intro choice
  by_cases hchoice : choice = action
  · subst choice
    rw [hmass, PMF.pure_apply_self]
  · have hzero : law choice = 0 :=
      (PMF.apply_eq_zero_iff law choice).mpr (by
        rw [hsupport]
        simpa using hchoice)
    rw [hzero, PMF.pure_apply, if_neg hchoice]

private theorem mass_lt_one_of_ne_pure (law : PMF Action)
    (action : Action) (hne : law ≠ PMF.pure action) :
    mass law action < 1 := by
  have hle : mass law action ≤ 1 := by
    exact (ENNReal.toReal_le_toReal (PMF.apply_ne_top law action)
      (by norm_num)).2 (PMF.coe_le_one law action)
  apply lt_of_le_of_ne hle
  intro heq
  apply hne
  apply pmf_eq_pure_of_apply_eq_one law action
  exact (ENNReal.toReal_eq_one_iff (law action)).mp heq

theorem dummy_two_next_mass_eq_zero
    (mixed : Player → PMF Action)
    (hnash : (quittingTwoDateTimingGame reward).mixedExtension.IsNash mixed) :
    mixed 2 next = 0 := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  letI : ∀ player, Finite
      ((quittingTwoDateTimingGame reward).Strategy player) := fun _ => by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  have hother := dummy_now_mass_eq_zero mixed hnash 3 (by decide) (by decide)
  have hrowLt := mass_lt_one_of_ne_pure (mixed 0) now
    (row_not_pure_now mixed hnash)
  have hcolumnLt := mass_lt_one_of_ne_pure (mixed 1) now
    (column_not_pure_now mixed hnash)
  have hnextValue := dummy_two_next_payoff mixed hother
  have hnextNegative :
      (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update mixed 2 (PMF.pure next)) 2 < 0 := by
    rw [hnextValue]
    have hfirst : 0 < 1 - mass (mixed 0) now := sub_pos.mpr hrowLt
    have hsecond : 0 < 1 - mass (mixed 1) now := sub_pos.mpr hcolumnLt
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hfirst) hsecond
  by_contra hmass
  have hsupport := mixedGain_eq_zero_of_mem_support
    (quittingTwoDateTimingGame reward) mixed hnash 2 next hmass
  have hnever := ((quittingTwoDateTimingGame reward).isNash_iff_gains_nonpos
    mixed).mp hnash 2 never
  unfold KernelGame.mixedGain at hsupport hnever
  rw [dummy_never_payoff mixed 2 (by decide) (by decide)] at hnever
  linarith

theorem dummy_three_next_mass_eq_zero
    (mixed : Player → PMF Action)
    (hnash : (quittingTwoDateTimingGame reward).mixedExtension.IsNash mixed) :
    mixed 3 next = 0 := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  letI : ∀ player, Finite
      ((quittingTwoDateTimingGame reward).Strategy player) := fun _ => by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  have hother := dummy_now_mass_eq_zero mixed hnash 2 (by decide) (by decide)
  have hrowLt := mass_lt_one_of_ne_pure (mixed 0) now
    (row_not_pure_now mixed hnash)
  have hcolumnLt := mass_lt_one_of_ne_pure (mixed 1) now
    (column_not_pure_now mixed hnash)
  have hnextValue := dummy_three_next_payoff mixed hother
  have hnextNegative :
      (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update mixed 3 (PMF.pure next)) 3 < 0 := by
    rw [hnextValue]
    have hfirst : 0 < 1 - mass (mixed 0) now := sub_pos.mpr hrowLt
    have hsecond : 0 < 1 - mass (mixed 1) now := sub_pos.mpr hcolumnLt
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hfirst) hsecond
  by_contra hmass
  have hsupport := mixedGain_eq_zero_of_mem_support
    (quittingTwoDateTimingGame reward) mixed hnash 3 next hmass
  have hnever := ((quittingTwoDateTimingGame reward).isNash_iff_gains_nonpos
    mixed).mp hnash 3 never
  unfold KernelGame.mixedGain at hsupport hnever
  rw [dummy_never_payoff mixed 3 (by decide) (by decide)] at hnever
  linarith

private theorem pmf_eq_pure_never_of_now_next_eq_zero (law : PMF Action)
    (hnow : law now = 0) (hnext : law next = 0) :
    law = PMF.pure never := by
  have hsum := Math.Probability.pmf_toReal_sum_one law
  rw [Fintype.sum_option, Fin.sum_univ_two] at hsum
  rw [show (none : Action) = never by rfl,
    show (some (0 : Fin 2) : Action) = now by rfl,
    show (some (1 : Fin 2) : Action) = next by rfl,
    hnow, hnext] at hsum
  simp at hsum
  apply pmf_eq_pure_of_apply_eq_one law never
  exact (ENNReal.toReal_eq_one_iff (law never)).mp hsum

theorem dummy_two_eq_pure_never
    (mixed : Player → PMF Action)
    (hnash : (quittingTwoDateTimingGame reward).mixedExtension.IsNash mixed) :
    mixed 2 = PMF.pure never := by
  apply pmf_eq_pure_never_of_now_next_eq_zero
  · exact dummy_now_mass_eq_zero mixed hnash 2 (by decide) (by decide)
  · exact dummy_two_next_mass_eq_zero mixed hnash

theorem dummy_three_eq_pure_never
    (mixed : Player → PMF Action)
    (hnash : (quittingTwoDateTimingGame reward).mixedExtension.IsNash mixed) :
    mixed 3 = PMF.pure never := by
  apply pmf_eq_pure_never_of_now_next_eq_zero
  · exact dummy_now_mass_eq_zero mixed hnash 3 (by decide) (by decide)
  · exact dummy_three_next_mass_eq_zero mixed hnash

private theorem law_eq_equilibriumLaw_of_masses
    (law : PMF Action)
    (hnow : mass law now = 1 / 4)
    (hnext : mass law next = 1 / 4)
    (hnever : mass law never = 1 / 2) :
    law = equilibriumLaw := by
  apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
  intro action
  cases action with
  | none =>
      change mass law never = mass equilibriumLaw never
      rw [hnever, equilibriumLaw_never]
  | some time =>
      fin_cases time
      · change mass law now = mass equilibriumLaw now
        rw [hnow, equilibriumLaw_now]
      · change mass law next = mass equilibriumLaw next
        rw [hnext, equilibriumLaw_next]

theorem active_laws_eq_equilibriumLaw
    (mixed : Player → PMF Action)
    (hnash : (quittingTwoDateTimingGame reward).mixedExtension.IsNash mixed) :
    mixed 0 = equilibriumLaw ∧ mixed 1 = equilibriumLaw := by
  have htwo := dummy_two_eq_pure_never mixed hnash
  have hthree := dummy_three_eq_pure_never mixed hnash
  have hprofile : mixed = activeProfile (mixed 0) (mixed 1) := by
    funext who
    fin_cases who <;> simp [activeProfile, htwo, hthree, never]
  have hnashActive :
      (quittingTwoDateTimingGame reward).mixedExtension.IsNash
        (activeProfile (mixed 0) (mixed 1)) := by
    rw [← hprofile]
    exact hnash
  let u := (quittingTwoDateTimingGame reward).mixedExtension.eu
    (activeProfile (mixed 0) (mixed 1)) 0
  have hrowNow := hnashActive 0 (PMF.pure now)
  have hrowNext := hnashActive 0 (PMF.pure next)
  have hrowNever := hnashActive 0 (PMF.pure never)
  rw [row_now_value] at hrowNow
  rw [row_next_value] at hrowNext
  rw [row_never_value] at hrowNever
  change 1 - 2 * mass (mixed 1) now ≤ u at hrowNow
  change 1 - 2 * mass (mixed 1) next ≤ u at hrowNext
  change 1 - mass (mixed 1) never ≤ u at hrowNever
  have hcolumnNow := hnashActive 1 (PMF.pure now)
  have hcolumnNext := hnashActive 1 (PMF.pure next)
  have hcolumnNever := hnashActive 1 (PMF.pure never)
  rw [column_now_value] at hcolumnNow
  rw [column_next_value] at hcolumnNext
  rw [column_never_value] at hcolumnNever
  have hzeroSum := mixedPayoff_one_eq_neg_zero
    (activeProfile (mixed 0) (mixed 1))
  change (quittingTwoDateTimingGame reward).mixedExtension.eu
      (activeProfile (mixed 0) (mixed 1)) 1 = -u at hzeroSum
  rw [hzeroSum] at hcolumnNow hcolumnNext hcolumnNever
  change 2 * mass (mixed 0) now - 1 ≤ -u at hcolumnNow
  change 2 * mass (mixed 0) next - 1 ≤ -u at hcolumnNext
  change mass (mixed 0) never - 1 ≤ -u at hcolumnNever
  have hrowSum := Math.Probability.pmf_toReal_sum_one (mixed 0)
  have hcolumnSum := Math.Probability.pmf_toReal_sum_one (mixed 1)
  rw [Fintype.sum_option, Fin.sum_univ_two] at hrowSum hcolumnSum
  rw [show (none : Action) = never by rfl,
    show (some (0 : Fin 2) : Action) = now by rfl,
    show (some (1 : Fin 2) : Action) = next by rfl] at hrowSum hcolumnSum
  change mass (mixed 0) never +
      (mass (mixed 0) now + mass (mixed 0) next) = 1 at hrowSum
  change mass (mixed 1) never +
      (mass (mixed 1) now + mass (mixed 1) next) = 1 at hcolumnSum
  have huLower : 1 / 2 ≤ u := by
    linarith only [hrowNow, hrowNext, hrowNever, hcolumnSum]
  have huUpper : u ≤ 1 / 2 := by
    linarith only [hcolumnNow, hcolumnNext, hcolumnNever, hrowSum]
  have hu : u = 1 / 2 := le_antisymm huUpper huLower
  have hcolumnNowLower : 1 / 4 ≤ mass (mixed 1) now := by
    linarith only [hrowNow, hu]
  have hcolumnNextLower : 1 / 4 ≤ mass (mixed 1) next := by
    linarith only [hrowNext, hu]
  have hcolumnNeverLower : 1 / 2 ≤ mass (mixed 1) never := by
    linarith only [hrowNever, hu]
  have hcolumnNowEq : mass (mixed 1) now = 1 / 4 := by
    linarith only [hcolumnNowLower, hcolumnNextLower,
      hcolumnNeverLower, hcolumnSum]
  have hcolumnNextEq : mass (mixed 1) next = 1 / 4 := by
    linarith only [hcolumnNowLower, hcolumnNextLower,
      hcolumnNeverLower, hcolumnSum]
  have hcolumnNeverEq : mass (mixed 1) never = 1 / 2 := by
    linarith only [hcolumnNowLower, hcolumnNextLower,
      hcolumnNeverLower, hcolumnSum]
  have hrowNowUpper : mass (mixed 0) now ≤ 1 / 4 := by
    linarith only [hcolumnNow, hu]
  have hrowNextUpper : mass (mixed 0) next ≤ 1 / 4 := by
    linarith only [hcolumnNext, hu]
  have hrowNeverUpper : mass (mixed 0) never ≤ 1 / 2 := by
    linarith only [hcolumnNever, hu]
  have hrowNowEq : mass (mixed 0) now = 1 / 4 := by
    linarith only [hrowNowUpper, hrowNextUpper, hrowNeverUpper, hrowSum]
  have hrowNextEq : mass (mixed 0) next = 1 / 4 := by
    linarith only [hrowNowUpper, hrowNextUpper, hrowNeverUpper, hrowSum]
  have hrowNeverEq : mass (mixed 0) never = 1 / 2 := by
    linarith only [hrowNowUpper, hrowNextUpper, hrowNeverUpper, hrowSum]
  exact ⟨law_eq_equilibriumLaw_of_masses _ hrowNowEq hrowNextEq hrowNeverEq,
    law_eq_equilibriumLaw_of_masses _
      hcolumnNowEq hcolumnNextEq hcolumnNeverEq⟩

/-- The canonical timing law is the unique mixed Nash equilibrium of the
two-date normal form, including the two strict-Continue dummy players. -/
theorem equilibriumProfile_isUniqueNash :
    ∃! mixed : Player → PMF Action,
      (quittingTwoDateTimingGame reward).mixedExtension.IsNash mixed := by
  refine ⟨equilibriumProfile, equilibriumProfile_isNash, ?_⟩
  intro mixed hnash
  obtain ⟨hzero, hone⟩ := active_laws_eq_equilibriumLaw mixed hnash
  have htwo := dummy_two_eq_pure_never mixed hnash
  have hthree := dummy_three_eq_pure_never mixed hnash
  funext who
  fin_cases who <;>
    simp only [equilibriumProfile, activeProfile] <;>
    assumption

theorem equilibriumProfile_terminalPayoff_zero :
    quittingTerminalPayoff reward
        (quittingTwoDateTimingProfile reward equilibriumProfile) 0 = 1 / 2 := by
  rw [quittingTerminalPayoff_twoDateTimingProfile_eq_mixedEU]
  exact equilibrium_row_payoff

def late : Option (Fin 3) := some ⟨2, by omega⟩

def liftAction : Action → Option (Fin 3)
  | none => none
  | some time => some ⟨time.val, by omega⟩

theorem pure_row_late_value (columnAction : Action) :
    purePayoff reward 3 ![late, liftAction columnAction, none, none] 0 = 1 := by
  cases columnAction with
  | none =>
      rw [purePayoff_succ_of_current_empty]
      · have htail : choicesTail ![late, liftAction none, none, none] =
            ![next, never, never, never] := by
          funext who
          fin_cases who <;> rfl
        rw [htail]
        simpa [next, never] using pure_row_next_value never
      · decide
  | some time =>
      fin_cases time
      · rw [purePayoff_succ_of_current_nonempty]
        · let current : Player → Bool := fun player =>
            actionCurrent (![late, liftAction now, none, none] player)
          have hzero : 0 ∉ quittingQuitters current := by decide
          have hone : 1 ∈ quittingQuitters current := by decide
          change reward ⟨quittingQuitters current, _⟩ 0 = 1
          simp [reward, hzero, hone]
        · exact ⟨1, by decide⟩
      · rw [purePayoff_succ_of_current_empty]
        · have htail : choicesTail
              ![late, liftAction (some ⟨1, by omega⟩), none, none] =
              ![next, now, never, never] := by
            funext who
            fin_cases who <;> rfl
          rw [htail]
          simpa [next, now] using pure_row_next_value now
        · decide

def lateCoordinateTime (player : Player) (action : Action) :
    Math.Probability.CompactStoppingTime :=
  if player = 0 then WithTop.some 2 else quittingTwoDateTimingActionTime action

theorem terminalPayoff_lateCoordinateTime
    (rowAction columnAction : Action) :
    quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward fun player =>
          lateCoordinateTime player
            (![rowAction, columnAction, never, never] player)) 0 = 1 := by
  have htimes : (fun player => lateCoordinateTime player
      (![rowAction, columnAction, never, never] player)) =
      (fun player => actionTime
        (![late, liftAction columnAction, none, none] player)) := by
    funext player
    fin_cases player <;> cases columnAction <;> rfl
  rw [htimes]
  exact pure_row_late_value columnAction

private theorem pureDeviationLaws_eq_map_lateCoordinateTime :
    (fun player =>
      (quittingPureDeviationCompactLaws
        (fun who => quittingTwoDateTimingLaw (equilibriumProfile who)) 0
        (WithTop.some 2) player).toPMF) =
      (fun player =>
        (equilibriumProfile player).map (lateCoordinateTime player)) := by
  funext player
  fin_cases player
  · have hplayer : (⟨0, by omega⟩ : Player) = 0 := by decide
    rw [quittingPureDeviationCompactLaws, if_pos hplayer,
      Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
    have htime : lateCoordinateTime (⟨0, by omega⟩ : Player) =
        Function.const Action (WithTop.some 2) := by
      funext action
      simp [lateCoordinateTime]
    rw [htime, PMF.map_const]
  · have hplayer : (⟨1, by omega⟩ : Player) ≠ 0 := by decide
    rw [quittingPureDeviationCompactLaws, if_neg hplayer,
      quittingTwoDateTimingLaw, quittingFiniteDeadlineTimingLaw,
      Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
    have htime : lateCoordinateTime (⟨1, by omega⟩ : Player) =
        quittingTwoDateTimingActionTime := by
      funext action
      simp [lateCoordinateTime]
    rw [htime]
  · have hplayer : (⟨2, by omega⟩ : Player) ≠ 0 := by decide
    rw [quittingPureDeviationCompactLaws, if_neg hplayer,
      quittingTwoDateTimingLaw, quittingFiniteDeadlineTimingLaw,
      Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
    have htime : lateCoordinateTime (⟨2, by omega⟩ : Player) =
        quittingTwoDateTimingActionTime := by
      funext action
      simp [lateCoordinateTime]
    rw [htime]
  · have hplayer : (⟨3, by omega⟩ : Player) ≠ 0 := by decide
    rw [quittingPureDeviationCompactLaws, if_neg hplayer,
      quittingTwoDateTimingLaw, quittingFiniteDeadlineTimingLaw,
      Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
    have htime : lateCoordinateTime (⟨3, by omega⟩ : Player) =
        quittingTwoDateTimingActionTime := by
      funext action
      simp [lateCoordinateTime]
    rw [htime]

theorem equilibriumProfile_quit_two_payoff_zero :
    quittingTerminalPayoff reward
        (Function.update
          (quittingTwoDateTimingProfile reward equilibriumProfile) 0
          (quittingPureTimeBehaviorStrategy reward 0 (WithTop.some 2))) 0 = 1 := by
  rw [quittingTwoDateTimingProfile, quittingFiniteDeadlineTimingProfile,
    quittingTerminalPayoff_update_compactStoppingLawProfile_pureTime_eq_expect,
    pureDeviationLaws_eq_map_lateCoordinateTime]
  change Math.Probability.expect
      (pmfPi (fun player => Math.ProbabilityMassFunction.pushforward
        (equilibriumProfile player) (lateCoordinateTime player)))
      (fun choices => quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward choices) 0) = 1
  rw [← pmfPi_push_coordwise]
  change Math.Probability.expect
      ((pmfPi equilibriumProfile).map fun choices player =>
        lateCoordinateTime player (choices player))
      (fun choices => quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward choices) 0) = 1
  rw [Math.Probability.expect_map, expect_pmfPi_fin4]
  simp only [equilibriumProfile, activeProfile,
    Math.Probability.expect_pure, Fin.isValue]
  simp_rw [terminalPayoff_lateCoordinateTime]
  simp

theorem equilibriumProfile_terminalDeviationDebt_zero_eq_half :
    quittingTerminalDeviationDebt reward
        (quittingTwoDateTimingProfile reward equilibriumProfile) 0 = 1 / 2 := by
  apply le_antisymm
  · exact quittingTerminalDeviationDebt_twoDateTimingProfile_le_half
      reward equilibriumProfile 0 (by norm_num) abs_reward_le_one
      equilibriumProfile_isNash
  · have hdeviation :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue reward
        (quittingTwoDateTimingProfile reward equilibriumProfile) 0
        (quittingPureTimeBehaviorStrategy reward 0 (WithTop.some 2))
    rw [equilibriumProfile_quit_two_payoff_zero] at hdeviation
    unfold quittingTerminalDeviationDebt
    rw [equilibriumProfile_terminalPayoff_zero]
    linarith


end TwoDateTimingNashSharpness
end GameTheory
