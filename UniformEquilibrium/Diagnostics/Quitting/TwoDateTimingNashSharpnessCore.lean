/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.FiniteFubini
import UniformEquilibrium.Diagnostics.Quitting.FiniteDeadlineTimingRecursion
import UniformEquilibrium.Diagnostics.Quitting.TwoDateTimingNashDebt

/-!
# Core of the sharp two-date timing-Nash regression

This module gives the exact normalized rational four-player regression for the
universal two-date timing-Nash theorem. Its displayed finite timing law is an
exact mixed Nash profile: both active players use planned-time masses
`(1 / 4, 1 / 4, 1 / 2)` on date zero, date one, and Never, while both dummy
players choose Never. The uniqueness and exact behavioral-debt layers are
proved in focused downstream modules.

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

def now : Action := some 0
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

theorem pure_row_now_value (columnAction : Action) :
    timingPurePayoff reward 2 ![now, columnAction, never, never] 0 =
      if columnAction = now then -1 else 1 := by
  cases columnAction with
  | none =>
      change timingPurePayoff reward 2 ![now, never, never, never] 0 = 1
      rw [timingPurePayoff_succ]
      rw [quittingRootPayoff, dif_pos]
      · simp [now, never, timingActionCurrent, reward, quittingQuitters]
      · exact ⟨0, by simp [now, timingActionCurrent, quittingQuitters]⟩
  | some time =>
      fin_cases time
      · change timingPurePayoff reward 2 ![now, now, never, never] 0 = -1
        rw [timingPurePayoff_succ]
        rw [quittingRootPayoff, dif_pos]
        · simp [now, timingActionCurrent, reward, quittingQuitters]
        · exact ⟨0, by simp [now, timingActionCurrent, quittingQuitters]⟩
      · change timingPurePayoff reward 2 ![now, next, never, never] 0 = 1
        rw [timingPurePayoff_succ]
        let current : Player → Bool := fun player =>
          timingActionCurrent (![now, next, never, never] player)
        have hzero : 0 ∈ quittingQuitters current := by decide
        have hone : 1 ∉ quittingQuitters current := by decide
        rw [quittingRootPayoff, dif_pos ⟨0, hzero⟩]
        change reward ⟨quittingQuitters current, _⟩ 0 = 1
        simp only [reward, if_pos hzero, if_neg hone]
        simp

theorem pure_row_next_value (columnAction : Action) :
    timingPurePayoff reward 2 ![next, columnAction, never, never] 0 =
      if columnAction = next then -1 else 1 := by
  cases columnAction with
  | none =>
      change timingPurePayoff reward 2 ![next, never, never, never] 0 = 1
      rw [timingPurePayoff_succ_of_current_empty]
      · rw [timingPurePayoff_succ_of_current_nonempty]
        · let current : Player → Bool := fun player =>
            timingActionCurrent (timingChoicesTail ![next, never, never, never] player)
          have hzero : 0 ∈ quittingQuitters current := by decide
          have hone : 1 ∉ quittingQuitters current := by decide
          change reward ⟨quittingQuitters current, _⟩ 0 = 1
          simp only [reward, if_pos hzero, if_neg hone]
          simp
        · exact ⟨0, by decide⟩
      · decide
  | some time =>
      fin_cases time
      · change timingPurePayoff reward 2 ![next, now, never, never] 0 = 1
        rw [timingPurePayoff_succ_of_current_nonempty]
        · let current : Player → Bool := fun player =>
            timingActionCurrent (![next, now, never, never] player)
          have hzero : 0 ∉ quittingQuitters current := by decide
          have hone : 1 ∈ quittingQuitters current := by decide
          change reward ⟨quittingQuitters current, _⟩ 0 = 1
          simp only [reward, if_neg hzero, if_pos hone]
          simp
        · exact ⟨1, by decide⟩
      · change timingPurePayoff reward 2 ![next, next, never, never] 0 = -1
        rw [timingPurePayoff_succ_of_current_empty]
        · rw [timingPurePayoff_succ_of_current_nonempty]
          · let current : Player → Bool := fun player =>
              timingActionCurrent (timingChoicesTail ![next, next, never, never] player)
            have hzero : 0 ∈ quittingQuitters current := by decide
            have hone : 1 ∈ quittingQuitters current := by decide
            change reward ⟨quittingQuitters current, _⟩ 0 = -1
            simp only [reward, if_pos hzero, if_pos hone]
            simp
          · exact ⟨0, by decide⟩
        · decide

theorem pure_row_never_value (columnAction : Action) :
    timingPurePayoff reward 2 ![never, columnAction, never, never] 0 =
      if columnAction = never then 0 else 1 := by
  cases columnAction with
  | none =>
      change timingPurePayoff reward 2 ![never, never, never, never] 0 = 0
      rw [timingPurePayoff_succ_of_current_empty]
      · rw [timingPurePayoff_succ_of_current_empty]
        · exact timingPurePayoff_zero reward _ 0
        · decide
      · decide
  | some time =>
      fin_cases time
      · change timingPurePayoff reward 2 ![never, now, never, never] 0 = 1
        rw [timingPurePayoff_succ_of_current_nonempty]
        · let current : Player → Bool := fun player =>
            timingActionCurrent (![never, now, never, never] player)
          have hzero : 0 ∉ quittingQuitters current := by decide
          have hone : 1 ∈ quittingQuitters current := by decide
          change reward ⟨quittingQuitters current, _⟩ 0 = 1
          simp only [reward, if_neg hzero, if_pos hone]
          simp
        · exact ⟨1, by decide⟩
      · change timingPurePayoff reward 2 ![never, next, never, never] 0 = 1
        rw [timingPurePayoff_succ_of_current_empty]
        · rw [timingPurePayoff_succ_of_current_nonempty]
          · let current : Player → Bool := fun player =>
              timingActionCurrent (timingChoicesTail ![never, next, never, never] player)
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
  change Math.Probability.expect
      (pmfPi (Function.update (activeProfile row column) 0 (PMF.pure now)))
      (fun choices => timingPurePayoff reward 2 choices 0) = _
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
  change Math.Probability.expect
      (pmfPi (Function.update (activeProfile row column) 0 (PMF.pure next)))
      (fun choices => timingPurePayoff reward 2 choices 0) = _
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
  change Math.Probability.expect
      (pmfPi (Function.update (activeProfile row column) 0 (PMF.pure never)))
      (fun choices => timingPurePayoff reward 2 choices 0) = _
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
      timingPurePayoff reward 2 ![now, action, never, never] 0) =
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
      timingPurePayoff reward 2 ![next, action, never, never] 0) =
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
      timingPurePayoff reward 2 ![never, action, never, never] 0) =
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
  change Math.Probability.expect (pmfPi (activeProfile row column))
      (fun choices => timingPurePayoff reward 2 choices 0) = _
  rw [expect_pmfPi_fin4]
  simp only [activeProfile, Math.Probability.expect_pure]
  rw [Math.Probability.expect_eq_sum, Fintype.sum_option,
    Fin.sum_univ_two]
  rw [show (some (0 : Fin 2) : Action) = now by rfl,
    show (some (1 : Fin 2) : Action) = next by rfl]
  rw [expect_pure_row_now, expect_pure_row_next]
  change mass row never *
      Math.Probability.expect column (fun b =>
        timingPurePayoff reward 2 ![never, b, never, never] 0) +
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
  simp_rw [terminalPayoff_one_eq_neg_zero]
  change Math.Probability.expect
      (pmfPi (Function.update (activeProfile row column) 1 (PMF.pure now)))
      (fun choices => -timingPurePayoff reward 2 choices 0) = _
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
  simp_rw [terminalPayoff_one_eq_neg_zero]
  change Math.Probability.expect
      (pmfPi (Function.update (activeProfile row column) 1 (PMF.pure next)))
      (fun choices => -timingPurePayoff reward 2 choices 0) = _
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
  simp_rw [terminalPayoff_one_eq_neg_zero]
  change Math.Probability.expect
      (pmfPi (Function.update (activeProfile row column) 1 (PMF.pure never)))
      (fun choices => -timingPurePayoff reward 2 choices 0) = _
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
    timingPurePayoff reward 2 ![rowAction, columnAction, now, never] 2 = -1 := by
  have hcurrent : (quittingQuitters fun player =>
      timingActionCurrent (![rowAction, columnAction, now, never] player)).Nonempty :=
    ⟨2, by simp [quittingQuitters, timingActionCurrent, now]⟩
  rw [timingPurePayoff_succ_of_current_nonempty reward 1 _ 2 hcurrent]
  simp only [reward, if_neg (by decide : (2 : Player) ≠ 0),
    if_neg (by decide : (2 : Player) ≠ 1)]
  simp [quittingQuitters, timingActionCurrent, now]

private theorem pure_dummy_two_never_value
    (rowAction columnAction : Action) :
    timingPurePayoff reward 2 ![rowAction, columnAction, never, never] 2 = 0 := by
  rw [timingPurePayoff_succ]
  unfold quittingRootPayoff
  split
  case isTrue hcurrent =>
    simp only [reward, if_neg (by decide : (2 : Player) ≠ 0),
      if_neg (by decide : (2 : Player) ≠ 1)]
    simp [quittingQuitters, timingActionCurrent, never]
  case isFalse hcurrent =>
    change timingPurePayoff reward 1
      (timingChoicesTail ![rowAction, columnAction, never, never]) 2 = 0
    rw [timingPurePayoff_succ]
    unfold quittingRootPayoff
    split
    case isTrue htail =>
      simp only [reward, if_neg (by decide : (2 : Player) ≠ 0),
        if_neg (by decide : (2 : Player) ≠ 1)]
      simp [quittingQuitters, timingActionCurrent, timingChoicesTail, timingActionTail, never]
    case isFalse htail => exact timingPurePayoff_zero reward _ 2

@[simp] theorem quittingQuitters_vec4 (a b c d : Bool) :
    quittingQuitters ![a, b, c, d] =
      (if a then {0} else ∅) ∪ (if b then {1} else ∅) ∪
        (if c then {2} else ∅) ∪ (if d then {3} else ∅) := by
  ext who
  fin_cases who <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp [quittingQuitters]

private theorem dummy_two_current_nonempty_iff
    (rowAction columnAction : Action) :
    (quittingQuitters fun player =>
        timingActionCurrent (![rowAction, columnAction, next, never] player)).Nonempty ↔
      rowAction = now ∨ columnAction = now := by
  rw [quittingQuitters_nonempty_iff]
  constructor
  · rintro ⟨player, hplayer⟩
    fin_cases player
    · exact Or.inl (by
        simpa only [now] using
          (timingActionCurrent_eq_true_iff rowAction).mp hplayer)
    · exact Or.inr (by
        simpa only [now] using
          (timingActionCurrent_eq_true_iff columnAction).mp hplayer)
    · exact False.elim ((by decide : timingActionCurrent next ≠ true) hplayer)
    · exact False.elim ((by decide : timingActionCurrent never ≠ true) hplayer)
  · rintro (hrow | hcolumn)
    · exact ⟨0, by simp [hrow, timingActionCurrent, now]⟩
    · exact ⟨1, by simp [hcolumn, timingActionCurrent, now]⟩

private theorem pure_dummy_two_next_value
    (rowAction columnAction : Action) :
    timingPurePayoff reward 2 ![rowAction, columnAction, next, never] 2 =
      if rowAction = now ∨ columnAction = now then 0 else -1 := by
  rw [timingPurePayoff_succ]
  unfold quittingRootPayoff
  split
  case isTrue hcurrent =>
    rw [if_pos ((dummy_two_current_nonempty_iff rowAction columnAction).mp
      hcurrent)]
    simp only [reward, if_neg (by decide : (2 : Player) ≠ 0),
      if_neg (by decide : (2 : Player) ≠ 1)]
    rw [if_neg]
    have hfun : (fun player =>
        timingActionCurrent (![rowAction, columnAction, next, never] player)) =
        ![timingActionCurrent rowAction, timingActionCurrent columnAction,
          timingActionCurrent next, timingActionCurrent never] := by
      funext player
      fin_cases player <;> rfl
    rw [hfun]
    have hnext : timingActionCurrent next = false := by decide
    rw [hnext]
    cases hrow : timingActionCurrent rowAction <;>
      cases hcolumn : timingActionCurrent columnAction <;>
        simp [quittingQuitters_vec4, timingActionCurrent, never]
  case isFalse hcurrent =>
    rw [if_neg (not_congr (dummy_two_current_nonempty_iff
      rowAction columnAction) |>.mp hcurrent)]
    change timingPurePayoff reward 1
      (timingChoicesTail ![rowAction, columnAction, next, never]) 2 = -1
    have htwo : 2 ∈ quittingQuitters (fun player => timingActionCurrent
        (timingChoicesTail ![rowAction, columnAction, next, never] player)) := by
      simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
        true_and]
      change timingActionCurrent (timingActionTail next) = true
      decide
    have htail : (quittingQuitters fun player => timingActionCurrent
        (timingChoicesTail ![rowAction, columnAction, next, never] player)).Nonempty :=
      ⟨2, htwo⟩
    rw [timingPurePayoff_succ_of_current_nonempty reward 0 _ 2 htail]
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
  change Math.Probability.expect
      (pmfPi (Function.update equilibriumProfile 2 (PMF.pure now)))
      (fun choices => timingPurePayoff reward 2 choices 2) = -1
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
  change Math.Probability.expect
      (pmfPi (Function.update equilibriumProfile 2 (PMF.pure never)))
      (fun choices => timingPurePayoff reward 2 choices 2) = 0
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
  change Math.Probability.expect
      (pmfPi (Function.update equilibriumProfile 2 (PMF.pure next)))
      (fun choices => timingPurePayoff reward 2 choices 2) = -9 / 16
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
    timingPurePayoff reward 2 ![rowAction, columnAction, never, now] 3 = -1 := by
  have hcurrent : (quittingQuitters fun player =>
      timingActionCurrent (![rowAction, columnAction, never, now] player)).Nonempty :=
    ⟨3, by simp [quittingQuitters, timingActionCurrent, now]⟩
  rw [timingPurePayoff_succ_of_current_nonempty reward 1 _ 3 hcurrent]
  simp only [reward, if_neg (by decide : (3 : Player) ≠ 0),
    if_neg (by decide : (3 : Player) ≠ 1)]
  simp [quittingQuitters, timingActionCurrent, now]

private theorem pure_dummy_three_never_value
    (rowAction columnAction : Action) :
    timingPurePayoff reward 2 ![rowAction, columnAction, never, never] 3 = 0 := by
  rw [timingPurePayoff_succ]
  unfold quittingRootPayoff
  split
  case isTrue hcurrent =>
    simp only [reward, if_neg (by decide : (3 : Player) ≠ 0),
      if_neg (by decide : (3 : Player) ≠ 1)]
    simp [quittingQuitters, timingActionCurrent, never]
  case isFalse hcurrent =>
    change timingPurePayoff reward 1
      (timingChoicesTail ![rowAction, columnAction, never, never]) 3 = 0
    rw [timingPurePayoff_succ]
    unfold quittingRootPayoff
    split
    case isTrue htail =>
      simp only [reward, if_neg (by decide : (3 : Player) ≠ 0),
        if_neg (by decide : (3 : Player) ≠ 1)]
      simp [quittingQuitters, timingActionCurrent, timingChoicesTail, timingActionTail, never]
    case isFalse htail => exact timingPurePayoff_zero reward _ 3

private theorem dummy_three_current_nonempty_iff
    (rowAction columnAction : Action) :
    (quittingQuitters fun player =>
        timingActionCurrent (![rowAction, columnAction, never, next] player)).Nonempty ↔
      rowAction = now ∨ columnAction = now := by
  rw [quittingQuitters_nonempty_iff]
  constructor
  · rintro ⟨player, hplayer⟩
    fin_cases player
    · exact Or.inl (by
        simpa only [now] using
          (timingActionCurrent_eq_true_iff rowAction).mp hplayer)
    · exact Or.inr (by
        simpa only [now] using
          (timingActionCurrent_eq_true_iff columnAction).mp hplayer)
    · exact False.elim ((by decide : timingActionCurrent never ≠ true) hplayer)
    · exact False.elim ((by decide : timingActionCurrent next ≠ true) hplayer)
  · rintro (hrow | hcolumn)
    · exact ⟨0, by simp [hrow, timingActionCurrent, now]⟩
    · exact ⟨1, by simp [hcolumn, timingActionCurrent, now]⟩

private theorem pure_dummy_three_next_value
    (rowAction columnAction : Action) :
    timingPurePayoff reward 2 ![rowAction, columnAction, never, next] 3 =
      if rowAction = now ∨ columnAction = now then 0 else -1 := by
  rw [timingPurePayoff_succ]
  unfold quittingRootPayoff
  split
  case isTrue hcurrent =>
    rw [if_pos ((dummy_three_current_nonempty_iff rowAction columnAction).mp
      hcurrent)]
    simp only [reward, if_neg (by decide : (3 : Player) ≠ 0),
      if_neg (by decide : (3 : Player) ≠ 1)]
    rw [if_neg]
    have hfun : (fun player =>
        timingActionCurrent (![rowAction, columnAction, never, next] player)) =
        ![timingActionCurrent rowAction, timingActionCurrent columnAction,
          timingActionCurrent never, timingActionCurrent next] := by
      funext player
      fin_cases player <;> rfl
    rw [hfun]
    have hnext : timingActionCurrent next = false := by decide
    rw [hnext]
    cases hrow : timingActionCurrent rowAction <;>
      cases hcolumn : timingActionCurrent columnAction <;>
        simp [quittingQuitters_vec4, timingActionCurrent, never]
  case isFalse hcurrent =>
    rw [if_neg (not_congr (dummy_three_current_nonempty_iff
      rowAction columnAction) |>.mp hcurrent)]
    change timingPurePayoff reward 1
      (timingChoicesTail ![rowAction, columnAction, never, next]) 3 = -1
    have hthree : 3 ∈ quittingQuitters (fun player => timingActionCurrent
        (timingChoicesTail ![rowAction, columnAction, never, next] player)) := by
      simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
        true_and]
      change timingActionCurrent (timingActionTail next) = true
      decide
    have htail : (quittingQuitters fun player => timingActionCurrent
        (timingChoicesTail ![rowAction, columnAction, never, next] player)).Nonempty :=
      ⟨3, hthree⟩
    rw [timingPurePayoff_succ_of_current_nonempty reward 0 _ 3 htail]
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
  change Math.Probability.expect
      (pmfPi (Function.update equilibriumProfile 3 (PMF.pure now)))
      (fun choices => timingPurePayoff reward 2 choices 3) = -1
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
  change Math.Probability.expect
      (pmfPi (Function.update equilibriumProfile 3 (PMF.pure never)))
      (fun choices => timingPurePayoff reward 2 choices 3) = 0
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
  change Math.Probability.expect
      (pmfPi (Function.update equilibriumProfile 3 (PMF.pure next)))
      (fun choices => timingPurePayoff reward 2 choices 3) = -9 / 16
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


end TwoDateTimingNashSharpness
end GameTheory
