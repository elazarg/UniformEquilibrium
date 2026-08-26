/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TwoDateTimingNashSharpness
import UniformEquilibrium.Diagnostics.Quitting.FixedPrefixArbitraryTailBarrier

/-!
# A noncanonical timing Nash for the fixed-prefix reward table

The fixed-prefix reward table differs from the sharp two-date table on
coalitions containing only dummy players.  That difference permits off-path
dummy stopping times to support a second timing-game Nash profile.  Concretely,
Never/date-zero/date-one/Never is Nash: player one's later deviations are held
to payoff minus one by player two's off-path date-one exit.

This module proves the complete pure-deviation table and the Nash property.  It
does not identify the fixed-prefix table with the distinct sharp table.
-/

noncomputable section

namespace GameTheory
namespace FixedPrefixTimingNashNonuniqueness

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct
open TwoDateTimingNashSharpness

abbrev Player := Fin 4
abbrev Action := QuittingTwoDateTimingAction

def prefixReward := FixedPrefixArbitraryTailBarrier.reward

theorem sharpReward_eq_prefixReward_of_active_mem
    (terminal : {S : Finset Player // S.Nonempty})
    (hactive : 0 ∈ terminal.1 ∨ 1 ∈ terminal.1) :
    reward terminal = prefixReward terminal := by
  funext who
  fin_cases who <;>
    simp only [reward, prefixReward,
      FixedPrefixArbitraryTailBarrier.reward] <;>
    by_cases hzero : 0 ∈ terminal.1 <;>
    by_cases hone : 1 ∈ terminal.1 <;>
    simp [hzero, hone] at hactive ⊢

theorem sharpReward_eq_prefixReward_at_dummy
    (terminal : {S : Finset Player // S.Nonempty})
    (dummy : Player) (hzero : dummy ≠ 0) (hone : dummy ≠ 1) :
    reward terminal dummy = prefixReward terminal dummy := by
  simp [reward, prefixReward, FixedPrefixArbitraryTailBarrier.reward,
    hzero, hone]

theorem purePayoff_eq_prefix_of_dummy
    (dates : ℕ) (choices : Player → Option (Fin dates))
    (dummy : Player) (hzero : dummy ≠ 0) (hone : dummy ≠ 1) :
    purePayoff reward dates choices dummy =
      purePayoff prefixReward dates choices dummy := by
  induction dates with
  | zero =>
      rw [purePayoff_zero reward, purePayoff_zero prefixReward]
  | succ dates ih =>
      by_cases hcurrent : (quittingQuitters fun player =>
          actionCurrent (choices player)).Nonempty
      · rw [purePayoff_succ_of_current_nonempty reward dates choices dummy
            hcurrent,
          purePayoff_succ_of_current_nonempty prefixReward dates choices dummy
            hcurrent]
        exact sharpReward_eq_prefixReward_at_dummy _ dummy hzero hone
      · rw [purePayoff_succ_of_current_empty reward dates choices dummy
            hcurrent,
          purePayoff_succ_of_current_empty prefixReward dates choices dummy
            hcurrent]
        exact ih (choicesTail choices)

private theorem active_mem_quittingQuitters_of_dummies_never
    {dates : ℕ} (choices : Player → Option (Fin (dates + 1)))
    (htwo : choices 2 = none) (hthree : choices 3 = none)
    (hcurrent : (quittingQuitters fun player =>
      actionCurrent (choices player)).Nonempty) :
    0 ∈ quittingQuitters (fun player => actionCurrent (choices player)) ∨
      1 ∈ quittingQuitters (fun player => actionCurrent (choices player)) := by
  obtain ⟨who, hwho⟩ := hcurrent
  fin_cases who
  · exact Or.inl hwho
  · exact Or.inr hwho
  · simp [quittingQuitters, htwo, actionCurrent] at hwho
  · simp [quittingQuitters, hthree, actionCurrent] at hwho

theorem purePayoff_eq_prefix_of_dummies_never
    (dates : ℕ) (choices : Player → Option (Fin dates))
    (htwo : choices 2 = none) (hthree : choices 3 = none)
    (who : Player) :
    purePayoff reward dates choices who =
      purePayoff prefixReward dates choices who := by
  induction dates with
  | zero =>
      rw [purePayoff_zero reward, purePayoff_zero prefixReward]
  | succ dates ih =>
      by_cases hcurrent : (quittingQuitters fun player =>
          actionCurrent (choices player)).Nonempty
      · rw [purePayoff_succ_of_current_nonempty reward dates choices who
            hcurrent,
          purePayoff_succ_of_current_nonempty prefixReward dates choices who
            hcurrent]
        exact congrFun (sharpReward_eq_prefixReward_of_active_mem _
          (active_mem_quittingQuitters_of_dummies_never choices htwo hthree
            hcurrent)) who
      · rw [purePayoff_succ_of_current_empty reward dates choices who
            hcurrent,
          purePayoff_succ_of_current_empty prefixReward dates choices who
            hcurrent]
        apply ih
        · simp [choicesTail, htwo, actionTail]
        · simp [choicesTail, hthree, actionTail]

theorem mixedEU_eq_prefix_at_dummy
    (mixed : Player → PMF Action)
    (dummy : Player) (hzero : dummy ≠ 0) (hone : dummy ≠ 1) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu mixed dummy =
      (quittingTwoDateTimingGame prefixReward).mixedExtension.eu mixed dummy := by
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu,
    (quittingTwoDateTimingGame prefixReward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [← actionTime_two]
  change Math.Probability.expect (pmfPi mixed)
      (fun choices => purePayoff reward 2 choices dummy) =
    Math.Probability.expect (pmfPi mixed)
      (fun choices => purePayoff prefixReward 2 choices dummy)
  congr 1
  funext choices
  exact purePayoff_eq_prefix_of_dummy 2 choices dummy hzero hone

theorem activeProfile_mixedEU_eq_prefix
    (row column : PMF Action) (who : Player) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (activeProfile row column) who =
      (quittingTwoDateTimingGame prefixReward).mixedExtension.eu
        (activeProfile row column) who := by
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu,
    (quittingTwoDateTimingGame prefixReward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [← actionTime_two]
  change Math.Probability.expect (pmfPi (activeProfile row column))
      (fun choices => purePayoff reward 2 choices who) =
    Math.Probability.expect (pmfPi (activeProfile row column))
      (fun choices => purePayoff prefixReward 2 choices who)
  rw [expect_pmfPi_fin4, expect_pmfPi_fin4]
  simp only [activeProfile, Math.Probability.expect_pure, Fin.isValue]
  congr 1
  funext rowAction
  congr 1
  funext columnAction
  exact purePayoff_eq_prefix_of_dummies_never 2
    ![rowAction, columnAction, never, never] rfl rfl who


def nonUniqueNashChoices : Player → Action :=
  ![never, now, next, never]

def nonUniqueNashProfile : Player → PMF Action :=
  fun who => PMF.pure (nonUniqueNashChoices who)

private theorem update_nonUniqueNashChoices_zero (action : Action) :
    Function.update nonUniqueNashChoices 0 action =
      ![action, now, next, never] := by
  funext who
  fin_cases who <;> simp [nonUniqueNashChoices]

private theorem update_nonUniqueNashChoices_one (action : Action) :
    Function.update nonUniqueNashChoices 1 action =
      ![never, action, next, never] := by
  funext who
  fin_cases who <;> simp [nonUniqueNashChoices]

private theorem update_nonUniqueNashChoices_two (action : Action) :
    Function.update nonUniqueNashChoices 2 action =
      ![never, now, action, never] := by
  funext who
  fin_cases who <;> simp [nonUniqueNashChoices]

private theorem update_nonUniqueNashChoices_three (action : Action) :
    Function.update nonUniqueNashChoices 3 action =
      ![never, now, next, action] := by
  funext who
  fin_cases who <;> simp [nonUniqueNashChoices]

private theorem actionCurrent_eq_true_iff (action : Action) :
    actionCurrent action = true ↔ action = now := by
  cases action with
  | none => simp [actionCurrent, now]
  | some time =>
      fin_cases time
      · simp [actionCurrent, now]
      · decide

private theorem purePayoff_prefix_of_column_now
    (rowAction dummyTwo dummyThree : Action) (who : Player) :
    purePayoff prefixReward 2
        ![rowAction, now, dummyTwo, dummyThree] who =
      if who = 0 then
        if rowAction = now then -1 else 1
      else if who = 1 then
        if rowAction = now then 1 else -1
      else if who = 2 then
        if dummyTwo = now then -1 else 0
      else if dummyThree = now then -1 else 0 := by
  rw [purePayoff_succ_of_current_nonempty]
  · fin_cases who <;>
      simp [prefixReward, FixedPrefixArbitraryTailBarrier.reward,
        quittingQuitters, actionCurrent_eq_true_iff, now]
  · exact ⟨1, by simp [quittingQuitters, actionCurrent, now]⟩

private theorem purePayoff_prefix_column_deviation
    (action : Action) :
    purePayoff prefixReward 2 ![never, action, next, never] 1 = -1 := by
  cases action with
  | none =>
      rw [purePayoff_succ_of_current_empty]
      · rw [purePayoff_succ_of_current_nonempty]
        · simp [prefixReward, FixedPrefixArbitraryTailBarrier.reward,
            quittingQuitters, choicesTail, actionTail, actionCurrent,
            never, next]
        · exact ⟨2, by decide⟩
      · decide
  | some time =>
      fin_cases time
      · simpa [never, now, next] using
          purePayoff_prefix_of_column_now never next never 1
      · rw [purePayoff_succ_of_current_empty]
        · rw [purePayoff_succ_of_current_nonempty]
          · simp [prefixReward, FixedPrefixArbitraryTailBarrier.reward,
              quittingQuitters, choicesTail, actionTail, actionCurrent,
              never, next]
          · exact ⟨1, by decide⟩
        · decide

theorem pure_nonUniqueNash_deviation_value
    (who : Player) (action : Action) :
    purePayoff prefixReward 2
        (Function.update nonUniqueNashChoices who action) who =
      match who with
      | 0 => if action = now then -1 else 1
      | 1 => -1
      | 2 => if action = now then -1 else 0
      | 3 => if action = now then -1 else 0 := by
  fin_cases who
  · change purePayoff prefixReward 2
        (Function.update nonUniqueNashChoices 0 action) 0 =
      (if action = now then -1 else 1)
    rw [update_nonUniqueNashChoices_zero]
    simpa using purePayoff_prefix_of_column_now action next never 0
  · change purePayoff prefixReward 2
        (Function.update nonUniqueNashChoices 1 action) 1 = -1
    rw [update_nonUniqueNashChoices_one]
    exact purePayoff_prefix_column_deviation action
  · change purePayoff prefixReward 2
        (Function.update nonUniqueNashChoices 2 action) 2 =
      (if action = now then -1 else 0)
    rw [update_nonUniqueNashChoices_two]
    simpa using purePayoff_prefix_of_column_now never action never 2
  · change purePayoff prefixReward 2
        (Function.update nonUniqueNashChoices 3 action) 3 =
      (if action = now then -1 else 0)
    rw [update_nonUniqueNashChoices_three]
    simpa using purePayoff_prefix_of_column_now never next action 3

theorem nonUniqueNash_deviation_value
    (who : Player) (action : Action) :
    (quittingTwoDateTimingGame prefixReward).mixedExtension.eu
        (Function.update nonUniqueNashProfile who (PMF.pure action)) who =
      match who with
      | 0 => if action = now then -1 else 1
      | 1 => -1
      | 2 => if action = now then -1 else 0
      | 3 => if action = now then -1 else 0 := by
  rw [(quittingTwoDateTimingGame prefixReward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  simp_rw [← actionTime_two]
  change Math.Probability.expect
      (pmfPi (Function.update nonUniqueNashProfile who (PMF.pure action)))
      (fun choices => purePayoff prefixReward 2 choices who) = _
  have hprofile : Function.update nonUniqueNashProfile who (PMF.pure action) =
      (fun player => PMF.pure
        (Function.update nonUniqueNashChoices who action player)) := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp
    · simp [Function.update_of_ne hplayer, nonUniqueNashProfile]
  rw [hprofile, pmfPi_pure, Math.Probability.expect_pure]
  exact pure_nonUniqueNash_deviation_value who action

theorem nonUniqueNash_payoff (who : Player) :
    (quittingTwoDateTimingGame prefixReward).mixedExtension.eu
        nonUniqueNashProfile who =
      match who with
      | 0 => 1
      | 1 => -1
      | 2 => 0
      | 3 => 0 := by
  have hupdate : Function.update nonUniqueNashProfile who
      (PMF.pure (nonUniqueNashChoices who)) = nonUniqueNashProfile := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [nonUniqueNashProfile]
    · rw [Function.update_of_ne hplayer]
  have hvalue := nonUniqueNash_deviation_value who
    (nonUniqueNashChoices who)
  have heq := congrArg (fun profile : Player → PMF Action =>
    (quittingTwoDateTimingGame prefixReward).mixedExtension.eu profile who)
    hupdate
  have hresult := heq.symm.trans hvalue
  fin_cases who <;>
    simpa [nonUniqueNashChoices, now, next, never] using hresult

theorem nonUniqueNashProfile_isNash :
    (quittingTwoDateTimingGame prefixReward).mixedExtension.IsNash
      nonUniqueNashProfile := by
  apply ((quittingTwoDateTimingGame prefixReward).isNash_iff_gains_nonpos
    nonUniqueNashProfile).mpr
  intro who action
  unfold KernelGame.mixedGain
  rw [nonUniqueNash_deviation_value, nonUniqueNash_payoff]
  fin_cases who <;> cases action with
  | none => simp [now]
  | some time => fin_cases time <;> norm_num [now]

private theorem canonical_pureDeviation_mixedEU_eq_prefix
    (who : Player) (action : Action) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update equilibriumProfile who (PMF.pure action)) who =
      (quittingTwoDateTimingGame prefixReward).mixedExtension.eu
        (Function.update equilibriumProfile who (PMF.pure action)) who := by
  by_cases hzero : who = 0
  · subst who
    have hupdate : Function.update equilibriumProfile 0 (PMF.pure action) =
        activeProfile (PMF.pure action) equilibriumLaw := by
      funext player
      fin_cases player <;> simp [equilibriumProfile, activeProfile]
    calc
      _ = (quittingTwoDateTimingGame reward).mixedExtension.eu
          (activeProfile (PMF.pure action) equilibriumLaw) 0 :=
        congrArg (fun profile : Player → PMF Action =>
          (quittingTwoDateTimingGame reward).mixedExtension.eu profile 0) hupdate
      _ = (quittingTwoDateTimingGame prefixReward).mixedExtension.eu
          (activeProfile (PMF.pure action) equilibriumLaw) 0 :=
        activeProfile_mixedEU_eq_prefix _ _ _
      _ = _ := (congrArg (fun profile : Player → PMF Action =>
          (quittingTwoDateTimingGame prefixReward).mixedExtension.eu profile 0)
        hupdate).symm
  · by_cases hone : who = 1
    · subst who
      have hupdate : Function.update equilibriumProfile 1 (PMF.pure action) =
        activeProfile equilibriumLaw (PMF.pure action) := by
        funext player
        fin_cases player <;> simp [equilibriumProfile, activeProfile]
      calc
        _ = (quittingTwoDateTimingGame reward).mixedExtension.eu
            (activeProfile equilibriumLaw (PMF.pure action)) 1 :=
          congrArg (fun profile : Player → PMF Action =>
            (quittingTwoDateTimingGame reward).mixedExtension.eu profile 1) hupdate
        _ = (quittingTwoDateTimingGame prefixReward).mixedExtension.eu
            (activeProfile equilibriumLaw (PMF.pure action)) 1 :=
          activeProfile_mixedEU_eq_prefix _ _ _
        _ = _ := (congrArg (fun profile : Player → PMF Action =>
            (quittingTwoDateTimingGame prefixReward).mixedExtension.eu profile 1)
          hupdate).symm
    · rw [(quittingTwoDateTimingGame reward).mixedExtension_eu,
        (quittingTwoDateTimingGame prefixReward).mixedExtension_eu]
      simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
      simp_rw [← actionTime_two]
      change Math.Probability.expect
          (pmfPi (Function.update equilibriumProfile who (PMF.pure action)))
          (fun choices => purePayoff reward 2 choices who) =
        Math.Probability.expect
          (pmfPi (Function.update equilibriumProfile who (PMF.pure action)))
          (fun choices => purePayoff prefixReward 2 choices who)
      congr 1
      funext choices
      exact purePayoff_eq_prefix_of_dummy 2 choices who hzero hone

theorem canonicalProfile_isNash :
    (quittingTwoDateTimingGame prefixReward).mixedExtension.IsNash
      equilibriumProfile := by
  apply ((quittingTwoDateTimingGame prefixReward).isNash_iff_gains_nonpos
    equilibriumProfile).mpr
  intro who action
  change Action at action
  have hsharp := ((quittingTwoDateTimingGame reward).isNash_iff_gains_nonpos
    equilibriumProfile).mp equilibriumProfile_isNash who action
  have hbase :
      (quittingTwoDateTimingGame reward).mixedExtension.eu
          equilibriumProfile who =
        (quittingTwoDateTimingGame prefixReward).mixedExtension.eu
          equilibriumProfile who := by
    simpa only [equilibriumProfile] using
      activeProfile_mixedEU_eq_prefix equilibriumLaw equilibriumLaw who
  unfold KernelGame.mixedGain at hsharp ⊢
  rw [← canonical_pureDeviation_mixedEU_eq_prefix who action,
    ← hbase]
  exact hsharp


theorem nonUniqueNashProfile_ne_canonical :
    nonUniqueNashProfile ≠ equilibriumProfile := by
  intro heq
  have hlaw := congrFun heq 0
  have hmass := congrArg (fun law : PMF Action => (law now).toReal) hlaw
  have hcanonical := equilibriumLaw_now
  unfold mass at hcanonical
  simp [nonUniqueNashProfile, nonUniqueNashChoices, equilibriumProfile,
    activeProfile, never, now] at hmass
  change 0 = (equilibriumLaw now).toReal at hmass
  linarith

theorem prefixTimingGame_not_existsUniqueNash :
    ¬ ∃! mixed : Player → PMF Action,
      (quittingTwoDateTimingGame prefixReward).mixedExtension.IsNash mixed := by
  rintro ⟨selected, _hnash, hunique⟩
  have hfirst := hunique equilibriumProfile canonicalProfile_isNash
  have hsecond := hunique nonUniqueNashProfile nonUniqueNashProfile_isNash
  exact nonUniqueNashProfile_ne_canonical (hsecond.trans hfirst.symm)

end FixedPrefixTimingNashNonuniqueness
end GameTheory
