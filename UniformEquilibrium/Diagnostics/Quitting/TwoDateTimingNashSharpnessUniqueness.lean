/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TwoDateTimingNashSharpnessCore
import UniformEquilibrium.Diagnostics.FiniteMixedNashSupport

/-!
# Uniqueness of the sharp two-date timing Nash law

For the concrete normalized four-player sharpness table, every mixed Nash law
has the displayed active masses and both dummy players choose Never. Thus the
canonical timing law is the unique normal-form mixed Nash equilibrium.
-/

noncomputable section

namespace GameTheory
namespace TwoDateTimingNashSharpness

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

private theorem pure_dummy_now_general (choices : Player → Action)
    (dummy : Player) (hzero : dummy ≠ 0) (hone : dummy ≠ 1) :
    timingPurePayoff reward 2 (Function.update choices dummy now) dummy = -1 := by
  have hcurrent : (quittingQuitters fun player => timingActionCurrent
      (Function.update choices dummy now player)).Nonempty :=
    ⟨dummy, by simp [quittingQuitters, timingActionCurrent, now]⟩
  rw [timingPurePayoff_succ_of_current_nonempty reward 1 _ dummy hcurrent]
  simp only [reward, if_neg hzero, if_neg hone]
  rw [if_pos]
  simp [quittingQuitters, timingActionCurrent, now]

private theorem pure_dummy_never_general (choices : Player → Action)
    (dummy : Player) (hzero : dummy ≠ 0) (hone : dummy ≠ 1) :
    timingPurePayoff reward 2 (Function.update choices dummy never) dummy = 0 := by
  rw [timingPurePayoff_succ]
  unfold quittingRootPayoff
  split
  case isTrue hcurrent =>
    simp only [reward, if_neg hzero, if_neg hone]
    rw [if_neg]
    simp [quittingQuitters, timingActionCurrent, never]
  case isFalse hcurrent =>
    change timingPurePayoff reward 1
      (timingChoicesTail (Function.update choices dummy never)) dummy = 0
    rw [timingPurePayoff_succ]
    unfold quittingRootPayoff
    split
    case isTrue htail =>
      simp only [reward, if_neg hzero, if_neg hone]
      rw [if_neg]
      simp [quittingQuitters, timingChoicesTail, timingActionTail,
        timingActionCurrent, never]
    case isFalse htail => exact timingPurePayoff_zero reward _ dummy

theorem dummy_now_payoff (mixed : Player → PMF Action)
    (dummy : Player) (hzero : dummy ≠ 0) (hone : dummy ≠ 1) :
    (quittingTwoDateTimingGame reward).mixedExtension.eu
        (Function.update mixed dummy (PMF.pure now)) dummy = -1 := by
  letI : Finite (quittingTwoDateTimingGame reward).Outcome := by
    unfold quittingTwoDateTimingGame quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingTwoDateTimingGame reward).mixedExtension_eu]
  simp only [quittingTwoDateTimingGame, KernelGame.eu_ofPureEU]
  change Math.Probability.expect
      (pmfPi (Function.update mixed dummy (PMF.pure now)))
      (fun choices => timingPurePayoff reward 2 choices dummy) = -1
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
  change Math.Probability.expect
      (pmfPi (Function.update mixed dummy (PMF.pure never)))
      (fun choices => timingPurePayoff reward 2 choices dummy) = 0
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
  have hsupport := KernelGame.mixedGain_eq_zero_of_mem_support
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
    (hne : action ≠ now) : timingActionCurrent action = false := by
  cases hcurrent : timingActionCurrent action
  · rfl
  · exact False.elim (hne (by
      simpa only [now] using
        (timingActionCurrent_eq_true_iff action).mp hcurrent))

private theorem pure_column_value_of_row_now
    (choices : Player → Action)
    (hrow : choices 0 = now) :
    timingPurePayoff reward 2 choices 1 =
      if choices 1 = now then 1 else -1 := by
  have hnonempty : (quittingQuitters fun player =>
      timingActionCurrent (choices player)).Nonempty :=
    ⟨0, by simp [quittingQuitters, hrow, timingActionCurrent, now]⟩
  rw [timingPurePayoff_succ_of_current_nonempty reward 1 _ 1 hnonempty]
  have hrowCurrent : timingActionCurrent (choices 0) = true := by
    rw [hrow]
    rfl
  by_cases hcolumn : choices 1 = now
  · rw [if_pos hcolumn]
    have hcolumnCurrent : timingActionCurrent (choices 1) = true := by
      rw [hcolumn]
      rfl
    have hzeroMem : 0 ∈ quittingQuitters (fun player =>
        timingActionCurrent (choices player)) := by
      simpa [quittingQuitters] using hrowCurrent
    have honeMem : 1 ∈ quittingQuitters (fun player =>
        timingActionCurrent (choices player)) := by
      simpa [quittingQuitters] using hcolumnCurrent
    simp [reward, hzeroMem, honeMem]
  · rw [if_neg hcolumn]
    have hcolumnCurrent : timingActionCurrent (choices 1) = false :=
      actionCurrent_eq_false_of_ne_now _ hcolumn
    have hzeroMem : 0 ∈ quittingQuitters (fun player =>
        timingActionCurrent (choices player)) := by
      simpa [quittingQuitters] using hrowCurrent
    have honeMem : 1 ∉ quittingQuitters (fun player =>
        timingActionCurrent (choices player)) := by
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
  let deviated := Function.update mixed 1 (PMF.pure action)
  change Math.Probability.expect (pmfPi deviated)
      (fun choices => timingPurePayoff reward 2 choices 1) = _
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
    timingPurePayoff reward 2 choices 0 =
      if choices 0 = now then -1 else 1 := by
  have hnonempty : (quittingQuitters fun player =>
      timingActionCurrent (choices player)).Nonempty :=
    ⟨1, by simp [quittingQuitters, hcolumn, timingActionCurrent, now]⟩
  rw [timingPurePayoff_succ_of_current_nonempty reward 1 _ 0 hnonempty]
  have hcolumnCurrent : timingActionCurrent (choices 1) = true := by
    rw [hcolumn]
    rfl
  by_cases hrow : choices 0 = now
  · rw [if_pos hrow]
    have hrowCurrent : timingActionCurrent (choices 0) = true := by
      rw [hrow]
      rfl
    have hzeroMem : 0 ∈ quittingQuitters (fun player =>
        timingActionCurrent (choices player)) := by
      simpa [quittingQuitters] using hrowCurrent
    have honeMem : 1 ∈ quittingQuitters (fun player =>
        timingActionCurrent (choices player)) := by
      simpa [quittingQuitters] using hcolumnCurrent
    simp [reward, hzeroMem, honeMem]
  · rw [if_neg hrow]
    have hrowCurrent : timingActionCurrent (choices 0) = false :=
      actionCurrent_eq_false_of_ne_now _ hrow
    have hzeroMem : 0 ∉ quittingQuitters (fun player =>
        timingActionCurrent (choices player)) := by
      simpa [quittingQuitters] using hrowCurrent
    have honeMem : 1 ∈ quittingQuitters (fun player =>
        timingActionCurrent (choices player)) := by
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
  let deviated := Function.update mixed 0 (PMF.pure action)
  change Math.Probability.expect (pmfPi deviated)
      (fun choices => timingPurePayoff reward 2 choices 0) = _
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
      have hsupport := KernelGame.mixedGain_eq_zero_of_mem_support
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
        have hsupport := KernelGame.mixedGain_eq_zero_of_mem_support
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
    timingPurePayoff reward 2 choices 1 =
      if choices 0 = now then 1 else -1 := by
  have hnonempty : (quittingQuitters fun player =>
      timingActionCurrent (choices player)).Nonempty :=
    ⟨1, by simp [quittingQuitters, hcolumn, timingActionCurrent, now]⟩
  rw [timingPurePayoff_succ_of_current_nonempty reward 1 _ 1 hnonempty]
  have honeMem : 1 ∈ quittingQuitters (fun player =>
      timingActionCurrent (choices player)) := by
    simp [quittingQuitters, hcolumn, timingActionCurrent, now]
  by_cases hrow : choices 0 = now
  · rw [if_pos hrow]
    have hzeroMem : 0 ∈ quittingQuitters (fun player =>
        timingActionCurrent (choices player)) := by
      simp [quittingQuitters, hrow, timingActionCurrent, now]
    simp [reward, hzeroMem, honeMem]
  · rw [if_neg hrow]
    have hzeroCurrent := actionCurrent_eq_false_of_ne_now _ hrow
    have hzeroMem : 0 ∉ quittingQuitters (fun player =>
        timingActionCurrent (choices player)) := by
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
  let deviated := Function.update mixed 1 (PMF.pure now)
  change Math.Probability.expect (pmfPi deviated)
      (fun choices => timingPurePayoff reward 2 choices 1) = -1
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
  have hsupport := KernelGame.mixedGain_eq_zero_of_mem_support
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
      timingActionCurrent (choices player)).Nonempty := by
  rw [quittingQuitters_nonempty_iff]
  rintro ⟨player, hcurrent⟩
  exact hall player (by
    simpa only [now] using
      (timingActionCurrent_eq_true_iff _).mp hcurrent)

private theorem pure_column_next_value_of_no_dummy_now
    (rowAction dummyTwo dummyThree : Action)
    (htwo : dummyTwo ≠ now) (hthree : dummyThree ≠ now) :
    timingPurePayoff reward 2 ![rowAction, next, dummyTwo, dummyThree] 1 =
      if rowAction = next then 1 else -1 := by
  cases rowAction with
  | none =>
      change timingPurePayoff reward 2 ![never, next, dummyTwo, dummyThree] 1 =
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
      rw [timingPurePayoff_succ_of_current_empty reward 1 _ 1 hcurrent]
      have hone : 1 ∈ quittingQuitters (fun player => timingActionCurrent
          (timingChoicesTail ![never, next, dummyTwo, dummyThree] player)) := by
        simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
          true_and]
        change timingActionCurrent (timingActionTail next) = true
        decide
      rw [timingPurePayoff_succ_of_current_nonempty reward 0 _ 1 ⟨1, hone⟩]
      have hzero : 0 ∉ quittingQuitters (fun player => timingActionCurrent
          (timingChoicesTail ![never, next, dummyTwo, dummyThree] player)) := by
        simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
          true_and]
        change timingActionCurrent (timingActionTail never) ≠ true
        decide
      simp [reward, hzero, hone]
  | some rowTime =>
      fin_cases rowTime
      · change timingPurePayoff reward 2 ![now, next, dummyTwo, dummyThree] 1 =
          (if now = next then 1 else -1)
        rw [if_neg (by decide : now ≠ next)]
        have hcurrent : (quittingQuitters fun player =>
            timingActionCurrent (![now, next, dummyTwo, dummyThree] player)).Nonempty :=
          ⟨0, by simp [quittingQuitters, timingActionCurrent, now]⟩
        rw [timingPurePayoff_succ_of_current_nonempty reward 1 _ 1 hcurrent]
        have hzero : 0 ∈ quittingQuitters (fun player =>
            timingActionCurrent (![now, next, dummyTwo, dummyThree] player)) := by
          simp [quittingQuitters, timingActionCurrent, now]
        have hone : 1 ∉ quittingQuitters (fun player =>
            timingActionCurrent (![now, next, dummyTwo, dummyThree] player)) := by
          simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
            true_and]
          change timingActionCurrent next ≠ true
          decide
        simp [reward, hzero, hone]
      · change timingPurePayoff reward 2 ![next, next, dummyTwo, dummyThree] 1 =
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
        rw [timingPurePayoff_succ_of_current_empty reward 1 _ 1 hcurrent]
        have hzero : 0 ∈ quittingQuitters (fun player => timingActionCurrent
            (timingChoicesTail ![next, next, dummyTwo, dummyThree] player)) := by
          simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
            true_and]
          change timingActionCurrent (timingActionTail next) = true
          decide
        have hone : 1 ∈ quittingQuitters (fun player => timingActionCurrent
            (timingChoicesTail ![next, next, dummyTwo, dummyThree] player)) := by
          simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
            true_and]
          change timingActionCurrent (timingActionTail next) = true
          decide
        rw [timingPurePayoff_succ_of_current_nonempty reward 0 _ 1 ⟨1, hone⟩]
        simp [reward, hzero, hone]

private theorem pure_column_never_value_of_no_dummy_now
    (rowAction dummyTwo dummyThree : Action)
    (htwo : dummyTwo ≠ now) (hthree : dummyThree ≠ now) :
    timingPurePayoff reward 2 ![rowAction, never, dummyTwo, dummyThree] 1 =
      if rowAction = never then 0 else -1 := by
  cases rowAction with
  | none =>
      change timingPurePayoff reward 2 ![never, never, dummyTwo, dummyThree] 1 =
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
      rw [timingPurePayoff_succ_of_current_empty reward 1 _ 1 hcurrent]
      rw [timingPurePayoff_succ]
      unfold quittingRootPayoff
      split
      case isTrue htail =>
        have hzero : 0 ∉ quittingQuitters (fun player => timingActionCurrent
            (timingChoicesTail ![never, never, dummyTwo, dummyThree] player)) := by
          simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
            true_and]
          change timingActionCurrent (timingActionTail never) ≠ true
          decide
        have hone : 1 ∉ quittingQuitters (fun player => timingActionCurrent
            (timingChoicesTail ![never, never, dummyTwo, dummyThree] player)) := by
          simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
            true_and]
          change timingActionCurrent (timingActionTail never) ≠ true
          decide
        simp [reward, hzero, hone]
      case isFalse htail => exact timingPurePayoff_zero reward _ 1
  | some rowTime =>
      fin_cases rowTime
      · change timingPurePayoff reward 2 ![now, never, dummyTwo, dummyThree] 1 =
          (if now = never then 0 else -1)
        rw [if_neg (by decide : now ≠ never)]
        have hcurrent : (quittingQuitters fun player =>
            timingActionCurrent (![now, never, dummyTwo, dummyThree] player)).Nonempty :=
          ⟨0, by simp [quittingQuitters, timingActionCurrent, now]⟩
        rw [timingPurePayoff_succ_of_current_nonempty reward 1 _ 1 hcurrent]
        have hzero : 0 ∈ quittingQuitters (fun player =>
            timingActionCurrent (![now, never, dummyTwo, dummyThree] player)) := by
          simp [quittingQuitters, timingActionCurrent, now]
        have hone : 1 ∉ quittingQuitters (fun player =>
            timingActionCurrent (![now, never, dummyTwo, dummyThree] player)) := by
          simp [quittingQuitters, timingActionCurrent, never]
        simp [reward, hzero, hone]
      · change timingPurePayoff reward 2 ![next, never, dummyTwo, dummyThree] 1 =
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
        rw [timingPurePayoff_succ_of_current_empty reward 1 _ 1 hcurrent]
        have hzero : 0 ∈ quittingQuitters (fun player => timingActionCurrent
            (timingChoicesTail ![next, never, dummyTwo, dummyThree] player)) := by
          simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
            true_and]
          change timingActionCurrent (timingActionTail next) = true
          decide
        have hone : 1 ∉ quittingQuitters (fun player => timingActionCurrent
            (timingChoicesTail ![next, never, dummyTwo, dummyThree] player)) := by
          simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
            true_and]
          change timingActionCurrent (timingActionTail never) ≠ true
          decide
        rw [timingPurePayoff_succ_of_current_nonempty reward 0 _ 1 ⟨0, hzero⟩]
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
  let deviated := Function.update mixed 1 (PMF.pure next)
  change Math.Probability.expect (pmfPi deviated)
      (fun choices => timingPurePayoff reward 2 choices 1) = _
  have hintegrand : Math.Probability.expect (pmfPi deviated)
      (fun choices => timingPurePayoff reward 2 choices 1) =
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
  let deviated := Function.update mixed 1 (PMF.pure never)
  change Math.Probability.expect (pmfPi deviated)
      (fun choices => timingPurePayoff reward 2 choices 1) = _
  have hintegrand : Math.Probability.expect (pmfPi deviated)
      (fun choices => timingPurePayoff reward 2 choices 1) =
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
    (quittingQuitters fun player => timingActionCurrent
        (![rowAction, columnAction, next, otherAction] player)).Nonempty ↔
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
    · apply False.elim
      apply hother
      apply (timingActionCurrent_eq_true_iff otherAction).mp
      simpa using hplayer
  · rintro (hrow | hcolumn)
    · exact ⟨0, by simp [hrow, timingActionCurrent, now]⟩
    · exact ⟨1, by simp [hcolumn, timingActionCurrent, now]⟩

private theorem pure_dummy_two_next_value_of_other_ne_now
    (rowAction columnAction otherAction : Action)
    (hother : otherAction ≠ now) :
    timingPurePayoff reward 2 ![rowAction, columnAction, next, otherAction] 2 =
      if rowAction = now ∨ columnAction = now then 0 else -1 := by
  rw [timingPurePayoff_succ]
  unfold quittingRootPayoff
  split
  case isTrue hcurrent =>
    rw [if_pos ((dummy_two_current_nonempty_iff_of_other_ne_now
      rowAction columnAction otherAction hother).mp hcurrent)]
    simp only [reward, if_neg (by decide : (2 : Player) ≠ 0),
      if_neg (by decide : (2 : Player) ≠ 1)]
    rw [if_neg]
    have hfun : (fun player => timingActionCurrent
        (![rowAction, columnAction, next, otherAction] player)) =
        ![timingActionCurrent rowAction, timingActionCurrent columnAction,
          timingActionCurrent next, timingActionCurrent otherAction] := by
      funext player
      fin_cases player <;> rfl
    rw [hfun]
    have hnext : timingActionCurrent next = false := by decide
    have hotherCurrent := actionCurrent_eq_false_of_ne_now _ hother
    rw [hnext, hotherCurrent]
    cases hrow : timingActionCurrent rowAction <;>
      cases hcolumn : timingActionCurrent columnAction <;>
        simp [quittingQuitters_vec4]
  case isFalse hcurrent =>
    rw [if_neg (not_congr (dummy_two_current_nonempty_iff_of_other_ne_now
      rowAction columnAction otherAction hother) |>.mp hcurrent)]
    change timingPurePayoff reward 1
      (timingChoicesTail ![rowAction, columnAction, next, otherAction]) 2 = -1
    have htwo : 2 ∈ quittingQuitters (fun player => timingActionCurrent
        (timingChoicesTail ![rowAction, columnAction, next, otherAction] player)) := by
      simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
        true_and]
      change timingActionCurrent (timingActionTail next) = true
      decide
    rw [timingPurePayoff_succ_of_current_nonempty reward 0 _ 2 ⟨2, htwo⟩]
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
  let deviated := Function.update mixed 2 (PMF.pure next)
  change Math.Probability.expect (pmfPi deviated)
      (fun choices => timingPurePayoff reward 2 choices 2) = _
  have hintegrand : Math.Probability.expect (pmfPi deviated)
      (fun choices => timingPurePayoff reward 2 choices 2) =
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
    (quittingQuitters fun player => timingActionCurrent
        (![rowAction, columnAction, otherAction, next] player)).Nonempty ↔
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
    · apply False.elim
      apply hother
      apply (timingActionCurrent_eq_true_iff otherAction).mp
      simpa using hplayer
    · exact False.elim ((by decide : timingActionCurrent next ≠ true) hplayer)
  · rintro (hrow | hcolumn)
    · exact ⟨0, by simp [hrow, timingActionCurrent, now]⟩
    · exact ⟨1, by simp [hcolumn, timingActionCurrent, now]⟩

private theorem pure_dummy_three_next_value_of_other_ne_now
    (rowAction columnAction otherAction : Action)
    (hother : otherAction ≠ now) :
    timingPurePayoff reward 2 ![rowAction, columnAction, otherAction, next] 3 =
      if rowAction = now ∨ columnAction = now then 0 else -1 := by
  rw [timingPurePayoff_succ]
  unfold quittingRootPayoff
  split
  case isTrue hcurrent =>
    rw [if_pos ((dummy_three_current_nonempty_iff_of_other_ne_now
      rowAction columnAction otherAction hother).mp hcurrent)]
    simp only [reward, if_neg (by decide : (3 : Player) ≠ 0),
      if_neg (by decide : (3 : Player) ≠ 1)]
    rw [if_neg]
    have hfun : (fun player => timingActionCurrent
        (![rowAction, columnAction, otherAction, next] player)) =
        ![timingActionCurrent rowAction, timingActionCurrent columnAction,
          timingActionCurrent otherAction, timingActionCurrent next] := by
      funext player
      fin_cases player <;> rfl
    rw [hfun]
    have hnext : timingActionCurrent next = false := by decide
    have hotherCurrent := actionCurrent_eq_false_of_ne_now _ hother
    rw [hnext, hotherCurrent]
    cases hrow : timingActionCurrent rowAction <;>
      cases hcolumn : timingActionCurrent columnAction <;>
        simp [quittingQuitters_vec4]
  case isFalse hcurrent =>
    rw [if_neg (not_congr (dummy_three_current_nonempty_iff_of_other_ne_now
      rowAction columnAction otherAction hother) |>.mp hcurrent)]
    change timingPurePayoff reward 1
      (timingChoicesTail ![rowAction, columnAction, otherAction, next]) 3 = -1
    have hthree : 3 ∈ quittingQuitters (fun player => timingActionCurrent
        (timingChoicesTail ![rowAction, columnAction, otherAction, next] player)) := by
      simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
        true_and]
      change timingActionCurrent (timingActionTail next) = true
      decide
    rw [timingPurePayoff_succ_of_current_nonempty reward 0 _ 3 ⟨3, hthree⟩]
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
  let deviated := Function.update mixed 3 (PMF.pure next)
  change Math.Probability.expect (pmfPi deviated)
      (fun choices => timingPurePayoff reward 2 choices 3) = _
  have hintegrand : Math.Probability.expect (pmfPi deviated)
      (fun choices => timingPurePayoff reward 2 choices 3) =
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
  have hsupport := KernelGame.mixedGain_eq_zero_of_mem_support
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
  have hsupport := KernelGame.mixedGain_eq_zero_of_mem_support
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


end TwoDateTimingNashSharpness
end GameTheory
