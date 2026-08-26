/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.Independence
import MathUE.ProbabilityMassFunction.Coupling
import UniformEquilibrium.Diagnostics.Quitting.FiniteDeadlineTimingGame

/-!
# Finite-deadline timing recursion

This module owns the table-independent first-date decomposition of finite
quitting timing laws. It supplies exact marginal disintegration, Bellman
peeling, conditional-tail Nash transfer under positive current Continue
reach, and the one-step behavioral spine identification.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (reward : {S : Finset ι // S.Nonempty} → Payoff ι)

/-! ## Splitting a finite timing action at its first date -/

/-- Whether a timing action stops at the current date. -/
def timingActionCurrent {dates : ℕ} :
    QuittingFiniteDeadlineTimingAction (dates + 1) → Bool
  | none => false
  | some time => Fin.cases true (fun _ => false) time

/-- Remove the current date from a timing action which continues now.
The current action itself is sent to `Never`; this fallback is irrelevant
after conditioning on current continuation. -/
def timingActionTail {dates : ℕ} :
    QuittingFiniteDeadlineTimingAction (dates + 1) →
      QuittingFiniteDeadlineTimingAction dates
  | none => none
  | some time => Fin.cases none (fun tail => some tail) time

/-- Embed a tail timing action one date after the current date. -/
def timingActionLift {dates : ℕ} :
    QuittingFiniteDeadlineTimingAction dates →
      QuittingFiniteDeadlineTimingAction (dates + 1)
  | none => none
  | some time => some time.succ

@[simp] theorem timingActionCurrent_zero {dates : ℕ}
    (hzero : 0 < dates + 1) :
    timingActionCurrent (some ⟨0, hzero⟩) = true := by
  simp [timingActionCurrent]

/-- A finite timing action quits at the current date exactly when it is the
distinguished date-zero action. -/
theorem timingActionCurrent_eq_true_iff {dates : ℕ}
    (action : QuittingFiniteDeadlineTimingAction (dates + 1)) :
    timingActionCurrent action = true ↔
      action = some (0 : Fin (dates + 1)) := by
  cases action with
  | none => simp [timingActionCurrent]
  | some time =>
      cases time using Fin.cases with
      | zero => simp [timingActionCurrent]
      | succ tail => simp [timingActionCurrent]

@[simp] theorem timingActionTail_zero {dates : ℕ}
    (hzero : 0 < dates + 1) :
    timingActionTail (some ⟨0, hzero⟩) = none := rfl

@[simp] theorem timingActionCurrent_lift {dates : ℕ}
    (action : QuittingFiniteDeadlineTimingAction dates) :
    timingActionCurrent (timingActionLift action) = false := by
  cases action with
  | none => rfl
  | some time => simp [timingActionLift, timingActionCurrent]

@[simp] theorem timingActionTail_lift {dates : ℕ}
    (action : QuittingFiniteDeadlineTimingAction dates) :
    timingActionTail (timingActionLift action) = action := by
  cases action with
  | none => rfl
  | some time =>
      simp only [timingActionLift]
      cases time with
      | mk value hvalue =>
          simp [timingActionTail]

theorem timingAction_lift_tail_of_continue {dates : ℕ}
    (action : QuittingFiniteDeadlineTimingAction (dates + 1))
    (hcontinue : timingActionCurrent action = false) :
    timingActionLift (timingActionTail action) = action := by
  cases action with
  | none => rfl
  | some time =>
      cases time using Fin.cases with
      | zero =>
          change true = false at hcontinue
          simp at hcontinue
      | succ time =>
          apply congrArg some
          apply Fin.ext
          rfl

/-- The conditional shifted tail law after the player continues now. -/
def timingLawTail {dates : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction (dates + 1))) :
    PMF (QuittingFiniteDeadlineTimingAction dates) :=
  (condOn law timingActionCurrent false).map timingActionTail

/-- Lifting the conditional tail law reconstructs the original law
conditioned on current continuation. -/
theorem timingLawTail_map_lift {dates : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hcontinue : pushforward law timingActionCurrent false ≠ 0) :
    (timingLawTail law).map timingActionLift =
      condOn law timingActionCurrent false := by
  rw [timingLawTail, PMF.map_comp]
  apply PMF.map_eq_self_of_eq_on_support
  intro action hmass
  apply timingAction_lift_tail_of_continue
  apply condOn_support_project law timingActionCurrent false hcontinue
  simpa only [PMF.mem_support_iff] using hmass

/-! ## The literal first-stage decomposition -/

omit [DecidableEq ι] in
/-- A finite timing-law profile is its first live root followed by its
all-Continue spine. -/
theorem finiteDeadlineTimingProfile_eq_rootThen_spine
    (dates : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction dates)) :
    quittingFiniteDeadlineTimingProfile reward dates mixed =
      quittingRootThenContinuationProfile reward
        (quittingProfileRoot reward
          (quittingFiniteDeadlineTimingProfile reward dates mixed))
        (quittingAllContinueProfileSpine reward
          (quittingFiniteDeadlineTimingProfile reward dates mixed) 1) := by
  funext who time history
  cases time with
  | zero => rfl
  | succ time => rfl

omit [DecidableEq ι] in
/-- The first live-root quitting probability is the mass of the current
timing action. -/
theorem finiteDeadlineTimingProfile_root_true
    (dates : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (who : ι) :
    ((quittingProfileRoot reward
        (quittingFiniteDeadlineTimingProfile reward (dates + 1) mixed)
        who true).toReal) =
      ((mixed who) (some ⟨0, Nat.zero_lt_succ dates⟩)).toReal := by
  unfold quittingProfileRoot quittingFiniteDeadlineTimingProfile
    quittingCompactStoppingLawProfile quittingStoppingLawBehaviorStrategy
    quittingFiniteDeadlineTimingLaw
  simp only [Math.Probability.CompactStoppingLaw.toPMF_ofPMF,
    Math.Probability.DiscreteHazard.ScalarHazard.toBoolean,
    Math.Probability.DiscreteHazard.booleanCoin_true_toReal]
  unfold Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard
  simp only [Math.Probability.DiscreteHazard.StoppingLaw.survival_zero,
    one_ne_zero, if_false, div_one]
  unfold Math.Probability.DiscreteHazard.StoppingLaw.finiteMass
  change (((mixed who).map quittingFiniteDeadlineTimingActionTime
      (WithTop.some 0)).toReal) = _
  rw [PMF.map_apply]
  rw [tsum_eq_single (some ⟨0, Nat.zero_lt_succ dates⟩)]
  · simp [quittingFiniteDeadlineTimingActionTime]
  · intro action haction
    cases action with
    | none => simp [quittingFiniteDeadlineTimingActionTime]
    | some time =>
        by_cases htime : time.val = 0
        · have heq : time = ⟨0, Nat.zero_lt_succ dates⟩ := Fin.ext htime
          exact (haction (congrArg some heq)).elim
        · simp only [quittingFiniteDeadlineTimingActionTime]
          split_ifs with heq
          · exfalso
            apply htime
            exact_mod_cast heq.symm
          · rfl

/-- Pushing a timing law to its current-action indicator reads exactly the
mass of the distinguished date-zero atom. -/
theorem timingActionCurrent_pushforward_true {dates : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction (dates + 1))) :
    (pushforward law timingActionCurrent true).toReal =
      (law (some ⟨0, Nat.zero_lt_succ dates⟩)).toReal := by
  unfold pushforward
  rw [PMF.map_apply]
  rw [tsum_eq_single (some ⟨0, Nat.zero_lt_succ dates⟩)]
  · have hzero : timingActionCurrent
        (some ⟨0, Nat.zero_lt_succ dates⟩) = true := rfl
    rw [hzero]
    simp
  · intro action haction
    cases action with
    | none => simp [timingActionCurrent]
    | some time =>
        cases time using Fin.cases with
        | zero => exact (haction rfl).elim
        | succ later => simp [timingActionCurrent]

/-- The current-Quit marginal is the distinguished date-zero atom. -/
theorem timingActionCurrent_pushforward_true_zero {dates : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction (dates + 1))) :
    (pushforward law timingActionCurrent true).toReal =
      (law (some (0 : Fin (dates + 1)))).toReal := by
  rw [timingActionCurrent_pushforward_true]
  congr 3

/-- Strictly subunit current mass gives positive probability of current
continuation, so the conditional tail law is in its genuine branch. -/
theorem timingActionCurrent_false_ne_zero_of_lt_one {dates : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hcurrent : (law (some ⟨0, Nat.zero_lt_succ dates⟩)).toReal < 1) :
    pushforward law timingActionCurrent false ≠ 0 := by
  have hsum := Math.Probability.pmf_toReal_sum_one
    (pushforward law timingActionCurrent)
  simp only [Fintype.sum_bool] at hsum
  have htrue := timingActionCurrent_pushforward_true law
  intro hzero
  have hfalse : (pushforward law timingActionCurrent false).toReal = 0 := by
    rw [hzero]
    rfl
  linarith

/-- A finite atom of the conditional tail is the corresponding shifted
source atom divided by the probability of current continuation. -/
theorem timingLawTail_apply_some {dates : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hcontinue : pushforward law timingActionCurrent false ≠ 0)
    (time : Fin dates) :
    timingLawTail law (some time) =
      law (some time.succ) /
        pushforward law timingActionCurrent false := by
  unfold timingLawTail
  rw [PMF.map_apply]
  rw [tsum_eq_single (some time.succ)]
  · have htail : timingActionTail (some time.succ) = some time := by
      simpa only [timingActionLift] using
        (timingActionTail_lift (some time))
    rw [htail, if_pos rfl,
      condOn_apply law timingActionCurrent false
        (some time.succ) hcontinue]
    simp [timingActionCurrent]
  · intro action haction
    cases action with
    | none => simp [timingActionTail]
    | some sourceTime =>
        cases sourceTime using Fin.cases with
        | zero =>
            simp only [timingActionTail]
            simp
        | succ sourceTail =>
            have htail : timingActionTail (some sourceTail.succ) =
                some sourceTail := by
              simpa only [timingActionLift] using
                (timingActionTail_lift (some sourceTail))
            rw [htail]
            by_cases heq : sourceTail = time
            · subst sourceTail
              exact (haction rfl).elim
            · rw [if_neg]
              exact fun h ↦ heq (Option.some.inj h.symm)

/-- Replace only the conditional tail of a timing law, preserving its
current-action component exactly. -/
def timingLawWithTail {dates : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (tail : PMF (QuittingFiniteDeadlineTimingAction dates)) :
    PMF (QuittingFiniteDeadlineTimingAction (dates + 1)) :=
  (pushforward law timingActionCurrent).bind fun now =>
    if now then condOn law timingActionCurrent true
    else tail.map timingActionLift

/-- Reinstalling a law's own conditional tail leaves the law unchanged. -/
theorem timingLawWithTail_self {dates : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hcontinue : pushforward law timingActionCurrent false ≠ 0) :
    timingLawWithTail law (timingLawTail law) = law := by
  rw [timingLawWithTail, timingLawTail_map_lift law hcontinue]
  have hdisintegration :=
    bind_pushforward_condOn_pure law timingActionCurrent
  calc
    (pushforward law timingActionCurrent).bind (fun now =>
        if now then condOn law timingActionCurrent true
        else condOn law timingActionCurrent false) =
      (pushforward law timingActionCurrent).bind (fun now =>
        condOn law timingActionCurrent now) := by
          congr 1
          funext now
          cases now <;> rfl
    _ = law := hdisintegration.symm

/-- Coordinatewise first-stage disintegration preserves independence: first
sample the current Boolean decisions, then independently sample every
conditional timing action. -/
theorem pmfPi_disintegrate_timingCurrent (dates : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (dates + 1))) :
    pmfPi mixed =
      (pmfPi fun who ↦ pushforward (mixed who) timingActionCurrent).bind
        (fun now ↦ pmfPi fun who ↦
          condOn (mixed who) timingActionCurrent (now who)) := by
  let current : ι → PMF Bool := fun who ↦
    pushforward (mixed who) timingActionCurrent
  let conditional : (ι → Bool) → ι →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)) :=
    fun now who ↦ condOn (mixed who) timingActionCurrent (now who)
  have hfactor := pmfPi_bind_pmfPi_of_disjoint_coords
    current conditional (fun who ↦ some who)
    (fun who hnone ↦ by simp at hnone)
    (fun who coordinate hcoordinate other hother source replacement ↦ by
      have hwho : who = coordinate := Option.some.inj hcoordinate
      subst coordinate
      unfold conditional
      change condOn (mixed who) timingActionCurrent
        (Function.update source other replacement who) =
          condOn (mixed who) timingActionCurrent (source who)
      rw [Function.update_of_ne (Ne.symm hother)])
    (fun first second coordinate hfirst hsecond ↦ by
      exact Option.some.inj (hfirst.trans hsecond.symm))
  rw [hfactor]
  symm
  apply congrArg pmfPi
  funext who
  calc
    (pmfPi current).bind (fun now ↦ conditional now who) =
        (pushforward (pmfPi current) fun now ↦ now who).bind
          (fun now ↦ condOn (mixed who) timingActionCurrent now) := by
            exact (PMF.bind_map (pmfPi current) (fun now ↦ now who)
              (fun now ↦ condOn (mixed who) timingActionCurrent now)).symm
    _ = (current who).bind
          (fun now ↦ condOn (mixed who) timingActionCurrent now) := by
            rw [pmfPi_push_coord]
    _ = mixed who :=
      (bind_pushforward_condOn_pure (mixed who) timingActionCurrent).symm

private theorem condOn_map_project_apply_other_eq_zero
    {A : Type*} (law : PMF A) (project : A → Bool)
    (value other : Bool) (hvalue : pushforward law project value ≠ 0)
    (hother : other ≠ value) :
    (condOn law project value).map project other = 0 := by
  rw [PMF.map_apply]
  rw [ENNReal.tsum_eq_zero]
  intro action
  by_cases haction : other = project action
  · rw [if_pos haction,
      condOn_apply law project value action hvalue]
    rw [if_neg]
    exact fun heq ↦ hother (haction.trans heq)
  · rw [if_neg haction]

/-- Conditioning a finite law on a positive projection fibre makes the
projected conditional law deterministic. -/
theorem condOn_map_timingActionCurrent_eq_pure {dates : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (value : Bool) (hvalue : pushforward law timingActionCurrent value ≠ 0) :
    (condOn law timingActionCurrent value).map timingActionCurrent =
      PMF.pure value := by
  cases value with
  | false =>
      apply Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
      rw [condOn_map_project_apply_other_eq_zero law timingActionCurrent
        false true hvalue (by decide)]
      rfl
  | true =>
      apply (pmf_eq_pure_true_iff_apply_false_eq_zero _).2
      exact condOn_map_project_apply_other_eq_zero law timingActionCurrent
        true false hvalue (by decide)

/-- Replacing the conditional tail preserves the current Boolean marginal. -/
theorem timingLawWithTail_map_current {dates : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (tail : PMF (QuittingFiniteDeadlineTimingAction dates)) :
    pushforward (timingLawWithTail law tail) timingActionCurrent =
      pushforward law timingActionCurrent := by
  unfold timingLawWithTail
  rw [pushforward_bind]
  let current := pushforward law timingActionCurrent
  calc
    current.bind (fun now ↦ pushforward
        (if now then condOn law timingActionCurrent true
        else tail.map timingActionLift) timingActionCurrent) =
      current.bind PMF.pure := by
        apply bind_congr_on_support
        intro now hnow
        cases now with
        | false =>
            simp only [Bool.false_eq_true, if_false]
            unfold pushforward
            rw [PMF.map_comp]
            convert PMF.map_const tail false using 1
            apply congrArg (fun mapChoice :
              QuittingFiniteDeadlineTimingAction dates → Bool ↦
                tail.map mapChoice)
            funext action
            exact timingActionCurrent_lift action
        | true =>
            simp only [if_true]
            apply condOn_map_timingActionCurrent_eq_pure
            simpa only [current, PMF.mem_support_iff] using hnow
    _ = current := PMF.bind_pure current

theorem map_timingActionLift_apply_eq_zero_of_current
    {dates : ℕ}
    (tail : PMF (QuittingFiniteDeadlineTimingAction dates))
    (action : QuittingFiniteDeadlineTimingAction (dates + 1))
    (haction : timingActionCurrent action = true) :
    tail.map timingActionLift action = 0 := by
  rw [PMF.map_apply, ENNReal.tsum_eq_zero]
  intro tailAction
  rw [if_neg]
  intro heq
  have hfalse := timingActionCurrent_lift tailAction
  rw [← heq, haction] at hfalse
  contradiction

private theorem timingLawWithTail_apply_of_continue {dates : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (tail : PMF (QuittingFiniteDeadlineTimingAction dates))
    (action : QuittingFiniteDeadlineTimingAction (dates + 1))
    (haction : timingActionCurrent action = false) :
    timingLawWithTail law tail action =
      pushforward law timingActionCurrent false *
        tail.map timingActionLift action := by
  unfold timingLawWithTail
  rw [PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
  simp only [Bool.false_eq_true, if_false, if_true]
  have htrueTerm :
      pushforward law timingActionCurrent true *
        condOn law timingActionCurrent true action = 0 := by
    by_cases htrue : pushforward law timingActionCurrent true = 0
    · simp [htrue]
    · rw [condOn_apply law timingActionCurrent true action htrue]
      simp [haction]
  rw [htrueTerm, zero_add]

/-- The conditional Continue fibre of a tail-replaced law is exactly the
lifted replacement tail. -/
theorem condOn_timingLawWithTail_false {dates : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (tail : PMF (QuittingFiniteDeadlineTimingAction dates))
    (hcontinue : pushforward law timingActionCurrent false ≠ 0) :
    condOn (timingLawWithTail law tail) timingActionCurrent false =
      tail.map timingActionLift := by
  have hsourceContinue : pushforward (timingLawWithTail law tail)
      timingActionCurrent false ≠ 0 := by
    rw [timingLawWithTail_map_current]
    exact hcontinue
  apply PMF.ext
  intro action
  rw [condOn_apply (timingLawWithTail law tail)
    timingActionCurrent false action hsourceContinue]
  by_cases haction : timingActionCurrent action = false
  · rw [if_pos haction,
      timingLawWithTail_apply_of_continue law tail action haction]
    rw [timingLawWithTail_map_current]
    rw [mul_comm]
    exact ENNReal.mul_div_cancel_right hcontinue
      (PMF.apply_ne_top (pushforward law timingActionCurrent) false)
  · have htrue : timingActionCurrent action = true := by
      cases hvalue : timingActionCurrent action <;> simp_all
    rw [if_neg haction,
      map_timingActionLift_apply_eq_zero_of_current tail action htrue]

/-- Extracting the conditional tail after replacement returns the supplied
tail law exactly. -/
theorem timingLawTail_withTail {dates : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (tail : PMF (QuittingFiniteDeadlineTimingAction dates))
    (hcontinue : pushforward law timingActionCurrent false ≠ 0) :
    timingLawTail (timingLawWithTail law tail) = tail := by
  unfold timingLawTail
  rw [condOn_timingLawWithTail_false law tail hcontinue,
    PMF.map_comp]
  convert PMF.map_id tail using 1
  apply congrArg (fun mapChoice :
    QuittingFiniteDeadlineTimingAction dates →
      QuittingFiniteDeadlineTimingAction dates ↦ tail.map mapChoice)
  funext action
  exact timingActionTail_lift action

theorem pmfPi_coord_ne_zero_of_ne_zero
    {I : Type*} [Fintype I] {A : I → Type*}
    (laws : (i : I) → PMF (A i)) (values : (i : I) → A i)
    (hvalues : pmfPi laws values ≠ 0) (who : I) :
    laws who (values who) ≠ 0 := by
  intro hzero
  apply hvalues
  rw [pmfPi_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ who) hzero

/-! ## Recursive pure timing payoffs -/

/-- Deterministic current root extracted from a pure timing profile. -/
def timingChoicesRoot {dates : ℕ}
    (choices : ι → QuittingFiniteDeadlineTimingAction (dates + 1)) :
    ι → PMF Bool :=
  fun who ↦ PMF.pure (timingActionCurrent (choices who))

/-- Shift every continuing pure timing action into the tail game. -/
def timingChoicesTail {dates : ℕ}
    (choices : ι → QuittingFiniteDeadlineTimingAction (dates + 1)) :
    ι → QuittingFiniteDeadlineTimingAction dates :=
  fun who ↦ timingActionTail (choices who)

omit [DecidableEq ι] in
/-- A deterministic timing profile peels into its current pure root and its
shifted deterministic tail. -/
theorem pureTimingProfile_succ_eq_rootThen
    (dates : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction (dates + 1)) :
    quittingPureStoppingTimeProfile reward (fun who ↦
        quittingFiniteDeadlineTimingActionTime (choices who)) =
      quittingRootThenContinuationProfile reward
        (timingChoicesRoot choices)
        (quittingPureStoppingTimeProfile reward (fun who ↦
          quittingFiniteDeadlineTimingActionTime
            (timingChoicesTail choices who))) := by
  funext who time history
  cases time with
  | zero =>
      unfold quittingPureStoppingTimeProfile
        quittingPureTimeBehaviorStrategy timingChoicesRoot
        quittingRootThenContinuationProfile
      cases hchoice : choices who with
      | none => simp [hchoice, quittingFiniteDeadlineTimingActionTime,
          timingActionCurrent, quittingPureTimeHazard]
      | some finiteTime =>
          cases finiteTime using Fin.cases with
          | zero => simp [hchoice, quittingFiniteDeadlineTimingActionTime,
              timingActionCurrent, quittingPureTimeHazard]
          | succ tailTime =>
              simp [hchoice, quittingFiniteDeadlineTimingActionTime,
                timingActionCurrent, quittingPureTimeHazard]
              change (if 0 = tailTime.val + 1 then PMF.pure true
                else PMF.pure false) = PMF.pure false
              simp
  | succ time =>
      unfold quittingPureStoppingTimeProfile
        quittingPureTimeBehaviorStrategy timingChoicesTail
        quittingRootThenContinuationProfile
      cases hchoice : choices who with
      | none => simp [hchoice, quittingFiniteDeadlineTimingActionTime,
          timingActionTail, quittingPureTimeHazard]
      | some finiteTime =>
          cases finiteTime using Fin.cases with
          | zero =>
              simp [hchoice, quittingFiniteDeadlineTimingActionTime,
                timingActionTail, quittingPureTimeHazard]
          | succ tailTime =>
              simp [hchoice, quittingFiniteDeadlineTimingActionTime,
                timingActionTail, quittingPureTimeHazard]
              change (if time + 1 = tailTime.val + 1 then PMF.pure true
                else PMF.pure false) =
                  if time = tailTime.val then PMF.pure true else PMF.pure false
              simp only [Nat.add_right_cancel_iff]

/-- Pure payoff of a finite timing profile, with a short name for the
backward-induction calculation. -/
def timingPurePayoff (dates : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction dates)
    (who : ι) : ℝ :=
  quittingTerminalPayoff reward
    (quittingPureStoppingTimeProfile reward fun player ↦
      quittingFiniteDeadlineTimingActionTime (choices player)) who

omit [DecidableEq ι] in
/-- Bellman peeling for a deterministic finite timing profile. -/
theorem timingPurePayoff_succ
    (dates : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction (dates + 1))
    (who : ι) :
    timingPurePayoff reward (dates + 1) choices who =
      quittingRootPayoff reward
        (fun player ↦ timingPurePayoff reward dates
          (timingChoicesTail choices) player)
        (fun player ↦ timingActionCurrent (choices player)) who := by
  unfold timingPurePayoff
  rw [pureTimingProfile_succ_eq_rootThen reward,
    quittingTerminalPayoff_rootThenContinuation_eq]
  unfold quittingRootExpectedPayoff timingChoicesRoot
  rw [pmfPi_pure]
  simp [Math.Probability.expect_pure]

omit [DecidableEq ι] in
/-- At a nonempty current quitting coalition, the pure timing payoff is the
corresponding terminal reward. -/
theorem timingPurePayoff_succ_of_current_nonempty
    (dates : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction (dates + 1))
    (who : ι)
    (hcurrent : (quittingQuitters fun player ↦
      timingActionCurrent (choices player)).Nonempty) :
    timingPurePayoff reward (dates + 1) choices who =
      reward
        ⟨quittingQuitters (fun player ↦
          timingActionCurrent (choices player)), hcurrent⟩ who := by
  rw [timingPurePayoff_succ reward, quittingRootPayoff, dif_pos hcurrent]

omit [DecidableEq ι] in
/-- If every player continues at the current date, the pure timing payoff is
the shifted tail payoff. -/
theorem timingPurePayoff_succ_of_current_empty
    (dates : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction (dates + 1))
    (who : ι)
    (hcurrent : ¬(quittingQuitters fun player ↦
      timingActionCurrent (choices player)).Nonempty) :
    timingPurePayoff reward (dates + 1) choices who =
      timingPurePayoff reward dates (timingChoicesTail choices) who := by
  rw [timingPurePayoff_succ reward, quittingRootPayoff, dif_neg hcurrent]

omit [DecidableEq ι] in
/-- A zero-date pure timing profile never quits and has zero terminal payoff. -/
theorem timingPurePayoff_zero
    (choices : ι → QuittingFiniteDeadlineTimingAction 0)
    (who : ι) : timingPurePayoff reward 0 choices who = 0 := by
  have hchoices : choices = fun _ ↦ none := by
    funext player
    cases h : choices player with
    | none => rfl
    | some time => exact Fin.elim0 time
  rw [hchoices]
  have hprofile :
      (quittingPureStoppingTimeProfile reward fun _ : ι ↦
        quittingFiniteDeadlineTimingActionTime
          (none : QuittingFiniteDeadlineTimingAction 0)) =
        quittingAlwaysContinueProfile reward := by
    funext player time history
    simp [quittingAlwaysContinueProfile, quittingPureStoppingTimeProfile,
      StochasticGame.stationaryBehaviorProfile,
      quittingPureTimeBehaviorStrategy,
      quittingFiniteDeadlineTimingActionTime, quittingPureTimeHazard]
    rfl
  unfold timingPurePayoff
  rw [hprofile, quittingTerminalPayoff_quittingAlwaysContinue]

/-- Expected payoff under independent mixed timing laws. -/
def timingMixedPayoff (dates : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction dates))
    (who : ι) : ℝ :=
  Math.Probability.expect (pmfPi mixed)
    (fun choices ↦ timingPurePayoff reward dates choices who)

omit [DecidableEq ι] in
private theorem timingActionCurrent_eq_of_mem_conditionalProduct_support
    (dates : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (now : ι → Bool)
    (hnow : pmfPi (fun who ↦
      pushforward (mixed who) timingActionCurrent) now ≠ 0)
    {choices : ι → QuittingFiniteDeadlineTimingAction (dates + 1)}
    (hchoices : choices ∈ (pmfPi fun who ↦
      condOn (mixed who) timingActionCurrent (now who)).support) :
    (fun who ↦ timingActionCurrent (choices who)) = now := by
  funext who
  have hnowWho : pushforward (mixed who) timingActionCurrent (now who) ≠ 0 :=
    pmfPi_coord_ne_zero_of_ne_zero
      (fun player ↦ pushforward (mixed player) timingActionCurrent)
      now hnow who
  have hchoiceWho :
      condOn (mixed who) timingActionCurrent (now who) (choices who) ≠ 0 :=
    pmfPi_coord_ne_zero_of_ne_zero
      (fun player ↦ condOn (mixed player) timingActionCurrent (now player))
      choices (by simpa only [PMF.mem_support_iff] using hchoices) who
  exact condOn_support_project (mixed who) timingActionCurrent (now who)
    hnowWho (by simpa only [PMF.mem_support_iff] using hchoiceWho)

omit [DecidableEq ι] in
/-- Conditional on a supported current root, the inner timing payoff is the
one-stage root payoff whose continuation is the independently shifted tail. -/
theorem expect_conditional_timingPurePayoff
    (dates : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (now : ι → Bool)
    (hnow : pmfPi (fun who ↦
      pushforward (mixed who) timingActionCurrent) now ≠ 0)
    (who : ι) :
    Math.Probability.expect
        (pmfPi fun player ↦
          condOn (mixed player) timingActionCurrent (now player))
        (fun choices ↦ timingPurePayoff reward (dates + 1) choices who) =
      quittingRootPayoff reward
        (fun player ↦ timingMixedPayoff reward dates
          (fun other ↦ timingLawTail (mixed other)) player)
        now who := by
  let conditional : PMF
      (ι → QuittingFiniteDeadlineTimingAction (dates + 1)) :=
    pmfPi fun player ↦
      condOn (mixed player) timingActionCurrent (now player)
  by_cases hquit : (quittingQuitters now).Nonempty
  · calc
      Math.Probability.expect conditional
          (fun choices ↦ timingPurePayoff reward (dates + 1) choices who) =
        Math.Probability.expect conditional (fun _ ↦
          reward ⟨quittingQuitters now, hquit⟩ who) := by
            apply Math.ProbabilityMassFunction.expect_congr_on_support
            intro choices hchoices
            rw [timingPurePayoff_succ reward]
            have hcurrent :=
              timingActionCurrent_eq_of_mem_conditionalProduct_support
                dates mixed now hnow hchoices
            rw [hcurrent]
            simp [quittingRootPayoff, hquit]
      _ = reward ⟨quittingQuitters now, hquit⟩ who :=
        Math.Probability.expect_const conditional _
      _ = quittingRootPayoff reward
          (fun player ↦ timingMixedPayoff reward dates
            (fun other ↦ timingLawTail (mixed other)) player)
          now who := by simp [quittingRootPayoff, hquit]
  · have hnowAll : now = quittingAllContinueAction :=
      eq_quittingAllContinueAction_of_quittingQuitters_not_nonempty now hquit
    have hmap : pushforward conditional timingChoicesTail =
        pmfPi (fun player ↦ timingLawTail (mixed player)) := by
      unfold conditional timingChoicesTail timingLawTail
      rw [hnowAll]
      rw [pmfPi_push_coordwise]
      rfl
    calc
      Math.Probability.expect conditional
          (fun choices ↦ timingPurePayoff reward (dates + 1) choices who) =
        Math.Probability.expect conditional
          (fun choices ↦ timingPurePayoff reward dates
            (timingChoicesTail choices) who) := by
              apply Math.ProbabilityMassFunction.expect_congr_on_support
              intro choices hchoices
              rw [timingPurePayoff_succ reward]
              have hcurrent :=
                timingActionCurrent_eq_of_mem_conditionalProduct_support
                  dates mixed now hnow hchoices
              rw [hcurrent, hnowAll]
              simp [quittingRootPayoff]
      _ = Math.Probability.expect
          (pushforward conditional timingChoicesTail)
          (fun choices ↦ timingPurePayoff reward dates choices who) := by
            unfold pushforward
            exact (Math.Probability.expect_map timingChoicesTail conditional
              (fun choices ↦ timingPurePayoff reward dates choices who)).symm
      _ = timingMixedPayoff reward dates
          (fun player ↦ timingLawTail (mixed player)) who := by
            rw [hmap]
            rfl
      _ = quittingRootPayoff reward
          (fun player ↦ timingMixedPayoff reward dates
            (fun other ↦ timingLawTail (mixed other)) player)
          now who := by
            rw [hnowAll]
            simp [quittingRootPayoff]

/-- Bellman peeling for arbitrary independent mixed timing laws. The
zero-mass fallback branch of `condOn` disappears under the outer expectation,
so no positivity assumption is needed here. -/
theorem timingMixedPayoff_bellman
    (dates : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (who : ι) :
    timingMixedPayoff reward (dates + 1) mixed who =
      quittingRootExpectedPayoff reward
        (fun player ↦ timingMixedPayoff reward dates
          (fun other ↦ timingLawTail (mixed other)) player)
        (fun player ↦ pushforward (mixed player) timingActionCurrent)
        who := by
  unfold timingMixedPayoff
  rw [pmfPi_disintegrate_timingCurrent,
    Math.Probability.expect_bind]
  unfold quittingRootExpectedPayoff
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro now hnow
  exact expect_conditional_timingPurePayoff reward dates mixed now
    (by simpa only [PMF.mem_support_iff] using hnow) who

omit [DecidableEq ι] in
/-- The short mixed-payoff evaluator is exactly the finite timing game's
expected-utility evaluator. -/
theorem finiteDeadlineTimingGame_mixedEU_eq_timingMixedPayoff
    (dates : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction dates))
    (who : ι) :
    (quittingFiniteDeadlineTimingGame reward dates).mixedExtension.eu
        mixed who = timingMixedPayoff reward dates mixed who := by
  letI : Finite (quittingFiniteDeadlineTimingGame reward dates).Outcome := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingFiniteDeadlineTimingGame reward dates).mixedExtension_eu]
  unfold timingMixedPayoff timingPurePayoff
    quittingFiniteDeadlineTimingGame
  simp only [KernelGame.eu_ofPureEU]
  rfl

/-- Pure-deviation gain in the finite timing game, expressed through the
recursive timing-payoff evaluator. -/
theorem finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub
    (dates : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction dates))
    (who : ι)
    (action : QuittingFiniteDeadlineTimingAction dates) :
    (quittingFiniteDeadlineTimingGame reward dates).mixedGain
        mixed who action =
      timingMixedPayoff reward dates
          (Function.update mixed who (PMF.pure action)) who -
        timingMixedPayoff reward dates mixed who := by
  unfold KernelGame.mixedGain
  letI : Finite (quittingFiniteDeadlineTimingGame reward dates).Outcome := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingFiniteDeadlineTimingGame reward dates).mixedExtension_eu,
    (quittingFiniteDeadlineTimingGame reward dates).mixedExtension_eu]
  unfold timingMixedPayoff timingPurePayoff
    quittingFiniteDeadlineTimingGame
  simp only [KernelGame.eu_ofPureEU]
  rfl

/-! ## Positive-reach tail splicing -/

/-- Replace one player's conditional timing tail while preserving its current
hazard. -/
def timingMixedWithTail {dates : ℕ}
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (who : ι)
    (replacement : PMF (QuittingFiniteDeadlineTimingAction dates)) :
    ι → PMF (QuittingFiniteDeadlineTimingAction (dates + 1)) :=
  Function.update mixed who
    (timingLawWithTail (mixed who) replacement)

omit [Fintype ι] in
/-- Tail replacement preserves every current root marginal. -/
theorem timingMixedWithTail_current {dates : ℕ}
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (who : ι)
    (replacement : PMF (QuittingFiniteDeadlineTimingAction dates)) :
    (fun player ↦ pushforward
      (timingMixedWithTail mixed who replacement player)
      timingActionCurrent) =
      fun player ↦ pushforward (mixed player) timingActionCurrent := by
  funext player
  by_cases hplayer : player = who
  · subst player
    rw [timingMixedWithTail, Function.update_self,
      timingLawWithTail_map_current]
  · rw [timingMixedWithTail, Function.update_of_ne hplayer]

omit [Fintype ι] in
/-- Under positive current continuation, the shifted tail family of a
one-coordinate replacement is the corresponding updated tail family. -/
theorem timingMixedWithTail_tail {dates : ℕ}
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (who : ι)
    (replacement : PMF (QuittingFiniteDeadlineTimingAction dates))
    (hcontinue : pushforward (mixed who) timingActionCurrent false ≠ 0) :
    (fun player ↦ timingLawTail
      (timingMixedWithTail mixed who replacement player)) =
      Function.update (fun player ↦ timingLawTail (mixed player))
        who replacement := by
  funext player
  by_cases hplayer : player = who
  · subst player
    rw [timingMixedWithTail, Function.update_self,
      Function.update_self, timingLawTail_withTail _ _ hcontinue]
  · rw [timingMixedWithTail, Function.update_of_ne hplayer,
      Function.update_of_ne hplayer]

/-- Exact payoff transport for replacing one conditional tail. -/
theorem timingMixedPayoff_withTail_sub
    (dates : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (who : ι)
    (replacement : PMF (QuittingFiniteDeadlineTimingAction dates))
    (hcontinue : pushforward (mixed who) timingActionCurrent false ≠ 0) :
    timingMixedPayoff reward (dates + 1)
          (timingMixedWithTail mixed who replacement) who -
        timingMixedPayoff reward (dates + 1) mixed who =
      quittingStationaryContinueMass
          (fun player ↦ pushforward (mixed player) timingActionCurrent) *
        (timingMixedPayoff reward dates
            (Function.update (fun player ↦ timingLawTail (mixed player))
              who replacement) who -
          timingMixedPayoff reward dates
            (fun player ↦ timingLawTail (mixed player)) who) := by
  rw [timingMixedPayoff_bellman reward, timingMixedPayoff_bellman reward,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    timingMixedWithTail_current,
    timingMixedWithTail_tail mixed who replacement hcontinue]
  ring

omit [DecidableEq ι] in
/-- Coordinatewise positive current continuation gives positive joint
all-Continue reach. -/
theorem timingCurrentRoot_continueMass_pos
    (dates : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hcontinue : ∀ who,
      pushforward (mixed who) timingActionCurrent false ≠ 0) :
    0 < quittingStationaryContinueMass
      (fun who ↦ pushforward (mixed who) timingActionCurrent) := by
  rw [quittingStationaryContinueMass_eq_prod]
  apply Finset.prod_pos
  intro who _
  exact ENNReal.toReal_pos (hcontinue who)
    (PMF.apply_ne_top (pushforward (mixed who) timingActionCurrent) false)

/-- Ordinary normal-form Nash plus positive current reach makes the
coordinatewise conditioned tail a Nash equilibrium of the shorter timing
game. No subgame-perfect refinement is assumed. -/
theorem timingLawTail_isNash_of_isNash_of_positiveContinue
    (dates : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward (dates + 1)).mixedExtension.IsNash
      mixed)
    (hcontinue : ∀ who,
      pushforward (mixed who) timingActionCurrent false ≠ 0) :
    (quittingFiniteDeadlineTimingGame reward dates).mixedExtension.IsNash
      (fun who ↦ timingLawTail (mixed who)) := by
  intro who replacement
  have hnashSplice := hnash who
    (timingLawWithTail (mixed who) replacement)
  have htransport := timingMixedPayoff_withTail_sub reward
    dates mixed who replacement (hcontinue who)
  rw [← finiteDeadlineTimingGame_mixedEU_eq_timingMixedPayoff
      reward (dates + 1) mixed who,
    ← finiteDeadlineTimingGame_mixedEU_eq_timingMixedPayoff
      reward (dates + 1) (timingMixedWithTail mixed who replacement) who]
    at htransport
  change (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.eu mixed who ≥
    (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.eu
        (timingMixedWithTail mixed who replacement) who at hnashSplice
  have hreach := timingCurrentRoot_continueMass_pos dates mixed hcontinue
  rw [finiteDeadlineTimingGame_mixedEU_eq_timingMixedPayoff,
    finiteDeadlineTimingGame_mixedEU_eq_timingMixedPayoff]
  by_contra htail
  have htailPos : 0 <
      timingMixedPayoff reward dates
          (Function.update (fun player ↦ timingLawTail (mixed player))
            who replacement) who -
        timingMixedPayoff reward dates
          (fun player ↦ timingLawTail (mixed player)) who :=
    sub_pos.mpr (lt_of_not_ge htail)
  have hmulPos := mul_pos hreach htailPos
  have hwholeNonpos :
      (quittingFiniteDeadlineTimingGame reward
          (dates + 1)).mixedExtension.eu
            (timingMixedWithTail mixed who replacement) who -
        (quittingFiniteDeadlineTimingGame reward
          (dates + 1)).mixedExtension.eu mixed who ≤ 0 :=
    sub_nonpos.mpr hnashSplice
  have hmulNonpos :
      quittingStationaryContinueMass
          (fun player ↦ pushforward (mixed player) timingActionCurrent) *
        (timingMixedPayoff reward dates
            (Function.update (fun player ↦ timingLawTail (mixed player))
              who replacement) who -
          timingMixedPayoff reward dates
            (fun player ↦ timingLawTail (mixed player)) who) ≤ 0 := by
    rw [← htransport]
    exact hwholeNonpos
  exact (not_lt_of_ge hmulNonpos) hmulPos

/-! ## Conditional tails in the behavioral realization -/

/-- The finite timing-action encoding is injective. -/
theorem quittingFiniteDeadlineTimingActionTime_injective
    {dates : ℕ} :
    Function.Injective
      (quittingFiniteDeadlineTimingActionTime (deadline := dates)) := by
  intro first second heq
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some secondTime =>
          simp [quittingFiniteDeadlineTimingActionTime] at heq
  | some firstTime =>
      cases second with
      | none =>
          simp [quittingFiniteDeadlineTimingActionTime] at heq
      | some secondTime =>
          apply congrArg some
          apply Fin.ext
          simpa [quittingFiniteDeadlineTimingActionTime] using heq

/-- Mapping a finite timing law to literal stopping times preserves each
finite atom exactly. -/
theorem quittingFiniteDeadlineTimingLaw_apply_some
    {dates : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction dates))
    (time : Fin dates) :
    (quittingFiniteDeadlineTimingLaw law).toPMF
        (WithTop.some time.val) = law (some time) := by
  rw [quittingFiniteDeadlineTimingLaw,
    Math.Probability.CompactStoppingLaw.toPMF_ofPMF, PMF.map_apply]
  rw [tsum_eq_single (some time)]
  · simp [quittingFiniteDeadlineTimingActionTime]
  · intro other hother
    split_ifs with heq
    · apply (hother
        (quittingFiniteDeadlineTimingActionTime_injective ?_)).elim
      simpa [quittingFiniteDeadlineTimingActionTime] using heq.symm
    · rfl

/-- After conditioning on current continuation, each shifted finite atom is
renormalized by the current Continue mass. -/
theorem finiteDeadlineTimingLaw_finiteMass_succ_eq_continue_mul_tail
    {dates : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hcontinue : pushforward law timingActionCurrent false ≠ 0)
    (time : Fin dates) :
    Math.Probability.DiscreteHazard.StoppingLaw.finiteMass
        (quittingFiniteDeadlineTimingLaw law).toPMF (time.val + 1) =
      (pushforward law timingActionCurrent false).toReal *
        Math.Probability.DiscreteHazard.StoppingLaw.finiteMass
          (quittingFiniteDeadlineTimingLaw
            (timingLawTail law)).toPMF time.val := by
  have hcontinueReal :
      (pushforward law timingActionCurrent false).toReal ≠ 0 :=
    (ENNReal.toReal_ne_zero.mpr
      ⟨hcontinue, PMF.apply_ne_top
        (pushforward law timingActionCurrent) false⟩)
  unfold Math.Probability.DiscreteHazard.StoppingLaw.finiteMass
  change ((quittingFiniteDeadlineTimingLaw law).toPMF
      (WithTop.some (time.val + 1))).toReal =
    (pushforward law timingActionCurrent false).toReal *
      ((quittingFiniteDeadlineTimingLaw (timingLawTail law)).toPMF
        (WithTop.some time.val)).toReal
  rw [show time.val + 1 = time.succ.val by rfl,
    quittingFiniteDeadlineTimingLaw_apply_some law time.succ,
    quittingFiniteDeadlineTimingLaw_apply_some (timingLawTail law) time,
    timingLawTail_apply_some law hcontinue time,
    ENNReal.toReal_div]
  field_simp

/-- Survival of the original timing law one date later is current Continue
mass times survival of its conditional shifted tail. -/
theorem finiteDeadlineTimingLaw_survival_succ
    {dates : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hcontinue : pushforward law timingActionCurrent false ≠ 0)
    (cutoff : ℕ) (hcutoff : cutoff ≤ dates) :
    Math.Probability.DiscreteHazard.StoppingLaw.survival
        (quittingFiniteDeadlineTimingLaw law).toPMF (cutoff + 1) =
      (pushforward law timingActionCurrent false).toReal *
        Math.Probability.DiscreteHazard.StoppingLaw.survival
          (quittingFiniteDeadlineTimingLaw
            (timingLawTail law)).toPMF cutoff := by
  induction cutoff with
  | zero =>
      rw [Math.Probability.DiscreteHazard.StoppingLaw.survival_succ,
        Math.Probability.DiscreteHazard.StoppingLaw.survival_zero,
        Math.Probability.DiscreteHazard.StoppingLaw.survival_zero]
      unfold Math.Probability.DiscreteHazard.StoppingLaw.finiteMass
      change 1 - ((quittingFiniteDeadlineTimingLaw law).toPMF
        (WithTop.some 0)).toReal =
          (pushforward law timingActionCurrent false).toReal * 1
      have hzero : (quittingFiniteDeadlineTimingLaw law).toPMF
          (WithTop.some 0) = law (some (0 : Fin (dates + 1))) := by
        simpa using quittingFiniteDeadlineTimingLaw_apply_some law
          (0 : Fin (dates + 1))
      rw [hzero, ← timingActionCurrent_pushforward_true_zero]
      rw [Math.PMFProduct.pmfBool_false_toReal]
      ring
  | succ cutoff ih =>
      have hcutoffLt : cutoff < dates := by omega
      have hcutoffLe : cutoff ≤ dates := hcutoffLt.le
      rw [Math.Probability.DiscreteHazard.StoppingLaw.survival_succ
          (quittingFiniteDeadlineTimingLaw law).toPMF (cutoff + 1),
        Math.Probability.DiscreteHazard.StoppingLaw.survival_succ
          (quittingFiniteDeadlineTimingLaw
            (timingLawTail law)).toPMF cutoff,
        ih hcutoffLe,
        finiteDeadlineTimingLaw_finiteMass_succ_eq_continue_mul_tail
          law hcontinue ⟨cutoff, hcutoffLt⟩]
      ring

/-- Reconstructing hazards commutes with conditioning on current Continue
and deleting the survived current date. -/
theorem finiteDeadlineTimingLaw_toScalarHazard_succ
    {dates : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hcontinue : pushforward law timingActionCurrent false ≠ 0)
    (time : ℕ) :
    (Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard
        (quittingFiniteDeadlineTimingLaw law).toPMF).stop (time + 1) =
      (Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard
        (quittingFiniteDeadlineTimingLaw
          (timingLawTail law)).toPMF).stop time := by
  let source := (quittingFiniteDeadlineTimingLaw law).toPMF
  let tail := (quittingFiniteDeadlineTimingLaw (timingLawTail law)).toPMF
  by_cases htime : time < dates
  · have hsurvival := finiteDeadlineTimingLaw_survival_succ
      law hcontinue time htime.le
    have hmass :=
      finiteDeadlineTimingLaw_finiteMass_succ_eq_continue_mul_tail
        law hcontinue ⟨time, htime⟩
    have hcontinueReal :
        (pushforward law timingActionCurrent false).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr
        ⟨hcontinue, PMF.apply_ne_top
          (pushforward law timingActionCurrent) false⟩
    unfold Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard
    dsimp only
    change (if Math.Probability.DiscreteHazard.StoppingLaw.survival
        source (time + 1) = 0 then 0 else
          Math.Probability.DiscreteHazard.StoppingLaw.finiteMass
            source (time + 1) /
              Math.Probability.DiscreteHazard.StoppingLaw.survival
                source (time + 1)) =
      (if Math.Probability.DiscreteHazard.StoppingLaw.survival tail time = 0
        then 0 else
          Math.Probability.DiscreteHazard.StoppingLaw.finiteMass tail time /
            Math.Probability.DiscreteHazard.StoppingLaw.survival tail time)
    change Math.Probability.DiscreteHazard.StoppingLaw.survival source
        (time + 1) =
      (pushforward law timingActionCurrent false).toReal *
        Math.Probability.DiscreteHazard.StoppingLaw.survival tail time
      at hsurvival
    change Math.Probability.DiscreteHazard.StoppingLaw.finiteMass source
        (time + 1) =
      (pushforward law timingActionCurrent false).toReal *
        Math.Probability.DiscreteHazard.StoppingLaw.finiteMass tail time
      at hmass
    rw [hsurvival, hmass]
    by_cases htailSurvival :
        Math.Probability.DiscreteHazard.StoppingLaw.survival tail time = 0
    · simp [htailSurvival]
    · rw [if_neg (mul_ne_zero hcontinueReal htailSurvival),
        if_neg htailSurvival]
      field_simp
  · have hdates : dates ≤ time := Nat.le_of_not_gt htime
    have hsourceMass :
        Math.Probability.DiscreteHazard.StoppingLaw.finiteMass source
          (time + 1) = 0 := by
      unfold Math.Probability.DiscreteHazard.StoppingLaw.finiteMass
      have happly : (quittingFiniteDeadlineTimingLaw law).toPMF
          (WithTop.some (time + 1)) = 0 :=
        quittingFiniteDeadlineTimingLaw_some_eq_zero_of_le law (by omega)
      change (((quittingFiniteDeadlineTimingLaw law).toPMF
        (WithTop.some (time + 1))).toReal) = 0
      rw [happly]
      rfl
    have htailMass :
        Math.Probability.DiscreteHazard.StoppingLaw.finiteMass tail time = 0 := by
      unfold Math.Probability.DiscreteHazard.StoppingLaw.finiteMass
      have happly :
          (quittingFiniteDeadlineTimingLaw (timingLawTail law)).toPMF
            (WithTop.some time) = 0 :=
        quittingFiniteDeadlineTimingLaw_some_eq_zero_of_le
          (timingLawTail law) hdates
      change (((quittingFiniteDeadlineTimingLaw
        (timingLawTail law)).toPMF (WithTop.some time)).toReal) = 0
      rw [happly]
      rfl
    unfold Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard
    dsimp only
    change (if Math.Probability.DiscreteHazard.StoppingLaw.survival
        source (time + 1) = 0 then 0 else
          Math.Probability.DiscreteHazard.StoppingLaw.finiteMass
            source (time + 1) /
              Math.Probability.DiscreteHazard.StoppingLaw.survival
                source (time + 1)) =
      (if Math.Probability.DiscreteHazard.StoppingLaw.survival tail time = 0
        then 0 else
          Math.Probability.DiscreteHazard.StoppingLaw.finiteMass tail time /
            Math.Probability.DiscreteHazard.StoppingLaw.survival tail time)
    simp [hsourceMass, htailMass]

theorem pmfBool_eq_of_true_toReal_eq
    (first second : PMF Bool)
    (htrue : (first true).toReal = (second true).toReal) :
    first = second := by
  apply PMF.ext
  intro value
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top first value) (PMF.apply_ne_top second value)).mp
  cases value with
  | false =>
      rw [Math.PMFProduct.pmfBool_false_toReal,
        Math.PMFProduct.pmfBool_false_toReal, htrue]
  | true => exact htrue

omit [DecidableEq ι] in
/-- The first behavioral root of a finite timing profile is exactly the
pushforward of each timing law to its current Boolean action. -/
theorem finiteDeadlineTimingProfile_root_eq_current
    (dates : ℕ)
    (mixed : ι →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1))) :
    quittingProfileRoot reward
        (quittingFiniteDeadlineTimingProfile reward (dates + 1) mixed) =
      fun who ↦ pushforward (mixed who) timingActionCurrent := by
  funext who
  apply pmfBool_eq_of_true_toReal_eq
  rw [finiteDeadlineTimingProfile_root_true reward,
    timingActionCurrent_pushforward_true]

omit [DecidableEq ι] in
/-- Under genuine current continuation, deleting the first behavioral date
of a finite timing profile is exactly the profile of the conditional shifted
timing laws. -/
theorem finiteDeadlineTimingProfile_spine_one_eq_tail
    (dates : ℕ)
    (mixed : ι →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hcontinue : ∀ who,
      pushforward (mixed who) timingActionCurrent false ≠ 0) :
    quittingAllContinueProfileSpine reward
        (quittingFiniteDeadlineTimingProfile reward (dates + 1) mixed) 1 =
      quittingFiniteDeadlineTimingProfile reward dates
        (fun who ↦ timingLawTail (mixed who)) := by
  funext who time history
  change (Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard
      (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF).toBoolean
        (time + 1) =
    (Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard
      (quittingFiniteDeadlineTimingLaw
        (timingLawTail (mixed who))).toPMF).toBoolean time
  apply pmfBool_eq_of_true_toReal_eq
  simp only [Math.Probability.DiscreteHazard.ScalarHazard.toBoolean,
    Math.Probability.DiscreteHazard.booleanCoin_true_toReal]
  exact finiteDeadlineTimingLaw_toScalarHazard_succ
    (mixed who) (hcontinue who) time



/-! ## Additional tail reconstruction and endpoint adapters -/

omit [Fintype ι] in
/-- Shifting a one-coordinate update is the corresponding update of the
shifted marginal family. -/
theorem timingLawTail_update {dates : ℕ}
    (mixed : ι →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (who : ι)
    (law : PMF (QuittingFiniteDeadlineTimingAction (dates + 1))) :
    (fun player ↦ timingLawTail (Function.update mixed who law player)) =
      Function.update (fun player ↦ timingLawTail (mixed player)) who
        (timingLawTail law) := by
  funext player
  by_cases hplayer : player = who
  · subst player
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hplayer, Function.update_of_ne hplayer]


/-- Shifting a tail law forward by one date and conditioning on current
continuation recovers the original tail law exactly. -/
@[simp] theorem timingLawTail_map_lifted {dates : ℕ}
    (tail : PMF (QuittingFiniteDeadlineTimingAction dates)) :
    timingLawTail (tail.map timingActionLift) = tail := by
  let law := tail.map (timingActionLift (dates := dates))
  have hcurrent : pushforward law timingActionCurrent = PMF.pure false := by
    unfold law pushforward
    rw [PMF.map_comp]
    convert PMF.map_const tail false using 1
    apply congrArg (fun mapChoice :
      QuittingFiniteDeadlineTimingAction dates → Bool ↦
        tail.map mapChoice)
    funext action
    exact timingActionCurrent_lift action
  have hcontinue : pushforward law timingActionCurrent false ≠ 0 := by
    rw [hcurrent]
    simp
  have hcond : condOn law timingActionCurrent false = law := by
    have hden : pushforward law timingActionCurrent false = 1 := by
      rw [hcurrent]
      simp
    apply PMF.ext
    intro action
    rw [condOn_apply law timingActionCurrent false action hcontinue]
    by_cases haction : timingActionCurrent action = false
    · rw [if_pos haction, hden, div_one]
    · have htrue : timingActionCurrent action = true := by
        simpa using haction
      rw [if_neg haction]
      exact (map_timingActionLift_apply_eq_zero_of_current
        tail action htrue).symm
  have hlift := timingLawTail_map_lift law hcontinue
  rw [hcond] at hlift
  have hmapped := congrArg (fun source ↦ source.map timingActionTail) hlift
  have hcomp :
      (timingActionTail (dates := dates)) ∘
          (timingActionLift (dates := dates)) =
        (id : QuittingFiniteDeadlineTimingAction dates →
          QuittingFiniteDeadlineTimingAction dates) := by
    funext action
    exact timingActionTail_lift action
  unfold law at hmapped
  simpa only [PMF.map_comp, hcomp, PMF.map_id] using hmapped


/-- Pure-Quit root payoff is independent of the declared continuation
payoff, because a sure own Quit makes joint continuation impossible. -/
theorem quittingRootQuitPayoff_tail_irrel
    (first second : Payoff ι) (root : ι → PMF Bool)
    (who : ι) :
    quittingRootQuitPayoff reward first root who =
      quittingRootQuitPayoff reward second root who := by
  unfold quittingRootQuitPayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingStationaryContinueMass_update_pure_true_eq_zero]
  ring

theorem map_liftedTail_current {dates : ℕ}
    (tail : PMF (QuittingFiniteDeadlineTimingAction dates)) :
    pushforward (tail.map timingActionLift) timingActionCurrent =
      PMF.pure false := by
  unfold pushforward
  rw [PMF.map_comp]
  convert PMF.map_const tail false using 1
  apply congrArg (fun mapChoice :
    QuittingFiniteDeadlineTimingAction dates → Bool ↦
      tail.map mapChoice)
  funext action
  exact timingActionCurrent_lift action

/-- Pure current stopping in the timing game is exactly the current root's
Quit endpoint against the conditioned-tail payoff. -/
theorem timingMixedPayoff_update_current_eq_quitPayoff
    (dates : ℕ)
    (mixed : ι →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (who : ι) :
    timingMixedPayoff reward (dates + 1)
        (Function.update mixed who
          (PMF.pure (some (0 : Fin (dates + 1))))) who =
      quittingRootQuitPayoff reward
        (fun player ↦ timingMixedPayoff reward dates
          (fun other ↦ timingLawTail (mixed other)) player)
        (fun player ↦ pushforward (mixed player) timingActionCurrent)
        who := by
  rw [timingMixedPayoff_bellman reward]
  let root : ι → PMF Bool := fun player ↦
    pushforward (mixed player) timingActionCurrent
  let updated := Function.update mixed who
    (PMF.pure (some (0 : Fin (dates + 1))))
  have hroot :
      (fun player ↦ pushforward (updated player) timingActionCurrent) =
        Function.update root who (PMF.pure true) := by
    funext player
    by_cases hplayer : player = who
    · subst player
      rw [Function.update_self]
      unfold updated pushforward
      rw [Function.update_self, PMF.pure_map]
      rfl
    · unfold updated root
      rw [Function.update_of_ne hplayer, Function.update_of_ne hplayer]
  rw [hroot]
  unfold quittingRootQuitPayoff
  exact quittingRootQuitPayoff_tail_irrel reward _ _ root who

/-- Replacing one timing marginal by its lifted conditioned tail is exactly
the current root's Continue endpoint. -/
theorem timingMixedPayoff_update_liftedTail_eq_continuePayoff
    (dates : ℕ)
    (mixed : ι →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (who : ι) :
    timingMixedPayoff reward (dates + 1)
        (Function.update mixed who
          ((timingLawTail (mixed who)).map timingActionLift)) who =
      quittingRootContinuePayoff reward
        (fun player ↦ timingMixedPayoff reward dates
          (fun other ↦ timingLawTail (mixed other)) player)
        (fun player ↦ pushforward (mixed player) timingActionCurrent)
        who := by
  rw [timingMixedPayoff_bellman reward]
  let root : ι → PMF Bool := fun player ↦
    pushforward (mixed player) timingActionCurrent
  let tails : ι →
      PMF (QuittingFiniteDeadlineTimingAction dates) := fun player ↦
    timingLawTail (mixed player)
  have hroot :
      (fun player ↦ pushforward
        (Function.update mixed who
          ((timingLawTail (mixed who)).map timingActionLift) player)
        timingActionCurrent) =
      Function.update root who (PMF.pure false) := by
    funext player
    by_cases hplayer : player = who
    · subst player
      rw [Function.update_self, Function.update_self]
      exact map_liftedTail_current _
    · unfold root
      rw [Function.update_of_ne hplayer, Function.update_of_ne hplayer]
  have htail :
      (fun player ↦ timingLawTail
        (Function.update mixed who
          ((timingLawTail (mixed who)).map timingActionLift) player)) =
      tails := by
    rw [timingLawTail_update, timingLawTail_map_lifted]
    exact Function.update_eq_self who tails
  rw [hroot, htail]
  rfl

/-! ## Exact marginal reconstruction -/

private theorem pmf_eq_pure_of_apply_toReal_eq_one
    {A : Type*} (law : PMF A) (point : A)
    (hpoint : (law point).toReal = 1) :
    law = PMF.pure point := by
  have hpointOne : law point = 1 :=
    (ENNReal.toReal_eq_one_iff (law point)).mp hpoint
  have hsupport : law.support = {point} :=
    (PMF.apply_eq_one_iff law point).mp hpointOne
  apply PMF.ext
  intro other
  by_cases hother : other = point
  · subst other
    rw [hpointOne]
    simp
  · have hnotMem : other ∉ law.support := by
      rw [hsupport]
      simpa using hother
    rw [(PMF.apply_eq_zero_iff law other).2 hnotMem]
    simp [hother]

/-- The positive current-Quit conditional fibre is the unique date-zero
timing action. -/
theorem condOn_timingActionCurrent_true_eq_pure_zero {dates : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hquit : pushforward law timingActionCurrent true ≠ 0) :
    condOn law timingActionCurrent true =
      PMF.pure (some (0 : Fin (dates + 1))) := by
  let conditional := condOn law timingActionCurrent true
  have hmap : pushforward conditional timingActionCurrent = PMF.pure true :=
    condOn_map_timingActionCurrent_eq_pure law true hquit
  apply pmf_eq_pure_of_apply_toReal_eq_one
  rw [← timingActionCurrent_pushforward_true_zero conditional, hmap]
  simp

/-- Equal current marginals and equal conditioned shifted tails determine the
original finite timing law exactly. -/
theorem timingLaw_eq_of_current_tail_eq {dates : ℕ}
    (first second :
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hcurrent : pushforward first timingActionCurrent =
      pushforward second timingActionCurrent)
    (htail : timingLawTail first = timingLawTail second)
    (hfirstContinue : pushforward first timingActionCurrent false ≠ 0)
    (hsecondContinue : pushforward second timingActionCurrent false ≠ 0) :
    first = second := by
  let firstCurrent := pushforward first timingActionCurrent
  let secondCurrent := pushforward second timingActionCurrent
  calc
    first = firstCurrent.bind
        (fun value ↦ condOn first timingActionCurrent value) :=
      bind_pushforward_condOn_pure first timingActionCurrent
    _ = firstCurrent.bind
        (fun value ↦ condOn second timingActionCurrent value) := by
          apply bind_congr_on_support
          intro value hvalue
          cases value with
          | false =>
              calc
                condOn first timingActionCurrent false =
                    (timingLawTail first).map timingActionLift :=
                  (timingLawTail_map_lift first hfirstContinue).symm
                _ = (timingLawTail second).map timingActionLift := by
                  rw [htail]
                _ = condOn second timingActionCurrent false :=
                  timingLawTail_map_lift second hsecondContinue
          | true =>
              have hfirstQuit :
                  pushforward first timingActionCurrent true ≠ 0 := by
                simpa only [firstCurrent, PMF.mem_support_iff] using hvalue
              have hsecondQuit :
                  pushforward second timingActionCurrent true ≠ 0 := by
                rw [← hcurrent]
                exact hfirstQuit
              rw [condOn_timingActionCurrent_true_eq_pure_zero first hfirstQuit,
                condOn_timingActionCurrent_true_eq_pure_zero second hsecondQuit]
    _ = secondCurrent.bind
        (fun value ↦ condOn second timingActionCurrent value) := by
          change (pushforward first timingActionCurrent).bind
              (fun value ↦ condOn second timingActionCurrent value) =
            (pushforward second timingActionCurrent).bind
              (fun value ↦ condOn second timingActionCurrent value)
          rw [hcurrent]
    _ = second :=
      (bind_pushforward_condOn_pure second timingActionCurrent).symm



end GameTheory
