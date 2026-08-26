/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.FinFourHardDeadlineTimingNashBarrier
import MathUE.PMFProduct.Independence

/-!
# Uniqueness of the Fin4 hard-deadline timing Nash law

This file supplies the conditioning infrastructure needed to prove that the
hard-deadline timing Nash law of the concrete Fin4 table is unique.  The key
distinction from rootwise uniqueness is that an arbitrary normal-form law may
correlate a player's current action with its planned later stopping time.  We
therefore split each marginal law into its current atom and its conditional
shifted tail before applying backward induction.
-/

noncomputable section

namespace GameTheory
namespace FinFourHardDeadlineTimingNashBarrier

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

private theorem KernelGame.mixedGain_eq_zero_of_mem_support
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
    fun choice ↦ (G.isNash_iff_gains_nonpos mixed).mp hnash who choice
  have hweighted := G.weighted_gain_sum_zero mixed who
  unfold Math.Probability.expect at hweighted
  rw [tsum_fintype] at hweighted
  have hterm :
      (mixed who action).toReal * G.mixedGain mixed who action = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos (fun choice _ ↦
      mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg
        (hgain choice))).mp hweighted action (Finset.mem_univ action)
  have hmass : 0 < (mixed who action).toReal :=
    ENNReal.toReal_pos haction (PMF.apply_ne_top _ _)
  exact (mul_eq_zero.mp hterm).resolve_left hmass.ne'

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

private theorem pmf_map_eq_self_of_eq_on_support {A : Type*}
    (law : PMF A) (mapChoice : A → A)
    (hfix : ∀ choice, law choice ≠ 0 → mapChoice choice = choice) :
    law.map mapChoice = law := by
  classical
  apply PMF.ext
  intro choice
  rw [PMF.map_apply, tsum_eq_single choice]
  · by_cases hchoice : law choice = 0
    · simp [hchoice]
    · simp [hfix choice hchoice]
  · intro other hother
    by_cases hmass : law other = 0
    · simp [hmass]
    · simp [hfix other hmass, hother.symm]

/-- Lifting the conditional tail law reconstructs the original law
conditioned on current continuation. -/
theorem timingLawTail_map_lift {dates : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hcontinue : pushforward law timingActionCurrent false ≠ 0) :
    (timingLawTail law).map timingActionLift =
      condOn law timingActionCurrent false := by
  rw [timingLawTail, PMF.map_comp]
  apply pmf_map_eq_self_of_eq_on_support
  intro action hmass
  apply timingAction_lift_tail_of_continue
  apply condOn_support_project law timingActionCurrent false hcontinue
  simpa only [PMF.mem_support_iff] using hmass

/-! ## The literal first-stage decomposition -/

/-- A finite timing-law profile is its first live root followed by its
all-Continue spine. -/
theorem finiteDeadlineTimingProfile_eq_rootThen_spine
    (dates : ℕ)
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction dates)) :
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

/-- The first live-root quitting probability is the mass of the current
timing action. -/
theorem finiteDeadlineTimingProfile_root_true
    (dates : ℕ)
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (who : Player) :
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
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction (dates + 1))) :
    pmfPi mixed =
      (pmfPi fun who ↦ pushforward (mixed who) timingActionCurrent).bind
        (fun now ↦ pmfPi fun who ↦
          condOn (mixed who) timingActionCurrent (now who)) := by
  let current : Player → PMF Bool := fun who ↦
    pushforward (mixed who) timingActionCurrent
  let conditional : (Player → Bool) → Player →
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

private theorem map_timingActionLift_apply_eq_zero_of_current
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

private theorem pmfPi_coord_ne_zero_of_ne_zero
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
    (choices : Player → QuittingFiniteDeadlineTimingAction (dates + 1)) :
    Player → PMF Bool :=
  fun who ↦ PMF.pure (timingActionCurrent (choices who))

/-- Shift every continuing pure timing action into the tail game. -/
def timingChoicesTail {dates : ℕ}
    (choices : Player → QuittingFiniteDeadlineTimingAction (dates + 1)) :
    Player → QuittingFiniteDeadlineTimingAction dates :=
  fun who ↦ timingActionTail (choices who)

/-- A deterministic timing profile peels into its current pure root and its
shifted deterministic tail. -/
theorem pureTimingProfile_succ_eq_rootThen
    (dates : ℕ)
    (choices : Player → QuittingFiniteDeadlineTimingAction (dates + 1)) :
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
    (choices : Player → QuittingFiniteDeadlineTimingAction dates)
    (who : Player) : ℝ :=
  quittingTerminalPayoff reward
    (quittingPureStoppingTimeProfile reward fun player ↦
      quittingFiniteDeadlineTimingActionTime (choices player)) who

/-- Bellman peeling for a deterministic finite timing profile. -/
theorem timingPurePayoff_succ
    (dates : ℕ)
    (choices : Player → QuittingFiniteDeadlineTimingAction (dates + 1))
    (who : Player) :
    timingPurePayoff (dates + 1) choices who =
      quittingRootPayoff reward
        (fun player ↦ timingPurePayoff dates
          (timingChoicesTail choices) player)
        (fun player ↦ timingActionCurrent (choices player)) who := by
  unfold timingPurePayoff
  rw [pureTimingProfile_succ_eq_rootThen,
    quittingTerminalPayoff_rootThenContinuation_eq]
  unfold quittingRootExpectedPayoff timingChoicesRoot
  rw [pmfPi_pure]
  simp [Math.Probability.expect_pure]

/-- Expected payoff under independent mixed timing laws. -/
def timingMixedPayoff (dates : ℕ)
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction dates))
    (who : Player) : ℝ :=
  Math.Probability.expect (pmfPi mixed)
    (fun choices ↦ timingPurePayoff dates choices who)

private theorem timingActionCurrent_eq_of_mem_conditionalProduct_support
    (dates : ℕ)
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (now : Player → Bool)
    (hnow : pmfPi (fun who ↦
      pushforward (mixed who) timingActionCurrent) now ≠ 0)
    {choices : Player → QuittingFiniteDeadlineTimingAction (dates + 1)}
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

/-- Conditional on a supported current root, the inner timing payoff is the
one-stage root payoff whose continuation is the independently shifted tail. -/
theorem expect_conditional_timingPurePayoff
    (dates : ℕ)
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (now : Player → Bool)
    (hnow : pmfPi (fun who ↦
      pushforward (mixed who) timingActionCurrent) now ≠ 0)
    (who : Player) :
    Math.Probability.expect
        (pmfPi fun player ↦
          condOn (mixed player) timingActionCurrent (now player))
        (fun choices ↦ timingPurePayoff (dates + 1) choices who) =
      quittingRootPayoff reward
        (fun player ↦ timingMixedPayoff dates
          (fun other ↦ timingLawTail (mixed other)) player)
        now who := by
  let conditional : PMF
      (Player → QuittingFiniteDeadlineTimingAction (dates + 1)) :=
    pmfPi fun player ↦
      condOn (mixed player) timingActionCurrent (now player)
  by_cases hquit : (quittingQuitters now).Nonempty
  · calc
      Math.Probability.expect conditional
          (fun choices ↦ timingPurePayoff (dates + 1) choices who) =
        Math.Probability.expect conditional (fun _ ↦
          reward ⟨quittingQuitters now, hquit⟩ who) := by
            apply Math.ProbabilityMassFunction.expect_congr_on_support
            intro choices hchoices
            rw [timingPurePayoff_succ]
            have hcurrent :=
              timingActionCurrent_eq_of_mem_conditionalProduct_support
                dates mixed now hnow hchoices
            rw [hcurrent]
            simp [quittingRootPayoff, hquit]
      _ = reward ⟨quittingQuitters now, hquit⟩ who :=
        Math.Probability.expect_const conditional _
      _ = quittingRootPayoff reward
          (fun player ↦ timingMixedPayoff dates
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
          (fun choices ↦ timingPurePayoff (dates + 1) choices who) =
        Math.Probability.expect conditional
          (fun choices ↦ timingPurePayoff dates
            (timingChoicesTail choices) who) := by
              apply Math.ProbabilityMassFunction.expect_congr_on_support
              intro choices hchoices
              rw [timingPurePayoff_succ]
              have hcurrent :=
                timingActionCurrent_eq_of_mem_conditionalProduct_support
                  dates mixed now hnow hchoices
              rw [hcurrent, hnowAll]
              simp [quittingRootPayoff]
      _ = Math.Probability.expect
          (pushforward conditional timingChoicesTail)
          (fun choices ↦ timingPurePayoff dates choices who) := by
            unfold pushforward
            exact (Math.Probability.expect_map timingChoicesTail conditional
              (fun choices ↦ timingPurePayoff dates choices who)).symm
      _ = timingMixedPayoff dates
          (fun player ↦ timingLawTail (mixed player)) who := by
            rw [hmap]
            rfl
      _ = quittingRootPayoff reward
          (fun player ↦ timingMixedPayoff dates
            (fun other ↦ timingLawTail (mixed other)) player)
          now who := by
            rw [hnowAll]
            simp [quittingRootPayoff]

/-- Bellman peeling for arbitrary independent mixed timing laws. The
zero-mass fallback branch of `condOn` disappears under the outer expectation,
so no positivity assumption is needed here. -/
theorem timingMixedPayoff_succ
    (dates : ℕ)
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (who : Player) :
    timingMixedPayoff (dates + 1) mixed who =
      quittingRootExpectedPayoff reward
        (fun player ↦ timingMixedPayoff dates
          (fun other ↦ timingLawTail (mixed other)) player)
        (fun player ↦ pushforward (mixed player) timingActionCurrent)
        who := by
  unfold timingMixedPayoff
  rw [pmfPi_disintegrate_timingCurrent,
    Math.Probability.expect_bind]
  unfold quittingRootExpectedPayoff
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro now hnow
  exact expect_conditional_timingPurePayoff dates mixed now
    (by simpa only [PMF.mem_support_iff] using hnow) who

/-- The short mixed-payoff evaluator is exactly the finite timing game's
expected-utility evaluator. -/
theorem finiteDeadlineTimingGame_mixedEU_eq_timingMixedPayoff
    (dates : ℕ)
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction dates))
    (who : Player) :
    (quittingFiniteDeadlineTimingGame reward dates).mixedExtension.eu
        mixed who = timingMixedPayoff dates mixed who := by
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
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction dates))
    (who : Player)
    (action : QuittingFiniteDeadlineTimingAction dates) :
    (quittingFiniteDeadlineTimingGame reward dates).mixedGain
        mixed who action =
      timingMixedPayoff dates
          (Function.update mixed who (PMF.pure action)) who -
        timingMixedPayoff dates mixed who := by
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
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (who : Player)
    (replacement : PMF (QuittingFiniteDeadlineTimingAction dates)) :
    Player → PMF (QuittingFiniteDeadlineTimingAction (dates + 1)) :=
  Function.update mixed who
    (timingLawWithTail (mixed who) replacement)

/-- Tail replacement preserves every current root marginal. -/
theorem timingMixedWithTail_current {dates : ℕ}
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (who : Player)
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

/-- Under positive current continuation, the shifted tail family of a
one-coordinate replacement is the corresponding updated tail family. -/
theorem timingMixedWithTail_tail {dates : ℕ}
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (who : Player)
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
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (who : Player)
    (replacement : PMF (QuittingFiniteDeadlineTimingAction dates))
    (hcontinue : pushforward (mixed who) timingActionCurrent false ≠ 0) :
    timingMixedPayoff (dates + 1)
          (timingMixedWithTail mixed who replacement) who -
        timingMixedPayoff (dates + 1) mixed who =
      quittingStationaryContinueMass
          (fun player ↦ pushforward (mixed player) timingActionCurrent) *
        (timingMixedPayoff dates
            (Function.update (fun player ↦ timingLawTail (mixed player))
              who replacement) who -
          timingMixedPayoff dates
            (fun player ↦ timingLawTail (mixed player)) who) := by
  rw [timingMixedPayoff_succ, timingMixedPayoff_succ,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    timingMixedWithTail_current,
    timingMixedWithTail_tail mixed who replacement hcontinue]
  ring

/-- Coordinatewise positive current continuation gives positive joint
all-Continue reach. -/
theorem timingCurrentRoot_continueMass_pos
    (dates : ℕ)
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
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
theorem timingLawTail_isNash_of_isNash
    (dates : ℕ)
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward (dates + 1)).mixedExtension.IsNash
      mixed)
    (hcontinue : ∀ who,
      pushforward (mixed who) timingActionCurrent false ≠ 0) :
    (quittingFiniteDeadlineTimingGame reward dates).mixedExtension.IsNash
      (fun who ↦ timingLawTail (mixed who)) := by
  intro who replacement
  have hnashSplice := hnash who
    (timingLawWithTail (mixed who) replacement)
  have htransport := timingMixedPayoff_withTail_sub
    dates mixed who replacement (hcontinue who)
  rw [← finiteDeadlineTimingGame_mixedEU_eq_timingMixedPayoff
      (dates + 1) mixed who,
    ← finiteDeadlineTimingGame_mixedEU_eq_timingMixedPayoff
      (dates + 1) (timingMixedWithTail mixed who replacement) who]
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
      timingMixedPayoff dates
          (Function.update (fun player ↦ timingLawTail (mixed player))
            who replacement) who -
        timingMixedPayoff dates
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
        (timingMixedPayoff dates
            (Function.update (fun player ↦ timingLawTail (mixed player))
              who replacement) who -
          timingMixedPayoff dates
            (fun player ↦ timingLawTail (mixed player)) who) ≤ 0 := by
    rw [← htransport]
    exact hwholeNonpos
  exact (not_lt_of_ge hmulNonpos) hmulPos

/-! ## Table-specific elimination of current boundary actions -/

theorem rootExpectedPayoff_update_true_two
    (root : Player → PMF Bool) (continuation : Payoff Player) :
    quittingRootExpectedPayoff reward continuation
        (Function.update root (2 : Player) (PMF.pure true)) 2 = -1 := by
  have hzero := Math.Probability.pmf_toReal_sum_one (root 0)
  have hone := Math.Probability.pmf_toReal_sum_one (root 1)
  have hthree := Math.Probability.pmf_toReal_sum_one (root 3)
  simp only [Fintype.sum_bool] at hzero hone hthree
  have hzero' : ((root 0) false).toReal = 1 - ((root 0) true).toReal := by
    linarith
  have hone' : ((root 1) false).toReal = 1 - ((root 1) true).toReal := by
    linarith
  have hthree' : ((root 3) false).toReal = 1 - ((root 3) true).toReal := by
    linarith
  unfold quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [reward, quittingRootPayoff, quittingQuitters,
    Math.Probability.expect_eq_sum]
  rw [hzero', hone', hthree']
  ring

theorem rootExpectedPayoff_update_true_three
    (root : Player → PMF Bool) (continuation : Payoff Player) :
    quittingRootExpectedPayoff reward continuation
        (Function.update root (3 : Player) (PMF.pure true)) 3 = -1 := by
  have hzero := Math.Probability.pmf_toReal_sum_one (root 0)
  have hone := Math.Probability.pmf_toReal_sum_one (root 1)
  have htwo := Math.Probability.pmf_toReal_sum_one (root 2)
  simp only [Fintype.sum_bool] at hzero hone htwo
  have hzero' : ((root 0) false).toReal = 1 - ((root 0) true).toReal := by
    linarith
  have hone' : ((root 1) false).toReal = 1 - ((root 1) true).toReal := by
    linarith
  have htwo' : ((root 2) false).toReal = 1 - ((root 2) true).toReal := by
    linarith
  unfold quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [reward, quittingRootPayoff, quittingQuitters,
    Math.Probability.expect_eq_sum]
  rw [hzero', hone', htwo']
  ring

theorem rootExpectedPayoff_update_false_two
    (root : Player → PMF Bool) (continuation : Payoff Player)
    (hcontinuation : continuation 2 = 0) :
    quittingRootExpectedPayoff reward continuation
        (Function.update root (2 : Player) (PMF.pure false)) 2 = 0 := by
  unfold quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [reward, quittingRootPayoff, quittingQuitters,
    Math.Probability.expect_eq_sum, hcontinuation]

theorem rootExpectedPayoff_update_false_three
    (root : Player → PMF Bool) (continuation : Payoff Player)
    (hcontinuation : continuation 3 = 0) :
    quittingRootExpectedPayoff reward continuation
        (Function.update root (3 : Player) (PMF.pure false)) 3 = 0 := by
  unfold quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [reward, quittingRootPayoff, quittingQuitters,
    Math.Probability.expect_eq_sum, hcontinuation]

theorem timingMixedPayoff_update_current_two
    (dates : ℕ)
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction (dates + 1))) :
    timingMixedPayoff (dates + 1)
        (Function.update mixed (2 : Player)
          (PMF.pure (some (0 : Fin (dates + 1))))) 2 = -1 := by
  rw [timingMixedPayoff_succ]
  have hroot :
      (fun player ↦ pushforward
        (Function.update mixed (2 : Player)
          (PMF.pure (some (0 : Fin (dates + 1)))) player)
        timingActionCurrent) =
      Function.update
        (fun player ↦ pushforward (mixed player) timingActionCurrent)
        (2 : Player) (PMF.pure true) := by
    funext player
    by_cases hplayer : player = 2
    · subst player
      rw [Function.update_self]
      unfold pushforward
      rw [PMF.pure_map, Function.update_self]
      have hcurrent : timingActionCurrent
          (some (0 : Fin (dates + 1))) = true := by
        simp [timingActionCurrent]
      rw [hcurrent]
    · simp [Function.update_of_ne hplayer]
  rw [hroot, rootExpectedPayoff_update_true_two]

theorem timingMixedPayoff_update_current_three
    (dates : ℕ)
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction (dates + 1))) :
    timingMixedPayoff (dates + 1)
        (Function.update mixed (3 : Player)
          (PMF.pure (some (0 : Fin (dates + 1))))) 3 = -1 := by
  rw [timingMixedPayoff_succ]
  have hroot :
      (fun player ↦ pushforward
        (Function.update mixed (3 : Player)
          (PMF.pure (some (0 : Fin (dates + 1)))) player)
        timingActionCurrent) =
      Function.update
        (fun player ↦ pushforward (mixed player) timingActionCurrent)
        (3 : Player) (PMF.pure true) := by
    funext player
    by_cases hplayer : player = 3
    · subst player
      rw [Function.update_self]
      unfold pushforward
      rw [PMF.pure_map, Function.update_self]
      have hcurrent : timingActionCurrent
          (some (0 : Fin (dates + 1))) = true := by
        simp [timingActionCurrent]
      rw [hcurrent]
    · simp [Function.update_of_ne hplayer]
  rw [hroot, rootExpectedPayoff_update_true_three]

theorem timingMixedPayoff_zero
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction 0))
    (who : Player) :
    timingMixedPayoff 0 mixed who = 0 := by
  unfold timingMixedPayoff
  calc
    Math.Probability.expect (pmfPi mixed)
        (fun choices ↦ timingPurePayoff 0 choices who) =
      Math.Probability.expect (pmfPi mixed) (fun _ ↦ 0) := by
        apply Math.ProbabilityMassFunction.expect_congr_on_support
        intro choices _
        have hchoices : choices = fun _ ↦ none := by
          funext player
          cases hchoice : choices player with
          | none => rfl
          | some impossible => exact Fin.elim0 impossible
        subst choices
        unfold timingPurePayoff
        have hprofile :
            quittingPureStoppingTimeProfile reward (fun _ : Player ↦ ⊤) =
              quittingAlwaysContinueProfile reward := by
          funext player time history
          simp [quittingPureStoppingTimeProfile,
            quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
            quittingAlwaysContinueProfile,
            StochasticGame.stationaryBehaviorProfile]
          rfl
        change quittingTerminalPayoff reward
          (quittingPureStoppingTimeProfile reward (fun _ : Player ↦ ⊤)) who = 0
        rw [hprofile, quittingTerminalPayoff_quittingAlwaysContinue]
    _ = 0 := Math.Probability.expect_const (pmfPi mixed) 0

@[simp] theorem timingLawTail_pure_none {dates : ℕ} :
    timingLawTail
        (PMF.pure none :
          PMF (QuittingFiniteDeadlineTimingAction (dates + 1))) =
      (PMF.pure none : PMF (QuittingFiniteDeadlineTimingAction dates)) := by
  let law : PMF (QuittingFiniteDeadlineTimingAction (dates + 1)) :=
    PMF.pure none
  have hcontinue : pushforward law timingActionCurrent false ≠ 0 := by
    unfold law pushforward
    rw [PMF.pure_map]
    simp [timingActionCurrent]
  have hcond : condOn law timingActionCurrent false = law := by
    apply PMF.ext
    intro action
    rw [condOn_apply law timingActionCurrent false action hcontinue]
    cases action with
    | none =>
        unfold pushforward law
        rw [PMF.pure_map]
        simp [timingActionCurrent]
    | some time => simp [law]
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
  rw [PMF.map_comp, hcomp, PMF.map_id] at hmapped
  dsimp only [law] at hmapped
  simpa only [PMF.pure_map, timingActionTail] using hmapped

/-- Shifting a one-coordinate update is the corresponding update of the
shifted marginal family. -/
theorem timingLawTail_update {dates : ℕ}
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (who : Player)
    (law : PMF (QuittingFiniteDeadlineTimingAction (dates + 1))) :
    (fun player ↦ timingLawTail (Function.update mixed who law player)) =
      Function.update (fun player ↦ timingLawTail (mixed player)) who
        (timingLawTail law) := by
  funext player
  by_cases hplayer : player = who
  · subst player
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hplayer, Function.update_of_ne hplayer]

/-- A dummy player who deterministically never stops has zero payoff in every
finite timing game. -/
theorem timingMixedPayoff_update_never_two :
    ∀ (dates : ℕ)
      (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction dates)),
      timingMixedPayoff dates
        (Function.update mixed (2 : Player) (PMF.pure none)) 2 = 0 := by
  intro dates
  induction dates with
  | zero =>
      intro mixed
      exact timingMixedPayoff_zero _ 2
  | succ dates ih =>
      intro mixed
      rw [timingMixedPayoff_succ]
      have hroot :
          (fun player ↦ pushforward
              (Function.update mixed (2 : Player) (PMF.pure none) player)
              timingActionCurrent) =
            Function.update
              (fun player ↦ pushforward (mixed player) timingActionCurrent)
              (2 : Player) (PMF.pure false) := by
        funext player
        by_cases hplayer : player = 2
        · subst player
          rw [Function.update_self, Function.update_self]
          unfold pushforward
          rw [PMF.pure_map]
          rfl
        · rw [Function.update_of_ne hplayer, Function.update_of_ne hplayer]
      have htail :
          (fun player ↦ timingLawTail
              (Function.update mixed (2 : Player) (PMF.pure none) player)) =
            Function.update (fun player ↦ timingLawTail (mixed player))
              (2 : Player) (PMF.pure none) := by
        rw [timingLawTail_update, timingLawTail_pure_none]
      rw [hroot, htail, rootExpectedPayoff_update_false_two]
      exact ih _

/-- The second dummy coordinate has the same exact zero-payoff Never
certificate. -/
theorem timingMixedPayoff_update_never_three :
    ∀ (dates : ℕ)
      (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction dates)),
      timingMixedPayoff dates
        (Function.update mixed (3 : Player) (PMF.pure none)) 3 = 0 := by
  intro dates
  induction dates with
  | zero =>
      intro mixed
      exact timingMixedPayoff_zero _ 3
  | succ dates ih =>
      intro mixed
      rw [timingMixedPayoff_succ]
      have hroot :
          (fun player ↦ pushforward
              (Function.update mixed (3 : Player) (PMF.pure none) player)
              timingActionCurrent) =
            Function.update
              (fun player ↦ pushforward (mixed player) timingActionCurrent)
              (3 : Player) (PMF.pure false) := by
        funext player
        by_cases hplayer : player = 3
        · subst player
          rw [Function.update_self, Function.update_self]
          unfold pushforward
          rw [PMF.pure_map]
          rfl
        · rw [Function.update_of_ne hplayer, Function.update_of_ne hplayer]
      have htail :
          (fun player ↦ timingLawTail
              (Function.update mixed (3 : Player) (PMF.pure none) player)) =
            Function.update (fun player ↦ timingLawTail (mixed player))
              (3 : Player) (PMF.pure none) := by
        rw [timingLawTail_update, timingLawTail_pure_none]
      rw [hroot, htail, rootExpectedPayoff_update_false_three]
      exact ih _

/-- In every positive-deadline Nash law, the first dummy player puts no mass
on the current stopping action. -/
theorem dummyTwo_current_eq_zero
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.IsNash mixed) :
    mixed 2 (some (0 : Fin (dates + 1))) = 0 := by
  letI : Finite (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).Outcome := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  letI (who : Player) : Finite
      ((quittingFiniteDeadlineTimingGame reward
        (dates + 1)).Strategy who) := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  by_contra hcurrent
  have hgain := KernelGame.mixedGain_eq_zero_of_mem_support
    (quittingFiniteDeadlineTimingGame reward (dates + 1)) mixed hnash 2
      (some (0 : Fin (dates + 1))) hcurrent
  rw [finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub,
    timingMixedPayoff_update_current_two] at hgain
  have hnever :=
    ((quittingFiniteDeadlineTimingGame reward
      (dates + 1)).isNash_iff_gains_nonpos mixed).mp hnash 2 none
  rw [finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub,
    timingMixedPayoff_update_never_two] at hnever
  linarith

/-- The second dummy player likewise puts no mass on the current stopping
action in any positive-deadline Nash law. -/
theorem dummyThree_current_eq_zero
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.IsNash mixed) :
    mixed 3 (some (0 : Fin (dates + 1))) = 0 := by
  letI : Finite (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).Outcome := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  letI (who : Player) : Finite
      ((quittingFiniteDeadlineTimingGame reward
        (dates + 1)).Strategy who) := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  by_contra hcurrent
  have hgain := KernelGame.mixedGain_eq_zero_of_mem_support
    (quittingFiniteDeadlineTimingGame reward (dates + 1)) mixed hnash 3
      (some (0 : Fin (dates + 1))) hcurrent
  rw [finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub,
    timingMixedPayoff_update_current_three] at hgain
  have hnever :=
    ((quittingFiniteDeadlineTimingGame reward
      (dates + 1)).isNash_iff_gains_nonpos mixed).mp hnash 3 none
  rw [finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub,
    timingMixedPayoff_update_never_three] at hnever
  linarith

/-- The first dummy's complete current Boolean marginal is deterministic
Continue. -/
theorem dummyTwo_currentLaw_eq_pure_false
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.IsNash mixed) :
    pushforward (mixed 2) timingActionCurrent = PMF.pure false := by
  apply Math.PMFProduct.eq_pure_false_of_true_toReal_eq_zero
  rw [timingActionCurrent_pushforward_true]
  have hzero :
      (some ⟨0, Nat.zero_lt_succ dates⟩ :
        QuittingFiniteDeadlineTimingAction (dates + 1)) =
        some (0 : Fin (dates + 1)) := by
    congr
  rw [hzero, dummyTwo_current_eq_zero dates mixed hnash]
  rfl

/-- The second dummy's complete current Boolean marginal is deterministic
Continue. -/
theorem dummyThree_currentLaw_eq_pure_false
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.IsNash mixed) :
    pushforward (mixed 3) timingActionCurrent = PMF.pure false := by
  apply Math.PMFProduct.eq_pure_false_of_true_toReal_eq_zero
  rw [timingActionCurrent_pushforward_true]
  have hzero :
      (some ⟨0, Nat.zero_lt_succ dates⟩ :
        QuittingFiniteDeadlineTimingAction (dates + 1)) =
        some (0 : Fin (dates + 1)) := by
    congr
  rw [hzero, dummyThree_current_eq_zero dates mixed hnash]
  rfl

/-! ## The two active sure-current corners -/

theorem rootExpectedPayoff_one_of_zero_sure
    (root : Player → PMF Bool) (continuation : Payoff Player)
    (hzero : root 0 = PMF.pure true)
    (htwo : root 2 = PMF.pure false)
    (hthree : root 3 = PMF.pure false) :
    quittingRootExpectedPayoff reward continuation root 1 =
      -1 + (root 1 true).toReal := by
  unfold quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [hzero, htwo, hthree, reward, quittingRootPayoff,
    quittingQuitters, Math.Probability.expect_eq_sum]
  rw [Math.PMFProduct.pmfBool_false_toReal]
  ring

theorem rootExpectedPayoff_zero_of_one_sure
    (root : Player → PMF Bool) (continuation : Payoff Player)
    (hone : root 1 = PMF.pure true)
    (htwo : root 2 = PMF.pure false)
    (hthree : root 3 = PMF.pure false) :
    quittingRootExpectedPayoff reward continuation root 0 =
      1 - (root 0 true).toReal := by
  unfold quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [hone, htwo, hthree, reward, quittingRootPayoff,
    quittingQuitters, Math.Probability.expect_eq_sum]
  rw [Math.PMFProduct.pmfBool_false_toReal]

/-- Under a sure current stop by player `0`, player `1`'s full timing payoff
depends only on its own current mass. -/
theorem timingMixedPayoff_one_of_zero_current_sure
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hzero : pushforward (mixed 0) timingActionCurrent = PMF.pure true)
    (htwo : pushforward (mixed 2) timingActionCurrent = PMF.pure false)
    (hthree : pushforward (mixed 3) timingActionCurrent = PMF.pure false) :
    timingMixedPayoff (dates + 1) mixed 1 =
      -1 + (pushforward (mixed 1) timingActionCurrent true).toReal := by
  rw [timingMixedPayoff_succ]
  exact rootExpectedPayoff_one_of_zero_sure _ _ hzero htwo hthree

/-- Against a sure current stop by player `0`, stopping now gives player `1`
the collision payoff zero. -/
theorem timingMixedPayoff_update_current_one_of_zero_current_sure
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hzero : pushforward (mixed 0) timingActionCurrent = PMF.pure true)
    (htwo : pushforward (mixed 2) timingActionCurrent = PMF.pure false)
    (hthree : pushforward (mixed 3) timingActionCurrent = PMF.pure false) :
    timingMixedPayoff (dates + 1)
      (Function.update mixed 1
        (PMF.pure (some (0 : Fin (dates + 1))))) 1 = 0 := by
  rw [timingMixedPayoff_succ]
  let root : Player → PMF Bool := fun player ↦
    pushforward (mixed player) timingActionCurrent
  have hroot :
      (fun player ↦ pushforward
        (Function.update mixed 1
          (PMF.pure (some (0 : Fin (dates + 1)))) player)
        timingActionCurrent) =
      Function.update root 1 (PMF.pure true) := by
    funext player
    by_cases hplayer : player = 1
    · subst player
      rw [Function.update_self, Function.update_self]
      unfold pushforward
      rw [PMF.pure_map]
      rfl
    · rw [Function.update_of_ne hplayer, Function.update_of_ne hplayer]
  rw [hroot, rootExpectedPayoff_one_of_zero_sure]
  · simp
  · simpa only [root, Function.update_of_ne (by decide : (0 : Player) ≠ 1)]
      using hzero
  · simpa only [root, Function.update_of_ne (by decide : (2 : Player) ≠ 1)]
      using htwo
  · simpa only [root, Function.update_of_ne (by decide : (3 : Player) ≠ 1)]
      using hthree

/-- Under a sure current stop by player `1`, player `0` gets one precisely
when it continues at the current root. -/
theorem timingMixedPayoff_zero_of_one_current_sure
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hone : pushforward (mixed 1) timingActionCurrent = PMF.pure true)
    (htwo : pushforward (mixed 2) timingActionCurrent = PMF.pure false)
    (hthree : pushforward (mixed 3) timingActionCurrent = PMF.pure false) :
    timingMixedPayoff (dates + 1) mixed 0 =
      1 - (pushforward (mixed 0) timingActionCurrent true).toReal := by
  rw [timingMixedPayoff_succ]
  exact rootExpectedPayoff_zero_of_one_sure _ _ hone htwo hthree

/-- Against player `1` stopping now surely, player `0` gets one by Never. -/
theorem timingMixedPayoff_update_never_zero_of_one_current_sure
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hone : pushforward (mixed 1) timingActionCurrent = PMF.pure true)
    (htwo : pushforward (mixed 2) timingActionCurrent = PMF.pure false)
    (hthree : pushforward (mixed 3) timingActionCurrent = PMF.pure false) :
    timingMixedPayoff (dates + 1)
      (Function.update mixed 0 (PMF.pure none)) 0 = 1 := by
  rw [timingMixedPayoff_succ]
  let root : Player → PMF Bool := fun player ↦
    pushforward (mixed player) timingActionCurrent
  have hroot :
      (fun player ↦ pushforward
        (Function.update mixed 0 (PMF.pure none) player)
        timingActionCurrent) =
      Function.update root 0 (PMF.pure false) := by
    funext player
    by_cases hplayer : player = 0
    · subst player
      rw [Function.update_self, Function.update_self]
      unfold pushforward
      rw [PMF.pure_map]
      rfl
    · rw [Function.update_of_ne hplayer, Function.update_of_ne hplayer]
  rw [hroot, rootExpectedPayoff_zero_of_one_sure]
  · simp
  · simpa only [root, Function.update_of_ne (by decide : (1 : Player) ≠ 0)]
      using hone
  · simpa only [root, Function.update_of_ne (by decide : (2 : Player) ≠ 0)]
      using htwo
  · simpa only [root, Function.update_of_ne (by decide : (3 : Player) ≠ 0)]
      using hthree

/-- Player `0` cannot stop surely at the current date in a positive-deadline
mixed Nash law. -/
theorem zero_currentMass_lt_one
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.IsNash mixed) :
    (mixed 0 (some (0 : Fin (dates + 1)))).toReal < 1 := by
  letI : Finite (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).Outcome := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  by_contra hnot
  have hle : (mixed 0 (some (0 : Fin (dates + 1)))).toReal ≤ 1 := by
    exact (ENNReal.toReal_le_toReal
      (PMF.apply_ne_top (mixed 0) (some (0 : Fin (dates + 1))))
      (by norm_num)).2 (PMF.coe_le_one _ _)
  have honeMass :
      (mixed 0 (some (0 : Fin (dates + 1)))).toReal = 1 :=
    le_antisymm hle (le_of_not_gt hnot)
  have hzeroCurrent :
      pushforward (mixed 0) timingActionCurrent = PMF.pure true := by
    apply Math.PMFProduct.eq_pure_true_of_true_toReal_eq_one
    rw [timingActionCurrent_pushforward_true]
    have hzero :
        (some ⟨0, Nat.zero_lt_succ dates⟩ :
          QuittingFiniteDeadlineTimingAction (dates + 1)) =
          some (0 : Fin (dates + 1)) := by
      congr
    rw [hzero, honeMass]
  have htwo := dummyTwo_currentLaw_eq_pure_false dates mixed hnash
  have hthree := dummyThree_currentLaw_eq_pure_false dates mixed hnash
  have hgainOne :=
    ((quittingFiniteDeadlineTimingGame reward
      (dates + 1)).isNash_iff_gains_nonpos mixed).mp hnash 1
        (some (0 : Fin (dates + 1)))
  rw [finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub,
    timingMixedPayoff_update_current_one_of_zero_current_sure
      dates mixed hzeroCurrent htwo hthree,
    timingMixedPayoff_one_of_zero_current_sure
      dates mixed hzeroCurrent htwo hthree] at hgainOne
  have hqLe :
      (pushforward (mixed 1) timingActionCurrent true).toReal ≤ 1 := by
    exact (ENNReal.toReal_le_toReal
      (PMF.apply_ne_top (pushforward (mixed 1) timingActionCurrent) true)
      (by norm_num)).2 (PMF.coe_le_one _ _)
  have hqOne :
      (pushforward (mixed 1) timingActionCurrent true).toReal = 1 := by
    linarith
  have honeCurrent :
      pushforward (mixed 1) timingActionCurrent = PMF.pure true :=
    Math.PMFProduct.eq_pure_true_of_true_toReal_eq_one _ hqOne
  have hgainNever :=
    ((quittingFiniteDeadlineTimingGame reward
      (dates + 1)).isNash_iff_gains_nonpos mixed).mp hnash 0 none
  rw [finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub,
    timingMixedPayoff_update_never_zero_of_one_current_sure
      dates mixed honeCurrent htwo hthree,
    timingMixedPayoff_zero_of_one_current_sure
      dates mixed honeCurrent htwo hthree,
    hzeroCurrent] at hgainNever
  norm_num at hgainNever

/-! ### The finite-law collision deviation at player `1`'s sure corner -/

theorem timingPurePayoff_zero_dates
    (choices : Player → QuittingFiniteDeadlineTimingAction 0)
    (who : Player) :
    timingPurePayoff 0 choices who = 0 := by
  have hchoices : choices = fun _ ↦ none := by
    funext player
    cases hchoice : choices player with
    | none => rfl
    | some impossible => exact Fin.elim0 impossible
  subst choices
  unfold timingPurePayoff
  have hprofile :
      quittingPureStoppingTimeProfile reward (fun _ : Player ↦ ⊤) =
        quittingAlwaysContinueProfile reward := by
    funext player time history
    simp [quittingPureStoppingTimeProfile,
      quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
      quittingAlwaysContinueProfile,
      StochasticGame.stationaryBehaviorProfile]
    rfl
  change quittingTerminalPayoff reward
    (quittingPureStoppingTimeProfile reward (fun _ : Player ↦ ⊤)) who = 0
  rw [hprofile, quittingTerminalPayoff_quittingAlwaysContinue]

/-- Player `1`'s pure payoff in this table is always either zero or minus
one, irrespective of the dummy players' timing actions. -/
theorem timingPurePayoff_one_eq_zero_or_neg_one :
    ∀ (dates : ℕ)
      (choices : Player → QuittingFiniteDeadlineTimingAction dates),
      timingPurePayoff dates choices 1 = 0 ∨
        timingPurePayoff dates choices 1 = -1 := by
  intro dates
  induction dates with
  | zero =>
      intro choices
      left
      exact timingPurePayoff_zero_dates choices 1
  | succ dates ih =>
      intro choices
      rw [timingPurePayoff_succ]
      by_cases hquit :
          (quittingQuitters (fun player ↦
            timingActionCurrent (choices player))).Nonempty
      · unfold quittingRootPayoff
        simp only [dif_pos hquit]
        simp only [reward_one]
        split_ifs <;> simp
      · unfold quittingRootPayoff
        simp only [dif_neg hquit]
        exact ih (timingChoicesTail choices)

/-- If the two active players select the same timing action, player `1`'s
pure payoff is zero, even when a dummy player stops earlier. -/
theorem timingPurePayoff_one_eq_zero_of_active_eq :
    ∀ (dates : ℕ)
      (choices : Player → QuittingFiniteDeadlineTimingAction dates),
      choices 0 = choices 1 → timingPurePayoff dates choices 1 = 0 := by
  intro dates
  induction dates with
  | zero =>
      intro choices _
      exact timingPurePayoff_zero_dates choices 1
  | succ dates ih =>
      intro choices heq
      rw [timingPurePayoff_succ]
      have hcurrent :
          timingActionCurrent (choices 0) =
            timingActionCurrent (choices 1) :=
        congrArg timingActionCurrent heq
      have htail :
          timingChoicesTail choices 0 = timingChoicesTail choices 1 :=
        congrArg timingActionTail heq
      by_cases hquit :
          (quittingQuitters (fun player ↦
            timingActionCurrent (choices player))).Nonempty
      · unfold quittingRootPayoff
        simp only [dif_pos hquit]
        simp only [reward_one]
        rw [if_pos]
        simp [quittingQuitters, hcurrent]
      · unfold quittingRootPayoff
        simp only [dif_neg hquit]
        exact ih (timingChoicesTail choices) htail

/-- A pure deviation by player `1` to an action used by player `0` improves
the pointwise floor from `-1` to `0` on the matching atom. -/
theorem timingPurePayoff_one_ge_matching_floor
    (dates : ℕ)
    (choices : Player → QuittingFiniteDeadlineTimingAction dates)
    (action : QuittingFiniteDeadlineTimingAction dates)
    (hone : choices 1 = action) :
    (if choices 0 = action then 0 else -1) ≤
      timingPurePayoff dates choices 1 := by
  by_cases hzero : choices 0 = action
  · rw [if_pos hzero,
      timingPurePayoff_one_eq_zero_of_active_eq dates choices
        (hzero.trans hone.symm)]
  · rw [if_neg hzero]
    rcases timingPurePayoff_one_eq_zero_or_neg_one dates choices with
      hpayoff | hpayoff
    · rw [hpayoff]
      norm_num
    · rw [hpayoff]

/-- The payoff from copying any positive-mass timing action of player `0` is
at least `-1` plus that atom's mass. -/
theorem timingMixedPayoff_update_one_ge_neg_one_add_atom
    (dates : ℕ)
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction dates))
    (action : QuittingFiniteDeadlineTimingAction dates) :
    -1 + (mixed 0 action).toReal ≤
      timingMixedPayoff dates
        (Function.update mixed 1 (PMF.pure action)) 1 := by
  let updated := Function.update mixed 1 (PMF.pure action)
  let joint := pmfPi updated
  let floor :
      (Player → QuittingFiniteDeadlineTimingAction dates) → ℝ :=
    fun choices ↦ if choices 0 = action then 0 else -1
  have hmono : Math.Probability.expect joint floor ≤
      Math.Probability.expect joint
        (fun choices ↦ timingPurePayoff dates choices 1) := by
    apply Math.ProbabilityMassFunction.expect_mono_on_support
    intro choices hchoices
    have hmass : joint choices ≠ 0 := by
      simpa only [PMF.mem_support_iff] using hchoices
    have honeMass := pmfPi_coord_ne_zero_of_ne_zero
      updated choices hmass 1
    have hone : choices 1 = action := by
      unfold updated at honeMass
      rw [Function.update_self] at honeMass
      by_contra hne
      rw [PMF.pure_apply_of_ne action (choices 1) hne] at honeMass
      exact honeMass rfl
    exact timingPurePayoff_one_ge_matching_floor dates choices action hone
  have hcoord :
      pushforward joint (fun choices ↦ choices 0) = mixed 0 := by
    unfold joint
    rw [pmfPi_push_coord]
    unfold updated
    rw [Function.update_of_ne (by decide : (0 : Player) ≠ 1)]
  have hfloor : Math.Probability.expect joint floor =
      -1 + (mixed 0 action).toReal := by
    calc
      Math.Probability.expect joint floor =
          Math.Probability.expect
            (pushforward joint fun choices ↦ choices 0)
            (fun choice ↦ if choice = action then 0 else -1) := by
              unfold pushforward floor
              exact (Math.Probability.expect_map
                (fun choices ↦ choices 0) joint
                (fun choice ↦ if choice = action then 0 else -1)).symm
      _ = Math.Probability.expect (mixed 0)
          (fun choice ↦ if choice = action then 0 else -1) := by
            rw [hcoord]
      _ = Math.Probability.expect (mixed 0)
          (fun choice ↦ (if choice = action then 1 else 0) - 1) := by
            congr 1
            funext choice
            split_ifs <;> ring
      _ = (mixed 0 action).toReal - 1 := by
            rw [Math.Probability.expect_sub,
              Math.Probability.apply_toReal_eq_expect_indicator,
              Math.Probability.expect_const]
      _ = -1 + (mixed 0 action).toReal := by ring
  rw [hfloor] at hmono
  exact hmono

theorem rootExpectedPayoff_one_of_one_sure_zero_continue
    (root : Player → PMF Bool) (continuation : Payoff Player)
    (hzero : root 0 = PMF.pure false)
    (hone : root 1 = PMF.pure true)
    (htwo : root 2 = PMF.pure false)
    (hthree : root 3 = PMF.pure false) :
    quittingRootExpectedPayoff reward continuation root 1 = -1 := by
  unfold quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [hzero, hone, htwo, hthree, reward, quittingRootPayoff,
    quittingQuitters, Math.Probability.expect_eq_sum]

theorem timingMixedPayoff_one_of_one_current_sure_zero_continue
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hzero : pushforward (mixed 0) timingActionCurrent = PMF.pure false)
    (hone : pushforward (mixed 1) timingActionCurrent = PMF.pure true)
    (htwo : pushforward (mixed 2) timingActionCurrent = PMF.pure false)
    (hthree : pushforward (mixed 3) timingActionCurrent = PMF.pure false) :
    timingMixedPayoff (dates + 1) mixed 1 = -1 := by
  rw [timingMixedPayoff_succ]
  exact rootExpectedPayoff_one_of_one_sure_zero_continue
    _ _ hzero hone htwo hthree

/-- Player `1` also cannot stop surely at the current date in a
positive-deadline mixed Nash law. The decisive deviation copies one
positive-mass timing atom of player `0`. -/
theorem one_currentMass_lt_one
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.IsNash mixed) :
    (mixed 1 (some (0 : Fin (dates + 1)))).toReal < 1 := by
  letI : Finite (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).Outcome := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  by_contra hnot
  have hle : (mixed 1 (some (0 : Fin (dates + 1)))).toReal ≤ 1 := by
    exact (ENNReal.toReal_le_toReal
      (PMF.apply_ne_top (mixed 1) (some (0 : Fin (dates + 1))))
      (by norm_num)).2 (PMF.coe_le_one _ _)
  have honeMass :
      (mixed 1 (some (0 : Fin (dates + 1)))).toReal = 1 :=
    le_antisymm hle (le_of_not_gt hnot)
  have honeCurrent :
      pushforward (mixed 1) timingActionCurrent = PMF.pure true := by
    apply Math.PMFProduct.eq_pure_true_of_true_toReal_eq_one
    rw [timingActionCurrent_pushforward_true]
    have hzero :
        (some ⟨0, Nat.zero_lt_succ dates⟩ :
          QuittingFiniteDeadlineTimingAction (dates + 1)) =
          some (0 : Fin (dates + 1)) := by
      congr
    rw [hzero, honeMass]
  have htwo := dummyTwo_currentLaw_eq_pure_false dates mixed hnash
  have hthree := dummyThree_currentLaw_eq_pure_false dates mixed hnash
  have hgainNever :=
    ((quittingFiniteDeadlineTimingGame reward
      (dates + 1)).isNash_iff_gains_nonpos mixed).mp hnash 0 none
  rw [finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub,
    timingMixedPayoff_update_never_zero_of_one_current_sure
      dates mixed honeCurrent htwo hthree,
    timingMixedPayoff_zero_of_one_current_sure
      dates mixed honeCurrent htwo hthree] at hgainNever
  have hpNonneg : 0 ≤
      (pushforward (mixed 0) timingActionCurrent true).toReal :=
    ENNReal.toReal_nonneg
  have hpZero :
      (pushforward (mixed 0) timingActionCurrent true).toReal = 0 := by
    linarith
  have hzeroCurrent :
      pushforward (mixed 0) timingActionCurrent = PMF.pure false :=
    Math.PMFProduct.eq_pure_false_of_true_toReal_eq_zero _ hpZero
  obtain ⟨action, hactionSupport⟩ := (mixed 0).support_nonempty
  have haction : mixed 0 action ≠ 0 := by
    simpa only [PMF.mem_support_iff] using hactionSupport
  have hactionPos : 0 < (mixed 0 action).toReal :=
    ENNReal.toReal_pos haction (PMF.apply_ne_top (mixed 0) action)
  have hgainAction :=
    ((quittingFiniteDeadlineTimingGame reward
      (dates + 1)).isNash_iff_gains_nonpos mixed).mp hnash 1 action
  rw [finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub,
    timingMixedPayoff_one_of_one_current_sure_zero_continue
      dates mixed hzeroCurrent honeCurrent htwo hthree] at hgainAction
  have hlower := timingMixedPayoff_update_one_ge_neg_one_add_atom
    (dates + 1) mixed action
  linarith

/-- Every coordinate has positive current-Continue mass in a
positive-deadline Nash law. -/
theorem all_currentContinue_ne_zero
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.IsNash mixed) :
    ∀ who, pushforward (mixed who) timingActionCurrent false ≠ 0 := by
  intro who
  have hcases : who = 0 ∨ who = 1 ∨ who = 2 ∨ who = 3 := by
    fin_cases who <;> simp
  rcases hcases with rfl | rfl | rfl | rfl
  · exact timingActionCurrent_false_ne_zero_of_lt_one _
      (zero_currentMass_lt_one dates mixed hnash)
  · exact timingActionCurrent_false_ne_zero_of_lt_one _
      (one_currentMass_lt_one dates mixed hnash)
  · rw [dummyTwo_currentLaw_eq_pure_false dates mixed hnash]
    simp
  · rw [dummyThree_currentLaw_eq_pure_false dates mixed hnash]
    simp

/-! ## Exact active-root identification -/

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

theorem rootEndpointDifference_zero_formula
    (dates : ℕ) (root : Player → PMF Bool)
    (htwo : root 2 = PMF.pure false)
    (hthree : root 3 = PMF.pure false) :
    quittingRootEndpointDifference reward (valueAfter dates) root 0 =
      (1 - (root 1 true).toReal) / 2 -
        ((root 1 true).toReal +
          (1 - (root 1 true).toReal) * zeroValue dates) := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4, expect_pmfPi_fin4]
  simp [htwo, hthree, valueAfter, reward, quittingRootPayoff,
    quittingQuitters, Math.Probability.expect_eq_sum]
  rw [Math.PMFProduct.pmfBool_false_toReal]
  ring

theorem rootEndpointDifference_one_formula
    (dates : ℕ) (root : Player → PMF Bool)
    (htwo : root 2 = PMF.pure false)
    (hthree : root 3 = PMF.pure false) :
    quittingRootEndpointDifference reward (valueAfter dates) root 1 =
      (-1 + (root 0 true).toReal) -
        (-(root 0 true).toReal +
          (1 - (root 0 true).toReal) * oneValue dates) := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4, expect_pmfPi_fin4]
  simp [htwo, hthree, valueAfter, reward, quittingRootPayoff,
    quittingQuitters, Math.Probability.expect_eq_sum]
  rw [Math.PMFProduct.pmfBool_false_toReal]
  ring

/-- Pure-Quit root payoff is independent of the declared continuation
payoff, because a sure own Quit makes joint continuation impossible. -/
theorem quittingRootQuitPayoff_tail_irrel
    (first second : Payoff Player) (root : Player → PMF Bool)
    (who : Player) :
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
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (who : Player) :
    timingMixedPayoff (dates + 1)
        (Function.update mixed who
          (PMF.pure (some (0 : Fin (dates + 1))))) who =
      quittingRootQuitPayoff reward
        (fun player ↦ timingMixedPayoff dates
          (fun other ↦ timingLawTail (mixed other)) player)
        (fun player ↦ pushforward (mixed player) timingActionCurrent)
        who := by
  rw [timingMixedPayoff_succ]
  let root : Player → PMF Bool := fun player ↦
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
  exact quittingRootQuitPayoff_tail_irrel _ _ root who

/-- Replacing one timing marginal by its lifted conditioned tail is exactly
the current root's Continue endpoint. -/
theorem timingMixedPayoff_update_liftedTail_eq_continuePayoff
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (who : Player) :
    timingMixedPayoff (dates + 1)
        (Function.update mixed who
          ((timingLawTail (mixed who)).map timingActionLift)) who =
      quittingRootContinuePayoff reward
        (fun player ↦ timingMixedPayoff dates
          (fun other ↦ timingLawTail (mixed other)) player)
        (fun player ↦ pushforward (mixed player) timingActionCurrent)
        who := by
  rw [timingMixedPayoff_succ]
  let root : Player → PMF Bool := fun player ↦
    pushforward (mixed player) timingActionCurrent
  let tails : Player →
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

/-- A timing Nash law with the displayed conditioned-tail payoff has
nonpositive current endpoint difference at every coordinate. -/
theorem currentRoot_endpointDifference_nonpos
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.IsNash mixed)
    (htailPayoff :
      (fun player ↦ timingMixedPayoff dates
        (fun other ↦ timingLawTail (mixed other)) player) =
        valueAfter dates)
    (who : Player) :
    quittingRootEndpointDifference reward (valueAfter dates)
      (fun player ↦ pushforward (mixed player) timingActionCurrent) who ≤ 0 := by
  letI : Finite (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).Outcome := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  have hgain :=
    ((quittingFiniteDeadlineTimingGame reward
      (dates + 1)).isNash_iff_gains_nonpos mixed).mp hnash who
        (some (0 : Fin (dates + 1)))
  rw [finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub,
    timingMixedPayoff_update_current_eq_quitPayoff,
    timingMixedPayoff_succ] at hgain
  change quittingRootQuitPayoff reward
      (fun player ↦ timingMixedPayoff dates
        (fun other ↦ timingLawTail (mixed other)) player)
      (fun player ↦ pushforward (mixed player) timingActionCurrent) who -
    quittingRootSuccessorPayoff reward
      (fun player ↦ timingMixedPayoff dates
        (fun other ↦ timingLawTail (mixed other)) player)
      (fun player ↦ pushforward (mixed player) timingActionCurrent) who ≤ 0
    at hgain
  rw [htailPayoff,
    quittingRootQuitPayoff_sub_successorPayoff] at hgain
  have hcontinue := all_currentContinue_ne_zero dates mixed hnash who
  have hcontinuePos : 0 <
      (pushforward (mixed who) timingActionCurrent false).toReal :=
    ENNReal.toReal_pos hcontinue
      (PMF.apply_ne_top (pushforward (mixed who) timingActionCurrent) false)
  rw [mul_comm] at hgain
  exact nonpos_of_mul_nonpos_left hgain hcontinuePos

/-- Positive mass on the current timing atom pins the corresponding endpoint
difference to zero. -/
theorem currentRoot_endpointDifference_eq_zero_of_current_ne_zero
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.IsNash mixed)
    (htailPayoff :
      (fun player ↦ timingMixedPayoff dates
        (fun other ↦ timingLawTail (mixed other)) player) =
        valueAfter dates)
    (who : Player)
    (hcurrent : mixed who (some (0 : Fin (dates + 1))) ≠ 0) :
    quittingRootEndpointDifference reward (valueAfter dates)
      (fun player ↦ pushforward (mixed player) timingActionCurrent) who = 0 := by
  letI : Finite (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).Outcome := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  letI (player : Player) : Finite
      ((quittingFiniteDeadlineTimingGame reward
        (dates + 1)).Strategy player) := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  have hgain := KernelGame.mixedGain_eq_zero_of_mem_support
    (quittingFiniteDeadlineTimingGame reward (dates + 1)) mixed hnash who
      (some (0 : Fin (dates + 1))) hcurrent
  rw [finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub,
    timingMixedPayoff_update_current_eq_quitPayoff,
    timingMixedPayoff_succ] at hgain
  change quittingRootQuitPayoff reward
      (fun player ↦ timingMixedPayoff dates
        (fun other ↦ timingLawTail (mixed other)) player)
      (fun player ↦ pushforward (mixed player) timingActionCurrent) who -
    quittingRootSuccessorPayoff reward
      (fun player ↦ timingMixedPayoff dates
        (fun other ↦ timingLawTail (mixed other)) player)
      (fun player ↦ pushforward (mixed player) timingActionCurrent) who = 0
    at hgain
  rw [htailPayoff,
    quittingRootQuitPayoff_sub_successorPayoff] at hgain
  have hcontinue := all_currentContinue_ne_zero dates mixed hnash who
  have hcontinuePos : 0 <
      (pushforward (mixed who) timingActionCurrent false).toReal :=
    ENNReal.toReal_pos hcontinue
      (PMF.apply_ne_top (pushforward (mixed who) timingActionCurrent) false)
  exact (mul_eq_zero.mp hgain).resolve_left hcontinuePos.ne'

theorem timingActionCurrent_pushforward_true_zero {dates : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction (dates + 1))) :
    (pushforward law timingActionCurrent true).toReal =
      (law (some (0 : Fin (dates + 1)))).toReal := by
  rw [timingActionCurrent_pushforward_true]
  congr 3

/-- The active player `0` has positive current mass once the conditioned tail
has the displayed shorter-game payoff. -/
theorem zero_current_ne_zero_of_tailPayoff
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.IsNash mixed)
    (htailPayoff :
      (fun player ↦ timingMixedPayoff dates
        (fun other ↦ timingLawTail (mixed other)) player) =
        valueAfter dates) :
    mixed 0 (some (0 : Fin (dates + 1))) ≠ 0 := by
  let root : Player → PMF Bool := fun player ↦
    pushforward (mixed player) timingActionCurrent
  have htwo : root 2 = PMF.pure false :=
    dummyTwo_currentLaw_eq_pure_false dates mixed hnash
  have hthree : root 3 = PMF.pure false :=
    dummyThree_currentLaw_eq_pure_false dates mixed hnash
  have hdiffZero := currentRoot_endpointDifference_nonpos
    dates mixed hnash htailPayoff 0
  by_contra hzero
  have hpZero : (root 0 true).toReal = 0 := by
    unfold root
    rw [timingActionCurrent_pushforward_true_zero, hzero]
    rfl
  have hdiffOneFormula := rootEndpointDifference_one_formula
    dates root htwo hthree
  rw [hpZero] at hdiffOneFormula
  by_cases hone : mixed 1 (some (0 : Fin (dates + 1))) = 0
  · have hqZero : (root 1 true).toReal = 0 := by
      unfold root
      rw [timingActionCurrent_pushforward_true_zero, hone]
      rfl
    have hdiffZeroFormula := rootEndpointDifference_zero_formula
      dates root htwo hthree
    rw [hqZero] at hdiffZeroFormula
    have hvalue := zeroValue_lt_half dates
    linarith
  · have hdiffOne :=
      currentRoot_endpointDifference_eq_zero_of_current_ne_zero
        dates mixed hnash htailPayoff 1 hone
    have hvalue := oneValue_gt_neg_one dates
    linarith

/-- Player `1`'s current mass is then positive as well. -/
theorem one_current_ne_zero_of_tailPayoff
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.IsNash mixed)
    (htailPayoff :
      (fun player ↦ timingMixedPayoff dates
        (fun other ↦ timingLawTail (mixed other)) player) =
        valueAfter dates) :
    mixed 1 (some (0 : Fin (dates + 1))) ≠ 0 := by
  have hzero := zero_current_ne_zero_of_tailPayoff
    dates mixed hnash htailPayoff
  have hdiffZero :=
    currentRoot_endpointDifference_eq_zero_of_current_ne_zero
      dates mixed hnash htailPayoff 0 hzero
  let root : Player → PMF Bool := fun player ↦
    pushforward (mixed player) timingActionCurrent
  have htwo : root 2 = PMF.pure false :=
    dummyTwo_currentLaw_eq_pure_false dates mixed hnash
  have hthree : root 3 = PMF.pure false :=
    dummyThree_currentLaw_eq_pure_false dates mixed hnash
  have hformula := rootEndpointDifference_zero_formula
    dates root htwo hthree
  by_contra hone
  have hqZero : (root 1 true).toReal = 0 := by
    unfold root
    rw [timingActionCurrent_pushforward_true_zero, hone]
    rfl
  rw [hqZero] at hformula
  have hvalue := zeroValue_lt_half dates
  linarith

private theorem pmfBool_eq_of_true_toReal_eq
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

/-- The current Boolean root of any Nash law with the unique shorter tail is
exactly the displayed backward-induction root. -/
theorem currentRoot_eq_rootBefore_of_tailPayoff
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.IsNash mixed)
    (htailPayoff :
      (fun player ↦ timingMixedPayoff dates
        (fun other ↦ timingLawTail (mixed other)) player) =
        valueAfter dates) :
    (fun player ↦ pushforward (mixed player) timingActionCurrent) =
      rootBefore dates := by
  let root : Player → PMF Bool := fun player ↦
    pushforward (mixed player) timingActionCurrent
  have htwo : root 2 = PMF.pure false :=
    dummyTwo_currentLaw_eq_pure_false dates mixed hnash
  have hthree : root 3 = PMF.pure false :=
    dummyThree_currentLaw_eq_pure_false dates mixed hnash
  have hzero := zero_current_ne_zero_of_tailPayoff
    dates mixed hnash htailPayoff
  have hone := one_current_ne_zero_of_tailPayoff
    dates mixed hnash htailPayoff
  have hdiffZero :=
    currentRoot_endpointDifference_eq_zero_of_current_ne_zero
      dates mixed hnash htailPayoff 0 hzero
  have hdiffOne :=
    currentRoot_endpointDifference_eq_zero_of_current_ne_zero
      dates mixed hnash htailPayoff 1 hone
  have hformulaZero := rootEndpointDifference_zero_formula
    dates root htwo hthree
  have hformulaOne := rootEndpointDifference_one_formula
    dates root htwo hthree
  have hp : (root 0 true).toReal = zeroHazard dates := by
    rw [zeroHazard_eq_indifference]
    have hden : 0 < 2 + oneValue dates := by
      have := oneValue_gt_neg_one dates
      linarith
    apply (eq_div_iff hden.ne').2
    nlinarith
  have hq : (root 1 true).toReal = oneHazard dates := by
    rw [oneHazard_eq_indifference]
    have hden : 0 < 3 / 2 - zeroValue dates := by
      have := zeroValue_lt_half dates
      linarith
    apply (eq_div_iff hden.ne').2
    nlinarith
  funext who
  have hcases : who = 0 ∨ who = 1 ∨ who = 2 ∨ who = 3 := by
    fin_cases who <;> simp
  rcases hcases with rfl | rfl | rfl | rfl
  · apply pmfBool_eq_of_true_toReal_eq
    rw [hp, rootBefore_zero_true_toReal]
  · apply pmfBool_eq_of_true_toReal_eq
    rw [hq, rootBefore_one_true_toReal]
  · change root 2 = rootBefore dates 2
    rw [htwo, rootBefore_two]
  · change root 3 = rootBefore dates 3
    rw [hthree, rootBefore_three]

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

/-! ## Backward induction and exact uniqueness -/

/-- Every Nash law of the finite timing game is unique and has the displayed
backward-induction payoff. -/
theorem timingNash_unique_and_payoff :
    ∀ (dates : ℕ)
      (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction dates)),
      (quittingFiniteDeadlineTimingGame reward dates).mixedExtension.IsNash
          mixed →
        (fun who ↦ timingMixedPayoff dates mixed who) = valueAfter dates ∧
        ∀ other : Player →
            PMF (QuittingFiniteDeadlineTimingAction dates),
          (quittingFiniteDeadlineTimingGame reward dates).mixedExtension.IsNash
              other →
            other = mixed := by
  intro dates
  induction dates with
  | zero =>
      intro mixed _hnash
      constructor
      · funext who
        rw [timingMixedPayoff_zero]
        fin_cases who <;> simp [valueAfter]
      · intro other _hother
        funext who
        calc
          other who = (PMF.pure none :
              PMF (QuittingFiniteDeadlineTimingAction 0)) :=
            Math.ProbabilityMassFunction.eq_pure_of_subsingleton _ none
          _ = mixed who :=
            (Math.ProbabilityMassFunction.eq_pure_of_subsingleton
              (mixed who) none).symm
  | succ dates ih =>
      intro mixed hnash
      let tails : Player →
          PMF (QuittingFiniteDeadlineTimingAction dates) := fun who ↦
        timingLawTail (mixed who)
      have hcontinue := all_currentContinue_ne_zero dates mixed hnash
      have htailNash :
          (quittingFiniteDeadlineTimingGame reward dates).mixedExtension.IsNash
            tails := by
        exact timingLawTail_isNash_of_isNash dates mixed hnash hcontinue
      have htailResult := ih tails htailNash
      have htailPayoff :
          (fun who ↦ timingMixedPayoff dates tails who) = valueAfter dates :=
        htailResult.1
      have hroot := currentRoot_eq_rootBefore_of_tailPayoff
        dates mixed hnash htailPayoff
      constructor
      · funext who
        rw [timingMixedPayoff_succ]
        change quittingRootSuccessorPayoff reward
          (fun player ↦ timingMixedPayoff dates tails player)
          (fun player ↦ pushforward (mixed player) timingActionCurrent) who =
            valueAfter (dates + 1) who
        rw [htailPayoff, hroot]
        exact (congrFun (valueAfter_succ_eq_successor dates) who).symm
      · intro other hother
        let otherTails : Player →
            PMF (QuittingFiniteDeadlineTimingAction dates) := fun who ↦
          timingLawTail (other who)
        have hotherContinue := all_currentContinue_ne_zero dates other hother
        have hotherTailNash :
            (quittingFiniteDeadlineTimingGame reward dates).mixedExtension.IsNash
              otherTails := by
          exact timingLawTail_isNash_of_isNash
            dates other hother hotherContinue
        have hotherTailResult := ih otherTails hotherTailNash
        have hotherTailPayoff :
            (fun who ↦ timingMixedPayoff dates otherTails who) =
              valueAfter dates := hotherTailResult.1
        have hotherRoot := currentRoot_eq_rootBefore_of_tailPayoff
          dates other hother hotherTailPayoff
        have htails : otherTails = tails :=
          htailResult.2 otherTails hotherTailNash
        have hroots :
            (fun who ↦ pushforward (other who) timingActionCurrent) =
              (fun who ↦ pushforward (mixed who) timingActionCurrent) :=
          hotherRoot.trans hroot.symm
        funext who
        apply timingLaw_eq_of_current_tail_eq
        · exact congrFun hroots who
        · exact congrFun htails who
        · exact hotherContinue who
        · exact hcontinue who

/-- The concrete hard Fin4 timing game has exactly one mixed Nash law at
every finite deadline, including deadline zero. -/
theorem existsUnique_finiteDeadlineTimingNash (deadline : ℕ) :
    ∃! mixed : Player →
        PMF (QuittingFiniteDeadlineTimingAction deadline),
      (quittingFiniteDeadlineTimingGame reward
        deadline).mixedExtension.IsNash mixed := by
  letI (who : Player) : Finite
      ((quittingFiniteDeadlineTimingGame reward deadline).Strategy who) := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  letI (who : Player) : Nonempty
      ((quittingFiniteDeadlineTimingGame reward deadline).Strategy who) := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  letI : Finite
      (quittingFiniteDeadlineTimingGame reward deadline).Outcome := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  obtain ⟨mixed, hnash⟩ :=
    (quittingFiniteDeadlineTimingGame reward deadline).mixed_nash_exists
  refine ⟨mixed, hnash, ?_⟩
  intro other hother
  exact (timingNash_unique_and_payoff deadline mixed hnash).2 other hother

/-- The unique timing Nash law has the displayed backward-induction payoff. -/
theorem finiteDeadlineTimingNash_payoff_eq_valueAfter
    (deadline : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      deadline).mixedExtension.IsNash mixed) :
    (fun who ↦ timingMixedPayoff deadline mixed who) =
      valueAfter deadline :=
  (timingNash_unique_and_payoff deadline mixed hnash).1

/-! ## Reverse realization of the unique law -/

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

/-- The first behavioral root of a finite timing profile is exactly the
pushforward of each timing law to its current Boolean action. -/
theorem finiteDeadlineTimingProfile_root_eq_current
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1))) :
    quittingProfileRoot reward
        (quittingFiniteDeadlineTimingProfile reward (dates + 1) mixed) =
      fun who ↦ pushforward (mixed who) timingActionCurrent := by
  funext who
  apply pmfBool_eq_of_true_toReal_eq
  rw [finiteDeadlineTimingProfile_root_true,
    timingActionCurrent_pushforward_true]

/-- Under genuine current continuation, deleting the first behavioral date
of a finite timing profile is exactly the profile of the conditional shifted
timing laws. -/
theorem finiteDeadlineTimingProfile_spine_one_eq_tail
    (dates : ℕ)
    (mixed : Player →
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

/-- The explicit hard-deadline behavior chain is its displayed current root
followed by the shorter hard-deadline chain. -/
theorem hardDeadlineProfile_succ (dates : ℕ) :
    hardDeadlineProfile (dates + 1) =
      quittingRootThenContinuationProfile reward (rootBefore dates)
        (hardDeadlineProfile dates) := by
  funext who time history
  cases time with
  | zero =>
      simp [hardDeadlineProfile, quittingInfinitePathProfile,
        quittingRootSequenceProfile, hardDeadlineRoots]
  | succ time =>
      simp only [hardDeadlineProfile, quittingInfinitePathProfile,
        quittingRootSequenceProfile,
        quittingRootThenContinuationProfile]
      simp only [Nat.zero_add]
      change hardDeadlineRoots (dates + 1) (time + 1) who =
        hardDeadlineRoots dates time who
      by_cases htime : time < dates
      · simp [hardDeadlineRoots, htime]
      · have hle : dates ≤ time := Nat.le_of_not_gt htime
        simp [hardDeadlineRoots, htime]

/-- Every Nash law of the finite hard table realizes the explicit
hard-deadline behavioral profile, not merely the same normal-form payoff. -/
theorem finiteDeadlineTimingNash_profile_eq_hardDeadlineProfile :
    ∀ (deadline : ℕ)
      (mixed : Player →
        PMF (QuittingFiniteDeadlineTimingAction deadline)),
      (quittingFiniteDeadlineTimingGame reward
        deadline).mixedExtension.IsNash mixed →
        quittingFiniteDeadlineTimingProfile reward deadline mixed =
          hardDeadlineProfile deadline := by
  intro deadline
  induction deadline with
  | zero =>
      intro mixed _hnash
      funext who time history
      have hlaw : mixed who =
          (PMF.pure none :
            PMF (QuittingFiniteDeadlineTimingAction 0)) :=
        Math.ProbabilityMassFunction.eq_pure_of_subsingleton _ none
      unfold quittingFiniteDeadlineTimingProfile
        quittingCompactStoppingLawProfile
        quittingStoppingLawBehaviorStrategy
      dsimp only
      rw [hlaw]
      simp only [quittingFiniteDeadlineTimingLaw,
        Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
      rw [PMF.pure_map]
      simp only [hardDeadlineProfile, quittingInfinitePathProfile,
        quittingRootSequenceProfile, hardDeadlineRoots]
      change (Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard
        (PMF.pure (none : Option ℕ))).toBoolean time = PMF.pure false
      apply Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
      simp [
        Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard,
        Math.Probability.DiscreteHazard.StoppingLaw.finiteMass,
        Math.Probability.DiscreteHazard.StoppingLaw.survival,
        Math.Probability.DiscreteHazard.ScalarHazard.toBoolean]
  | succ dates ih =>
      intro mixed hnash
      let tails : Player →
          PMF (QuittingFiniteDeadlineTimingAction dates) := fun who ↦
        timingLawTail (mixed who)
      have hcontinue := all_currentContinue_ne_zero dates mixed hnash
      have htailNash :
          (quittingFiniteDeadlineTimingGame reward
            dates).mixedExtension.IsNash tails :=
        timingLawTail_isNash_of_isNash dates mixed hnash hcontinue
      have htailPayoff :=
        finiteDeadlineTimingNash_payoff_eq_valueAfter
          dates tails htailNash
      have hroot := currentRoot_eq_rootBefore_of_tailPayoff
        dates mixed hnash htailPayoff
      calc
        quittingFiniteDeadlineTimingProfile reward (dates + 1) mixed =
            quittingRootThenContinuationProfile reward
              (quittingProfileRoot reward
                (quittingFiniteDeadlineTimingProfile reward
                  (dates + 1) mixed))
              (quittingAllContinueProfileSpine reward
                (quittingFiniteDeadlineTimingProfile reward
                  (dates + 1) mixed) 1) :=
          finiteDeadlineTimingProfile_eq_rootThen_spine (dates + 1) mixed
        _ = quittingRootThenContinuationProfile reward (rootBefore dates)
              (quittingFiniteDeadlineTimingProfile reward dates tails) := by
          rw [finiteDeadlineTimingProfile_root_eq_current dates mixed,
            hroot,
            finiteDeadlineTimingProfile_spine_one_eq_tail
              dates mixed hcontinue]
        _ = quittingRootThenContinuationProfile reward (rootBefore dates)
              (hardDeadlineProfile dates) := by
          rw [ih tails htailNash]
        _ = hardDeadlineProfile (dates + 1) :=
          (hardDeadlineProfile_succ dates).symm

/-- The unique Nash law, strengthened with its exact behavioral
realization. -/
theorem existsUnique_finiteDeadlineTimingNash_realizing_hardDeadlineProfile
    (deadline : ℕ) :
    ∃! mixed : Player →
        PMF (QuittingFiniteDeadlineTimingAction deadline),
      (quittingFiniteDeadlineTimingGame reward
          deadline).mixedExtension.IsNash mixed ∧
        quittingFiniteDeadlineTimingProfile reward deadline mixed =
          hardDeadlineProfile deadline := by
  obtain ⟨mixed, hnash, hunique⟩ :=
    existsUnique_finiteDeadlineTimingNash deadline
  refine ⟨mixed, ⟨hnash,
    finiteDeadlineTimingNash_profile_eq_hardDeadlineProfile
      deadline mixed hnash⟩, ?_⟩
  intro other hother
  exact hunique other hother.1

/-- A canonical representative of the unique hard-deadline timing Nash law. -/
noncomputable def hardDeadlineTimingNashLaw (deadline : ℕ) :
    Player → PMF (QuittingFiniteDeadlineTimingAction deadline) :=
  Classical.choose (existsUnique_finiteDeadlineTimingNash deadline)

theorem hardDeadlineTimingNashLaw_isNash (deadline : ℕ) :
    (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.IsNash
      (hardDeadlineTimingNashLaw deadline) :=
  Classical.choose_spec
    (existsUnique_finiteDeadlineTimingNash deadline) |>.1

theorem hardDeadlineTimingNashLaw_profile_eq (deadline : ℕ) :
    quittingFiniteDeadlineTimingProfile reward deadline
        (hardDeadlineTimingNashLaw deadline) =
      hardDeadlineProfile deadline :=
  finiteDeadlineTimingNash_profile_eq_hardDeadlineProfile deadline
    (hardDeadlineTimingNashLaw deadline)
    (hardDeadlineTimingNashLaw_isNash deadline)

/-- Every positive-deadline timing Nash law has exactly the packet's
unrestricted behavioral debt at player `0`. -/
theorem finiteDeadlineTimingNash_debt_zero_eq_hardDeadlineDebt
    (deadline : ℕ) (hdeadline : 0 < deadline)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      deadline).mixedExtension.IsNash mixed) :
    quittingTerminalDeviationDebt reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) 0 =
      hardDeadlineDebt deadline := by
  rw [finiteDeadlineTimingNash_profile_eq_hardDeadlineProfile
      deadline mixed hnash,
    hardDeadlineProfile_debt_zero_eq,
    oneNeverMass_div_two_eq_hardDeadlineDebt deadline hdeadline]

/-- Every positive-deadline timing Nash law has exact unrestricted semantic
exploitability `D_N`, independently of how an existence theorem selected it. -/
theorem finiteDeadlineTimingNash_exploitability_eq_hardDeadlineDebt
    (deadline : ℕ) (hdeadline : 0 < deadline)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      deadline).mixedExtension.IsNash mixed) :
    quittingTerminalSemanticExploitability
        (quittingTerminalSemanticPair reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed)) =
      hardDeadlineDebt deadline := by
  rw [finiteDeadlineTimingNash_profile_eq_hardDeadlineProfile
      deadline mixed hnash,
    hardDeadlineProfile_exploitability_eq_hardDeadlineDebt
      deadline hdeadline]

/-- The hard-table timing Nash family has a selection-independent strict
quarter barrier at every positive deadline. -/
theorem quarter_lt_finiteDeadlineTimingNash_exploitability
    (deadline : ℕ) (hdeadline : 0 < deadline)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      deadline).mixedExtension.IsNash mixed) :
    1 / 4 < quittingTerminalSemanticExploitability
      (quittingTerminalSemanticPair reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed)) := by
  rw [finiteDeadlineTimingNash_exploitability_eq_hardDeadlineDebt
    deadline hdeadline mixed hnash]
  exact hardDeadlineDebt_gt_quarter deadline hdeadline

end FinFourHardDeadlineTimingNashBarrier
end GameTheory
