/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.AllContinuePrefixSemantics
import UniformEquilibrium.Quitting.Root.OneDateNeverNashDebt

/-
Exact pure-time deviation values of a padded one-date profile.

A *padded one-date profile* plays `t` all-Continue rows, then one product root
`root`, then Continue forever.  Every deterministic quit plan against it has a
closed-form value.  Quitting strictly before the root is a solo quit worth the
player's singleton reward; quitting exactly at the root is the zero-tail Quit
endpoint of `root`; quitting strictly after the root is the zero-tail Continue
endpoint plus the opponents' all-Continue mass times the solo reward; never
quitting is the Continue endpoint itself.

Because the behavioral best-response envelope is the supremum of the
deterministic quit-plan values, the padded profile's cap is the maximum of
exactly those four numbers, which collapses to a three-term maximum.  Padding
is what makes the bare solo reward one of the arguments: with no padding rows
the early branch is empty, and a sure opponent quitter then erases the late
branch as well, leaving the two root endpoints alone.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Scalar abbreviations -/

/-- The zero-tail Quit endpoint of a product root. -/
def oneDateProductQuitEndpoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingRootQuitPayoff reward (0 : Payoff ι) root who

/-- The zero-tail Continue endpoint of a product root. -/
def oneDateProductContinueEndpoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingRootContinuePayoff reward (0 : Payoff ι) root who

/-- The probability that every opponent of `who` continues at the root. -/
def oneDateProductOppContinue (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingRootOpponentContinueMass root who

theorem oneDateProductQuitEndpoint_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    oneDateProductQuitEndpoint reward root who =
      quittingRootQuitPayoff reward (0 : Payoff ι) root who := rfl

theorem oneDateProductContinueEndpoint_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    oneDateProductContinueEndpoint reward root who =
      quittingRootContinuePayoff reward (0 : Payoff ι) root who := rfl

theorem oneDateProductOppContinue_eq (root : ι → PMF Bool) (who : ι) :
    oneDateProductOppContinue root who = quittingRootOpponentContinueMass root who := rfl

theorem oneDateProductOppContinue_nonneg (root : ι → PMF Bool) (who : ι) :
    0 ≤ oneDateProductOppContinue root who :=
  quittingRootOpponentContinueMass_nonneg root who

theorem oneDateProductOppContinue_le_one (root : ι → PMF Bool) (who : ι) :
    oneDateProductOppContinue root who ≤ 1 :=
  quittingRootOpponentContinueMass_le_one root who

/-! ## Pure-time deviations across one arbitrary root -/

/-- Deviating to a shifted pure quit plan across one arbitrary product root is
the same literal profile as forcing the observer's root marginal to Continue
and deviating to the unshifted plan afterwards. -/
theorem oneDateProductQuittingPureTimeUpdate_rootThenContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (observer : ι) (choice : Option ℕ) :
    Function.update
        (quittingRootThenContinuationProfile reward root continuation)
        observer
        (quittingPureTimeBehaviorStrategy reward observer
          (quittingPureTimeShift choice)) =
      quittingRootThenContinuationProfile reward
        (Function.update root observer (PMF.pure false))
        (Function.update continuation observer
          (quittingPureTimeBehaviorStrategy reward observer choice)) := by
  funext player time hist
  rcases eq_or_ne player observer with rfl | hplayer
  · rw [Function.update_self]
    cases time with
    | zero =>
        show quittingPureTimeHazard (quittingPureTimeShift choice) 0 =
          Function.update root player (PMF.pure false) player
        rw [Function.update_self]
        cases choice with
        | none => rfl
        | some quitTime =>
            show quittingPureTimeHazard (some (quitTime + 1)) 0 =
              PMF.pure false
            simp [quittingPureTimeHazard]
    | succ pastTime =>
        show quittingPureTimeHazard (quittingPureTimeShift choice)
            (pastTime + 1) =
          Function.update continuation player
            (quittingPureTimeBehaviorStrategy reward player choice) player
            pastTime (Fin.tail hist.1, hist.2)
        rw [Function.update_self]
        cases choice with
        | none => rfl
        | some quitTime =>
            show quittingPureTimeHazard (some (quitTime + 1)) (pastTime + 1) =
              quittingPureTimeHazard (some quitTime) pastTime
            simp [quittingPureTimeHazard]
  · rw [Function.update_of_ne hplayer]
    cases time with
    | zero =>
        show root player =
          Function.update root observer (PMF.pure false) player
        rw [Function.update_of_ne hplayer]
    | succ pastTime =>
        show continuation player pastTime (Fin.tail hist.1, hist.2) =
          Function.update continuation observer
            (quittingPureTimeBehaviorStrategy reward observer choice) player
            pastTime (Fin.tail hist.1, hist.2)
        rw [Function.update_of_ne hplayer]

/-- Quitting at date zero across one arbitrary product root is the same literal
profile as forcing the observer's root marginal to sure Quit and never quitting
afterwards. -/
theorem oneDateProductQuittingPureTimeUpdate_rootThenContinuation_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile) (observer : ι) :
    Function.update
        (quittingRootThenContinuationProfile reward root continuation)
        observer (quittingPureTimeBehaviorStrategy reward observer (some 0)) =
      quittingRootThenContinuationProfile reward
        (Function.update root observer (PMF.pure true))
        (Function.update continuation observer
          (quittingPureTimeBehaviorStrategy reward observer none)) := by
  funext player time hist
  rcases eq_or_ne player observer with rfl | hplayer
  · rw [Function.update_self]
    cases time with
    | zero =>
        show quittingPureTimeHazard (some 0) 0 =
          Function.update root player (PMF.pure true) player
        rw [Function.update_self]
        simp [quittingPureTimeHazard]
    | succ pastTime =>
        show quittingPureTimeHazard (some 0) (pastTime + 1) =
          Function.update continuation player
            (quittingPureTimeBehaviorStrategy reward player none) player
            pastTime (Fin.tail hist.1, hist.2)
        rw [Function.update_self]
        simp [quittingPureTimeHazard, quittingPureTimeBehaviorStrategy]
  · rw [Function.update_of_ne hplayer]
    cases time with
    | zero =>
        show root player =
          Function.update root observer (PMF.pure true) player
        rw [Function.update_of_ne hplayer]
    | succ pastTime =>
        show continuation player pastTime (Fin.tail hist.1, hist.2) =
          Function.update continuation observer
            (quittingPureTimeBehaviorStrategy reward observer none) player
            pastTime (Fin.tail hist.1, hist.2)
        rw [Function.update_of_ne hplayer]

/-! ## Perpetual continuation -/

omit [DecidableEq ι] in
/-- Splicing one all-Continue root in front of perpetual continuation returns
perpetual continuation. -/
theorem oneDateProductAllContinuePrefix_alwaysContinueProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingRootThenContinuationProfile reward quittingAllContinueRoot
        (quittingAlwaysContinueProfile reward) =
      quittingAlwaysContinueProfile reward := by
  funext who time hist
  cases time <;> rfl

/-- Never quitting is exactly what perpetual continuation already prescribes. -/
theorem oneDateProductUpdate_alwaysContinueProfile_pureTime_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    Function.update (quittingAlwaysContinueProfile reward) who
        (quittingPureTimeBehaviorStrategy reward who none) =
      quittingAlwaysContinueProfile reward := by
  rw [show quittingPureTimeBehaviorStrategy reward who none =
    quittingAlwaysContinueProfile reward who from rfl]
  exact Function.update_eq_self who _

omit [DecidableEq ι] in
/-- Perpetual continuation prescribes the zero payoff vector. -/
theorem oneDateProductTerminalPayoff_alwaysContinueProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (fun player => quittingTerminalPayoff reward
        (quittingAlwaysContinueProfile reward) player) = (0 : Payoff ι) := by
  funext player
  exact quittingTerminalPayoff_quittingAlwaysContinue reward player

/-- Against perpetual continuation every deterministic quit date is a solo
quit worth the observer's singleton reward. -/
theorem oneDateProductPureTimeDeviationPayoff_alwaysContinueProfile_some
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) (q : ℕ) :
    quittingPureTimeDeviationPayoff reward
        (quittingAlwaysContinueProfile reward) who (some q) =
      reward (quittingSingletonTerminal who) who := by
  induction q with
  | zero =>
      have hzero := quittingPureTimeDeviationPayoff_allContinuePrefix_zero
        reward (quittingAlwaysContinueProfile reward) who
      rwa [oneDateProductAllContinuePrefix_alwaysContinueProfile] at hzero
  | succ q ih =>
      have hshift := quittingPureTimeDeviationPayoff_allContinuePrefix_shift
        reward (quittingAlwaysContinueProfile reward) who (some q)
      rw [oneDateProductAllContinuePrefix_alwaysContinueProfile] at hshift
      have hstep : quittingPureTimeDeviationPayoff reward
          (quittingAlwaysContinueProfile reward) who (some (q + 1)) =
        quittingPureTimeDeviationPayoff reward
          (quittingAlwaysContinueProfile reward) who (some q) := hshift
      rw [hstep]
      exact ih

/-! ## The unpadded one-date profile -/

/-- Quitting at the root date of a one-date-then-Never profile is worth the
zero-tail Quit endpoint. -/
theorem oneDateProductPureTimeDeviationPayoff_oneDateThenNever_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingPureTimeDeviationPayoff reward
        (quittingOneDateThenNeverProfile reward root) who (some 0) =
      oneDateProductQuitEndpoint reward root who := by
  unfold quittingPureTimeDeviationPayoff quittingOneDateThenNeverProfile
  rw [oneDateProductQuittingPureTimeUpdate_rootThenContinuation_zero,
    quittingTerminalPayoff_rootThenContinuation_eq,
    oneDateProductUpdate_alwaysContinueProfile_pureTime_none,
    oneDateProductTerminalPayoff_alwaysContinueProfile]
  rfl

/-- Every shifted deterministic plan against a one-date-then-Never profile
forces the observer's root marginal to Continue and defers the unshifted plan
to perpetual continuation. -/
theorem oneDateProductPureTimeDeviationPayoff_oneDateThenNever_shift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (choice : Option ℕ) :
    quittingPureTimeDeviationPayoff reward
        (quittingOneDateThenNeverProfile reward root) who
        (quittingPureTimeShift choice) =
      quittingRootExpectedPayoff reward
        (fun player => quittingTerminalPayoff reward
          (Function.update (quittingAlwaysContinueProfile reward) who
            (quittingPureTimeBehaviorStrategy reward who choice)) player)
        (Function.update root who (PMF.pure false)) who := by
  unfold quittingPureTimeDeviationPayoff quittingOneDateThenNeverProfile
  rw [oneDateProductQuittingPureTimeUpdate_rootThenContinuation,
    quittingTerminalPayoff_rootThenContinuation_eq]

/-- Never quitting against a one-date-then-Never profile is worth the zero-tail
Continue endpoint. -/
theorem oneDateProductPureTimeDeviationPayoff_oneDateThenNever_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingPureTimeDeviationPayoff reward
        (quittingOneDateThenNeverProfile reward root) who none =
      oneDateProductContinueEndpoint reward root who := by
  have hbase := oneDateProductPureTimeDeviationPayoff_oneDateThenNever_shift
    reward root who none
  rw [oneDateProductUpdate_alwaysContinueProfile_pureTime_none,
    oneDateProductTerminalPayoff_alwaysContinueProfile] at hbase
  exact hbase

/-- Quitting strictly after the root date of a one-date-then-Never profile is
worth the zero-tail Continue endpoint plus the opponents' all-Continue mass
times the observer's singleton reward. -/
theorem oneDateProductPureTimeDeviationPayoff_oneDateThenNever_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (q : ℕ) :
    quittingPureTimeDeviationPayoff reward
        (quittingOneDateThenNeverProfile reward root) who (some (q + 1)) =
      oneDateProductContinueEndpoint reward root who +
        oneDateProductOppContinue root who *
          reward (quittingSingletonTerminal who) who := by
  have hbase := oneDateProductPureTimeDeviationPayoff_oneDateThenNever_shift
    reward root who (some q)
  have hcoord : (fun player => quittingTerminalPayoff reward
        (Function.update (quittingAlwaysContinueProfile reward) who
          (quittingPureTimeBehaviorStrategy reward who (some q))) player) who =
      (fun _ : ι => reward (quittingSingletonTerminal who) who) who :=
    oneDateProductPureTimeDeviationPayoff_alwaysContinueProfile_some reward who q
  rw [quittingRootExpectedPayoff_continuation_congr reward _
    (fun _ : ι => reward (quittingSingletonTerminal who) who) _ who hcoord]
    at hbase
  have htarget : quittingRootContinuePayoff reward
      (fun _ : ι => reward (quittingSingletonTerminal who) who) root who =
    oneDateProductContinueEndpoint reward root who +
      oneDateProductOppContinue root who *
        reward (quittingSingletonTerminal who) who :=
    quittingRootContinuePayoff_const_singleton_eq reward root who
  rw [← htarget]
  exact hbase

/-! ## The padded one-date profile -/

/-- Play `t` all-Continue rows, then the product root `root`, then Continue
forever. -/
def oneDateProductPaddedOneDateProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (t : ℕ) (root : ι → PMF Bool) : (quittingGame reward).BehaviorProfile :=
  quittingAllContinuePrefixIterate reward
    (quittingOneDateThenNeverProfile reward root) t

omit [DecidableEq ι] in
theorem oneDateProductPaddedOneDateProfile_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (t : ℕ) (root : ι → PMF Bool) :
    oneDateProductPaddedOneDateProfile reward t root =
      quittingAllContinuePrefixIterate reward
        (quittingOneDateThenNeverProfile reward root) t := rfl

/-- Inside any all-Continue prefix stack, every quit date strictly below the
stack height is a solo quit. -/
theorem oneDateProductPureTimeDeviationPayoff_allContinuePrefixIterate_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    ∀ (q H : ℕ), q < H →
      quittingPureTimeDeviationPayoff reward
          (quittingAllContinuePrefixIterate reward profile H) who (some q) =
        reward (quittingSingletonTerminal who) who := by
  intro q
  induction q with
  | zero =>
      intro H hH
      obtain ⟨stack, rfl⟩ : ∃ stack, H = stack + 1 := ⟨H - 1, by omega⟩
      exact quittingPureTimeDeviationPayoff_allContinuePrefix_zero reward
        (quittingAllContinuePrefixIterate reward profile stack) who
  | succ q ih =>
      intro H hH
      obtain ⟨stack, rfl⟩ : ∃ stack, H = stack + 1 := ⟨H - 1, by omega⟩
      have hstep : quittingPureTimeDeviationPayoff reward
          (quittingAllContinuePrefixIterate reward profile (stack + 1)) who
            (some (q + 1)) =
        quittingPureTimeDeviationPayoff reward
          (quittingAllContinuePrefixIterate reward profile stack) who
            (some q) :=
        quittingPureTimeDeviationPayoff_allContinuePrefix_shift reward
          (quittingAllContinuePrefixIterate reward profile stack) who (some q)
      rw [hstep]
      exact ih stack (by omega)

/-- **Early dates.**  Quitting strictly before the root date of a padded
one-date profile is a solo quit. -/
theorem oneDateProductPureTimeDeviationPayoff_paddedOneDateProfile_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (t : ℕ) (root : ι → PMF Bool) (who : ι) {q : ℕ} (hq : q < t) :
    quittingPureTimeDeviationPayoff reward
        (oneDateProductPaddedOneDateProfile reward t root) who (some q) =
      reward (quittingSingletonTerminal who) who := by
  rw [oneDateProductPaddedOneDateProfile_eq]
  exact oneDateProductPureTimeDeviationPayoff_allContinuePrefixIterate_lt reward
    (quittingOneDateThenNeverProfile reward root) who q t hq

/-- **The root date.**  Quitting exactly at the root date of a padded one-date
profile is worth the zero-tail Quit endpoint. -/
theorem oneDateProductPureTimeDeviationPayoff_paddedOneDateProfile_root
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (t : ℕ) (root : ι → PMF Bool) (who : ι) :
    quittingPureTimeDeviationPayoff reward
        (oneDateProductPaddedOneDateProfile reward t root) who (some t) =
      oneDateProductQuitEndpoint reward root who := by
  have hshift := quittingPureTimeDeviationPayoff_allContinuePrefixIterate_some
    reward (quittingOneDateThenNeverProfile reward root) who t 0
  rw [Nat.zero_add] at hshift
  rw [oneDateProductPaddedOneDateProfile_eq, hshift]
  exact oneDateProductPureTimeDeviationPayoff_oneDateThenNever_zero reward root who

/-- **Late dates.**  Quitting strictly after the root date of a padded one-date
profile is worth the zero-tail Continue endpoint plus the opponents'
all-Continue mass times the observer's singleton reward. -/
theorem oneDateProductPureTimeDeviationPayoff_paddedOneDateProfile_late
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (t : ℕ) (root : ι → PMF Bool) (who : ι) (q : ℕ) :
    quittingPureTimeDeviationPayoff reward
        (oneDateProductPaddedOneDateProfile reward t root) who (some (t + 1 + q)) =
      oneDateProductContinueEndpoint reward root who +
        oneDateProductOppContinue root who *
          reward (quittingSingletonTerminal who) who := by
  rw [oneDateProductPaddedOneDateProfile_eq,
    show t + 1 + q = (q + 1) + t by omega,
    quittingPureTimeDeviationPayoff_allContinuePrefixIterate_some]
  exact oneDateProductPureTimeDeviationPayoff_oneDateThenNever_succ reward root who q

/-- **Never.**  Never quitting against a padded one-date profile is worth the
zero-tail Continue endpoint. -/
theorem oneDateProductPureTimeDeviationPayoff_paddedOneDateProfile_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (t : ℕ) (root : ι → PMF Bool) (who : ι) :
    quittingPureTimeDeviationPayoff reward
        (oneDateProductPaddedOneDateProfile reward t root) who none =
      oneDateProductContinueEndpoint reward root who := by
  rw [oneDateProductPaddedOneDateProfile_eq,
    quittingPureTimeDeviationPayoff_allContinuePrefixIterate_none]
  exact oneDateProductPureTimeDeviationPayoff_oneDateThenNever_none reward root who

/-! ## The cap of a padded one-date profile -/

/-- **Cap formula.**  With at least one padding row, the behavioral
best-response cap of a padded one-date profile is the maximum of the solo
reward, the zero-tail Quit endpoint, and the zero-tail Continue endpoint raised
by the opponents' all-Continue mass times the positive part of the solo
reward. -/
theorem oneDateProductQuittingContinuationBestResponseValue_paddedOneDateProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {t : ℕ} (ht : 0 < t) (root : ι → PMF Bool) (who : ι) :
    quittingContinuationBestResponseValue reward
        (oneDateProductPaddedOneDateProfile reward t root) who =
      max (reward (quittingSingletonTerminal who) who)
        (max (oneDateProductQuitEndpoint reward root who)
          (oneDateProductContinueEndpoint reward root who +
            oneDateProductOppContinue root who *
              max 0 (reward (quittingSingletonTerminal who) who))) := by
  have hmass : 0 ≤ oneDateProductOppContinue root who := oneDateProductOppContinue_nonneg root who
  have hpart : 0 ≤ oneDateProductOppContinue root who *
      max 0 (reward (quittingSingletonTerminal who) who) :=
    mul_nonneg hmass (le_max_left _ _)
  have hsolo : oneDateProductOppContinue root who *
        reward (quittingSingletonTerminal who) who ≤
      oneDateProductOppContinue root who *
        max 0 (reward (quittingSingletonTerminal who) who) :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hmass
  have hbdd := bddAbove_range_quittingPureTimeDeviationPayoff reward
    (oneDateProductPaddedOneDateProfile reward t root) who
  rw [quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
  apply le_antisymm
  · refine csSup_le (Set.range_nonempty _) ?_
    rintro value ⟨choice, rfl⟩
    cases choice with
    | none =>
        rw [oneDateProductPureTimeDeviationPayoff_paddedOneDateProfile_none]
        refine le_trans ?_ (le_max_right _ _)
        refine le_trans ?_ (le_max_right _ _)
        linarith
    | some q =>
        rcases lt_trichotomy q t with hq | hq | hq
        · rw [oneDateProductPureTimeDeviationPayoff_paddedOneDateProfile_lt reward t
            root who hq]
          exact le_max_left _ _
        · subst hq
          rw [oneDateProductPureTimeDeviationPayoff_paddedOneDateProfile_root]
          exact le_trans (le_max_left _ _) (le_max_right _ _)
        · obtain ⟨late, rfl⟩ : ∃ late, q = t + 1 + late := ⟨q - t - 1, by omega⟩
          rw [oneDateProductPureTimeDeviationPayoff_paddedOneDateProfile_late]
          refine le_trans ?_ (le_max_right _ _)
          refine le_trans ?_ (le_max_right _ _)
          linarith
  · refine max_le ?_ (max_le ?_ ?_)
    · rw [← oneDateProductPureTimeDeviationPayoff_paddedOneDateProfile_lt reward t root
        who ht]
      exact le_csSup hbdd ⟨some 0, rfl⟩
    · rw [← oneDateProductPureTimeDeviationPayoff_paddedOneDateProfile_root reward t
        root who]
      exact le_csSup hbdd ⟨some t, rfl⟩
    · rcases le_total 0 (reward (quittingSingletonTerminal who) who) with
        hpos | hnonpos
      · rw [max_eq_right hpos, ←
          oneDateProductPureTimeDeviationPayoff_paddedOneDateProfile_late reward t root
            who 0]
        exact le_csSup hbdd ⟨some (t + 1 + 0), rfl⟩
      · rw [max_eq_left hnonpos, mul_zero, add_zero, ←
          oneDateProductPureTimeDeviationPayoff_paddedOneDateProfile_none reward t root
            who]
        exact le_csSup hbdd ⟨none, rfl⟩

/-- **Sandwich.**  The padded one-date cap sits between the plain maximum of
the solo reward and the two root endpoints and that maximum raised by the
opponents' all-Continue mass times a uniform reward bound. -/
theorem oneDateProductQuittingContinuationBestResponseValue_paddedOneDateProfile_sandwich
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {t : ℕ} (ht : 0 < t) (root : ι → PMF Bool) (who : ι) {bound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    max (reward (quittingSingletonTerminal who) who)
          (max (oneDateProductQuitEndpoint reward root who)
            (oneDateProductContinueEndpoint reward root who)) ≤
        quittingContinuationBestResponseValue reward
          (oneDateProductPaddedOneDateProfile reward t root) who ∧
      quittingContinuationBestResponseValue reward
          (oneDateProductPaddedOneDateProfile reward t root) who ≤
        max (reward (quittingSingletonTerminal who) who)
            (max (oneDateProductQuitEndpoint reward root who)
              (oneDateProductContinueEndpoint reward root who)) +
          oneDateProductOppContinue root who * bound := by
  have hcap := oneDateProductQuittingContinuationBestResponseValue_paddedOneDateProfile
    reward ht root who
  have hmass : 0 ≤ oneDateProductOppContinue root who := oneDateProductOppContinue_nonneg root who
  have hbound : 0 ≤ bound :=
    le_trans (abs_nonneg _) (hreward (quittingSingletonTerminal who) who)
  have hsoloBound : reward (quittingSingletonTerminal who) who ≤ bound :=
    le_of_abs_le (hreward (quittingSingletonTerminal who) who)
  have hpartBound : max 0 (reward (quittingSingletonTerminal who) who) ≤
      bound := max_le hbound hsoloBound
  have hpart : 0 ≤ oneDateProductOppContinue root who *
      max 0 (reward (quittingSingletonTerminal who) who) :=
    mul_nonneg hmass (le_max_left _ _)
  have hpartLe : oneDateProductOppContinue root who *
        max 0 (reward (quittingSingletonTerminal who) who) ≤
      oneDateProductOppContinue root who * bound :=
    mul_le_mul_of_nonneg_left hpartBound hmass
  have hprodNonneg : 0 ≤ oneDateProductOppContinue root who * bound :=
    mul_nonneg hmass hbound
  have hsoloLe : reward (quittingSingletonTerminal who) who ≤
      max (reward (quittingSingletonTerminal who) who)
        (max (oneDateProductQuitEndpoint reward root who)
          (oneDateProductContinueEndpoint reward root who)) := le_max_left _ _
  have hquitLe : oneDateProductQuitEndpoint reward root who ≤
      max (reward (quittingSingletonTerminal who) who)
        (max (oneDateProductQuitEndpoint reward root who)
          (oneDateProductContinueEndpoint reward root who)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hcontLe : oneDateProductContinueEndpoint reward root who ≤
      max (reward (quittingSingletonTerminal who) who)
        (max (oneDateProductQuitEndpoint reward root who)
          (oneDateProductContinueEndpoint reward root who)) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  constructor
  · rw [hcap]
    exact max_le_max le_rfl (max_le_max le_rfl (by linarith))
  · rw [hcap]
    refine max_le ?_ (max_le ?_ ?_)
    · linarith
    · linarith
    · linarith

/-! ## The unpadded profile against a sure opponent quitter -/

/-- A sure opponent quitter kills the opponents' all-Continue mass. -/
theorem oneDateProductOppContinue_eq_zero_of_sureQuitter
    (root : ι → PMF Bool) (who : ι) {quitter : ι} (hne : quitter ≠ who)
    (hsure : (root quitter true).toReal = 1) :
    oneDateProductOppContinue root who = 0 := by
  have hprod : oneDateProductOppContinue root who =
      ∏ player, ((Function.update root who (PMF.pure false)) player
        false).toReal := by
    rw [oneDateProductOppContinue_eq]
    unfold quittingRootOpponentContinueMass
    exact quittingStationaryContinueMass_eq_prod_continueProbability _
  rw [hprod]
  refine Finset.prod_eq_zero (Finset.mem_univ quitter) ?_
  rw [Function.update_of_ne hne]
  have hsum := quittingRoot_continueProbability_add_quitProbability root quitter
  linarith

/-- **Unpadded cap against a sure opponent quitter.**  With no padding rows and
some opponent quitting surely at the root, the behavioral best-response cap of
the one-date-then-Never profile is the maximum of the two zero-tail root
endpoints; the solo reward is not an argument. -/
theorem oneDateProductQuittingContinuationBestResponseValue_oneDateThenNever_sureQuitter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) {quitter : ι} (hne : quitter ≠ who)
    (hsure : (root quitter true).toReal = 1) :
    quittingContinuationBestResponseValue reward
        (quittingOneDateThenNeverProfile reward root) who =
      max (oneDateProductQuitEndpoint reward root who)
        (oneDateProductContinueEndpoint reward root who) := by
  have hzero : oneDateProductOppContinue root who = 0 :=
    oneDateProductOppContinue_eq_zero_of_sureQuitter root who hne hsure
  have hbdd := bddAbove_range_quittingPureTimeDeviationPayoff reward
    (quittingOneDateThenNeverProfile reward root) who
  rw [quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
  apply le_antisymm
  · refine csSup_le (Set.range_nonempty _) ?_
    rintro value ⟨choice, rfl⟩
    cases choice with
    | none =>
        rw [oneDateProductPureTimeDeviationPayoff_oneDateThenNever_none]
        exact le_max_right _ _
    | some q =>
        cases q with
        | zero =>
            rw [oneDateProductPureTimeDeviationPayoff_oneDateThenNever_zero]
            exact le_max_left _ _
        | succ late =>
            rw [oneDateProductPureTimeDeviationPayoff_oneDateThenNever_succ, hzero,
              zero_mul, add_zero]
            exact le_max_right _ _
  · refine max_le ?_ ?_
    · rw [← oneDateProductPureTimeDeviationPayoff_oneDateThenNever_zero reward root who]
      exact le_csSup hbdd ⟨some 0, rfl⟩
    · rw [← oneDateProductPureTimeDeviationPayoff_oneDateThenNever_none reward root who]
      exact le_csSup hbdd ⟨none, rfl⟩

end GameTheory
