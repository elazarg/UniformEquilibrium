/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Root.TerminalSemanticMoment
import UniformEquilibrium.Quitting.Root.TerminalSemanticPair
import UniformEquilibrium.Quitting.Stationary.LiveMass
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeRectangle
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn

/-
All-Continue prefix time-escape regression for finite quitting games.

Splicing one all-Continue root in front of a behavior profile moves every
deterministic quit plan one date later, yet changes neither the terminal
semantic pair (prescribed payoff and best-response envelope) nor the terminal
outcome law, provided the envelope already dominates every singleton quitting
reward.  Iterating the prefix therefore pushes any fixed pure quit date
arbitrarily far into the future at constant semantics and constant law.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## One all-Continue prefix on a semantic pair -/

/-- An all-Continue prefix fixes every semantic pair whose envelope already
dominates the singleton quitting rewards. -/
theorem quittingTerminalSemanticPrefix_allContinueRoot_eq_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who ≤ pair.2 who) :
    quittingTerminalSemanticPrefix reward quittingAllContinueRoot pair = pair :=
  quittingTerminalSemanticPrefix_allContinue_eq_of_singleton_le_cap reward pair hsolo

/-- Literal all-Continue splicing leaves the whole terminal semantic pair
unchanged under the same envelope domination hypothesis. -/
theorem quittingTerminalSemanticPair_allContinuePrefix_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who ≤
      quittingContinuationBestResponseValue reward profile who) :
    quittingTerminalSemanticPair reward
        (quittingRootThenContinuationProfile reward quittingAllContinueRoot profile) =
      quittingTerminalSemanticPair reward profile := by
  rw [quittingTerminalSemanticPair_rootThenContinuation]
  exact quittingTerminalSemanticPrefix_allContinueRoot_eq_self reward _ hsolo

/-! ## The iterated all-Continue prefix -/

/-- Splice `H` all-Continue roots in front of a behavior profile. -/
def quittingAllContinuePrefixIterate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    ℕ → (quittingGame reward).BehaviorProfile
  | 0 => profile
  | H + 1 =>
      quittingRootThenContinuationProfile reward quittingAllContinueRoot
        (quittingAllContinuePrefixIterate reward profile H)

/-- Every all-Continue prefix stage keeps the literal terminal semantic
pair. -/
theorem quittingTerminalSemanticPair_allContinuePrefixIterate_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who ≤
      quittingContinuationBestResponseValue reward profile who) (H : ℕ) :
    quittingTerminalSemanticPair reward
        (quittingAllContinuePrefixIterate reward profile H) =
      quittingTerminalSemanticPair reward profile := by
  induction H with
  | zero => rfl
  | succ H ih =>
      have hcap : ∀ who, reward (quittingSingletonTerminal who) who ≤
          quittingContinuationBestResponseValue reward
            (quittingAllContinuePrefixIterate reward profile H) who := by
        intro who
        have hcoordinate : quittingContinuationBestResponseValue reward
            (quittingAllContinuePrefixIterate reward profile H) who =
              quittingContinuationBestResponseValue reward profile who :=
          congrArg (fun pair : QuittingTerminalSemanticPair ι => pair.2 who) ih
        rw [hcoordinate]
        exact hsolo who
      show quittingTerminalSemanticPair reward
        (quittingRootThenContinuationProfile reward quittingAllContinueRoot
          (quittingAllContinuePrefixIterate reward profile H)) = _
      rw [quittingTerminalSemanticPair_allContinuePrefix_eq reward _ hcap]
      exact ih

/-! ## Law invariance of an all-Continue prefix -/

/-- The all-Continue root absorbs no nonempty coalition. -/
theorem quittingRootCoalitionMass_allContinueRoot_eq_zero
    (coalition : Finset ι) (hcoalition : coalition.Nonempty) :
    quittingRootCoalitionMass (quittingAllContinueRoot : ι → PMF Bool) coalition = 0 := by
  obtain ⟨player, hplayer⟩ := hcoalition
  have hrate : quittingRootQuitRates (quittingAllContinueRoot : ι → PMF Bool) player = 0 := by
    simp [quittingRootQuitRates, quittingAllContinueRoot]
  unfold quittingRootCoalitionMass coalitionMass
  rw [Finset.prod_eq_zero hplayer hrate, zero_mul]

/-- One all-Continue prefix transports the complete terminal outcome law
identically: it inserts no fresh absorption and loses no live mass.  No
envelope hypothesis is used. -/
theorem quittingTerminalOutcomeMass_allContinueRoot_prefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : (quittingGame reward).BehaviorProfile)
    (outcome : QuittingTerminalOutcome ι) :
    quittingTerminalOutcomeMass reward
        (quittingRootThenContinuationProfile reward quittingAllContinueRoot continuation)
        outcome = quittingTerminalOutcomeMass reward continuation outcome := by
  cases outcome with
  | none =>
      simp [quittingTerminalOutcomeMass_rootThenContinuation,
        quittingStationaryContinueMass_allContinueRoot]
  | some terminal =>
      simp [quittingTerminalOutcomeMass_rootThenContinuation,
        quittingStationaryContinueMass_allContinueRoot,
        quittingRootCoalitionMass_allContinueRoot_eq_zero terminal.val terminal.2]

/-- The iterated all-Continue prefix keeps the complete terminal outcome law,
unconditionally. -/
theorem quittingTerminalOutcomeMass_allContinuePrefix_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (H : ℕ) :
    quittingTerminalOutcomeMass reward
        (quittingAllContinuePrefixIterate reward profile H) =
      quittingTerminalOutcomeMass reward profile := by
  induction H with
  | zero => rfl
  | succ H ih =>
      funext outcome
      show quittingTerminalOutcomeMass reward
        (quittingRootThenContinuationProfile reward quittingAllContinueRoot
          (quittingAllContinuePrefixIterate reward profile H)) outcome = _
      rw [quittingTerminalOutcomeMass_allContinueRoot_prefix]
      exact congrFun ih outcome

/-! ## Pure-time deviations shift by one date -/

/-- Shift a deterministic quit plan one date later. -/
def quittingPureTimeShift : Option ℕ → Option ℕ
  | none => none
  | some quitTime => some (quitTime + 1)

/-- Deviating to a shifted pure quit plan inside a spliced profile is the
same literal profile as splicing the all-Continue root in front of the
unshifted deviation. -/
theorem quittingPureTimeUpdate_allContinuePrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (observer : ι) (choice : Option ℕ) :
    Function.update
        (quittingRootThenContinuationProfile reward quittingAllContinueRoot profile)
        observer
        (quittingPureTimeBehaviorStrategy reward observer
          (quittingPureTimeShift choice)) =
      quittingRootThenContinuationProfile reward quittingAllContinueRoot
        (Function.update profile observer
          (quittingPureTimeBehaviorStrategy reward observer choice)) := by
  funext player time hist
  rcases eq_or_ne player observer with rfl | hplayer
  · rw [Function.update_self]
    cases time with
    | zero =>
        cases choice with
        | none => rfl
        | some quitTime =>
            show quittingPureTimeHazard (some (quitTime + 1)) 0 =
              quittingAllContinueRoot player
            simp [quittingPureTimeHazard, quittingAllContinueRoot]
    | succ pastTime =>
        show quittingPureTimeHazard (quittingPureTimeShift choice) (pastTime + 1) =
          Function.update profile player
            (quittingPureTimeBehaviorStrategy reward player choice) player pastTime
            (Fin.tail hist.1, hist.2)
        rw [Function.update_self]
        cases choice with
        | none => rfl
        | some quitTime =>
            show quittingPureTimeHazard (some (quitTime + 1)) (pastTime + 1) =
              quittingPureTimeHazard (some quitTime) pastTime
            simp [quittingPureTimeHazard]
  · rw [Function.update_of_ne hplayer]
    cases time with
    | zero => rfl
    | succ pastTime =>
        show profile player pastTime (Fin.tail hist.1, hist.2) =
          Function.update profile observer
            (quittingPureTimeBehaviorStrategy reward observer choice) player pastTime
            (Fin.tail hist.1, hist.2)
        rw [Function.update_of_ne hplayer]

/-- One all-Continue prefix shifts every pure-time deviation payoff by exactly
one date, and fixes the never-quit plan. -/
theorem quittingPureTimeDeviationPayoff_allContinuePrefix_shift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (observer : ι) (choice : Option ℕ) :
    quittingPureTimeDeviationPayoff reward
        (quittingRootThenContinuationProfile reward quittingAllContinueRoot profile)
        observer (quittingPureTimeShift choice) =
      quittingPureTimeDeviationPayoff reward profile observer choice := by
  unfold quittingPureTimeDeviationPayoff
  rw [quittingPureTimeUpdate_allContinuePrefix,
    quittingTerminalPayoff_rootThenContinuation_eq]
  exact congrFun (quittingRootSuccessorPayoff_allContinueRoot_eq reward _) observer

/-- Quitting at date zero inside a spliced profile is literally the
all-Continue root with the observer's marginal replaced by sure Quit, followed
by the never-quit deviation. -/
theorem quittingPureTimeUpdate_allContinuePrefix_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι) :
    Function.update
        (quittingRootThenContinuationProfile reward quittingAllContinueRoot profile)
        observer (quittingPureTimeBehaviorStrategy reward observer (some 0)) =
      quittingRootThenContinuationProfile reward
        (Function.update quittingAllContinueRoot observer (PMF.pure true))
        (Function.update profile observer
          (quittingPureTimeBehaviorStrategy reward observer none)) := by
  funext player time hist
  rcases eq_or_ne player observer with rfl | hplayer
  · rw [Function.update_self]
    cases time with
    | zero =>
        show quittingPureTimeHazard (some 0) 0 =
          Function.update quittingAllContinueRoot player (PMF.pure true) player
        rw [Function.update_self]
        simp [quittingPureTimeHazard]
    | succ pastTime =>
        show quittingPureTimeHazard (some 0) (pastTime + 1) =
          Function.update profile player
            (quittingPureTimeBehaviorStrategy reward player none) player pastTime
            (Fin.tail hist.1, hist.2)
        rw [Function.update_self]
        simp [quittingPureTimeHazard, quittingPureTimeBehaviorStrategy]
  · rw [Function.update_of_ne hplayer]
    cases time with
    | zero =>
        show quittingAllContinueRoot player =
          Function.update quittingAllContinueRoot observer (PMF.pure true) player
        rw [Function.update_of_ne hplayer]
    | succ pastTime =>
        show profile player pastTime (Fin.tail hist.1, hist.2) =
          Function.update profile observer
            (quittingPureTimeBehaviorStrategy reward observer none) player pastTime
            (Fin.tail hist.1, hist.2)
        rw [Function.update_of_ne hplayer]

/-- Inside a spliced profile, quitting at date zero is worth exactly the
observer's singleton quitting reward. -/
theorem quittingPureTimeDeviationPayoff_allContinuePrefix_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι) :
    quittingPureTimeDeviationPayoff reward
        (quittingRootThenContinuationProfile reward quittingAllContinueRoot profile)
        observer (some 0) =
      reward (quittingSingletonTerminal observer) observer := by
  unfold quittingPureTimeDeviationPayoff
  rw [quittingPureTimeUpdate_allContinuePrefix_zero,
    quittingTerminalPayoff_rootThenContinuation_eq]
  exact quittingRootQuitPayoff_allContinueRoot reward
    (fun player => quittingTerminalPayoff reward
      (Function.update profile observer
        (quittingPureTimeBehaviorStrategy reward observer none)) player) observer

/-! ## The iterated time escape -/

/-- After `H` all-Continue prefixes, quitting at date `t + H` is worth exactly
what quitting at date `t` was worth before. -/
theorem quittingPureTimeDeviationPayoff_allContinuePrefixIterate_some
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (observer : ι) (H t : ℕ) :
    quittingPureTimeDeviationPayoff reward
        (quittingAllContinuePrefixIterate reward profile H) observer (some (t + H)) =
      quittingPureTimeDeviationPayoff reward profile observer (some t) := by
  induction H with
  | zero => rfl
  | succ H ih =>
      show quittingPureTimeDeviationPayoff reward
        (quittingRootThenContinuationProfile reward quittingAllContinueRoot
          (quittingAllContinuePrefixIterate reward profile H)) observer
        (quittingPureTimeShift (some (t + H))) = _
      rw [quittingPureTimeDeviationPayoff_allContinuePrefix_shift]
      exact ih

/-- The never-quit deviation payoff is unchanged by all-Continue prefixes. -/
theorem quittingPureTimeDeviationPayoff_allContinuePrefixIterate_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι) (H : ℕ) :
    quittingPureTimeDeviationPayoff reward
        (quittingAllContinuePrefixIterate reward profile H) observer none =
      quittingPureTimeDeviationPayoff reward profile observer none := by
  induction H with
  | zero => rfl
  | succ H ih =>
      show quittingPureTimeDeviationPayoff reward
        (quittingRootThenContinuationProfile reward quittingAllContinueRoot
          (quittingAllContinuePrefixIterate reward profile H)) observer
        (quittingPureTimeShift none) = _
      rw [quittingPureTimeDeviationPayoff_allContinuePrefix_shift]
      exact ih

/-- **All-Continue prefix time escape.**  If the best-response envelope of a
behavior profile already dominates every singleton quitting reward, then for
every horizon `H` the `H`-fold all-Continue prefix has the same terminal
semantic pair and the same complete terminal outcome law, while every
deterministic quit plan is pushed exactly `H` dates later. -/
theorem allContinuePrefix_timeEscapeRegression
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who ≤
      quittingContinuationBestResponseValue reward profile who) (H : ℕ) :
    quittingTerminalSemanticPair reward
          (quittingAllContinuePrefixIterate reward profile H) =
        quittingTerminalSemanticPair reward profile ∧
      quittingTerminalOutcomeMass reward
          (quittingAllContinuePrefixIterate reward profile H) =
        quittingTerminalOutcomeMass reward profile ∧
      (∀ observer t, quittingPureTimeDeviationPayoff reward
            (quittingAllContinuePrefixIterate reward profile H) observer
            (some (t + H)) =
          quittingPureTimeDeviationPayoff reward profile observer (some t)) ∧
      (∀ observer, quittingPureTimeDeviationPayoff reward
            (quittingAllContinuePrefixIterate reward profile H) observer none =
          quittingPureTimeDeviationPayoff reward profile observer none) :=
  ⟨quittingTerminalSemanticPair_allContinuePrefixIterate_eq reward profile hsolo H,
    quittingTerminalOutcomeMass_allContinuePrefix_eq reward profile H,
    fun observer t =>
      quittingPureTimeDeviationPayoff_allContinuePrefixIterate_some
        reward profile observer H t,
    fun observer =>
      quittingPureTimeDeviationPayoff_allContinuePrefixIterate_none
        reward profile observer H⟩

end GameTheory
