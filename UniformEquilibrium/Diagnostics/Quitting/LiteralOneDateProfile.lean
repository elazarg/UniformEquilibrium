/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauLocalizedOtherDefect

/-!
# Literal one-date quitting profiles

A literal one-date override retains the complete behavioral strategy at every
other date.  The declarations here identify its live-root, payoff, response-cap,
and debt semantics with the canonical stage endpoint deviation.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def quittingLiteralOneDateOverride
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {who : ι} (strategy : (quittingGame reward).BehaviorStrategy who)
    (stage : ℕ) (action : Bool) :
    (quittingGame reward).BehaviorStrategy who :=
  fun time history => if time = stage then PMF.pure action else strategy time history

/-- A profile obtained by applying a literal pure override to one player. -/
def quittingLiteralOneDateProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (action : Bool) :
    (quittingGame reward).BehaviorProfile :=
  Function.update profile who
    (quittingLiteralOneDateOverride (profile who) stage action)

omit [DecidableEq ι] in
theorem quittingLiteralOneDateOverride_idem
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {who : ι} (strategy : (quittingGame reward).BehaviorStrategy who)
    (stage : ℕ) (action : Bool) :
    quittingLiteralOneDateOverride
        (quittingLiteralOneDateOverride strategy stage action) stage action =
      quittingLiteralOneDateOverride strategy stage action := by
  funext time history
  by_cases htime : time = stage
  · subst time
    simp [quittingLiteralOneDateOverride]
  · simp [quittingLiteralOneDateOverride, htime]

omit [DecidableEq ι] in
@[simp] theorem quittingLiteralOneDateOverride_self
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {who : ι} (strategy : (quittingGame reward).BehaviorStrategy who)
    (stage : ℕ) (action : Bool) :
    quittingLiteralOneDateOverride strategy stage action stage =
      fun _history => PMF.pure action := by
  funext history
  simp [quittingLiteralOneDateOverride]
  rfl

omit [DecidableEq ι] in
theorem quittingLiteralOneDateOverride_of_ne
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {who : ι} (strategy : (quittingGame reward).BehaviorStrategy who)
    (stage time : ℕ) (action : Bool) (h : time ≠ stage) :
    quittingLiteralOneDateOverride strategy stage action time = strategy time := by
  funext history
  simp [quittingLiteralOneDateOverride, h]

theorem quittingProfileLiveRoot_literalOneDateProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (action : Bool) :
    quittingProfileLiveRoot reward
        (quittingLiteralOneDateProfile reward profile who stage action) stage =
      Function.update (quittingProfileLiveRoot reward profile stage) who
        (PMF.pure action) := by
  let baseRoot : ι → PMF Bool := quittingProfileLiveRoot reward profile stage
  change quittingProfileLiveRoot reward
      (quittingLiteralOneDateProfile reward profile who stage action) stage =
    Function.update baseRoot who (PMF.pure action)
  funext player
  by_cases hplayer : player = who
  · subst player
    calc
      quittingProfileLiveRoot reward
          (quittingLiteralOneDateProfile reward profile who stage action)
          stage who = PMF.pure action := by
        unfold quittingProfileLiveRoot quittingLiteralOneDateProfile
        rw [Function.update_self, quittingLiteralOneDateOverride_self]
      _ = Function.update baseRoot who (PMF.pure action) who := by
        simp only [Function.update_apply, reduceIte]
  · calc
      quittingProfileLiveRoot reward
          (quittingLiteralOneDateProfile reward profile who stage action)
          stage player = baseRoot player := by
        unfold quittingProfileLiveRoot quittingLiteralOneDateProfile
        rw [Function.update_of_ne hplayer]
        rfl
      _ = Function.update baseRoot who (PMF.pure action) player := by
        simp only [Function.update_apply, hplayer, reduceIte]

omit [DecidableEq ι] in
theorem quittingBehaviorLiveHazard_literalOneDateOverride
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {who : ι} (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (action : Bool) :
    quittingBehaviorLiveHazard reward
        (quittingLiteralOneDateOverride (profile who) stage action) =
      quittingStageDeviationHazard (quittingProfileLiveRoot reward profile)
        who stage (PMF.pure action)
        (fun offset =>
          quittingProfileLiveRoot reward profile (stage + 1 + offset) who) := by
  let base : ℕ → PMF Bool :=
    fun time => quittingProfileLiveRoot reward profile time who
  let literal : ℕ → PMF Bool :=
    fun time => if time = stage then PMF.pure action else base time
  change quittingBehaviorLiveHazard reward
      (quittingLiteralOneDateOverride (profile who) stage action) =
    quittingStageDeviationHazard (quittingProfileLiveRoot reward profile)
      who stage (PMF.pure action) (fun offset => base (stage + 1 + offset))
  have hleft :
      quittingBehaviorLiveHazard reward
          (quittingLiteralOneDateOverride (profile who) stage action) = literal := by
    funext time
    rfl
  rw [hleft]
  funext time
  by_cases hlt : time < stage
  · rw [show literal time = base time by
      simp only [literal, ne_of_lt hlt, reduceIte]]
    rw [quittingStageDeviationHazard_of_lt
      (quittingProfileLiveRoot reward profile) who (PMF.pure action)
      (fun offset =>
        base (stage + 1 + offset)) hlt]
  · by_cases heq : time = stage
    · subst time
      rw [quittingStageDeviationHazard_self]
      simp only [literal, reduceIte]
    · have hstage : stage < time := lt_of_le_of_ne (Nat.le_of_not_gt hlt)
        (Ne.symm heq)
      rw [show literal time = base time by
        simp only [literal, heq, reduceIte]]
      rw [quittingStageDeviationHazard]
      simp only [hlt, heq, reduceIte]
      have htime : stage + 1 + (time - (stage + 1)) = time :=
        Nat.add_sub_of_le (Nat.succ_le_iff.mpr hstage)
      rw [htime]

theorem quittingProfileLiveRoot_literalOneDateProfile_eq_rootSequenceUpdate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (action : Bool) :
    quittingProfileLiveRoot reward
        (quittingLiteralOneDateProfile reward profile who stage action) =
      quittingRootSequenceUpdate (quittingProfileLiveRoot reward profile)
        who (quittingStageDeviationHazard
          (quittingProfileLiveRoot reward profile) who stage (PMF.pure action)
          (fun offset =>
            quittingProfileLiveRoot reward profile (stage + 1 + offset) who)) := by
  unfold quittingLiteralOneDateProfile
  rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate]
  rw [quittingBehaviorLiveHazard_literalOneDateOverride]

theorem quittingProfileLiveRoot_literalOneDateProfile_eq_canonical
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (action : Bool) :
    quittingProfileLiveRoot reward
        (quittingLiteralOneDateProfile reward profile who stage action) =
      quittingProfileLiveRoot reward
        (Function.update profile who
          (quittingStagePureEndpointBehaviorDeviation
            reward profile who stage action)) := by
  rw [quittingProfileLiveRoot_literalOneDateProfile_eq_rootSequenceUpdate,
    quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
    quittingBehaviorLiveHazard_stagePureEndpointBehaviorDeviation]

theorem quittingTerminalPayoff_literalOneDateProfile_eq_canonical
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (action : Bool) :
    quittingTerminalPayoff reward
        (quittingLiteralOneDateProfile reward profile who stage action) who =
      quittingTerminalPayoff reward
        (Function.update profile who
          (quittingStagePureEndpointBehaviorDeviation
            reward profile who stage action)) who := by
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingProfileLiveRoot_literalOneDateProfile_eq_canonical]

theorem quittingContinuationBestResponseValue_literalOneDateProfile_self_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (action : Bool) :
    quittingContinuationBestResponseValue reward
        (quittingLiteralOneDateProfile reward profile who stage action) who =
      quittingContinuationBestResponseValue reward profile who := by
  unfold quittingLiteralOneDateProfile
  exact quittingContinuationBestResponseValue_update_self
    reward profile who _

theorem quittingTerminalSemanticDebt_literalOneDateProfile_eq_sub_gain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (action : Bool) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingLiteralOneDateProfile reward profile who stage action)) who =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who -
        (quittingTerminalPayoff reward
          (quittingLiteralOneDateProfile reward profile who stage action) who -
          quittingTerminalPayoff reward profile who) := by
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  change quittingContinuationBestResponseValue reward
        (quittingLiteralOneDateProfile reward profile who stage action) who -
      quittingTerminalPayoff reward
        (quittingLiteralOneDateProfile reward profile who stage action) who =
    quittingContinuationBestResponseValue reward profile who -
      quittingTerminalPayoff reward profile who -
        (quittingTerminalPayoff reward
          (quittingLiteralOneDateProfile reward profile who stage action) who -
          quittingTerminalPayoff reward profile who)
  rw [quittingContinuationBestResponseValue_literalOneDateProfile_self_eq]
  ring

theorem quittingTerminalPayoff_literalOneDateProfile_gain_eq_liveMass_mul_defect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (action : Bool) :
    quittingTerminalPayoff reward
          (quittingLiteralOneDateProfile reward profile who stage action) who -
        quittingTerminalPayoff reward profile who =
      quittingLiveMass reward profile stage *
        (quittingRootSuccessorPayoff reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (stage + 1))).1
          (Function.update (quittingProfileLiveRoot reward profile stage) who
            (PMF.pure action)) who -
          quittingRootSuccessorPayoff reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile (stage + 1))).1
            (quittingProfileLiveRoot reward profile stage) who) := by
  rw [quittingTerminalPayoff_literalOneDateProfile_eq_canonical]
  exact quittingTerminalPayoff_stagePureEndpointDeviation_sub_eq_liveMass_mul
    reward profile who stage action


end GameTheory
