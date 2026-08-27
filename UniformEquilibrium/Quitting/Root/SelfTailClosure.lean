/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Root.LiteralExactPrefixStack

/-!
# Literal self-tail closure

Copy the actual live roots of a quitting profile through a displayed date,
then restart that same complete behavioral profile.  The resulting finite
literal root stack has the original live roots through the displayed date and
its full all-Continue continuation is exactly the original profile.

These are structural profile identities.  No equilibrium, cap-Nash, or
near-minimality property is asserted for the copied roots against the new
continuation.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι]

/-! ## Literal root-stack shifts -/

/-- Moving one step farther along an all-Continue spine can equivalently be
done before iterating the remaining number of steps. -/
theorem quittingAllContinueProfileSpine_succ_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingAllContinueProfileSpine reward profile (time + 1) =
      quittingAllContinueProfileSpine reward
        (quittingProfileAllContinueContinuation reward profile) time := by
  induction time with
  | zero => rfl
  | succ time ih =>
      simpa only [quittingAllContinueProfileSpine] using
        congrArg (quittingProfileAllContinueContinuation reward) ih

/-- Two profiles that agree at every date from `start` onward have literally
equal all-Continue spines from `start`.  The histories in the agreement
hypothesis are arbitrary, so this retains complete off-live behavior too. -/
theorem quittingAllContinueProfileSpine_eq_of_eq_from
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile) (start : ℕ)
    (heq : ∀ who time history, start ≤ time →
      first who time history = second who time history) :
    quittingAllContinueProfileSpine reward first start =
      quittingAllContinueProfileSpine reward second start := by
  induction start generalizing first second with
  | zero =>
      funext who time history
      exact heq who time history (Nat.zero_le time)
  | succ start ih =>
      rw [quittingAllContinueProfileSpine_succ_eq,
        quittingAllContinueProfileSpine_succ_eq]
      apply ih
      intro who time history htime
      unfold quittingProfileAllContinueContinuation StochasticGame.shiftProfile
      exact heq who (time + 1) _ (by omega)

/-- The all-Continue continuation of a nonempty literal root stack drops its
first root and retains the same terminal profile. -/
theorem quittingProfileAllContinueContinuation_literalRootStackProfile_cons
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) :
    quittingProfileAllContinueContinuation reward
        (quittingLiteralRootStackProfile reward (root :: roots) terminal) =
      quittingLiteralRootStackProfile reward roots terminal := by
  simpa only [quittingLiteralRootStackProfile_cons,
    quittingProfileAllContinueContinuation] using
      shiftProfile_quittingRootThenContinuationProfile reward root
        (quittingLiteralRootStackProfile reward roots terminal)
        quittingAllContinueAction

/-- Shifting a literal root stack by any number of steps within the stack
leaves exactly the corresponding dropped stack. -/
theorem quittingAllContinueProfileSpine_literalRootStackProfile_eq_drop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (count : ℕ) (hcount : count ≤ roots.length) :
    quittingAllContinueProfileSpine reward
        (quittingLiteralRootStackProfile reward roots terminal) count =
      quittingLiteralRootStackProfile reward (roots.drop count) terminal := by
  induction count generalizing roots with
  | zero => rfl
  | succ count ih =>
      cases roots with
      | nil => simp at hcount
      | cons root roots =>
          rw [show count + 1 = count.succ by omega,
            quittingAllContinueProfileSpine_succ_eq,
            quittingProfileAllContinueContinuation_literalRootStackProfile_cons]
          simpa using ih roots (by simpa using hcount)

/-- After the entire finite root stack, the full all-Continue continuation is
the declared terminal profile. -/
theorem quittingAllContinueProfileSpine_literalRootStackProfile_length
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) :
    quittingAllContinueProfileSpine reward
        (quittingLiteralRootStackProfile reward roots terminal) roots.length =
      terminal := by
  rw [quittingAllContinueProfileSpine_literalRootStackProfile_eq_drop
    reward roots terminal roots.length le_rfl, List.drop_length]
  rfl

/-- At every position inside a literal root stack, its actual live root is
the corresponding stored root. -/
theorem quittingProfileLiveRoot_literalRootStackProfile_eq_getElem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (time : ℕ) (htime : time < roots.length) :
    quittingProfileLiveRoot reward
        (quittingLiteralRootStackProfile reward roots terminal) time =
      roots[time] := by
  calc
    quittingProfileLiveRoot reward
          (quittingLiteralRootStackProfile reward roots terminal) time =
        quittingProfileRoot reward
          (quittingAllContinueProfileSpine reward
            (quittingLiteralRootStackProfile reward roots terminal) time) := by
      exact (congrFun
        (quittingProfileSpineRoot_eq_profileLiveRoot reward
          (quittingLiteralRootStackProfile reward roots terminal)) time).symm
    _ = quittingProfileRoot reward
          (quittingLiteralRootStackProfile reward (roots.drop time) terminal) := by
      rw [quittingAllContinueProfileSpine_literalRootStackProfile_eq_drop
        reward roots terminal time htime.le]
    _ = roots[time] := by
      rw [List.drop_eq_getElem_cons htime,
        quittingLiteralRootStackProfile_cons,
        quittingProfileRoot_rootThenContinuationProfile]

/-! ## Self-tail closure -/

/-- The finite word of actual live roots through `stage`, inclusive. -/
def quittingSelfTailRootStack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) : List (ι → PMF Bool) :=
  List.ofFn fun time : Fin (stage + 1) =>
    quittingProfileLiveRoot reward profile time

/-- Copy the actual live roots through `stage`, then restart the same complete
behavioral profile after all players Continue at the displayed row. -/
def quittingSelfTailClosure
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward
    (quittingSelfTailRootStack reward profile stage) profile

/-- Copy the actual live roots of `prefixProfile` through `stage`, then restart
an independently supplied complete behavioral profile.  This is the
two-profile version of `quittingSelfTailClosure`; it deliberately makes no
semantic or equilibrium comparison between the two profiles. -/
def quittingCrossTailClosure
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (prefixProfile tailProfile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward
    (quittingSelfTailRootStack reward prefixProfile stage) tailProfile

/-- The copied self-tail root word contains exactly the displayed prefix. -/
@[simp]
theorem quittingSelfTailRootStack_length
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ) :
    (quittingSelfTailRootStack reward profile stage).length = stage + 1 := by
  simp [quittingSelfTailRootStack]

/-- The self-tail closure has exactly the original actual live root at every
date through the copied stage. -/
theorem quittingProfileLiveRoot_selfTailClosure_eq_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage time : ℕ) (htime : time ≤ stage) :
    quittingProfileLiveRoot reward
        (quittingSelfTailClosure reward profile stage) time =
      quittingProfileLiveRoot reward profile time := by
  have hinside : time <
      (quittingSelfTailRootStack reward profile stage).length := by
    rw [quittingSelfTailRootStack_length]
    omega
  rw [quittingSelfTailClosure,
    quittingProfileLiveRoot_literalRootStackProfile_eq_getElem
      reward (quittingSelfTailRootStack reward profile stage) profile time hinside]
  simp only [quittingSelfTailRootStack, List.getElem_ofFn]

/-- A cross-tail closure has exactly the prefix profile's live root at every
copied date, independently of the restarted tail profile. -/
theorem quittingProfileLiveRoot_crossTailClosure_eq_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (prefixProfile tailProfile : (quittingGame reward).BehaviorProfile)
    (stage time : ℕ) (htime : time ≤ stage) :
    quittingProfileLiveRoot reward
        (quittingCrossTailClosure reward prefixProfile tailProfile stage) time =
      quittingProfileLiveRoot reward prefixProfile time := by
  have hinside : time <
      (quittingSelfTailRootStack reward prefixProfile stage).length := by
    rw [quittingSelfTailRootStack_length]
    omega
  rw [quittingCrossTailClosure,
    quittingProfileLiveRoot_literalRootStackProfile_eq_getElem
      reward (quittingSelfTailRootStack reward prefixProfile stage)
        tailProfile time hinside]
  simp only [quittingSelfTailRootStack, List.getElem_ofFn]

/-- The complete all-Continue continuation after the copied marked row is
literally the original behavioral profile, not merely a semantic equivalent. -/
theorem quittingAllContinueProfileSpine_selfTailClosure
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ) :
    quittingAllContinueProfileSpine reward
        (quittingSelfTailClosure reward profile stage) (stage + 1) =
      profile := by
  have hlength :
      (quittingSelfTailRootStack reward profile stage).length = stage + 1 :=
    quittingSelfTailRootStack_length reward profile stage
  rw [quittingSelfTailClosure, ← hlength]
  exact quittingAllContinueProfileSpine_literalRootStackProfile_length reward
    (quittingSelfTailRootStack reward profile stage) profile

/-- After the copied marked row, a cross-tail closure is literally the
declared second behavioral profile. -/
theorem quittingAllContinueProfileSpine_crossTailClosure
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (prefixProfile tailProfile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) :
    quittingAllContinueProfileSpine reward
        (quittingCrossTailClosure reward prefixProfile tailProfile stage)
        (stage + 1) =
      tailProfile := by
  have hlength :
      (quittingSelfTailRootStack reward prefixProfile stage).length = stage + 1 :=
    quittingSelfTailRootStack_length reward prefixProfile stage
  rw [quittingCrossTailClosure, ← hlength]
  exact quittingAllContinueProfileSpine_literalRootStackProfile_length reward
    (quittingSelfTailRootStack reward prefixProfile stage) tailProfile

end GameTheory
