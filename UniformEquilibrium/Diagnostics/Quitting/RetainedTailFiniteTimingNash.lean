/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.ContinuePrefixAtomAccess
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashChronology
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeRectangle
import UniformEquilibrium.Quitting.Paths.SurvivalWeightedSuffixRegret

/-!
# Finite timing Nash grafts over an arbitrary retained tail

A finite word of independent quitting roots is viewed as a mixed finite-timing
block.  The all-Continue timing action resumes one supplied behavioral tail
literally.  `IsQuittingRetainedTailFiniteTimingNash` records exactly the two
pure timing comparisons supplied by a Nash equilibrium of that finite timing
game: finite stopping dates are no better than the graft payoff, and passing
through the whole word to the prescribed tail is no better either.

The main theorem upgrades those pure timing comparisons to the full
behavioral strategy class.  The remaining terminal debt is at most the
player-deleted survival of the timing word times the debt of the retained
tail.  No best response is assumed to be attained.

This module does not construct a timing equilibrium, identify the graft
payoff with the tail payoff, or assert that a timing block remains Nash after
its tail is changed.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The behavioral realization of a finite timing word followed by a literal
retained tail. -/
def quittingRetainedTailFiniteTimingGraft
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward roots tail

/-- The prescribed timing action which Continues through the whole finite
word and then resumes the retained tail. -/
def quittingRetainedTailFiniteTimingPassProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile) (who : ι) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward
    (quittingLiteralRootStackForceContinue roots who) tail

/-- Exact pure-action Nash data for a finite timing word returning to an
arbitrary behavioral tail.  The `finiteStop_le` field covers precisely the
dates before the retained tail; `pass_le` covers the timing action `Never`.
-/
structure IsQuittingRetainedTailFiniteTimingNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile) : Prop where
  finiteStop_le : ∀ (who : ι) (time : ℕ), time < roots.length →
    quittingPureTimeDeviationPayoff reward
        (quittingRetainedTailFiniteTimingGraft reward roots tail) who
        (some time) ≤
      quittingTerminalPayoff reward
        (quittingRetainedTailFiniteTimingGraft reward roots tail) who
  pass_le : ∀ who : ι,
    quittingTerminalPayoff reward
        (quittingRetainedTailFiniteTimingPassProfile reward roots tail who) who ≤
      quittingTerminalPayoff reward
        (quittingRetainedTailFiniteTimingGraft reward roots tail) who

omit [DecidableEq ι] in
/-- Rebasing a pure stopping time past a finite root word is literally the
strategy which Continues through that word and then uses the relative pure
time in the retained tail. -/
theorem quittingPureTimeBehaviorStrategy_absolute_eq_continueDeviation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) (who : ι) (choice : Option ℕ) :
    quittingPureTimeBehaviorStrategy reward who
        (quittingAbsolutePureTime roots.length choice) =
      quittingLiteralRootStackContinueDeviation reward roots
        (quittingPureTimeBehaviorStrategy reward who choice) := by
  induction roots with
  | nil =>
      cases choice <;>
        simp [quittingAbsolutePureTime,
          quittingLiteralRootStackContinueDeviation]
  | cons root roots ih =>
      funext time history
      cases time with
      | zero =>
          change quittingPureTimeHazard
              (quittingAbsolutePureTime (roots.length + 1) choice) 0 =
            PMF.pure false
          cases choice with
          | none => rfl
          | some delay =>
              exact quittingPureTimeHazard_some_of_ne (by omega)
      | succ time =>
          change quittingPureTimeHazard
              (quittingAbsolutePureTime (roots.length + 1) choice) (time + 1) =
            quittingLiteralRootStackContinueDeviation reward roots
              (quittingPureTimeBehaviorStrategy reward who choice) time
              (Fin.tail history.1, history.2)
          rw [← ih]
          change quittingPureTimeHazard
              (quittingAbsolutePureTime (roots.length + 1) choice) (time + 1) =
            quittingPureTimeHazard
              (quittingAbsolutePureTime roots.length choice) time
          cases choice with
          | none => rfl
          | some delay =>
              simp only [quittingAbsolutePureTime]
              by_cases htime : time = roots.length + delay
              · have htime' : time + 1 = roots.length + 1 + delay := by omega
                simp only [quittingPureTimeHazard]
                rw [if_pos htime', if_pos htime]
              · have htime' : time + 1 ≠ roots.length + 1 + delay := by omega
                simp only [quittingPureTimeHazard]
                rw [if_neg htime', if_neg htime]

omit [DecidableEq ι] in
/-- Quitting at the current date is the root Quit endpoint followed by an
irrelevant continuation. -/
theorem quittingPureTimeBehaviorStrategy_zero_eq_rootDeviation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingPureTimeBehaviorStrategy reward who (some 0) =
      quittingRootAndContinuationDeviation reward (PMF.pure true)
        (quittingPureTimeBehaviorStrategy reward who none) := by
  funext time history
  cases time with
  | zero => simp [quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
      quittingRootAndContinuationDeviation]
  | succ time => simp [quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
      quittingRootAndContinuationDeviation]

omit [DecidableEq ι] in
/-- Quitting one date after a splice is pure Continue at the current root and
the predecessor stopping time in the continuation. -/
theorem quittingPureTimeBehaviorStrategy_succ_eq_rootDeviation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (time : ℕ) :
    quittingPureTimeBehaviorStrategy reward who (some (time + 1)) =
      quittingRootAndContinuationDeviation reward (PMF.pure false)
        (quittingPureTimeBehaviorStrategy reward who (some time)) := by
  funext current history
  cases current with
  | zero => simp [quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
      quittingRootAndContinuationDeviation]
  | succ current =>
      simp only [quittingPureTimeBehaviorStrategy,
        quittingRootAndContinuationDeviation]
      by_cases hcurrent : current = time
      · simp [quittingPureTimeHazard, hcurrent]
      · simp [quittingPureTimeHazard, hcurrent]

/-- A deterministic stop inside the finite word is independent of the tail
placed after the word. -/
theorem quittingPureTimeDeviationPayoff_retainedTail_eq_of_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (first second : (quittingGame reward).BehaviorProfile)
    (who : ι) (time : ℕ) (htime : time < roots.length) :
    quittingPureTimeDeviationPayoff reward
        (quittingRetainedTailFiniteTimingGraft reward roots first) who
        (some time) =
      quittingPureTimeDeviationPayoff reward
        (quittingRetainedTailFiniteTimingGraft reward roots second) who
        (some time) := by
  induction roots generalizing time with
  | nil => simp at htime
  | cons root roots ih =>
      cases time with
      | zero =>
          unfold quittingPureTimeDeviationPayoff
          unfold quittingRetainedTailFiniteTimingGraft
          rw [quittingLiteralRootStackProfile_cons,
            quittingLiteralRootStackProfile_cons,
            quittingPureTimeBehaviorStrategy_zero_eq_rootDeviation,
            quittingTerminalPayoff_update_rootAndContinuationDeviation_eq,
            quittingTerminalPayoff_update_rootAndContinuationDeviation_eq]
          apply quittingRootExpectedPayoff_eq_of_hasSureQuitter
          exact ⟨who, Function.update_self who (PMF.pure true) root⟩
      | succ time =>
          have htime' : time < roots.length := by simpa using htime
          unfold quittingPureTimeDeviationPayoff
          unfold quittingRetainedTailFiniteTimingGraft
          rw [quittingLiteralRootStackProfile_cons,
            quittingLiteralRootStackProfile_cons,
            quittingPureTimeBehaviorStrategy_succ_eq_rootDeviation,
            quittingTerminalPayoff_update_rootAndContinuationDeviation_eq,
            quittingTerminalPayoff_update_rootAndContinuationDeviation_eq]
          apply quittingRootExpectedPayoff_continuation_congr
          simp only [Function.update_self]
          exact ih time htime'

/-- The payoff of a stopping time rebased past the finite word is the payoff
of the literal force-Continue prefix followed by the corresponding tail
deviation. -/
theorem quittingPureTimeDeviationPayoff_absolute_eq_retainedTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile)
    (who : ι) (choice : Option ℕ) :
    quittingPureTimeDeviationPayoff reward
        (quittingRetainedTailFiniteTimingGraft reward roots tail) who
        (quittingAbsolutePureTime roots.length choice) =
      quittingTerminalPayoff reward
        (quittingLiteralRootStackProfile reward
          (quittingLiteralRootStackForceContinue roots who)
          (Function.update tail who
            (quittingPureTimeBehaviorStrategy reward who choice))) who := by
  unfold quittingPureTimeDeviationPayoff
  rw [quittingPureTimeBehaviorStrategy_absolute_eq_continueDeviation]
  unfold quittingRetainedTailFiniteTimingGraft
  rw [
    update_quittingLiteralRootStackProfile_continueDeviation]

/-- Exact late-deviation comparison.  A deviation which passes through the
whole timing word changes payoff by the player-deleted return probability
times the corresponding payoff change in the retained tail. -/
theorem quittingPureTimeDeviationPayoff_absolute_sub_pass_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile)
    (who : ι) (choice : Option ℕ) :
    quittingPureTimeDeviationPayoff reward
          (quittingRetainedTailFiniteTimingGraft reward roots tail) who
          (quittingAbsolutePureTime roots.length choice) -
        quittingTerminalPayoff reward
          (quittingRetainedTailFiniteTimingPassProfile reward roots tail who) who =
      quittingLiteralRootStackOpponentSurvival roots who *
        (quittingPureTimeDeviationPayoff reward tail who choice -
          quittingTerminalPayoff reward tail who) := by
  rw [quittingPureTimeDeviationPayoff_absolute_eq_retainedTail]
  unfold quittingRetainedTailFiniteTimingPassProfile
  rw [quittingTerminalPayoff_literalRootStack_sub_eq_continueProduct_mul]
  rw [show quittingCapNashStackContinueProduct
      (quittingLiteralRootStackForceContinue roots who) =
        quittingLiteralRootStackJointSurvival
          (quittingLiteralRootStackForceContinue roots who) by rfl]
  rw [quittingLiteralRootStackJointSurvival_forceContinue]
  rfl

/-- Cross-tail late-deviation comparison: the deviation uses `deviationTail`,
while the benchmark timing action passes to `benchmarkTail`. -/
theorem quittingPureTimeDeviationPayoff_absolute_sub_crossTailPass_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (deviationTail benchmarkTail : (quittingGame reward).BehaviorProfile)
    (who : ι) (choice : Option ℕ) :
    quittingPureTimeDeviationPayoff reward
          (quittingRetainedTailFiniteTimingGraft reward roots deviationTail) who
          (quittingAbsolutePureTime roots.length choice) -
        quittingTerminalPayoff reward
          (quittingRetainedTailFiniteTimingPassProfile reward roots benchmarkTail who)
          who =
      quittingLiteralRootStackOpponentSurvival roots who *
        (quittingPureTimeDeviationPayoff reward deviationTail who choice -
          quittingTerminalPayoff reward benchmarkTail who) := by
  rw [quittingPureTimeDeviationPayoff_absolute_eq_retainedTail]
  unfold quittingRetainedTailFiniteTimingPassProfile
  rw [quittingTerminalPayoff_literalRootStack_sub_eq_continueProduct_mul]
  rw [show quittingCapNashStackContinueProduct
      (quittingLiteralRootStackForceContinue roots who) =
        quittingLiteralRootStackJointSurvival
          (quittingLiteralRootStackForceContinue roots who) by rfl]
  rw [quittingLiteralRootStackJointSurvival_forceContinue]
  rfl

/-- Two arbitrary tails behind the same force-Continue timing prefix differ
at a late pure stopping time by exactly player-deleted return times the tail
payoff difference. -/
theorem quittingPureTimeDeviationPayoff_absolute_sub_absolute_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (first second : (quittingGame reward).BehaviorProfile)
    (who : ι) (choice : Option ℕ) :
    quittingPureTimeDeviationPayoff reward
          (quittingRetainedTailFiniteTimingGraft reward roots first) who
          (quittingAbsolutePureTime roots.length choice) -
        quittingPureTimeDeviationPayoff reward
          (quittingRetainedTailFiniteTimingGraft reward roots second) who
          (quittingAbsolutePureTime roots.length choice) =
      quittingLiteralRootStackOpponentSurvival roots who *
        (quittingPureTimeDeviationPayoff reward first who choice -
          quittingPureTimeDeviationPayoff reward second who choice) := by
  rw [quittingPureTimeDeviationPayoff_absolute_eq_retainedTail,
    quittingPureTimeDeviationPayoff_absolute_eq_retainedTail,
    quittingTerminalPayoff_literalRootStack_sub_eq_continueProduct_mul]
  rw [show quittingCapNashStackContinueProduct
      (quittingLiteralRootStackForceContinue roots who) =
        quittingLiteralRootStackJointSurvival
          (quittingLiteralRootStackForceContinue roots who) by rfl]
  rw [quittingLiteralRootStackJointSurvival_forceContinue]
  rfl

/-- Replacing the retained tail changes every pure timing-deviation payoff by
at most the reward diameter times player-deleted return. -/
theorem quittingPureTimeDeviationPayoff_retainedTail_le_add_two_mul_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (first second : (quittingGame reward).BehaviorProfile)
    (who : ι) (choice : Option ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hreward : ∀ S player, |reward S player| ≤ R) :
    quittingPureTimeDeviationPayoff reward
        (quittingRetainedTailFiniteTimingGraft reward roots first) who choice ≤
      quittingPureTimeDeviationPayoff reward
          (quittingRetainedTailFiniteTimingGraft reward roots second) who choice +
        2 * R * quittingLiteralRootStackOpponentSurvival roots who := by
  cases choice with
  | none =>
      have hexact := quittingPureTimeDeviationPayoff_absolute_sub_absolute_eq
        reward roots first second who none
      have hfirst := abs_quittingTerminalPayoff_le reward
        (Function.update first who
          (quittingPureTimeBehaviorStrategy reward who none)) who hreward
      have hsecond := abs_quittingTerminalPayoff_le reward
        (Function.update second who
          (quittingPureTimeBehaviorStrategy reward who none)) who hreward
      have htail : quittingPureTimeDeviationPayoff reward first who none -
          quittingPureTimeDeviationPayoff reward second who none ≤ 2 * R := by
        unfold quittingPureTimeDeviationPayoff
        linarith [le_of_abs_le hfirst, neg_le_of_abs_le hsecond]
      have hscaled := mul_le_mul_of_nonneg_left htail
        (quittingLiteralRootStackOpponentSurvival_nonneg roots who)
      simp only [quittingAbsolutePureTime] at hexact
      nlinarith
  | some time =>
      by_cases hearly : time < roots.length
      · rw [quittingPureTimeDeviationPayoff_retainedTail_eq_of_lt
          reward roots first second who time hearly]
        exact le_add_of_nonneg_right <| by
          exact mul_nonneg (mul_nonneg (by norm_num) hR)
            (quittingLiteralRootStackOpponentSurvival_nonneg roots who)
      · let delay := time - roots.length
        have htime : roots.length + delay = time := by
          dsimp only [delay]
          omega
        have hexact := quittingPureTimeDeviationPayoff_absolute_sub_absolute_eq
          reward roots first second who (some delay)
        have hfirst := abs_quittingTerminalPayoff_le reward
          (Function.update first who
            (quittingPureTimeBehaviorStrategy reward who (some delay))) who
          hreward
        have hsecond := abs_quittingTerminalPayoff_le reward
          (Function.update second who
            (quittingPureTimeBehaviorStrategy reward who (some delay))) who
          hreward
        have htail : quittingPureTimeDeviationPayoff reward first who (some delay) -
            quittingPureTimeDeviationPayoff reward second who (some delay) ≤
              2 * R := by
          unfold quittingPureTimeDeviationPayoff
          linarith [le_of_abs_le hfirst, neg_le_of_abs_le hsecond]
        have hscaled := mul_le_mul_of_nonneg_left htail
          (quittingLiteralRootStackOpponentSurvival_nonneg roots who)
        rw [show quittingAbsolutePureTime roots.length (some delay) =
          some time by simp [quittingAbsolutePureTime, htime]] at hexact
        nlinarith

/-- Behavioral best-response values inherit the same sharp player-deleted
tail-replacement bound. -/
theorem quittingContinuationBestResponseValue_retainedTail_le_add_two_mul_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (first second : (quittingGame reward).BehaviorProfile)
    (who : ι) (R : ℝ) (hR : 0 ≤ R)
    (hreward : ∀ S player, |reward S player| ≤ R) :
    quittingContinuationBestResponseValue reward
        (quittingRetainedTailFiniteTimingGraft reward roots first) who ≤
      quittingContinuationBestResponseValue reward
          (quittingRetainedTailFiniteTimingGraft reward roots second) who +
        2 * R * quittingLiteralRootStackOpponentSurvival roots who := by
  rw [quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
  apply csSup_le (Set.range_nonempty _)
  rintro value ⟨choice, rfl⟩
  calc
    quittingPureTimeDeviationPayoff reward
        (quittingRetainedTailFiniteTimingGraft reward roots first) who choice ≤
      quittingPureTimeDeviationPayoff reward
          (quittingRetainedTailFiniteTimingGraft reward roots second) who choice +
        2 * R * quittingLiteralRootStackOpponentSurvival roots who :=
      quittingPureTimeDeviationPayoff_retainedTail_le_add_two_mul_bound
        reward roots first second who choice R hR hreward
    _ ≤ quittingContinuationBestResponseValue reward
            (quittingRetainedTailFiniteTimingGraft reward roots second) who +
          2 * R * quittingLiteralRootStackOpponentSurvival roots who := by
      simpa only [quittingPureTimeDeviationPayoff, add_comm] using
        add_le_add_right
          (quittingTerminalPayoff_update_le_continuationBestResponseValue
            reward (quittingRetainedTailFiniteTimingGraft reward roots second) who
            (quittingPureTimeBehaviorStrategy reward who choice))
          (2 * R * quittingLiteralRootStackOpponentSurvival roots who)

omit [DecidableEq ι] in
/-- Exact prescribed-payoff change under a retained-tail replacement. -/
theorem quittingRetainedTailFiniteTimingGraft_payoff_sub_eq_jointReturn_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (first second : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff reward
          (quittingRetainedTailFiniteTimingGraft reward roots first) who -
        quittingTerminalPayoff reward
          (quittingRetainedTailFiniteTimingGraft reward roots second) who =
      quittingLiteralRootStackJointSurvival roots *
        (quittingTerminalPayoff reward first who -
          quittingTerminalPayoff reward second who) := by
  unfold quittingRetainedTailFiniteTimingGraft
  rw [quittingTerminalPayoff_literalRootStack_sub_eq_continueProduct_mul]
  rfl

omit [DecidableEq ι] in
/-- The prescribed payoff changes by at most reward diameter times joint
return when the retained tail is replaced. -/
theorem abs_quittingRetainedTailFiniteTimingGraft_payoff_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (first second : (quittingGame reward).BehaviorProfile)
    (who : ι) (R : ℝ)
    (hreward : ∀ S player, |reward S player| ≤ R) :
    |quittingTerminalPayoff reward
          (quittingRetainedTailFiniteTimingGraft reward roots first) who -
        quittingTerminalPayoff reward
          (quittingRetainedTailFiniteTimingGraft reward roots second) who| ≤
      2 * R * quittingLiteralRootStackJointSurvival roots := by
  rw [quittingRetainedTailFiniteTimingGraft_payoff_sub_eq_jointReturn_mul,
    abs_mul, abs_of_nonneg
      (quittingLiteralRootStackJointSurvival_nonneg roots)]
  have hfirst := abs_quittingTerminalPayoff_le reward first who hreward
  have hsecond := abs_quittingTerminalPayoff_le reward second who hreward
  have hdiff : |quittingTerminalPayoff reward first who -
      quittingTerminalPayoff reward second who| ≤ 2 * R := by
    rw [abs_le]
    constructor <;> linarith [le_of_abs_le hfirst, neg_le_of_abs_le hfirst,
      le_of_abs_le hsecond, neg_le_of_abs_le hsecond]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left hdiff
      (quittingLiteralRootStackJointSurvival_nonneg roots)

/-- Every deterministic stopping time, including `Never`, is bounded by the
graft payoff plus player-deleted survival times retained-tail debt. -/
theorem IsQuittingRetainedTailFiniteTimingNash.pureTimePayoff_le
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {roots : List (ι → PMF Bool)}
    {tail : (quittingGame reward).BehaviorProfile}
    (nash : IsQuittingRetainedTailFiniteTimingNash reward roots tail)
    (who : ι) (choice : Option ℕ) :
    quittingPureTimeDeviationPayoff reward
        (quittingRetainedTailFiniteTimingGraft reward roots tail) who choice ≤
      quittingTerminalPayoff reward
          (quittingRetainedTailFiniteTimingGraft reward roots tail) who +
        quittingLiteralRootStackOpponentSurvival roots who *
          quittingTerminalDeviationDebt reward tail who := by
  have hsurvival :=
    quittingLiteralRootStackOpponentSurvival_nonneg roots who
  have htailDebt := quittingTerminalDeviationDebt_nonneg reward tail who
  cases choice with
  | none =>
      have hlate := quittingPureTimeDeviationPayoff_absolute_sub_pass_eq
        reward roots tail who none
      have hpure := quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward tail who (quittingPureTimeBehaviorStrategy reward who none)
      have htailComparison :
          quittingLiteralRootStackOpponentSurvival roots who *
              (quittingPureTimeDeviationPayoff reward tail who none -
                quittingTerminalPayoff reward tail who) ≤
            quittingLiteralRootStackOpponentSurvival roots who *
              quittingTerminalDeviationDebt reward tail who := by
        apply mul_le_mul_of_nonneg_left _ hsurvival
        simpa [quittingPureTimeDeviationPayoff,
          quittingTerminalDeviationDebt] using
            sub_le_sub_right hpure (quittingTerminalPayoff reward tail who)
      have hpass := nash.pass_le who
      simp only [quittingAbsolutePureTime] at hlate
      calc
        quittingPureTimeDeviationPayoff reward
              (quittingRetainedTailFiniteTimingGraft reward roots tail) who none =
            quittingTerminalPayoff reward
                (quittingRetainedTailFiniteTimingPassProfile reward roots tail who) who +
              quittingLiteralRootStackOpponentSurvival roots who *
                (quittingPureTimeDeviationPayoff reward tail who none -
                  quittingTerminalPayoff reward tail who) := by linarith
        _ ≤ quittingTerminalPayoff reward
                (quittingRetainedTailFiniteTimingPassProfile reward roots tail who) who +
                quittingLiteralRootStackOpponentSurvival roots who *
                quittingTerminalDeviationDebt reward tail who :=
            add_le_add_right htailComparison _
        _ ≤ _ := by
          simpa only [add_comm] using add_le_add_right hpass
            (quittingLiteralRootStackOpponentSurvival roots who *
              quittingTerminalDeviationDebt reward tail who)
  | some time =>
      by_cases hearly : time < roots.length
      · have hfinite := nash.finiteStop_le who time hearly
        exact hfinite.trans (le_add_of_nonneg_right (mul_nonneg hsurvival htailDebt))
      · let delay := time - roots.length
        have htime : roots.length + delay = time := by
          dsimp only [delay]
          omega
        have hlate := quittingPureTimeDeviationPayoff_absolute_sub_pass_eq
          reward roots tail who (some delay)
        have hpure := quittingTerminalPayoff_update_le_continuationBestResponseValue
          reward tail who
            (quittingPureTimeBehaviorStrategy reward who (some delay))
        have htailComparison :
            quittingLiteralRootStackOpponentSurvival roots who *
                (quittingPureTimeDeviationPayoff reward tail who (some delay) -
                  quittingTerminalPayoff reward tail who) ≤
              quittingLiteralRootStackOpponentSurvival roots who *
                quittingTerminalDeviationDebt reward tail who := by
          apply mul_le_mul_of_nonneg_left _ hsurvival
          simpa [quittingPureTimeDeviationPayoff,
            quittingTerminalDeviationDebt] using
              sub_le_sub_right hpure (quittingTerminalPayoff reward tail who)
        have hpass := nash.pass_le who
        rw [show quittingAbsolutePureTime roots.length (some delay) =
          some time by simp [quittingAbsolutePureTime, htime]] at hlate
        calc
          quittingPureTimeDeviationPayoff reward
                (quittingRetainedTailFiniteTimingGraft reward roots tail) who
                (some time) =
              quittingTerminalPayoff reward
                  (quittingRetainedTailFiniteTimingPassProfile reward roots tail who)
                  who +
                quittingLiteralRootStackOpponentSurvival roots who *
                  (quittingPureTimeDeviationPayoff reward tail who (some delay) -
                    quittingTerminalPayoff reward tail who) := by linarith
          _ ≤ quittingTerminalPayoff reward
                  (quittingRetainedTailFiniteTimingPassProfile reward roots tail who)
                  who +
                quittingLiteralRootStackOpponentSurvival roots who *
                  quittingTerminalDeviationDebt reward tail who :=
              add_le_add_right htailComparison _
          _ ≤ _ := by
            simpa only [add_comm] using add_le_add_right hpass
              (quittingLiteralRootStackOpponentSurvival roots who *
                quittingTerminalDeviationDebt reward tail who)

/-- The unrestricted behavioral debt of the timing graft is transported by
the player-deleted return probability.  The proof takes the supremum only
after bounding every deterministic stopping time. -/
theorem IsQuittingRetainedTailFiniteTimingNash.debt_le_deletedReturn_mul_tailDebt
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {roots : List (ι → PMF Bool)}
    {tail : (quittingGame reward).BehaviorProfile}
    (nash : IsQuittingRetainedTailFiniteTimingNash reward roots tail)
    (who : ι) :
    quittingTerminalDeviationDebt reward
        (quittingRetainedTailFiniteTimingGraft reward roots tail) who ≤
      quittingLiteralRootStackOpponentSurvival roots who *
        quittingTerminalDeviationDebt reward tail who := by
  rw [quittingTerminalDeviationDebt,
    quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
  have hsup : sSup (Set.range (quittingPureTimeDeviationPayoff reward
      (quittingRetainedTailFiniteTimingGraft reward roots tail) who)) ≤
      quittingTerminalPayoff reward
          (quittingRetainedTailFiniteTimingGraft reward roots tail) who +
        quittingLiteralRootStackOpponentSurvival roots who *
          quittingTerminalDeviationDebt reward tail who := by
    apply csSup_le (Set.range_nonempty _)
    rintro value ⟨choice, rfl⟩
    exact nash.pureTimePayoff_le who choice
  linarith

/-- If a replacement tail's behavioral cap is no larger than the prescribed
payoff of the timing action which returns to the original tail, the timing
block makes the replacement harmless for that player. -/
theorem IsQuittingRetainedTailFiniteTimingNash.replacementBestResponseValue_le
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {roots : List (ι → PMF Bool)}
    {tail : (quittingGame reward).BehaviorProfile}
    (nash : IsQuittingRetainedTailFiniteTimingNash reward roots tail)
    (replacement : (quittingGame reward).BehaviorProfile) (who : ι)
    (hcap : quittingContinuationBestResponseValue reward replacement who ≤
      quittingTerminalPayoff reward tail who) :
    quittingContinuationBestResponseValue reward
        (quittingRetainedTailFiniteTimingGraft reward roots replacement) who ≤
      quittingTerminalPayoff reward
        (quittingRetainedTailFiniteTimingGraft reward roots tail) who := by
  rw [quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
  apply csSup_le (Set.range_nonempty _)
  rintro value ⟨choice, rfl⟩
  cases choice with
  | none =>
      have hexact :=
        quittingPureTimeDeviationPayoff_absolute_sub_crossTailPass_eq
          reward roots replacement tail who none
      have hpure := quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward replacement who
          (quittingPureTimeBehaviorStrategy reward who none)
      have htail : quittingPureTimeDeviationPayoff reward replacement who none ≤
          quittingTerminalPayoff reward tail who := by
        exact hpure.trans hcap
      have hscaled := mul_nonpos_of_nonneg_of_nonpos
        (quittingLiteralRootStackOpponentSurvival_nonneg roots who)
        (sub_nonpos.mpr htail)
      have hpass := nash.pass_le who
      simp only [quittingAbsolutePureTime] at hexact
      linarith
  | some time =>
      by_cases hearly : time < roots.length
      · rw [quittingPureTimeDeviationPayoff_retainedTail_eq_of_lt
          reward roots replacement tail who time hearly]
        exact nash.finiteStop_le who time hearly
      · let delay := time - roots.length
        have htime : roots.length + delay = time := by
          dsimp only [delay]
          omega
        have hexact :=
          quittingPureTimeDeviationPayoff_absolute_sub_crossTailPass_eq
            reward roots replacement tail who (some delay)
        have hpure := quittingTerminalPayoff_update_le_continuationBestResponseValue
          reward replacement who
            (quittingPureTimeBehaviorStrategy reward who (some delay))
        have htail : quittingPureTimeDeviationPayoff reward replacement who
            (some delay) ≤ quittingTerminalPayoff reward tail who :=
          hpure.trans hcap
        have hscaled := mul_nonpos_of_nonneg_of_nonpos
          (quittingLiteralRootStackOpponentSurvival_nonneg roots who)
          (sub_nonpos.mpr htail)
        have hpass := nash.pass_le who
        rw [show quittingAbsolutePureTime roots.length (some delay) =
          some time by simp [quittingAbsolutePureTime, htime]] at hexact
        linarith

/-- Without a cap comparison, every replacement-tail behavioral deviation is
still bounded by the original timing payoff plus reward diameter times
player-deleted return. -/
theorem IsQuittingRetainedTailFiniteTimingNash.replacementBestResponseValue_le_add
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {roots : List (ι → PMF Bool)}
    {tail : (quittingGame reward).BehaviorProfile}
    (nash : IsQuittingRetainedTailFiniteTimingNash reward roots tail)
    (replacement : (quittingGame reward).BehaviorProfile)
    (who : ι) (R : ℝ) (hR : 0 ≤ R)
    (hreward : ∀ S player, |reward S player| ≤ R) :
    quittingContinuationBestResponseValue reward
        (quittingRetainedTailFiniteTimingGraft reward roots replacement) who ≤
      quittingTerminalPayoff reward
          (quittingRetainedTailFiniteTimingGraft reward roots tail) who +
        2 * R * quittingLiteralRootStackOpponentSurvival roots who := by
  rw [quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
  apply csSup_le (Set.range_nonempty _)
  rintro value ⟨choice, rfl⟩
  cases choice with
  | none =>
      have hexact :=
        quittingPureTimeDeviationPayoff_absolute_sub_crossTailPass_eq
          reward roots replacement tail who none
      have hreplacement := abs_quittingTerminalPayoff_le reward
        (Function.update replacement who
          (quittingPureTimeBehaviorStrategy reward who none)) who hreward
      have htailPayoff := abs_quittingTerminalPayoff_le reward tail who hreward
      have htail : quittingPureTimeDeviationPayoff reward replacement who none -
          quittingTerminalPayoff reward tail who ≤ 2 * R := by
        unfold quittingPureTimeDeviationPayoff
        linarith [le_of_abs_le hreplacement, neg_le_of_abs_le htailPayoff]
      have hscaled := mul_le_mul_of_nonneg_left htail
        (quittingLiteralRootStackOpponentSurvival_nonneg roots who)
      have hpass := nash.pass_le who
      simp only [quittingAbsolutePureTime] at hexact
      nlinarith
  | some time =>
      by_cases hearly : time < roots.length
      · rw [quittingPureTimeDeviationPayoff_retainedTail_eq_of_lt
          reward roots replacement tail who time hearly]
        exact (nash.finiteStop_le who time hearly).trans
          (le_add_of_nonneg_right <| mul_nonneg (mul_nonneg (by norm_num) hR)
            (quittingLiteralRootStackOpponentSurvival_nonneg roots who))
      · let delay := time - roots.length
        have htime : roots.length + delay = time := by
          dsimp only [delay]
          omega
        have hexact :=
          quittingPureTimeDeviationPayoff_absolute_sub_crossTailPass_eq
            reward roots replacement tail who (some delay)
        have hreplacement := abs_quittingTerminalPayoff_le reward
          (Function.update replacement who
            (quittingPureTimeBehaviorStrategy reward who (some delay))) who
          hreward
        have htailPayoff := abs_quittingTerminalPayoff_le reward tail who hreward
        have htail : quittingPureTimeDeviationPayoff reward replacement who
            (some delay) - quittingTerminalPayoff reward tail who ≤ 2 * R := by
          unfold quittingPureTimeDeviationPayoff
          linarith [le_of_abs_le hreplacement, neg_le_of_abs_le htailPayoff]
        have hscaled := mul_le_mul_of_nonneg_left htail
          (quittingLiteralRootStackOpponentSurvival_nonneg roots who)
        have hpass := nash.pass_le who
        rw [show quittingAbsolutePureTime roots.length (some delay) =
          some time by simp [quittingAbsolutePureTime, htime]] at hexact
        nlinarith

/-- Replacing the tail by a punishment whose cap is below the retained
payoff leaves the host with debt at most reward diameter times joint return.
-/
theorem IsQuittingRetainedTailFiniteTimingNash.hostPunishmentDebt_le
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {roots : List (ι → PMF Bool)}
    {tail : (quittingGame reward).BehaviorProfile}
    (nash : IsQuittingRetainedTailFiniteTimingNash reward roots tail)
    (punishment : (quittingGame reward).BehaviorProfile)
    (host : ι) (R : ℝ)
    (hreward : ∀ S player, |reward S player| ≤ R)
    (hcap : quittingContinuationBestResponseValue reward punishment host ≤
      quittingTerminalPayoff reward tail host) :
    quittingTerminalDeviationDebt reward
        (quittingRetainedTailFiniteTimingGraft reward roots punishment) host ≤
      2 * R * quittingLiteralRootStackJointSurvival roots := by
  have hbest := nash.replacementBestResponseValue_le punishment host hcap
  have hpayoff := abs_quittingRetainedTailFiniteTimingGraft_payoff_sub_le
    reward roots tail punishment host R hreward
  unfold quittingTerminalDeviationDebt
  linarith [le_of_abs_le hpayoff]

/-- Every non-host coordinate of the punishment graft is bounded by reward
diameter times the sum of player-deleted and joint return. -/
theorem IsQuittingRetainedTailFiniteTimingNash.punishmentDebt_le
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {roots : List (ι → PMF Bool)}
    {tail : (quittingGame reward).BehaviorProfile}
    (nash : IsQuittingRetainedTailFiniteTimingNash reward roots tail)
    (punishment : (quittingGame reward).BehaviorProfile)
    (who : ι) (R : ℝ) (hR : 0 ≤ R)
    (hreward : ∀ S player, |reward S player| ≤ R) :
    quittingTerminalDeviationDebt reward
        (quittingRetainedTailFiniteTimingGraft reward roots punishment) who ≤
      2 * R * (quittingLiteralRootStackOpponentSurvival roots who +
        quittingLiteralRootStackJointSurvival roots) := by
  have hbest := nash.replacementBestResponseValue_le_add
    punishment who R hR hreward
  have hpayoff := abs_quittingRetainedTailFiniteTimingGraft_payoff_sub_le
    reward roots tail punishment who R hreward
  unfold quittingTerminalDeviationDebt
  nlinarith [le_of_abs_le hpayoff]

end GameTheory
