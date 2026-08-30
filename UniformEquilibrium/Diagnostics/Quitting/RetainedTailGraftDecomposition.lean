/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CensoredFiniteClockOperationalEffect
import UniformEquilibrium.Diagnostics.Quitting.RetainedTailFiniteTimingRealization
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.ContinuePrefixAtomAccess

/-!
# Absolute decomposition of a retained-tail finite timing graft

`quittingRetainedTailFiniteTimingGraft` runs a finite word of Bernoulli
product roots and then hands play to a behavioral tail.  This file records the
absolute identities relating one such graft to the graft of the same word onto
the all-Continue tail, in which nobody ever quits after the word.

Three identities are stated.  The prescribed payoff splits as the all-Continue
value plus `quittingLiteralRootStackJointSurvival` times the tail payoff.  A
deterministic stop strictly inside the word absorbs before the tail is ever
reached, so its payoff does not move; the pure-time gain therefore loses
exactly the same joint-survival multiple of the tail payoff.  A player who
passes the whole word instead keeps its own continuation, so the value of
passing and then playing a tail strategy is the all-Continue passing value
plus `quittingLiteralRootStackOpponentSurvival` times the tail value of that
strategy.

Each identity is also given with its survival coefficient expanded as a
product of the playerwise `quittingLiteralRootStackOwnSurvival` coefficients.
No Nash, dispatch, alternative, or paid-edge conclusion is asserted here.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Prescribed payoff -/

omit [DecidableEq ι] in
/-- Absolute payoff decomposition of a retained-tail graft: the all-Continue
value plus the joint pass mass times the tail payoff. -/
theorem quittingTerminalPayoff_retainedTailFiniteTimingGraft_eq_add_jointSurvival_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff reward
        (quittingRetainedTailFiniteTimingGraft reward roots tail) who =
      quittingTerminalPayoff reward
          (quittingRetainedTailFiniteTimingHardGraft reward roots) who +
        quittingLiteralRootStackJointSurvival roots *
          quittingTerminalPayoff reward tail who := by
  have hsub :=
    quittingRetainedTailFiniteTimingGraft_payoff_sub_eq_jointReturn_mul
      reward roots tail (quittingAlwaysContinueProfile reward) who
  rw [quittingTerminalPayoff_quittingAlwaysContinue, sub_zero] at hsub
  unfold quittingRetainedTailFiniteTimingHardGraft
  linarith

omit [DecidableEq ι] in
/-- Payoff decomposition with the joint pass mass expanded as the product of
the playerwise pass coefficients. -/
theorem quittingTerminalPayoff_retainedTailFiniteTimingGraft_eq_add_prod_ownSurvival_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff reward
        (quittingRetainedTailFiniteTimingGraft reward roots tail) who =
      quittingTerminalPayoff reward
          (quittingRetainedTailFiniteTimingHardGraft reward roots) who +
        (∏ player, quittingLiteralRootStackOwnSurvival roots player) *
          quittingTerminalPayoff reward tail who := by
  rw [← quittingLiteralRootStackJointSurvival_eq_prod_ownSurvival]
  exact quittingTerminalPayoff_retainedTailFiniteTimingGraft_eq_add_jointSurvival_mul
    reward roots tail who

/-! ## Pure-time gain inside the word -/

/-- Absolute pure-time gain of a stop strictly inside the finite word.  The
deviation payoff is unchanged by the tail, so the gain against the grafted
profile is the all-Continue gain less the joint pass mass times the tail
payoff. -/
theorem quittingPureTimeDeviationPayoff_sub_terminalPayoff_graft_eq_sub_jointSurvival_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile) (who : ι)
    (time : ℕ) (htime : time < roots.length) :
    quittingPureTimeDeviationPayoff reward
          (quittingRetainedTailFiniteTimingGraft reward roots tail) who
          (some time) -
        quittingTerminalPayoff reward
          (quittingRetainedTailFiniteTimingGraft reward roots tail) who =
      quittingPureTimeDeviationPayoff reward
            (quittingRetainedTailFiniteTimingHardGraft reward roots) who
            (some time) -
          quittingTerminalPayoff reward
            (quittingRetainedTailFiniteTimingHardGraft reward roots) who -
        quittingLiteralRootStackJointSurvival roots *
          quittingTerminalPayoff reward tail who := by
  have hdeviation := quittingPureTimeDeviationPayoff_retainedTail_eq_of_lt
    reward roots tail (quittingAlwaysContinueProfile reward) who time htime
  have hpayoff :=
    quittingTerminalPayoff_retainedTailFiniteTimingGraft_eq_add_jointSurvival_mul
      reward roots tail who
  unfold quittingRetainedTailFiniteTimingHardGraft at hpayoff ⊢
  rw [hdeviation]
  linarith

/-- Pure-time gain inside the word with the joint pass mass expanded as the
product of the playerwise pass coefficients. -/
theorem quittingPureTimeDeviationPayoff_sub_terminalPayoff_graft_eq_sub_prod_ownSurvival_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile) (who : ι)
    (time : ℕ) (htime : time < roots.length) :
    quittingPureTimeDeviationPayoff reward
          (quittingRetainedTailFiniteTimingGraft reward roots tail) who
          (some time) -
        quittingTerminalPayoff reward
          (quittingRetainedTailFiniteTimingGraft reward roots tail) who =
      quittingPureTimeDeviationPayoff reward
            (quittingRetainedTailFiniteTimingHardGraft reward roots) who
            (some time) -
          quittingTerminalPayoff reward
            (quittingRetainedTailFiniteTimingHardGraft reward roots) who -
        (∏ player, quittingLiteralRootStackOwnSurvival roots player) *
          quittingTerminalPayoff reward tail who := by
  rw [← quittingLiteralRootStackJointSurvival_eq_prod_ownSurvival]
  exact
    quittingPureTimeDeviationPayoff_sub_terminalPayoff_graft_eq_sub_jointSurvival_mul
      reward roots tail who time htime

/-! ## Passing the whole word -/

/-- Absolute decomposition of the value of passing the whole word: the
all-Continue passing value plus the player-deleted pass mass times the tail
payoff. -/
theorem quittingTerminalPayoff_retainedTailFiniteTimingPassProfile_eq_add_opponentSurvival_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff reward
        (quittingRetainedTailFiniteTimingPassProfile reward roots tail who)
        who =
      quittingTerminalPayoff reward
          (quittingRetainedTailFiniteTimingPassProfile reward roots
            (quittingAlwaysContinueProfile reward) who) who +
        quittingLiteralRootStackOpponentSurvival roots who *
          quittingTerminalPayoff reward tail who := by
  have hgraft :=
    quittingTerminalPayoff_retainedTailFiniteTimingGraft_eq_add_jointSurvival_mul
      reward (quittingLiteralRootStackForceContinue roots who) tail who
  rw [quittingLiteralRootStackJointSurvival_forceContinue] at hgraft
  unfold quittingRetainedTailFiniteTimingHardGraft at hgraft
  exact hgraft

/-- Pass-through value of the finite word.  Continuing through the whole word
and then playing a pure tail strategy is worth the all-Continue passing value
plus the player-deleted pass mass times the tail value of that strategy. -/
theorem quittingPureTimeDeviationPayoff_absolute_eq_add_opponentSurvival_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile) (who : ι)
    (choice : Option ℕ) :
    quittingPureTimeDeviationPayoff reward
        (quittingRetainedTailFiniteTimingGraft reward roots tail) who
        (quittingAbsolutePureTime roots.length choice) =
      quittingTerminalPayoff reward
          (quittingRetainedTailFiniteTimingPassProfile reward roots
            (quittingAlwaysContinueProfile reward) who) who +
        quittingLiteralRootStackOpponentSurvival roots who *
          quittingPureTimeDeviationPayoff reward tail who choice := by
  have hlate := quittingPureTimeDeviationPayoff_absolute_sub_pass_eq
    reward roots tail who choice
  have hpass :=
    quittingTerminalPayoff_retainedTailFiniteTimingPassProfile_eq_add_opponentSurvival_mul
      reward roots tail who
  rw [mul_sub] at hlate
  linarith

/-- Pass-through value with the player-deleted pass mass expanded as the
product of the other players' pass coefficients. -/
theorem quittingPureTimeDeviationPayoff_absolute_eq_add_prod_erase_ownSurvival_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile) (who : ι)
    (choice : Option ℕ) :
    quittingPureTimeDeviationPayoff reward
        (quittingRetainedTailFiniteTimingGraft reward roots tail) who
        (quittingAbsolutePureTime roots.length choice) =
      quittingTerminalPayoff reward
          (quittingRetainedTailFiniteTimingPassProfile reward roots
            (quittingAlwaysContinueProfile reward) who) who +
        (∏ other ∈ Finset.univ.erase who,
            quittingLiteralRootStackOwnSurvival roots other) *
          quittingPureTimeDeviationPayoff reward tail who choice := by
  rw [← quittingLiteralRootStackOpponentSurvival_eq_prod_ownSurvival_erase]
  exact quittingPureTimeDeviationPayoff_absolute_eq_add_opponentSurvival_mul
    reward roots tail who choice

end GameTheory
