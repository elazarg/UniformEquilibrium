/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.OneDateProductRootCaps
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Thin one-date adapters for canonical pure sure-exit sets

This module adds only literal profile identities around the canonical
`quittingPureSetRoot` interface. Complete behavioral caps and debts are
delegated to `SureExitSet`; no alternative pure-set theory is reproduced.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct QuittingSureSetOwnerRepair

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- Exactly one pure coalition root followed by all-Continue forever. -/
def quittingPureCoalitionOneDateNeverProfile
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (coalition : Finset iota) : (quittingGame reward).BehaviorProfile :=
  quittingOneDateThenNeverProfile reward (quittingPureSetRoot coalition)

/-- Replacing a coordinate by Never literally deletes it from the one-date
coalition. -/
theorem update_pureCoalitionOneDateNever_with_never
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (coalition : Finset iota) (who : iota) :
    Function.update
        (quittingPureCoalitionOneDateNeverProfile reward coalition) who
        (quittingPureTimeBehaviorStrategy reward who none) =
      quittingPureCoalitionOneDateNeverProfile reward (coalition.erase who) := by
  funext player time history
  by_cases hplayer : player = who
  · subst player
    rw [Function.update_self]
    cases time <;>
      simp [quittingPureCoalitionOneDateNeverProfile,
        quittingOneDateThenNeverProfile, quittingRootThenContinuationProfile,
        quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
        quittingPureSetRoot, quittingSetAction, quittingAlwaysContinueProfile,
        StochasticGame.stationaryBehaviorProfile]; rfl
  · rw [Function.update_of_ne hplayer]
    cases time <;>
      simp [quittingPureCoalitionOneDateNeverProfile,
        quittingOneDateThenNeverProfile, quittingRootThenContinuationProfile,
        quittingPureSetRoot, quittingSetAction, hplayer]

/-- Replacing a coordinate by immediate Quit literally inserts it into the
one-date coalition. -/
theorem update_pureCoalitionOneDateNever_with_quitNow
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (coalition : Finset iota) (who : iota) :
    Function.update
        (quittingPureCoalitionOneDateNeverProfile reward coalition) who
        (quittingPureTimeBehaviorStrategy reward who (some 0)) =
      quittingPureCoalitionOneDateNeverProfile reward (insert who coalition) := by
  funext player time history
  by_cases hplayer : player = who
  · subst player
    rw [Function.update_self]
    cases time <;>
      simp [quittingPureCoalitionOneDateNeverProfile,
        quittingOneDateThenNeverProfile, quittingRootThenContinuationProfile,
        quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
        quittingPureSetRoot, quittingSetAction, quittingAlwaysContinueProfile,
        StochasticGame.stationaryBehaviorProfile]; rfl
  · rw [Function.update_of_ne hplayer]
    cases time <;>
      simp [quittingPureCoalitionOneDateNeverProfile,
        quittingOneDateThenNeverProfile, quittingRootThenContinuationProfile,
        quittingPureSetRoot, quittingSetAction, hplayer]

/-- The complete terminal semantic pair of a nonsingleton one-date coalition
is the canonical pure-set membership-toggle pair. -/
theorem quittingTerminalSemanticPair_pureCoalitionOneDateNever_eq
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (coalition : Finset iota) (hcard : 2 ≤ coalition.card) :
    quittingTerminalSemanticPair reward
        (quittingPureCoalitionOneDateNeverProfile reward coalition) =
      (quittingSetReward reward coalition,
        fun who ↦ max (quittingSetReward reward (insert who coalition) who)
          (quittingSetReward reward (coalition.erase who) who)) := by
  simpa only [quittingPureCoalitionOneDateNeverProfile,
    quittingOneDateThenNeverProfile] using
    quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card
      reward coalition hcard (quittingAlwaysContinueProfile reward)

/-- The prescribed payoff is the displayed nonempty coalition reward. -/
theorem quittingTerminalPayoff_pureCoalitionOneDateNever
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (coalition : Finset iota) (hnonempty : coalition.Nonempty) (who : iota) :
    quittingTerminalPayoff reward
        (quittingPureCoalitionOneDateNeverProfile reward coalition) who =
      quittingSetReward reward coalition who := by
  unfold quittingPureCoalitionOneDateNeverProfile
    quittingOneDateThenNeverProfile
  exact quittingTerminalPayoff_pureSetRootThenContinuation_eq_setReward
    coalition hnonempty (quittingAlwaysContinueProfile reward) who

/-- Exact unrestricted behavioral debt at a nonsingleton one-date pure
coalition, inherited from the canonical pure-set terminal semantic pair. -/
theorem quittingTerminalSemanticDebt_pureCoalitionOneDateNever_eq
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (coalition : Finset iota) (hcard : 2 ≤ coalition.card) (who : iota) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingPureCoalitionOneDateNeverProfile reward coalition)) who =
      max (quittingSetReward reward (insert who coalition) who)
          (quittingSetReward reward (coalition.erase who) who) -
        quittingSetReward reward coalition who := by
  rw [quittingTerminalSemanticPair_pureCoalitionOneDateNever_eq
    reward coalition hcard]
  rfl

end GameTheory
