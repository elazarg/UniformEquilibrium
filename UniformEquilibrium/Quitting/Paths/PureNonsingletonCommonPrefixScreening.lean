/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Root.LiteralExactPrefixStack
import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum

/-!
# Pure nonsingleton screening behind a common literal prefix

A pure quitting coalition with at least two members absorbs even after any
one player's complete behavioral replacement.  Its terminal semantic pair is
therefore independent of the counterfactual behavioral tail.  Prepending the
same finite literal root word preserves that semantic equality exactly.

The result screens only changes strictly behind the retained pure row.  It
does not compare different prefix words or roots with positive continuation
probability after a unilateral replacement.
-/

noncomputable section

namespace GameTheory

open Math.Probability
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A common literal root word preserves equality of complete terminal
semantic pairs, including unrestricted behavioral best-response caps. -/
theorem quittingTerminalSemanticPair_literalRootStack_congr
    (roots : List (ι → PMF Bool))
    (first second : (quittingGame reward).BehaviorProfile)
    (htails : quittingTerminalSemanticPair reward first =
      quittingTerminalSemanticPair reward second) :
    quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward roots first) =
      quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward roots second) := by
  induction roots with
  | nil => simpa
  | cons root roots ih =>
      simp only [quittingLiteralRootStackProfile_cons,
        quittingTerminalSemanticPair_rootThenContinuation]
      rw [ih]

/-- A pure coalition with at least two sure quitters screens arbitrary tails
even after the same finite literal root word is prepended. -/
theorem quittingTerminalSemanticPair_literalRootStack_pureSet_screen
    (roots : List (ι → PMF Bool))
    (coalition : Finset ι) (hcard : 2 ≤ coalition.card)
    (first second : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward roots
          (quittingRootThenContinuationProfile reward
            (quittingPureSetRoot coalition) first)) =
      quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward roots
          (quittingRootThenContinuationProfile reward
            (quittingPureSetRoot coalition) second)) := by
  apply quittingTerminalSemanticPair_literalRootStack_congr
  rw [quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card
      reward coalition hcard first,
    quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card
      reward coalition hcard second]

/-- Prescribed terminal payoffs are unchanged by a tail replacement behind
the same pure nonsingleton screen and common word. -/
theorem quittingTerminalPayoff_literalRootStack_pureSet_screen
    (roots : List (ι → PMF Bool))
    (coalition : Finset ι) (hcard : 2 ≤ coalition.card)
    (first second : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff reward
        (quittingLiteralRootStackProfile reward roots
          (quittingRootThenContinuationProfile reward
            (quittingPureSetRoot coalition) first)) who =
      quittingTerminalPayoff reward
        (quittingLiteralRootStackProfile reward roots
          (quittingRootThenContinuationProfile reward
            (quittingPureSetRoot coalition) second)) who := by
  exact congrArg (fun pair : QuittingTerminalSemanticPair ι ↦ pair.1 who)
    (quittingTerminalSemanticPair_literalRootStack_pureSet_screen
      roots coalition hcard first second)

/-- Unrestricted behavioral best-response caps are unchanged by the screened
tail replacement. -/
theorem quittingContinuationBestResponseValue_literalRootStack_pureSet_screen
    (roots : List (ι → PMF Bool))
    (coalition : Finset ι) (hcard : 2 ≤ coalition.card)
    (first second : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingContinuationBestResponseValue reward
        (quittingLiteralRootStackProfile reward roots
          (quittingRootThenContinuationProfile reward
            (quittingPureSetRoot coalition) first)) who =
      quittingContinuationBestResponseValue reward
        (quittingLiteralRootStackProfile reward roots
          (quittingRootThenContinuationProfile reward
            (quittingPureSetRoot coalition) second)) who := by
  exact congrArg (fun pair : QuittingTerminalSemanticPair ι ↦ pair.2 who)
    (quittingTerminalSemanticPair_literalRootStack_pureSet_screen
      roots coalition hcard first second)

/-- Every coordinate debt is unchanged by the screened tail replacement. -/
theorem quittingTerminalSemanticDebt_literalRootStack_pureSet_screen
    (roots : List (ι → PMF Bool))
    (coalition : Finset ι) (hcard : 2 ≤ coalition.card)
    (first second : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingLiteralRootStackProfile reward roots
            (quittingRootThenContinuationProfile reward
              (quittingPureSetRoot coalition) first))) who =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingLiteralRootStackProfile reward roots
            (quittingRootThenContinuationProfile reward
              (quittingPureSetRoot coalition) second))) who := by
  rw [quittingTerminalSemanticPair_literalRootStack_pureSet_screen
    roots coalition hcard first second]

/-- The coordinate-debt change of a screened tail replacement is literally
zero. -/
theorem quittingTerminalSemanticDebt_sub_literalRootStack_pureSet_screen_eq_zero
    (roots : List (ι → PMF Bool))
    (coalition : Finset ι) (hcard : 2 ≤ coalition.card)
    (first second : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots
              (quittingRootThenContinuationProfile reward
                (quittingPureSetRoot coalition) second))) who -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots
              (quittingRootThenContinuationProfile reward
                (quittingPureSetRoot coalition) first))) who = 0 := by
  rw [quittingTerminalSemanticDebt_literalRootStack_pureSet_screen
    roots coalition hcard first second, sub_self]

/-- Total terminal-semantic debt is unchanged by the screened tail
replacement. -/
theorem quittingTerminalSemanticDebtSum_literalRootStack_pureSet_screen
    (roots : List (ι → PMF Bool))
    (coalition : Finset ι) (hcard : 2 ≤ coalition.card)
    (first second : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingLiteralRootStackProfile reward roots
            (quittingRootThenContinuationProfile reward
              (quittingPureSetRoot coalition) first))) =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingLiteralRootStackProfile reward roots
            (quittingRootThenContinuationProfile reward
              (quittingPureSetRoot coalition) second))) := by
  rw [quittingTerminalSemanticPair_literalRootStack_pureSet_screen
    roots coalition hcard first second]

/-- The total-debt change of a screened tail replacement is literally zero. -/
theorem quittingTerminalSemanticDebtSum_sub_literalRootStack_pureSet_screen_eq_zero
    (roots : List (ι → PMF Bool))
    (coalition : Finset ι) (hcard : 2 ≤ coalition.card)
    (first second : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots
              (quittingRootThenContinuationProfile reward
                (quittingPureSetRoot coalition) second))) -
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots
              (quittingRootThenContinuationProfile reward
                (quittingPureSetRoot coalition) first))) = 0 := by
  rw [quittingTerminalSemanticDebtSum_literalRootStack_pureSet_screen
    roots coalition hcard first second, sub_self]

end GameTheory
