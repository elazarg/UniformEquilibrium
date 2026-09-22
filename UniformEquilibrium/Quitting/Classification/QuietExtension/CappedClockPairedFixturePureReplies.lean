/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPairedFixtureTerminal
import UniformEquilibrium.Quitting.Paths.FirstStoppingOutcomeCoalition
import UniformEquilibrium.Quitting.Paths.StoppingLawOperationalDistance
import UniformEquilibrium.Quitting.Root.PureTimeCapPrefixSelection

/-!
# Pure-date replies in the paired capped-clock fixture

This module computes the payoff of every deterministic unilateral reply to
the literal one-date profile.  The three cases are Quit at date zero, Quit at
any strictly later finite date, and Never.
-/

noncomputable section

namespace GameTheory
namespace CappedClockPairedFixturePureReplies

open _root_.Math.Probability Math.PMFProduct
open CappedClockPairedFamily CappedClockPairedFixtureTerminal

/-- Terminal payoff of one deterministic Quit-date/Never reply to the
displayed one-date profile. -/
def pureReplyValue (who : Player) (choice : Option ℕ) : ℝ :=
  quittingTerminalPayoff exampleReward
    (Function.update profile who
      (quittingPureTimeBehaviorStrategy exampleReward who choice)) who

private theorem pureTimeProfileBehavior_allNever :
    quittingPureTimeProfileBehavior exampleReward (fun _ : Player => none) =
      quittingAlwaysContinueProfile exampleReward := by
  rfl

private theorem allContinue_pureTime_some
    (who : Player) (time : ℕ) :
    quittingTerminalPayoff exampleReward
        (Function.update (quittingAlwaysContinueProfile exampleReward) who
          (quittingPureTimeBehaviorStrategy exampleReward who (some time)))
        who = 1 := by
  have hbehavior := quittingPureTimeProfileBehavior_update exampleReward
    (fun _ : Player => none) who (some time)
  rw [pureTimeProfileBehavior_allNever] at hbehavior
  rw [← hbehavior]
  rw [quittingTerminalPayoff_pureTimeProfileBehavior_eq_firstStoppingOutcome]
  have houtcome :
      quittingFirstStoppingOutcome
          (Function.update (fun _ : Player => none) who (some time)) =
        some ⟨{who}, Finset.singleton_nonempty who⟩ := by
    apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
      (time := time)
    · intro player hplayer
      have heq : player = who := Finset.mem_singleton.mp hplayer
      subst player
      simp
    · intro player hplayer
      have hne : player ≠ who := by simpa using hplayer
      rw [Function.update_of_ne hne]
      simp [quittingStoppingTimeValue]
  rw [houtcome]
  simpa only [quittingTerminalOutcomeReward, quittingSingletonTerminal] using
    singleton_self_eq_one exampleReward_conditions who

/-- Immediate deterministic replies have the displayed four payoff values. -/
theorem pureReplyValue_zero :
    (fun who => pureReplyValue who (some 0)) =
      ![(13 / 9 : ℝ), 2, 2 / 3, -2 / 9] := by
  funext who
  unfold pureReplyValue profile quittingOneDateThenNeverProfile
  rw [quittingTerminalPayoff_rootThen_pureTime_zero_eq_quitPayoff]
  simp_rw [quittingTerminalPayoff_quittingAlwaysContinue]
  fin_cases who
  all_goals
    unfold quittingRootQuitPayoff quittingRootExpectedPayoff
    rw [Math.PMFProduct.expect_pmfPi_fin4]
    simp [root, twoThirdsCoin, quittingRootPayoff, quittingQuitters,
      exampleReward, expect_eq_sum]
    norm_num

/-- Every strictly later finite deterministic reply has the same displayed
payoff, independently of its positive date. -/
theorem pureReplyValue_some_succ (time : ℕ) :
    (fun who => pureReplyValue who (some (time + 1))) =
      ![(1 : ℝ), 2, 2 / 3, 4 / 3] := by
  funext who
  unfold pureReplyValue profile quittingOneDateThenNeverProfile
  rw [show some (time + 1) = (some time).map Nat.succ by rfl]
  rw [quittingTerminalPayoff_rootThen_pureTime_map_succ_eq_continuePayoff]
  simp_rw [quittingTerminalPayoff_quittingAlwaysContinue]
  rw [allContinue_pureTime_some]
  fin_cases who
  all_goals
    unfold quittingRootContinuePayoff quittingRootExpectedPayoff
    rw [Math.PMFProduct.expect_pmfPi_fin4]
    simp [root, twoThirdsCoin, quittingRootPayoff, quittingQuitters,
      exampleReward, expect_eq_sum] <;> norm_num

/-- Never replies have the displayed four payoff values. -/
theorem pureReplyValue_none :
    (fun who => pureReplyValue who none) =
      ![(8 / 9 : ℝ), 2, 2 / 3, 4 / 3] := by
  funext who
  unfold pureReplyValue profile quittingOneDateThenNeverProfile
  rw [show none = (none : Option ℕ).map Nat.succ by rfl]
  rw [quittingTerminalPayoff_rootThen_pureTime_map_succ_eq_continuePayoff]
  simp_rw [quittingTerminalPayoff_quittingAlwaysContinue]
  rw [quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue]
  have hupdate :
      Function.update (quittingAlwaysContinueProfile exampleReward) who
          (quittingAlwaysContinueStrategy exampleReward who) =
        quittingAlwaysContinueProfile exampleReward := by
    apply Function.update_eq_self
  rw [hupdate, quittingTerminalPayoff_quittingAlwaysContinue]
  fin_cases who
  all_goals
    unfold quittingRootContinuePayoff quittingRootExpectedPayoff
    rw [Math.PMFProduct.expect_pmfPi_fin4]
    simp [root, twoThirdsCoin, quittingRootPayoff, quittingQuitters,
      exampleReward, expect_eq_sum] <;> norm_num

end CappedClockPairedFixturePureReplies
end GameTheory
