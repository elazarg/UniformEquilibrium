/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPairedFamily
import UniformEquilibrium.Quitting.Root.OneDateNeverNashDebt

/-!
# Terminal semantics of the paired capped-clock fixture

The explicit paired-family table has a one-date independent profile in which
player `0` quits surely, players `1` and `2` quit with probability `2/3`, and
player `3` continues surely.  After date zero every player continues forever.
This module computes both its prescribed terminal payoff and its unrestricted
behavioral response cap.
-/

noncomputable section

namespace GameTheory
namespace CappedClockPairedFixtureTerminal

open _root_.Math.Probability Math.PMFProduct
open CappedClockPairedFamily

/-- The two-thirds Quit marginal used by the two mixed players. -/
def twoThirdsCoin : PMF Bool :=
  Math.ProbabilityMassFunction.bernoulliBool (2 / 3 : ℝ)
    (by norm_num) (by norm_num)

@[simp] theorem twoThirdsCoin_true :
    (twoThirdsCoin true).toReal = 2 / 3 := by
  simp [twoThirdsCoin]

@[simp] theorem twoThirdsCoin_false :
    (twoThirdsCoin false).toReal = 1 / 3 := by
  simp [twoThirdsCoin]
  norm_num

/-- The literal date-zero root of the positive fixture. -/
def root : Player → PMF Bool :=
  ![PMF.pure true, twoThirdsCoin, twoThirdsCoin, PMF.pure false]

/-- The claimed common prescribed-payoff and full-cap vector. -/
def target : Payoff Player := ![13 / 9, 2, 2 / 3, 4 / 3]

/-- Play the displayed root once and then Continue forever. -/
def profile : (quittingGame exampleReward).BehaviorProfile :=
  quittingOneDateThenNeverProfile exampleReward root

/-- The literal one-date profile has the displayed prescribed terminal
payoff. -/
theorem profile_terminalPayoff :
    quittingTerminalPayoff exampleReward profile = target := by
  funext who
  unfold profile quittingOneDateThenNeverProfile
  rw [quittingTerminalPayoff_rootThenContinuation_eq]
  simp_rw [quittingTerminalPayoff_quittingAlwaysContinue]
  unfold quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4]
  fin_cases who
  all_goals
    simp [root, twoThirdsCoin, target, quittingRootPayoff, quittingQuitters,
      exampleReward, expect_eq_sum]
    norm_num

/-- The unrestricted behavioral response cap of the literal profile is the
same displayed vector. -/
theorem profile_continuationBestResponseValue :
    quittingContinuationBestResponseValue exampleReward profile = target := by
  funext who
  unfold profile quittingOneDateThenNeverProfile
  rw [quittingContinuationBestResponseValue_rootThenContinuation_eq_max]
  simp_rw [quittingTerminalPayoff_quittingAlwaysContinue]
  rw [quittingContinuationBestResponseValue_quittingAlwaysContinueProfile]
  have hsolo : exampleReward (quittingSingletonTerminal who) who = 1 :=
    singleton_self_eq_one exampleReward_conditions who
  rw [hsolo]
  fin_cases who
  all_goals
    unfold quittingRootQuitPayoff quittingRootContinuePayoff
      quittingRootExpectedPayoff
    rw [Math.PMFProduct.expect_pmfPi_fin4,
      Math.PMFProduct.expect_pmfPi_fin4]
    simp [root, twoThirdsCoin, target, quittingRootPayoff, quittingQuitters,
      exampleReward, expect_eq_sum]
    norm_num

/-- The literal one-date profile is exact terminal Nash against every
unilateral behavioral deviation. -/
theorem profile_exactTerminalNash :
    (quittingGame exampleReward).IsεAsymptoticNash
      (quittingTerminalPayoff exampleReward) 0 profile := by
  intro who deviation
  have hdeviation := quittingTerminalPayoff_update_le_continuationBestResponseValue
    exampleReward profile who deviation
  rw [congrFun profile_continuationBestResponseValue who] at hdeviation
  rw [congrFun profile_terminalPayoff who]
  simpa using hdeviation

end CappedClockPairedFixtureTerminal
end GameTheory
