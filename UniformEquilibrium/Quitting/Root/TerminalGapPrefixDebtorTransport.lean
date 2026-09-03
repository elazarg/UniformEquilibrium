/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.LiteralPrefixDeviationTransport
import UniformEquilibrium.Quitting.Root.PureTimeCapPrefixSelection
import UniformEquilibrium.Quitting.Terminal.ExploitabilityGap
import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineCapSelection

/-!
# Selecting and transporting one terminal-gap debtor through a literal prefix

At a profile where one owner Quits surely by a finite deadline and has debt
strictly below a terminal gap, the gap selects a different player.  That
outsider has a complete cap attained at `Never` or by the deadline.  Copying
the displayed outsider strategy through any literal root word and using that
one selected cap response in the unchanged suffix transports its full debt by
the word's joint survival.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A sure-deadline owner whose debt lies below a nonnegative terminal gap
leaves one fixed outsider cap response.  The same response, copied through an
arbitrary literal prefix, has exact gain equal to joint survival times the
outsider's original complete debt and forces the corresponding prefixed debt
lower bound. -/
theorem HasTerminalExploitabilityGap.exists_outsider_pureTimeCap_with_prefix_debt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {gap : ℝ} (hexploit : HasTerminalExploitabilityGap reward gap)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι) (deadline : ℕ)
    (hownerDebt : quittingTerminalDeviationDebt reward profile owner < gap)
    (hsure : quittingProfileLiveRoot reward profile deadline owner =
      PMF.pure true)
    (roots : List (ι → PMF Bool))
    (survivalFloor : ℝ)
    (hsurvival : survivalFloor ≤
      quittingLiteralRootStackJointSurvival roots) :
    ∃ (who : ι) (choice : Option ℕ),
      who ≠ owner ∧
        (choice = none ∨ ∃ time ≤ deadline, choice = some time) ∧
        quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who choice)) who =
          quittingContinuationBestResponseValue reward profile who ∧
        gap ≤ quittingTerminalDeviationDebt reward profile who ∧
        quittingTerminalPayoff reward
              (Function.update
                (quittingLiteralRootStackProfile reward roots profile) who
                (quittingCopyLiteralRootStackThenDeviation reward roots who
                  (quittingPureTimeBehaviorStrategy reward who choice))) who -
            quittingTerminalPayoff reward
              (quittingLiteralRootStackProfile reward roots profile) who =
          quittingLiteralRootStackJointSurvival roots *
            quittingTerminalDeviationDebt reward profile who ∧
        survivalFloor * gap ≤
          quittingTerminalDeviationDebt reward
            (quittingLiteralRootStackProfile reward roots profile) who := by
  have hgap : 0 ≤ gap :=
    (quittingTerminalDeviationDebt_nonneg reward profile owner).trans
      hownerDebt.le
  obtain ⟨who, deviation, hdeviation⟩ := hexploit profile
  have hwho : who ≠ owner := by
    intro heq
    subst who
    have hcap :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward profile owner deviation
    unfold quittingTerminalDeviationDebt at hownerDebt
    linarith
  obtain ⟨choice, hchoiceRange, hchoiceCap⟩ :=
    exists_pureTime_le_deadline_or_never_terminalPayoff_eq_cap
      reward profile deadline hwho.symm hsure
  have hdebt : gap ≤ quittingTerminalDeviationDebt reward profile who := by
    have hcap :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward profile who deviation
    unfold quittingTerminalDeviationDebt
    linarith
  refine ⟨who, choice, hwho, hchoiceRange, hchoiceCap, hdebt, ?_, ?_⟩
  · rw [quittingTerminalPayoff_copyLiteralRootStackThenDeviation_sub_eq,
      hchoiceCap]
    rfl
  · apply quittingLiteralRootStackProfile_debt_ge_survivalFloor_mul_gain
      reward roots profile who
        (quittingPureTimeBehaviorStrategy reward who choice)
      hsurvival hgap
    rw [hchoiceCap]
    unfold quittingTerminalDeviationDebt at hdebt
    linarith

end GameTheory
