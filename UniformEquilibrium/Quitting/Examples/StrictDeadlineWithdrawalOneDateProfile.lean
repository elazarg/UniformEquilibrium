import UniformEquilibrium.Quitting.Examples.StrictDeadlineWithdrawalTable
import UniformEquilibrium.Quitting.Root.FinFourEndpointRowSum
import UniformEquilibrium.Quitting.Root.OneDateNeverNashDebt
import UniformEquilibrium.Quitting.Root.PureTimeCapPrefixSelection
import UniformEquilibrium.Quitting.Root.AlwaysContinuePureTimeReplies
import UniformEquilibrium.Quitting.Stationary.BestResponse
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-! # The literal strict deadline date-zero profile and all complete responses

The root has hazards (1/2,1/3,1,0) and is followed by Never. Its full cap is
computed from the canonical root/continuation recursion, including the sure
quitter's counterfactual Never and every positive finite deadline. The same
profile, not a new profile selected for each accuracy, uniformizes at its
actual terminal payoff. It is not an input to the raw class theorem.
-/

noncomputable section

namespace GameTheory.StrictDeadlineWithdrawal

open GuardedCrossedResponseExamples FinFourLastPlayerChild QuittingFinFourEndpointRows Math.Finset
open Filter _root_.Math.Probability

def hazard : Fin 4 → ℝ := ![1 / 2, 1 / 3, 1, 0]

theorem hazard_bounds (who : Fin 4) : 0 ≤ hazard who ∧ hazard who ≤ 1 := by
  fin_cases who <;> norm_num [hazard]

def root : Fin 4 → PMF Bool :=
  rootOfHazard hazard (fun who => (hazard_bounds who).1) (fun who => (hazard_bounds who).2)

theorem root_hazard : hazardOfRoot root = hazard := hazardOfRoot_rootOfHazard _ _ _

/-- The actual source behavioral profile, not a supplied finite-menu witness. -/
def profile : (quittingGame reward).BehaviorProfile :=
  quittingOneDateThenNeverProfile reward root

def value : Payoff (Fin 4) := ![2 / 3, -9 / 16, -11 / 48, 23 / 16]
def quitValue : Payoff (Fin 4) := ![2 / 3, -9 / 16, -11 / 48, 5 / 48]
def neverValue : Payoff (Fin 4) := ![2 / 3, -9 / 16, -17 / 24, 23 / 16]
def lateValue : Payoff (Fin 4) := ![2 / 3, -9 / 16, -35 / 48, 23 / 16]

theorem sigma_eq (who : Fin 4) :
    sigmaValue (weightOfReward reward) hazard who = quitValue who := by
  rw [sigmaValue_eq_pureQuitEndpointRowSum]
  fin_cases who
  all_goals simp only [pureQuitEndpointRowSum, Fin.sum_univ_succ]
  all_goals simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ, hazard]
  all_goals norm_num +decide [weightOfReward, reward, integerReward, terminalShift,
      coalitionCode, quitValue]

theorem excluded_eq (who : Fin 4) :
    excludedValue (weightOfReward reward) hazard who = neverValue who := by
  rw [excludedValue_eq_excludedEndpointRowSum]
  fin_cases who
  all_goals simp only [excludedEndpointRowSum, Fin.sum_univ_succ]
  all_goals simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ, hazard]
  all_goals norm_num +decide [weightOfReward, reward, integerReward, terminalShift,
      coalitionCode, neverValue]

theorem deletedSurvival_eq (who : Fin 4) :
    continueMassExcl hazard who = ![0, 0, 1 / 3, 0] who := by
  fin_cases who
  · change continueMassExcl hazard (0 : Fin 4) = 0
    rw [continueMassExcl, show Finset.univ.erase (0 : Fin 4) = {1, 2, 3} by decide]
    norm_num [hazard]
  · change continueMassExcl hazard (1 : Fin 4) = 0
    rw [continueMassExcl, show Finset.univ.erase (1 : Fin 4) = {0, 2, 3} by decide]
    norm_num [hazard]
  · change continueMassExcl hazard (2 : Fin 4) = 1 / 3
    rw [continueMassExcl, show Finset.univ.erase (2 : Fin 4) = {0, 1, 3} by decide]
    norm_num [hazard]
  · change continueMassExcl hazard (3 : Fin 4) = 0
    rw [continueMassExcl, show Finset.univ.erase (3 : Fin 4) = {0, 1, 2} by decide]
    norm_num [hazard]

theorem terminalPayoff_eq (who : Fin 4) :
    quittingTerminalPayoff reward profile who = value who := by
  unfold profile quittingOneDateThenNeverProfile
  rw [quittingTerminalPayoff_rootThenContinuation_eq]
  simp only [quittingTerminalPayoff_quittingAlwaysContinue]
  change quittingRootSuccessorPayoff reward 0 root who = _
  rw [quittingRootSuccessorPayoff_eq_endpointMix, quittingRootQuitPayoff_eq_sigmaValue,
    quittingRootContinuePayoff_eq_gammaValue, Math.PMFProduct.pmfBool_false_toReal]
  change hazardOfRoot root who * _ + (1 - hazardOfRoot root who) * _ = _
  rw [root_hazard, sigma_eq, gammaValue, excluded_eq]
  fin_cases who <;> norm_num [hazard, quitValue, neverValue, value]

/-- The full behavioral cap, not just the two displayed finite-menu payoffs. -/
theorem fullCap_eq (who : Fin 4) :
    quittingContinuationBestResponseValue reward profile who = value who := by
  unfold profile quittingOneDateThenNeverProfile
  rw [quittingContinuationBestResponseValue_rootThenContinuation_eq_max]
  simp only [quittingTerminalPayoff_quittingAlwaysContinue,
    quittingContinuationBestResponseValue_quittingAlwaysContinueProfile]
  rw [quittingRootQuitPayoff_eq_sigmaValue, quittingRootContinuePayoff_eq_gammaValue,
    root_hazard, sigma_eq, gammaValue, excluded_eq, deletedSurvival_eq]
  simp only [Function.update_self, quittingSingletonTerminal, singleton_payoffs]
  fin_cases who <;> norm_num [quitValue, neverValue, value]

theorem quitZeroPayoff_eq (who : Fin 4) :
    quittingTerminalPayoff reward
        (Function.update profile who (quittingPureTimeBehaviorStrategy reward who (some 0)))
        who = quitValue who := by
  unfold profile quittingOneDateThenNeverProfile
  rw [quittingTerminalPayoff_rootThen_pureTime_zero_eq_quitPayoff,
    quittingRootQuitPayoff_eq_sigmaValue, root_hazard, sigma_eq]

private theorem shiftedReply_eq (who : Fin 4) (choice : Option ℕ) :
    quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who (choice.map Nat.succ))) who =
      (match choice with | none => neverValue who | some _ => lateValue who) := by
  unfold profile quittingOneDateThenNeverProfile
  rw [quittingTerminalPayoff_rootThen_pureTime_map_succ_eq_continuePayoff,
    quittingRootContinuePayoff_eq_gammaValue, root_hazard, gammaValue,
    excluded_eq, deletedSurvival_eq, Function.update_self]
  cases choice with
  | none =>
      simp only [quittingTerminalPayoff_alwaysContinueProfile_update_pureTime_none,
        mul_zero, add_zero]
  | some time =>
      rw [quittingTerminalPayoff_alwaysContinueProfile_update_pureTime_some]
      simp only [quittingSingletonTerminal, singleton_payoffs]
      fin_cases who <;> norm_num [neverValue, lateValue]

/-- Never is priced at its actual value, including the sure player's counterfactual. -/
theorem neverPayoff_eq (who : Fin 4) :
    quittingTerminalPayoff reward
        (Function.update profile who (quittingPureTimeBehaviorStrategy reward who none)) who =
      neverValue who := shiftedReply_eq who none

/-- Every positive finite deadline is retained, not erased by a menu restriction. -/
theorem positiveFinitePayoff_eq (who : Fin 4) (time : ℕ) (htime : 0 < time) :
    quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who (some time))) who = lateValue who := by
  obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero htime.ne'
  exact shiftedReply_eq who (some previous)

theorem terminalNash :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0 profile := by
  intro who deviation
  have h := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward profile who deviation
  rw [fullCap_eq] at h
  simpa only [terminalPayoff_eq, add_zero] using h

/-- The sure quitter's strictly late and Never values differ by the literal solo correction. -/
theorem sureOwner_late_sub_never_eq (time : ℕ) (htime : 0 < time) :
    quittingTerminalPayoff reward
        (Function.update profile 2 (quittingPureTimeBehaviorStrategy reward 2 (some time))) 2 -
      quittingTerminalPayoff reward
        (Function.update profile 2 (quittingPureTimeBehaviorStrategy reward 2 none)) 2 =
      -1 / 48 := by
  rw [positiveFinitePayoff_eq _ time htime, neverPayoff_eq]
  norm_num [lateValue, neverValue]

/-- The SAME actual profile works for every accuracy and all later horizons. -/
theorem sameProfile_uniform (error : ℝ) (herror : 0 < error) :
    ∃ threshold : ℕ, ∀ horizon, threshold ≤ horizon →
      (quittingGame reward).IsεHorizonNash none horizon error profile ∧
        ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon profile who - value who| ≤
          error := by
  obtain ⟨_, threshold, hthreshold⟩ :=
    quittingGame_uniformPayoffWitnesses_of_terminalTargetAcceptance_family
      reward value (fun _ : Unit => profile) (fun accuracy haccuracy => by
        refine ⟨(), terminalNash.mono haccuracy.le, ?_⟩
        intro who
        rw [terminalPayoff_eq, sub_self, abs_zero]
        exact haccuracy.le) error herror
  exact ⟨threshold, hthreshold⟩

theorem actualValue_uniformPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none value := by
  intro error herror
  obtain ⟨threshold, hthreshold⟩ := sameProfile_uniform error herror
  exact ⟨profile, threshold, hthreshold⟩

end GameTheory.StrictDeadlineWithdrawal

