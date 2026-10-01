import UniformEquilibrium.Quitting.Examples.StrictPatientWithdrawalTable
import UniformEquilibrium.Quitting.Root.FinFourEndpointRowSum
import UniformEquilibrium.Quitting.Root.OneDateNeverNashDebt
import UniformEquilibrium.Quitting.Root.PureTimeCapPrefixSelection
import UniformEquilibrium.Quitting.Root.AlwaysContinuePureTimeReplies
import UniformEquilibrium.Quitting.Stationary.BestResponse
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformization

/-! # The literal strict patient date-zero profile and all complete responses

The root has hazards (1/2,2/5,1,0) and is followed by Never. Its full cap is
computed from the canonical root/continuation recursion, including the sure
quitter's counterfactual Never and every positive finite deadline. The same
profile, not a new profile selected for each accuracy, uniformizes at its
actual terminal payoff. It is not an input to the raw class theorem.
-/

noncomputable section

namespace GameTheory.StrictPatientWithdrawal

open GuardedCrossedResponseExamples QuittingFinFourEndpointRows Math.Finset
open Filter _root_.Math.Probability

def hazard : Fin 4 → ℝ := ![1 / 2, 2 / 5, 1, 0]

theorem hazard_bounds (who : Fin 4) : 0 ≤ hazard who ∧ hazard who ≤ 1 := by
  fin_cases who <;> norm_num [hazard]

def root : Fin 4 → PMF Bool :=
  rootOfHazard hazard (fun who => (hazard_bounds who).1) (fun who => (hazard_bounds who).2)

theorem root_hazard : hazardOfRoot root = hazard := hazardOfRoot_rootOfHazard _ _ _

/-- The actual source behavioral profile, not a supplied finite-menu witness. -/
def profile : (quittingGame reward).BehaviorProfile :=
  quittingOneDateThenNeverProfile reward root

def value : Payoff (Fin 4) := ![0, -1, -2 / 5, 7 / 10]
def quitValue : Payoff (Fin 4) := ![0, -1, -2 / 5, -4 / 5]
def neverValue : Payoff (Fin 4) := ![0, -1, -7 / 10, 7 / 10]

theorem sigma_eq (who : Fin 4) :
    sigmaValue (weightOfReward reward) hazard who = quitValue who := by
  rw [sigmaValue_eq_pureQuitEndpointRowSum]
  fin_cases who
  all_goals
    simp only [pureQuitEndpointRowSum, Fin.sum_univ_succ]
    simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ, hazard]
    norm_num +decide [weightOfReward, reward, coalitionCode, quitValue]

theorem excluded_eq (who : Fin 4) :
    excludedValue (weightOfReward reward) hazard who = neverValue who := by
  rw [excludedValue_eq_excludedEndpointRowSum]
  fin_cases who
  all_goals
    simp only [excludedEndpointRowSum, Fin.sum_univ_succ]
    simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ, hazard]
    norm_num +decide [weightOfReward, reward, coalitionCode, neverValue]

theorem deletedSurvival_eq (who : Fin 4) :
    continueMassExcl hazard who = ![0, 0, 3 / 10, 0] who := by
  fin_cases who
  · change continueMassExcl hazard (0 : Fin 4) = 0
    rw [continueMassExcl, show Finset.univ.erase (0 : Fin 4) = {1, 2, 3} by decide]
    norm_num [hazard]
  · change continueMassExcl hazard (1 : Fin 4) = 0
    rw [continueMassExcl, show Finset.univ.erase (1 : Fin 4) = {0, 2, 3} by decide]
    norm_num [hazard]
  · change continueMassExcl hazard (2 : Fin 4) = 3 / 10
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
      neverValue who := by
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
      fin_cases who <;> norm_num

/-- Never is priced at its actual value, including the sure player's counterfactual. -/
theorem neverPayoff_eq (who : Fin 4) :
    quittingTerminalPayoff reward
        (Function.update profile who (quittingPureTimeBehaviorStrategy reward who none)) who =
      neverValue who := shiftedReply_eq who none

/-- Every positive finite deadline is retained, not erased by a menu restriction. -/
theorem positiveFinitePayoff_eq (who : Fin 4) (time : ℕ) (htime : 0 < time) :
    quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who (some time))) who = neverValue who := by
  obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero htime.ne'
  exact shiftedReply_eq who (some previous)

theorem terminalNash :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0 profile := by
  intro who deviation
  have h := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward profile who deviation
  rw [fullCap_eq] at h
  simpa only [terminalPayoff_eq, add_zero] using h

/-- The SAME actual profile works for every accuracy and all later horizons. -/
theorem sameProfile_uniform (error : ℝ) (herror : 0 < error) :
    ∃ threshold : ℕ, ∀ horizon, threshold ≤ horizon →
      (quittingGame reward).IsεHorizonNash none horizon error profile ∧
        ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon profile who - value who| ≤
          error := by
  obtain ⟨nashThreshold, hnash⟩ :=
    quittingGame_isUniformεEquilibrium_of_terminalNash reward profile herror terminalNash
  have hdelivery : ∀ᶠ horizon : ℕ in atTop, ∀ who,
      |(quittingGame reward).finiteAveragePayoff none horizon profile who - value who| < error := by
    apply Filter.eventually_all.mpr
    intro who
    have hlimit := (tendsto_finiteAveragePayoff_quittingGame reward profile who).sub_const
      (value who)
    rw [terminalPayoff_eq, sub_self] at hlimit
    have habs := hlimit.abs
    rw [abs_zero] at habs
    exact (tendsto_order.mp habs).2 error herror
  obtain ⟨deliveryThreshold, hdelivery⟩ := Filter.eventually_atTop.mp hdelivery
  refine ⟨max nashThreshold deliveryThreshold, fun horizon hhorizon => ?_⟩
  exact ⟨hnash horizon ((Nat.le_max_left _ _).trans hhorizon),
    fun who => (hdelivery horizon ((Nat.le_max_right _ _).trans hhorizon) who).le⟩

theorem actualValue_uniformPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none value := by
  intro error herror
  obtain ⟨threshold, hthreshold⟩ := sameProfile_uniform error herror
  exact ⟨profile, threshold, hthreshold⟩

end GameTheory.StrictPatientWithdrawal
