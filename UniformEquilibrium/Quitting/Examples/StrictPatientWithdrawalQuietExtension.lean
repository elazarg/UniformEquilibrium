import UniformEquilibrium.Quitting.Examples.StrictPatientWithdrawalCertificate
import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalFinFourExistence
import UniformEquilibrium.Quitting.Terminal.TerminalExploitability

/-! # Actual quiet-debt and uniform-payoff consequences of the strict patient table -/

noncomputable section

namespace GameTheory.StrictPatientWithdrawal

/-- The same literal table supplies the certificate for its unique deleted outsider. -/
def certificateFamily (who : {who : Fin 4 // who = 3}) :
    PatientWithdrawalRewardCertificate (quittingChildWithOutsiderReward reward (· = 3) who) := by
  have heq : who = outside := Subtype.ext who.2
  subst who
  exact certificate

/-- The bound concerns every actual child behavioral profile and its complete caps. -/
theorem outsideDebt_le
    (profile : (quittingGame (quittingDeleteReward reward (· = 3))).BehaviorProfile) :
    quittingBehaviorDeviationPayoffCap reward
          (quittingLiftDeletedProfile reward (· = 3) profile) 3 -
        quittingTerminalPayoff reward
          (quittingLiftDeletedProfile reward (· = 3) profile) 3 ≤
      (1 / 2) * (quittingBehaviorDeviationPayoffCap
          (quittingDeleteReward reward (· = 3)) profile (child 0) -
        quittingTerminalPayoff (quittingDeleteReward reward (· = 3)) profile (child 0)) +
      3 * (quittingBehaviorDeviationPayoffCap
          (quittingDeleteReward reward (· = 3)) profile (child 2) -
        quittingTerminalPayoff (quittingDeleteReward reward (· = 3)) profile (child 2)) := by
  have h := quittingLiftDeletedProfile_outsideDebt_le_of_patientWithdrawal
    (· = 3) reward outside certificate profile
  simpa [sum_child, PatientWithdrawalRewardCertificate.debtWeight, certificate,
    certificateOfSlacks, advanceWeight, withdrawalWeight, child, outside] using h

/-- Literal patient rows amplify terminal regret by exactly the printed factor 7/2. -/
theorem lifted_terminalNash
    (profile : (quittingGame (quittingDeleteReward reward (· = 3))).BehaviorProfile)
    {error : ℝ} (herror : 0 ≤ error)
    (hnash : (quittingGame (quittingDeleteReward reward (· = 3))).IsεAsymptoticNash
      (quittingTerminalPayoff (quittingDeleteReward reward (· = 3))) error profile) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
      ((7 / 2) * error) (quittingLiftDeletedProfile reward (· = 3) profile) := by
  apply isεAsymptoticNash_quietLift_of_outsideTerminalDebtBounds (· = 3) reward
    (fun who => (certificateFamily who).debtWeight)
    (fun who i => (certificateFamily who).debtWeight_nonneg i) (7 / 2) (by norm_num)
    _ herror profile _ hnash
  · intro who
    have heq : who = outside := Subtype.ext who.2
    subst who
    norm_num [certificateFamily, certificate, certificateOfSlacks,
      PatientWithdrawalRewardCertificate.debtWeight, sum_child,
      advanceWeight, withdrawalWeight, child]
  · intro who
    exact quittingLiftDeletedProfile_outsideDebt_le_of_patientWithdrawal
      (· = 3) reward who (certificateFamily who) profile

/-- The canonical maximum of the actual full child debts has amplification 7/2. -/
theorem lifted_exploitability_le
    (profile : (quittingGame (quittingDeleteReward reward (· = 3))).BehaviorProfile) :
    quittingTerminalExploitability reward (quittingLiftDeletedProfile reward (· = 3) profile) ≤
      (7 / 2) * quittingTerminalExploitability (quittingDeleteReward reward (· = 3)) profile := by
  apply quittingTerminalExploitability_le_of_isεAsymptoticNash
  · exact mul_nonneg (by norm_num) (quittingTerminalExploitability_nonneg _ _)
  · exact lifted_terminalNash profile (quittingTerminalExploitability_nonneg _ _)
      (isεAsymptoticNash_of_quittingTerminalExploitability_le profile le_rfl)

/-- Actual low-cardinality child existence supplies the target internally. -/
theorem exists_uniformPayoff :
    ∃ payoff : Payoff (Fin 4), (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_of_finFour_patientWithdrawalFamily
    (· = 3) reward certificateFamily

end GameTheory.StrictPatientWithdrawal
