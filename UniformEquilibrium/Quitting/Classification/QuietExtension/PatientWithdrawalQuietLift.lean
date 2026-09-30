import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalFullBehavioralDebt

/-! # Literal patient terminal debt for actual child behavioral profiles -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance patientWithdrawalQuietChildNonempty :
    Nonempty {who : Option ι // ¬ who = none} :=
  Nonempty.map (fun who => ⟨some who, Option.some_ne_none who⟩)
    (inferInstance : Nonempty ι)

/-- Every actual independent child behavioral profile has the patient
lambda-plus-mu terminal full-debt bound under its literal Never lift. The
private finite-delay responses and payoff-limit cap are produced internally. -/
theorem patientWithdrawal_quietLift_outsideBehaviorDebt_le_weighted_childDebt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : PatientWithdrawalRewardCertificate reward)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile) :
    let lifted := quittingLiftDeletedProfile reward (· = none) childProfile
    quittingBehaviorDeviationPayoffCap reward lifted none -
        quittingTerminalPayoff reward lifted none ≤
      ∑ i, certificate.debtWeight i *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some i, Option.some_ne_none i⟩ -
          quittingTerminalPayoff
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some i, Option.some_ne_none i⟩) := by
  have h :=
    quietLift_outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt_add_const_of_canonical
      reward certificate.debtWeight quittingTerminalEvaluation childProfile 0
      (by
        simpa only [quittingBehaviorEvaluatedDeviationPayoffCap_terminalEvaluation,
          quittingBehaviorEvaluatedPayoff_terminalEvaluation, add_zero] using
          patientWithdrawal_outsideBehaviorDebt_le_weighted_childDebt
            reward certificate (quietOutsiderChildLaws reward childProfile))
  simpa only [quittingBehaviorEvaluatedDeviationPayoffCap_terminalEvaluation,
    quittingBehaviorEvaluatedPayoff_terminalEvaluation, add_zero] using h

end GameTheory
