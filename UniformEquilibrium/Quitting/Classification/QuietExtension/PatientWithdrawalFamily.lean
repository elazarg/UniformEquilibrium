import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalQuietLift
import UniformEquilibrium.Quitting.Classification.QuietExtension.TerminalOneOutsiderTransport

/-! # Quiet-outside terminal families from literal patient reward certificates -/

noncomputable section

namespace GameTheory

open StochasticGame

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Total lambda-plus-mu weight for one outsider's literal patient rows. -/
def patientWithdrawalOutsiderWeight
    (deleted : α → Prop) [DecidablePred deleted]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      PatientWithdrawalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (outside : {who : α // deleted who}) : ℝ :=
  ∑ who, (certificate outside).debtWeight who

/-- Fixed terminal amplification, including the unchanged-child factor one. -/
def patientWithdrawalOutsiderMaxWeight
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty {who : α // deleted who}]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      PatientWithdrawalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside)) : ℝ :=
  max 1 (Finset.univ.sup' Finset.univ_nonempty
    (patientWithdrawalOutsiderWeight deleted reward certificate))

/-- The actual full-game outsider debt from literal patient rows, using the
shared one-outsider deletion/reindex transport. No response cap is a premise. -/
theorem quittingLiftDeletedProfile_outsideDebt_le_of_patientWithdrawal
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (outside : {who : α // deleted who})
    (certificate : PatientWithdrawalRewardCertificate
      (quittingChildWithOutsiderReward reward deleted outside))
    (profile : (quittingGame (quittingDeleteReward reward deleted)).BehaviorProfile) :
    quittingBehaviorDeviationPayoffCap reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 -
        quittingTerminalPayoff reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 ≤
      ∑ who, certificate.debtWeight who *
        (quittingBehaviorDeviationPayoffCap (quittingDeleteReward reward deleted) profile who -
          quittingTerminalPayoff (quittingDeleteReward reward deleted) profile who) := by
  exact quittingLiftDeletedProfile_outsideTerminalDebt_le_of_oneOutsiderBound
    deleted reward outside certificate.debtWeight
    (fun childProfile => patientWithdrawal_quietLift_outsideBehaviorDebt_le_weighted_childDebt
      (quittingChildWithOutsiderReward reward deleted outside) certificate childProfile) profile

/-- The same full-game quiet lift preserves every child debt and controls
every outsider simultaneously by its literal patient certificate. -/
theorem quittingLiftDeletedProfile_debt_of_patientWithdrawalFamily
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      PatientWithdrawalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (profile : (quittingGame (quittingDeleteReward reward deleted)).BehaviorProfile) :
    (∀ who : QuittingChildPlayer deleted,
      quittingBehaviorDeviationPayoffCap reward
            (quittingLiftDeletedProfile reward deleted profile) who.1 -
          quittingTerminalPayoff reward
            (quittingLiftDeletedProfile reward deleted profile) who.1 =
        quittingBehaviorDeviationPayoffCap (quittingDeleteReward reward deleted) profile who -
          quittingTerminalPayoff (quittingDeleteReward reward deleted) profile who) ∧
    ∀ outside : {who : α // deleted who},
      quittingBehaviorDeviationPayoffCap reward
            (quittingLiftDeletedProfile reward deleted profile) outside.1 -
          quittingTerminalPayoff reward
            (quittingLiftDeletedProfile reward deleted profile) outside.1 ≤
        ∑ who, (certificate outside).debtWeight who *
          (quittingBehaviorDeviationPayoffCap
              (quittingDeleteReward reward deleted) profile who -
            quittingTerminalPayoff (quittingDeleteReward reward deleted) profile who) := by
  exact ⟨fun who => quittingBehaviorDeviationDebt_liftDeletedProfile reward deleted profile who,
    fun outside => quittingLiftDeletedProfile_outsideDebt_le_of_patientWithdrawal
      deleted reward outside (certificate outside) profile⟩

end GameTheory
