import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalFamily
import UniformEquilibrium.Quitting.Classification.QuietExtension.TerminalWeightedDebtLift
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalNashLift

/-! # Fixed child-target extension from literal patient terminal certificates -/

noncomputable section

namespace GameTheory

open StochasticGame

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Each outsider's lambda-plus-mu sum is below the fixed amplification. -/
theorem patientWithdrawalOutsiderWeight_le_maxWeight
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty {who : α // deleted who}]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      PatientWithdrawalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (outside : {who : α // deleted who}) :
    patientWithdrawalOutsiderWeight deleted reward certificate outside ≤
      patientWithdrawalOutsiderMaxWeight deleted reward certificate := by
  exact (Finset.le_sup' (f := patientWithdrawalOutsiderWeight deleted reward certificate)
    (Finset.mem_univ outside)).trans (le_max_right _ _)

/-- Literal patient rows amplify every actual child terminal approximate
equilibrium at one fixed factor, with unrestricted behavioral deviations. -/
theorem isεAsymptoticNash_liftDeletedProfile_of_patientWithdrawalFamily
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    [Nonempty {who : α // deleted who}]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      PatientWithdrawalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    {error : ℝ} (herror : 0 ≤ error)
    (profile : (quittingGame (quittingDeleteReward reward deleted)).BehaviorProfile)
    (hnash : (quittingGame (quittingDeleteReward reward deleted)).IsεAsymptoticNash
      (quittingTerminalPayoff (quittingDeleteReward reward deleted)) error profile) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
      (patientWithdrawalOutsiderMaxWeight deleted reward certificate * error)
      (quittingLiftDeletedProfile reward deleted profile) := by
  exact isεAsymptoticNash_quietLift_of_outsideTerminalDebtBounds
    deleted reward (fun outside => (certificate outside).debtWeight)
    (fun outside child => (certificate outside).debtWeight_nonneg child)
    (patientWithdrawalOutsiderMaxWeight deleted reward certificate) (le_max_left _ _)
    (fun outside => patientWithdrawalOutsiderWeight_le_maxWeight deleted reward certificate outside)
    herror profile
    (fun outside => quittingLiftDeletedProfile_outsideDebt_le_of_patientWithdrawal
      deleted reward outside (certificate outside) profile) hnash

/-- Every specified child uniform-equilibrium payoff extends to one fixed
parent target from literal patient rows. Accuracy-dependent profiles do not
change the child target or replace the full behavioral deviation envelope. -/
theorem exists_uniformEquilibriumPayoff_eq_on_child_of_patientWithdrawalFamily
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    [Nonempty {who : α // deleted who}]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      PatientWithdrawalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (target : Payoff (QuittingChildPlayer deleted))
    (htarget : (quittingGame (quittingDeleteReward reward deleted)).IsUniformEquilibriumPayoff
      none target) :
    ∃ payoff : Payoff α,
      (∀ who : QuittingChildPlayer deleted, payoff who.1 = target who) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  exact exists_uniformEquilibriumPayoff_eq_on_image_of_terminalNash_lift
    reward (quittingDeleteReward reward deleted) (fun who => who.1)
    (quittingLiftDeletedProfile reward deleted)
    (patientWithdrawalOutsiderMaxWeight deleted reward certificate)
    (fun profile who => quittingTerminalPayoff_liftDeletedProfile reward deleted profile who)
    (fun herror profile hnash => isεAsymptoticNash_liftDeletedProfile_of_patientWithdrawalFamily
      deleted reward certificate herror profile hnash) target htarget

end GameTheory
