import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityTerminalFamily
import UniformEquilibrium.Quitting.Classification.QuietExtension.TerminalWeightedDebtLift
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalNashLift

/-! # Fixed child targets extend under literal untruncated security rows -/

noncomputable section

namespace GameTheory

open StochasticGame

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Every outsider total is below the fixed family amplification. -/
theorem deadlineSecurityTerminalOutsiderWeight_le_maxWeight
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty {who : α // deleted who}]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      DeadlineSecurityTerminalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (outside : {who : α // deleted who}) :
    deadlineSecurityTerminalOutsiderWeight deleted reward certificate outside ≤
      deadlineSecurityTerminalOutsiderMaxWeight deleted reward certificate := by
  exact (Finset.le_sup'
    (f := deadlineSecurityTerminalOutsiderWeight deleted reward certificate)
    (Finset.mem_univ outside)).trans (le_max_right _ _)

/-- Every child terminal approximate equilibrium lifts at the fixed factor
computed from the literal gamma certificates, retaining the actual quiet
profile and unrestricted behavioral deviation coverage. -/
theorem isεAsymptoticNash_liftDeletedProfile_of_deadlineSecurityTerminalFamily
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    [Nonempty {who : α // deleted who}]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      DeadlineSecurityTerminalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    {error : ℝ} (herror : 0 ≤ error)
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile)
    (hnash : (quittingGame
      (quittingDeleteReward reward deleted)).IsεAsymptoticNash
        (quittingTerminalPayoff (quittingDeleteReward reward deleted)) error profile) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
      (deadlineSecurityTerminalOutsiderMaxWeight deleted reward certificate * error)
      (quittingLiftDeletedProfile reward deleted profile) := by
  exact isεAsymptoticNash_quietLift_of_outsideTerminalDebtBounds
    deleted reward (fun outside => (certificate outside).debtWeight)
    (fun outside child => (certificate outside).debtWeight_nonneg child)
    (deadlineSecurityTerminalOutsiderMaxWeight deleted reward certificate)
    (le_max_left _ _)
    (fun outside => deadlineSecurityTerminalOutsiderWeight_le_maxWeight
      deleted reward certificate outside)
    herror profile
    (fun outside => quittingLiftDeletedProfile_outsideDebt_le_of_deadlineSecurityTerminal
      deleted reward outside (certificate outside) profile) hnash

/-- Every specified child UE payoff extends to one fixed parent UE payoff
agreeing at every child coordinate, from literal gamma rows alone. The child
target is fixed before the accuracy-dependent profiles are selected. -/
theorem exists_uniformPayoffWitnesses_eq_on_child_of_deadlineSecurityTerminalFamily
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    [Nonempty {who : α // deleted who}]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      DeadlineSecurityTerminalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (target : Payoff (QuittingChildPlayer deleted))
    (htarget : (quittingGame
      (quittingDeleteReward reward deleted)).IsUniformEquilibriumPayoff none target) :
    ∃ payoff : Payoff α,
      (∀ who : QuittingChildPlayer deleted, payoff who.1 = target who) ∧
        ∀ ε : ℝ, 0 < ε →
          ∃ (profile : (quittingGame
              (quittingDeleteReward reward deleted)).BehaviorProfile) (threshold : ℕ),
            ∀ horizon, threshold ≤ horizon →
              (quittingGame reward).IsεHorizonNash none horizon ε
                  (quittingLiftDeletedProfile reward deleted profile) ∧
                ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
                  (quittingLiftDeletedProfile reward deleted profile) who - payoff who| ≤ ε := by
  exact exists_uniformPayoffWitnesses_eq_on_image_of_terminalNash_lift
    reward (quittingDeleteReward reward deleted) (fun who => who.1)
    (quittingLiftDeletedProfile reward deleted)
    (deadlineSecurityTerminalOutsiderMaxWeight deleted reward certificate)
    (fun profile who => quittingTerminalPayoff_liftDeletedProfile reward deleted profile who)
    (fun herror profile hnash =>
      isεAsymptoticNash_liftDeletedProfile_of_deadlineSecurityTerminalFamily
        deleted reward certificate herror profile hnash)
    target htarget

/-- Project the actual quiet witnesses to the usual fixed-target UE conclusion. -/
theorem exists_uniformEquilibriumPayoff_eq_on_child_of_deadlineSecurityTerminalFamily
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    [Nonempty {who : α // deleted who}]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      DeadlineSecurityTerminalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (target : Payoff (QuittingChildPlayer deleted))
    (htarget : (quittingGame
      (quittingDeleteReward reward deleted)).IsUniformEquilibriumPayoff none target) :
    ∃ payoff : Payoff α,
      (∀ who : QuittingChildPlayer deleted, payoff who.1 = target who) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨payoff, hcoordinates, hwitnesses⟩ :=
    exists_uniformPayoffWitnesses_eq_on_child_of_deadlineSecurityTerminalFamily
      deleted reward certificate target htarget
  refine ⟨payoff, hcoordinates, fun ε hε => ?_⟩
  obtain ⟨profile, threshold, hwitness⟩ := hwitnesses ε hε
  exact ⟨quittingLiftDeletedProfile reward deleted profile, threshold, hwitness⟩

end GameTheory
