import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityTerminalQuietLift
import UniformEquilibrium.Quitting.Classification.QuietExtension.TerminalOneOutsiderTransport

/-!
# Quiet-outside families from literal untruncated security rows

Each outsider uses the actual restricted child-plus-one-outsider table. All
certificates control the same actual full-game Never lift; their security
floors retain positive gamma without making an evaluated-payoff claim.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Total maximum-mix weight from one outsider's literal gamma rows. -/
def deadlineSecurityTerminalOutsiderWeight
    (deleted : α → Prop) [DecidablePred deleted]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      DeadlineSecurityTerminalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (outside : {who : α // deleted who}) : ℝ :=
  ∑ who, (certificate outside).debtWeight who

/-- The fixed family amplification includes the unchanged-child factor one. -/
def deadlineSecurityTerminalOutsiderMaxWeight
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty {who : α // deleted who}]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      DeadlineSecurityTerminalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside)) : ℝ :=
  max 1 (Finset.univ.sup' Finset.univ_nonempty
    (deadlineSecurityTerminalOutsiderWeight deleted reward certificate))

/-- An outsider's actual full-game terminal debt obeys its literal raw gamma
certificate after exact deletion and player reindexing. Rewards on coalitions
with several outsiders are unrestricted by these unilateral experiments. -/
theorem quittingLiftDeletedProfile_outsideDebt_le_of_deadlineSecurityTerminal
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (outside : {who : α // deleted who})
    (certificate : DeadlineSecurityTerminalRewardCertificate
      (quittingChildWithOutsiderReward reward deleted outside))
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile) :
    quittingBehaviorDeviationPayoffCap reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 -
        quittingTerminalPayoff reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 ≤
      ∑ who, certificate.debtWeight who *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward deleted) profile who -
          quittingTerminalPayoff (quittingDeleteReward reward deleted) profile who) := by
  exact quittingLiftDeletedProfile_outsideTerminalDebt_le_of_oneOutsiderBound
    deleted reward outside certificate.debtWeight
    (fun childProfile =>
      deadlineSecurityTerminal_quietLift_outsideBehaviorDebt_le_weighted_childDebt
        (quittingChildWithOutsiderReward reward deleted outside) certificate childProfile) profile

/-- Every child debt is unchanged, and every outsider debt is controlled
simultaneously for the same full quiet lift by its untruncated gamma rows. -/
theorem quittingLiftDeletedProfile_debt_of_deadlineSecurityTerminalFamily
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      DeadlineSecurityTerminalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile) :
    (∀ who : QuittingChildPlayer deleted,
      quittingBehaviorDeviationPayoffCap reward
            (quittingLiftDeletedProfile reward deleted profile) who.1 -
          quittingTerminalPayoff reward
            (quittingLiftDeletedProfile reward deleted profile) who.1 =
        quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward deleted) profile who -
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
  exact ⟨fun who => quittingBehaviorDeviationDebt_liftDeletedProfile
      reward deleted profile who,
    fun outside => quittingLiftDeletedProfile_outsideDebt_le_of_deadlineSecurityTerminal
      deleted reward outside (certificate outside) profile⟩

end GameTheory
