import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalFixedTarget

/-!
# All-evaluation maximum and sum debt for deadline-withdrawal families

The finite consequences of the simultaneous playerwise D comparison use the
same quiet lift for every nonnegative antitone evaluation and every outsider.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]


/-- The literal D-family maximum-debt factor is the maximum of one and all
outsider sums of `max(a_ki,b_ki)`, uniformly over evaluations and profiles. -/
theorem quittingBehaviorEvaluatedMaxDebt_liftDeletedProfile_le_of_deadlineWithdrawal
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    [Nonempty {who : α // deleted who}]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      DeadlineWithdrawalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile) :
    quittingBehaviorEvaluatedMaxDebt reward evaluation
        (quittingLiftDeletedProfile reward deleted profile) ≤
      deadlineWithdrawalOutsiderMaxWeight deleted reward certificate *
        quittingBehaviorEvaluatedMaxDebt
          (quittingDeleteReward reward deleted) evaluation profile := by
  exact quittingBehaviorEvaluatedMaxDebt_liftDeletedProfile_le_of_outsideDebtBounds
    deleted reward (fun outside => (certificate outside).debtWeight)
    (fun outside child => (certificate outside).debtWeight_nonneg child)
    (deadlineWithdrawalOutsiderMaxWeight deleted reward certificate) (le_max_left _ _)
    (fun outside => deadlineWithdrawalOutsiderWeight_le_maxWeight
      deleted reward certificate outside)
    evaluation evaluation_nonneg evaluation_antitone profile
    (fun outside => quittingLiftDeletedProfile_outsideEvaluatedDebt_le_of_deadlineWithdrawal
      deleted reward outside (certificate outside) evaluation
      evaluation_nonneg evaluation_antitone profile)

/-- The literal D-family sum-debt bound accumulates each outsider's
`max(a_ki,b_ki)` on each preserved child debt. -/
theorem quittingBehaviorEvaluatedTotalDebt_liftDeletedProfile_le_of_deadlineWithdrawal
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      DeadlineWithdrawalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile) :
    quittingBehaviorEvaluatedTotalDebt reward evaluation
        (quittingLiftDeletedProfile reward deleted profile) ≤
      ∑ child : QuittingChildPlayer deleted,
        (1 + ∑ outside : {who : α // deleted who},
          (certificate outside).debtWeight child) *
          (quittingBehaviorEvaluatedDeviationPayoffCap
              (quittingDeleteReward reward deleted) evaluation profile child -
            quittingBehaviorEvaluatedPayoff
              (quittingDeleteReward reward deleted) evaluation profile child) := by
  exact quittingBehaviorEvaluatedTotalDebt_liftDeletedProfile_le_of_outsideDebtBounds
    deleted reward (fun outside => (certificate outside).debtWeight) evaluation profile
    (fun outside => quittingLiftDeletedProfile_outsideEvaluatedDebt_le_of_deadlineWithdrawal
      deleted reward outside (certificate outside) evaluation
      evaluation_nonneg evaluation_antitone profile)

end GameTheory
