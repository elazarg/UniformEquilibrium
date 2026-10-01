import UniformEquilibrium.Quitting.Classification.QuietExtension.CancellationWithdrawalFamily

/-!
# All-evaluation maximum and sum debt for evaluated-cancellation families

The simultaneous evaluated cancellation comparison adds the advance and
withdrawal weights on each child debt. Its finite maximum and sum bounds use
the same quiet lift for every nonnegative antitone evaluation and every outsider.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
variable (deleted : α → Prop) [DecidablePred deleted]
variable [Nonempty (QuittingChildPlayer deleted)]

/-- The literal cancellation-family maximum-debt factor is the maximum of one and all
outsider sums of `lambda_ki+mu_ki`, uniformly over evaluations and profiles. -/
theorem quittingBehaviorEvaluatedMaxDebt_liftDeletedProfile_le_of_cancellationWithdrawal
    [Nonempty {who : α // deleted who}]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      CancellationWithdrawalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile) :
    quittingBehaviorEvaluatedMaxDebt reward evaluation
        (quittingLiftDeletedProfile reward deleted profile) ≤
      cancellationWithdrawalOutsiderMaxWeight deleted reward certificate *
        quittingBehaviorEvaluatedMaxDebt
          (quittingDeleteReward reward deleted) evaluation profile := by
  exact quittingBehaviorEvaluatedMaxDebt_liftDeletedProfile_le_of_outsideDebtBounds
    deleted reward (fun outside => (certificate outside).debtWeight)
    (fun outside child => (certificate outside).debtWeight_nonneg child)
    (cancellationWithdrawalOutsiderMaxWeight deleted reward certificate) (le_max_left _ _)
    (fun outside => cancellationWithdrawalOutsiderWeight_le_maxWeight
      deleted reward certificate outside)
    evaluation evaluation_nonneg evaluation_antitone profile
    (fun outside => quittingLiftDeletedProfile_outsideEvaluatedDebt_le_of_cancellationWithdrawal
      deleted reward outside (certificate outside) evaluation
      evaluation_nonneg evaluation_antitone profile)

/-- The literal cancellation-family sum-debt bound accumulates each outsider's
`lambda_ki+mu_ki` on each preserved child debt. -/
theorem quittingBehaviorEvaluatedTotalDebt_liftDeletedProfile_le_of_cancellationWithdrawal
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      CancellationWithdrawalRewardCertificate
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
    (fun outside => quittingLiftDeletedProfile_outsideEvaluatedDebt_le_of_cancellationWithdrawal
      deleted reward outside (certificate outside) evaluation
      evaluation_nonneg evaluation_antitone profile)

end GameTheory
