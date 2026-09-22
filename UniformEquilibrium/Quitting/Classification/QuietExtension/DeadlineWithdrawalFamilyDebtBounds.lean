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

private theorem deadlineWithdrawalBehaviorEvaluatedDebt_nonneg
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (profile : (quittingGame reward).BehaviorProfile) (who : α) :
    0 ≤ quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation profile who -
      quittingBehaviorEvaluatedPayoff reward evaluation profile who := by
  apply sub_nonneg.mpr
  unfold quittingBehaviorEvaluatedDeviationPayoffCap
  apply le_csSup
    (bddAbove_range_quittingBehaviorEvaluatedPayoff_update
      reward evaluation evaluation_nonneg evaluation_antitone profile who)
  exact ⟨profile who, by simp⟩

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
  let factor := deadlineWithdrawalOutsiderMaxWeight deleted reward certificate
  let childReward := quittingDeleteReward reward deleted
  let lifted := quittingLiftDeletedProfile reward deleted profile
  let childDebt := fun who : QuittingChildPlayer deleted =>
    quittingBehaviorEvaluatedDeviationPayoffCap childReward evaluation profile who -
      quittingBehaviorEvaluatedPayoff childReward evaluation profile who
  let childMax := quittingBehaviorEvaluatedMaxDebt childReward evaluation profile
  have hchildLe (who : QuittingChildPlayer deleted) : childDebt who ≤ childMax :=
    Finset.le_sup' (f := childDebt) (Finset.mem_univ who)
  have hchildMaxNonneg : 0 ≤ childMax := by
    obtain ⟨who⟩ := (inferInstance : Nonempty (QuittingChildPlayer deleted))
    exact (deadlineWithdrawalBehaviorEvaluatedDebt_nonneg childReward evaluation
      evaluation_nonneg evaluation_antitone profile who).trans (hchildLe who)
  have hfamily :=
    quittingLiftDeletedProfile_evaluatedDebt_of_deadlineWithdrawalFamily
      deleted reward certificate evaluation evaluation_nonneg evaluation_antitone
      profile
  unfold quittingBehaviorEvaluatedMaxDebt
  apply Finset.sup'_le
  intro who _
  by_cases hdeleted : deleted who
  · let outside : {who : α // deleted who} := ⟨who, hdeleted⟩
    calc
      quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation lifted who -
          quittingBehaviorEvaluatedPayoff reward evaluation lifted who ≤
        ∑ child, (certificate outside).debtWeight child * childDebt child :=
        hfamily.2 outside
      _ ≤ ∑ child, (certificate outside).debtWeight child * childMax := by
        apply Finset.sum_le_sum
        intro child _
        exact mul_le_mul_of_nonneg_left (hchildLe child)
          ((certificate outside).debtWeight_nonneg child)
      _ = deadlineWithdrawalOutsiderWeight deleted reward certificate outside *
          childMax := by
        rw [← Finset.sum_mul]
        rfl
      _ ≤ factor * childMax :=
        mul_le_mul_of_nonneg_right
          (deadlineWithdrawalOutsiderWeight_le_maxWeight
            deleted reward certificate outside) hchildMaxNonneg
  · let child : QuittingChildPlayer deleted := ⟨who, hdeleted⟩
    calc
      quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation lifted who -
          quittingBehaviorEvaluatedPayoff reward evaluation lifted who =
        childDebt child := hfamily.1 child
      _ ≤ childMax := hchildLe child
      _ ≤ factor * childMax := by
        have hone : 1 ≤ factor := le_max_left _ _
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hone hchildMaxNonneg

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
  let lifted := quittingLiftDeletedProfile reward deleted profile
  let childReward := quittingDeleteReward reward deleted
  let parentDebt := fun who : α =>
    quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation lifted who -
      quittingBehaviorEvaluatedPayoff reward evaluation lifted who
  let childDebt := fun who : QuittingChildPlayer deleted =>
    quittingBehaviorEvaluatedDeviationPayoffCap childReward evaluation profile who -
      quittingBehaviorEvaluatedPayoff childReward evaluation profile who
  have hfamily :=
    quittingLiftDeletedProfile_evaluatedDebt_of_deadlineWithdrawalFamily
      deleted reward certificate evaluation evaluation_nonneg evaluation_antitone
      profile
  change (∑ who, parentDebt who) ≤
    ∑ child, (1 + ∑ outside : {who : α // deleted who},
      (certificate outside).debtWeight child) * childDebt child
  calc
    (∑ who, parentDebt who) =
        (∑ outside : {who : α // deleted who}, parentDebt outside.1) +
          ∑ child : QuittingChildPlayer deleted, parentDebt child.1 := by
      exact (Fintype.sum_subtype_add_sum_subtype deleted parentDebt).symm
    _ ≤ (∑ outside : {who : α // deleted who},
          ∑ child, (certificate outside).debtWeight child * childDebt child) +
        ∑ child : QuittingChildPlayer deleted, childDebt child := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro outside _
        exact hfamily.2 outside
      · apply Finset.sum_le_sum
        intro child _
        exact le_of_eq (hfamily.1 child)
    _ = ∑ child, (1 + ∑ outside : {who : α // deleted who},
          (certificate outside).debtWeight child) * childDebt child := by
      simp only [add_mul, one_mul, Finset.sum_add_distrib, Finset.sum_mul]
      rw [Finset.sum_comm]
      ac_rfl

end GameTheory
