import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalMultipleOutsiderFamily
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalNashLift

/-!
# Fixed-target quiet extension from deadline-withdrawal rows

The terminal evaluation of the simultaneous all-evaluation debt comparison
provides a fixed-multiplier terminal Nash lift. The existing target-tail
consumer then preserves every specified child uniform-equilibrium target.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]

omit [Nonempty α] in
/-- A displayed raw deadline-withdrawal outsider weight is below the family
maximum, which also includes the unchanged child-coordinate factor one. -/
theorem deadlineWithdrawalOutsiderWeight_le_maxWeight
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty {who : α // deleted who}]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      DeadlineWithdrawalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (outside : {who : α // deleted who}) :
    deadlineWithdrawalOutsiderWeight deleted reward certificate outside ≤
      deadlineWithdrawalOutsiderMaxWeight deleted reward certificate := by
  apply le_trans (Finset.le_sup'
    (f := deadlineWithdrawalOutsiderWeight deleted reward certificate)
    (Finset.mem_univ outside))
  exact le_max_right _ _

/-- Every child terminal approximate equilibrium lifts at the finite fixed
factor from the raw D certificates, for the same quiet lifted profile. -/
theorem isεAsymptoticNash_liftDeletedProfile_of_deadlineWithdrawalFamily
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    [Nonempty {who : α // deleted who}]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      DeadlineWithdrawalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    {error : ℝ} (herror : 0 ≤ error)
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile)
    (hnash : (quittingGame
      (quittingDeleteReward reward deleted)).IsεAsymptoticNash
        (quittingTerminalPayoff (quittingDeleteReward reward deleted))
        error profile) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward)
      (deadlineWithdrawalOutsiderMaxWeight deleted reward certificate * error)
      (quittingLiftDeletedProfile reward deleted profile) := by
  let factor := deadlineWithdrawalOutsiderMaxWeight deleted reward certificate
  let lifted := quittingLiftDeletedProfile reward deleted profile
  have hchildDebt (who : QuittingChildPlayer deleted) :
      quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward deleted) profile who -
          quittingTerminalPayoff
            (quittingDeleteReward reward deleted) profile who ≤ error := by
    rw [quittingBehaviorDeviationPayoffCap_eq_bestReplyValue]
    apply sub_le_iff_le_add.mpr
    apply quittingBestReplyValue_le
    intro deviation
    have h := hnash who deviation
    linarith
  have hfamilyEval :=
    quittingLiftDeletedProfile_evaluatedDebt_of_deadlineWithdrawalFamily
      deleted reward certificate quittingTerminalEvaluation
      quittingTerminalEvaluation_nonneg quittingTerminalEvaluation_antitone
      profile
  have hfamily :
      (∀ who : QuittingChildPlayer deleted,
        quittingBehaviorDeviationPayoffCap reward lifted who.1 -
          quittingTerminalPayoff reward lifted who.1 =
        quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward deleted) profile who -
          quittingTerminalPayoff
            (quittingDeleteReward reward deleted) profile who) ∧
      ∀ outside : {who : α // deleted who},
        quittingBehaviorDeviationPayoffCap reward lifted outside.1 -
          quittingTerminalPayoff reward lifted outside.1 ≤
        ∑ who, (certificate outside).debtWeight who *
          (quittingBehaviorDeviationPayoffCap
              (quittingDeleteReward reward deleted) profile who -
            quittingTerminalPayoff
              (quittingDeleteReward reward deleted) profile who) := by
    simpa only [lifted,
      quittingBehaviorEvaluatedDeviationPayoffCap_terminalEvaluation,
      quittingBehaviorEvaluatedPayoff_terminalEvaluation] using hfamilyEval
  have hdebt (who : α) :
      quittingBehaviorDeviationPayoffCap reward lifted who -
        quittingTerminalPayoff reward lifted who ≤ factor * error := by
    by_cases hdeleted : deleted who
    · let outside : {who : α // deleted who} := ⟨who, hdeleted⟩
      calc
        quittingBehaviorDeviationPayoffCap reward lifted who -
            quittingTerminalPayoff reward lifted who ≤
          ∑ child, (certificate outside).debtWeight child *
            (quittingBehaviorDeviationPayoffCap
                (quittingDeleteReward reward deleted) profile child -
              quittingTerminalPayoff
                (quittingDeleteReward reward deleted) profile child) :=
          hfamily.2 outside
        _ ≤ ∑ child, (certificate outside).debtWeight child * error := by
          apply Finset.sum_le_sum
          intro child _
          exact mul_le_mul_of_nonneg_left (hchildDebt child)
            ((certificate outside).debtWeight_nonneg child)
        _ = deadlineWithdrawalOutsiderWeight deleted reward certificate outside *
            error := by
          rw [← Finset.sum_mul]
          rfl
        _ ≤ factor * error :=
          mul_le_mul_of_nonneg_right
            (deadlineWithdrawalOutsiderWeight_le_maxWeight
              deleted reward certificate outside) herror
    · let child : QuittingChildPlayer deleted := ⟨who, hdeleted⟩
      calc
        quittingBehaviorDeviationPayoffCap reward lifted who -
            quittingTerminalPayoff reward lifted who =
          quittingBehaviorDeviationPayoffCap
              (quittingDeleteReward reward deleted) profile child -
            quittingTerminalPayoff
              (quittingDeleteReward reward deleted) profile child :=
          hfamily.1 child
        _ ≤ error := hchildDebt child
        _ ≤ factor * error := by
          have hone : 1 ≤ factor := le_max_left _ _
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hone herror
  intro who deviation
  have hdeviation := le_quittingBestReplyValue reward lifted who deviation
  rw [← quittingBehaviorDeviationPayoffCap_eq_bestReplyValue] at hdeviation
  change quittingTerminalPayoff reward lifted who + factor * error ≥ _
  linarith [hdebt who]

/-- Every specified child uniform-equilibrium target extends under raw
deadline-withdrawal certificates for all outsiders, with no favorable child
profile supplied beyond the target's actual uniform-equilibrium property. -/
theorem exists_uniformEquilibriumPayoff_eq_on_child_of_deadlineWithdrawalFamily
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    [Nonempty {who : α // deleted who}]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (certificate : ∀ outside : {who : α // deleted who},
      DeadlineWithdrawalRewardCertificate
        (quittingChildWithOutsiderReward reward deleted outside))
    (target : Payoff (QuittingChildPlayer deleted))
    (htarget : (quittingGame
      (quittingDeleteReward reward deleted)).IsUniformEquilibriumPayoff
        none target) :
    ∃ payoff : Payoff α,
      (∀ who : QuittingChildPlayer deleted, payoff who.1 = target who) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  exact exists_uniformEquilibriumPayoff_eq_on_image_of_terminalNash_lift
    reward (quittingDeleteReward reward deleted) (fun who => who.1)
    (quittingLiftDeletedProfile reward deleted)
    (deadlineWithdrawalOutsiderMaxWeight deleted reward certificate)
    (fun profile who =>
      quittingTerminalPayoff_liftDeletedProfile reward deleted profile who)
    (fun herror profile hnash =>
      isεAsymptoticNash_liftDeletedProfile_of_deadlineWithdrawalFamily
        deleted reward certificate herror profile hnash)
    target htarget

end GameTheory
