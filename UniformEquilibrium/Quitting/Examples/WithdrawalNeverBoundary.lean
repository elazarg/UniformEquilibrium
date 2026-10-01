import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockMissingNeverFixture
import UniformEquilibrium.Quitting.Classification.QuietExtension.WithdrawalFutureJoinDebt

/-! # Exact terminal boundary at an omitted Never row

This reuses the canonical literal one-child table and actual quiet profile.
All five withdrawal F/J kinds pass with zero weights, but the actual outsider
debt and omitted Never residual both equal one. No positive singleton exists.
-/

noncomputable section

namespace GameTheory.WithdrawalBoundaryExamples

open scoped BigOperators
open CappedClockMissingNeverFixture

private theorem withdrawalFutureWeight_zero (kind : WithdrawalFutureJoinKind) :
    kind.futureWeight 0 = 0 := by
  cases kind <;> rfl

/-- Every original withdrawal F/J system passes with zero lambda and mu. -/
def neverResidualCertificate (kind : WithdrawalFutureJoinKind) :
    WithdrawalFutureJoinRewardCertificate kind reward where
  advanceWeight := 0
  withdrawalWeight := 0
  advanceWeight_nonneg := by simp
  withdrawalWeight_nonneg := by simp
  future_row := by
    intro A hA
    simp only [reward_outsider, sub_self, Pi.zero_apply,
      zero_mul, withdrawalFutureWeight_zero, add_zero, Finset.sum_const_zero, le_refl]
  join_row := by
    intro A hA
    simp only [reward_outsider, sub_self, Pi.zero_apply,
      zero_mul, add_zero, Finset.sum_const_zero, le_refl]

/-- The exact positive-part Never residual is one for every withdrawal kind. -/
theorem neverResidual_excess_eq_one (kind : WithdrawalFutureJoinKind) :
    (neverResidualCertificate kind).neverExcess = 1 := by
  cases kind <;> norm_num [WithdrawalFutureJoinRewardCertificate.neverExcess,
    WithdrawalFutureJoinRewardCertificate.neverRightSide,
    WithdrawalFutureJoinKind.neverBonus, neverResidualCertificate,
    patientWithdrawalOwnNeverAlternative]

/-- The actual canonical one-child all-Never profile has complete debt zero. -/
theorem neverResidual_childDebt_eq_zero
    (who : {who : Player // ¬ who = none}) :
    quittingBehaviorDeviationPayoffCap (quittingDeleteReward reward (· = none))
        childProfile who -
      quittingTerminalPayoff (quittingDeleteReward reward (· = none)) childProfile who = 0 := by
  rw [quittingBehaviorDeviationPayoffCap_eq_bestReplyValue]
  change quittingContinuationBestResponseValue (quittingDeleteReward reward (· = none))
      childProfile who -
    quittingTerminalPayoff (quittingDeleteReward reward (· = none)) childProfile who = 0
  unfold CappedClockMissingNeverFixture.childProfile
  rw [quittingContinuationBestResponseValue_quittingAlwaysContinueProfile,
    quittingTerminalPayoff_quittingAlwaysContinue, quittingDeleteReward_singletonTerminal]
  have hwho : who.1 ≠ none := who.2
  simp [CappedClockMissingNeverFixture.reward, hwho]

/-- The child's actual product stopping law has joint-Never mass one. -/
theorem neverResidual_childJointNever_eq_one :
    (∏ i, (quietOutsiderChildLaws reward childProfile i none).toReal) = 1 := by
  have hlaw (i : Child) : quietOutsiderChildLaws reward childProfile i = PMF.pure none := by
    change quittingBehaviorStoppingLaw (quittingDeleteReward reward (· = none))
      (quittingPureTimeBehaviorStrategy (quittingDeleteReward reward (· = none))
        ⟨some i, Option.some_ne_none i⟩ none) = PMF.pure none
    exact quittingBehaviorStoppingLaw_pureTime_never _ _
  simp_rw [hlaw]
  simp

/-- The actual canonical quiet lift has outside complete behavioral debt one. -/
theorem neverResidual_outsideDebt_eq_one :
    quittingBehaviorDeviationPayoffCap reward liftedProfile none -
      quittingTerminalPayoff reward liftedProfile none = 1 :=
  liftedProfile_outsiderDebt_eq_one

/-- The source-produced residual times joint-Never is exactly the actual gap. -/
theorem neverResidual_outsideDebt_eq_residual_times_childJointNever
    (kind : WithdrawalFutureJoinKind) :
    quittingBehaviorDeviationPayoffCap reward liftedProfile none -
        quittingTerminalPayoff reward liftedProfile none =
      (neverResidualCertificate kind).neverExcess *
        ∏ i, (quietOutsiderChildLaws reward childProfile i none).toReal := by
  rw [neverResidual_outsideDebt_eq_one, neverResidual_excess_eq_one,
    neverResidual_childJointNever_eq_one, mul_one]

/-- No child own singleton has the sign needed to absorb the residual. -/
theorem neverResidual_no_positive_childSingleton (i : Child) :
    ¬ 0 < reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) := by
  rw [reward_child]
  exact lt_irrefl 0

/-- Discarding the Never correction would assert the false inequality one<=zero. -/
theorem neverResidual_outsideDebt_gt_weighted_childDebt (kind : WithdrawalFutureJoinKind) :
    (∑ i, (neverResidualCertificate kind).debtWeight i *
      (quittingBehaviorDeviationPayoffCap (quittingDeleteReward reward (· = none))
          childProfile ⟨some i, Option.some_ne_none i⟩ -
        quittingTerminalPayoff (quittingDeleteReward reward (· = none)) childProfile
          ⟨some i, Option.some_ne_none i⟩)) <
      quittingBehaviorDeviationPayoffCap reward liftedProfile none -
        quittingTerminalPayoff reward liftedProfile none := by
  simp_rw [neverResidual_childDebt_eq_zero]
  rw [neverResidual_outsideDebt_eq_one]
  simp

end GameTheory.WithdrawalBoundaryExamples
