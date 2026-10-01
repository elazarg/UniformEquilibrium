import UniformEquilibrium.Quitting.Classification.QuietExtension.WithdrawalFutureJoinRaw

/-! # Actual terminal debt with an omitted Never row

All source comparisons delegate to the canonical five full-row producers.
The N-row residual remains multiplied by the actual child joint-Never mass
before positive-singleton charging. No statement protects all evaluations.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private instance : Nonempty {who : Option ι // ¬ who = none} :=
  Nonempty.map (fun who => ⟨some who, Option.some_ne_none who⟩)
    (inferInstance : Nonempty ι)

omit [Nonempty ι] in
private theorem patient_toShifted_debtWeight
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : WithdrawalFutureJoinRewardCertificate .patient reward) (i : ι) :
    PatientWithdrawalRewardCertificate.debtWeight certificate.toShifted i =
      certificate.debtWeight i := by
  rfl

omit [Nonempty ι] in
private theorem deadline_toShifted_debtWeight
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : WithdrawalFutureJoinRewardCertificate .deadline reward) (i : ι) :
    DeadlineWithdrawalRewardCertificate.debtWeight certificate.toShifted i =
      certificate.debtWeight i := by
  rfl

omit [Nonempty ι] in
private theorem evaluatedSecurity_toShifted_debtWeight
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : WithdrawalFutureJoinRewardCertificate .evaluatedSecurity reward) (i : ι) :
    DeadlineSecurityRewardCertificate.debtWeight certificate.toShifted i =
      certificate.debtWeight i := by
  rfl

omit [Nonempty ι] in
private theorem terminalSecurity_toShifted_debtWeight
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : WithdrawalFutureJoinRewardCertificate .terminalSecurity reward) (i : ι) :
    DeadlineRestartRewardCertificate.debtWeight certificate.toShifted i =
      certificate.debtWeight i := by
  rfl

omit [Nonempty ι] in
private theorem cancellation_toShifted_debtWeight
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : WithdrawalFutureJoinRewardCertificate .cancellation reward) (i : ι) :
    CancellationWithdrawalRewardCertificate.debtWeight certificate.toShifted i =
      certificate.debtWeight i := by
  rfl

private def ShiftedQuietDebtBound
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (excess : ℝ) (weight : ι → ℝ)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile) : Prop :=
    let shifted := withdrawalOutsideTerminalShift reward excess
    let lifted := quittingLiftDeletedProfile reward (· = none) childProfile
    quittingBehaviorDeviationPayoffCap shifted lifted none -
        quittingTerminalPayoff shifted lifted none ≤
      ∑ i, weight i *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some i, Option.some_ne_none i⟩ -
          quittingTerminalPayoff (quittingDeleteReward reward (· = none)) childProfile
            ⟨some i, Option.some_ne_none i⟩)

omit [Nonempty ι] in
private theorem shiftedQuietDebtBound_transport
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (excess : ℝ) (weight : ι → ℝ)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile)
    (h :
      let shifted := withdrawalOutsideTerminalShift reward excess
      let lifted := quittingLiftDeletedProfile shifted (· = none) childProfile
      quittingBehaviorDeviationPayoffCap shifted lifted none -
          quittingTerminalPayoff shifted lifted none ≤
        ∑ i, weight i *
          (quittingBehaviorDeviationPayoffCap
              (quittingDeleteReward shifted (· = none)) childProfile
                ⟨some i, Option.some_ne_none i⟩ -
            quittingTerminalPayoff (quittingDeleteReward shifted (· = none)) childProfile
              ⟨some i, Option.some_ne_none i⟩)) :
    ShiftedQuietDebtBound reward excess weight childProfile := by
  have hprofile := quittingLiftDeletedProfile_withdrawalOutsideTerminalShift
    reward excess childProfile
  have hreward := quittingDeleteReward_withdrawalOutsideTerminalShift reward excess
  have hleft := congrArg
    (fun profile : (quittingGame
        (withdrawalOutsideTerminalShift reward excess)).BehaviorProfile =>
      quittingBehaviorDeviationPayoffCap (withdrawalOutsideTerminalShift reward excess)
          profile none -
        quittingTerminalPayoff (withdrawalOutsideTerminalShift reward excess) profile none)
    hprofile
  have hright := congrArg
    (fun childReward : {A : Finset {who : Option ι // ¬ who = none} // A.Nonempty} →
        Payoff {who : Option ι // ¬ who = none} =>
      ∑ i : ι, weight i *
        (quittingBehaviorDeviationPayoffCap childReward childProfile
            ⟨some i, Option.some_ne_none i⟩ -
          quittingTerminalPayoff childReward childProfile ⟨some i, Option.some_ne_none i⟩))
    hreward
  exact hleft.symm.trans_le (h.trans_eq hright)

private theorem childEvaluatedDebtSum_terminal
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (weight : ι → ℝ)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile) :
    (∑ i, weight i *
      (quittingBehaviorEvaluatedDeviationPayoffCap
          (quittingDeleteReward reward (· = none)) quittingTerminalEvaluation childProfile
            ⟨some i, Option.some_ne_none i⟩ -
        quittingBehaviorEvaluatedPayoff
          (quittingDeleteReward reward (· = none)) quittingTerminalEvaluation childProfile
            ⟨some i, Option.some_ne_none i⟩)) =
      ∑ i, weight i *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some i, Option.some_ne_none i⟩ -
          quittingTerminalPayoff (quittingDeleteReward reward (· = none)) childProfile
            ⟨some i, Option.some_ne_none i⟩) := by
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun debt : ℝ => weight i * debt)
    (congrArg₂ (fun cap payoff : ℝ => cap - payoff)
      (quittingBehaviorEvaluatedDeviationPayoffCap_terminalEvaluation
        (quittingDeleteReward reward (· = none)) childProfile
        ⟨some i, Option.some_ne_none i⟩)
      (quittingBehaviorEvaluatedPayoff_terminalEvaluation
        (quittingDeleteReward reward (· = none)) childProfile
        ⟨some i, Option.some_ne_none i⟩))

private theorem patient_shiftedQuietDebtBound
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : WithdrawalFutureJoinRewardCertificate .patient reward)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile) :
    ShiftedQuietDebtBound reward certificate.neverExcess certificate.debtWeight childProfile := by
  have h := patientWithdrawal_quietLift_outsideBehaviorDebt_le_weighted_childDebt
    (withdrawalOutsideTerminalShift reward certificate.neverExcess) certificate.toShifted
    childProfile
  simp only [patient_toShifted_debtWeight] at h
  exact shiftedQuietDebtBound_transport reward certificate.neverExcess certificate.debtWeight
    childProfile h

private theorem deadline_shiftedQuietDebtBound
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : WithdrawalFutureJoinRewardCertificate .deadline reward)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile) :
    ShiftedQuietDebtBound reward certificate.neverExcess certificate.debtWeight childProfile := by
  have h := deadlineWithdrawal_quietLift_outsideBehaviorDebt_le_weighted_childDebt
    (withdrawalOutsideTerminalShift reward certificate.neverExcess) certificate.toShifted
    quittingTerminalEvaluation quittingTerminalEvaluation_nonneg
    quittingTerminalEvaluation_antitone childProfile
  simp only [quittingBehaviorEvaluatedDeviationPayoffCap_terminalEvaluation,
    quittingBehaviorEvaluatedPayoff_terminalEvaluation] at h
  simp only [deadline_toShifted_debtWeight] at h
  exact shiftedQuietDebtBound_transport reward certificate.neverExcess certificate.debtWeight
    childProfile (h.trans_eq (childEvaluatedDebtSum_terminal
      (withdrawalOutsideTerminalShift reward certificate.neverExcess)
      certificate.debtWeight childProfile))

private theorem evaluatedSecurity_shiftedQuietDebtBound
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : WithdrawalFutureJoinRewardCertificate .evaluatedSecurity reward)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile) :
    ShiftedQuietDebtBound reward certificate.neverExcess certificate.debtWeight childProfile := by
  have h := deadlineSecurity_quietLift_outsideBehaviorDebt_le_weighted_childDebt
    (withdrawalOutsideTerminalShift reward certificate.neverExcess) certificate.toShifted
    quittingTerminalEvaluation quittingTerminalEvaluation_nonneg
    quittingTerminalEvaluation_antitone childProfile
  simp only [quittingBehaviorEvaluatedDeviationPayoffCap_terminalEvaluation,
    quittingBehaviorEvaluatedPayoff_terminalEvaluation] at h
  simp only [evaluatedSecurity_toShifted_debtWeight] at h
  exact shiftedQuietDebtBound_transport reward certificate.neverExcess certificate.debtWeight
    childProfile (h.trans_eq (childEvaluatedDebtSum_terminal
      (withdrawalOutsideTerminalShift reward certificate.neverExcess)
      certificate.debtWeight childProfile))

private theorem terminalSecurity_shiftedQuietDebtBound
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : WithdrawalFutureJoinRewardCertificate .terminalSecurity reward)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile) :
    ShiftedQuietDebtBound reward certificate.neverExcess certificate.debtWeight childProfile := by
  have h := deadlineSecurityTerminal_quietLift_outsideBehaviorDebt_le_weighted_childDebt
    (withdrawalOutsideTerminalShift reward certificate.neverExcess) certificate.toShifted
    childProfile
  simp only [terminalSecurity_toShifted_debtWeight] at h
  exact shiftedQuietDebtBound_transport reward certificate.neverExcess certificate.debtWeight
    childProfile h

private theorem cancellation_shiftedQuietDebtBound
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : WithdrawalFutureJoinRewardCertificate .cancellation reward)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile) :
    ShiftedQuietDebtBound reward certificate.neverExcess certificate.debtWeight childProfile := by
  have h := cancellationWithdrawal_quietLift_outsideBehaviorDebt_le_weighted_childDebt
    (withdrawalOutsideTerminalShift reward certificate.neverExcess) certificate.toShifted
    quittingTerminalEvaluation quittingTerminalEvaluation_nonneg
    quittingTerminalEvaluation_antitone childProfile
  simp only [quittingBehaviorEvaluatedDeviationPayoffCap_terminalEvaluation,
    quittingBehaviorEvaluatedPayoff_terminalEvaluation] at h
  simp only [cancellation_toShifted_debtWeight] at h
  exact shiftedQuietDebtBound_transport reward certificate.neverExcess certificate.debtWeight
    childProfile (h.trans_eq (childEvaluatedDebtSum_terminal
      (withdrawalOutsideTerminalShift reward certificate.neverExcess)
      certificate.debtWeight childProfile))

private theorem shiftedWithdrawalQuietDebt_le
    {kind : WithdrawalFutureJoinKind}
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : WithdrawalFutureJoinRewardCertificate kind reward)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile) :
    let shifted := withdrawalOutsideTerminalShift reward certificate.neverExcess
    let lifted := quittingLiftDeletedProfile reward (· = none) childProfile
    quittingBehaviorDeviationPayoffCap shifted lifted none -
        quittingTerminalPayoff shifted lifted none ≤
      ∑ i, certificate.debtWeight i *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some i, Option.some_ne_none i⟩ -
          quittingTerminalPayoff (quittingDeleteReward reward (· = none)) childProfile
            ⟨some i, Option.some_ne_none i⟩) := by
  cases kind with
  | patient => exact patient_shiftedQuietDebtBound reward certificate childProfile
  | deadline => exact deadline_shiftedQuietDebtBound reward certificate childProfile
  | evaluatedSecurity =>
      exact evaluatedSecurity_shiftedQuietDebtBound reward certificate childProfile
  | terminalSecurity => exact terminalSecurity_shiftedQuietDebtBound reward certificate childProfile
  | cancellation => exact cancellation_shiftedQuietDebtBound reward certificate childProfile

/-- Exact source-produced terminal correction for every actual quiet child lift. -/
theorem withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess
    {kind : WithdrawalFutureJoinKind}
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : WithdrawalFutureJoinRewardCertificate kind reward)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile) :
    let lifted := quittingLiftDeletedProfile reward (· = none) childProfile
    quittingBehaviorDeviationPayoffCap reward lifted none -
        quittingTerminalPayoff reward lifted none ≤
      (∑ i, certificate.debtWeight i *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some i, Option.some_ne_none i⟩ -
          quittingTerminalPayoff (quittingDeleteReward reward (· = none)) childProfile
            ⟨some i, Option.some_ne_none i⟩)) +
      certificate.neverExcess *
        ∏ i, (quietOutsiderChildLaws reward childProfile i none).toReal := by
  have hshift := withdrawalOutsideTerminalDebt_le_shiftedDebt_add_neverMass reward
    certificate.neverExcess certificate.neverExcess_nonneg
    (quittingLiftDeletedProfile reward (· = none) childProfile)
  rw [quittingLiveMassLimit_quietLift_eq_childJointNever] at hshift
  exact hshift.trans (add_le_add
    (shiftedWithdrawalQuietDebt_le reward certificate childProfile) le_rfl)

/-- Zero actual child joint-Never mass removes the correction without any
singleton sign assumption. The profile is still the same actual quiet lift. -/
theorem withdrawalFutureJoin_quietLift_outsideDebt_le_of_jointNever_zero
    {kind : WithdrawalFutureJoinKind}
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : WithdrawalFutureJoinRewardCertificate kind reward)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile)
    (hnever : (∏ i, (quietOutsiderChildLaws reward childProfile i none).toReal) = 0) :
    let lifted := quittingLiftDeletedProfile reward (· = none) childProfile
    quittingBehaviorDeviationPayoffCap reward lifted none -
        quittingTerminalPayoff reward lifted none ≤
      ∑ i, certificate.debtWeight i *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some i, Option.some_ne_none i⟩ -
          quittingTerminalPayoff (quittingDeleteReward reward (· = none)) childProfile
            ⟨some i, Option.some_ne_none i⟩) := by
  simpa only [hnever, mul_zero, add_zero] using
    withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess
      reward certificate childProfile

/-- Exact residual charging, retaining the original lambda-plus-mu or maximum
coefficient and adding only residual/singleton to the chosen pivot. -/
theorem withdrawalFutureJoin_quietLift_outsideDebt_le_of_positiveSingleton
    {kind : WithdrawalFutureJoinKind}
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : WithdrawalFutureJoinRewardCertificate kind reward)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile)
    (pivot : ι)
    (hpivot : 0 < reward ⟨{some pivot}, Finset.singleton_nonempty (some pivot)⟩
      (some pivot)) :
    let lifted := quittingLiftDeletedProfile reward (· = none) childProfile
    quittingBehaviorDeviationPayoffCap reward lifted none -
        quittingTerminalPayoff reward lifted none ≤
      (∑ i, certificate.debtWeight i *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some i, Option.some_ne_none i⟩ -
          quittingTerminalPayoff (quittingDeleteReward reward (· = none)) childProfile
            ⟨some i, Option.some_ne_none i⟩)) +
      (certificate.neverExcess /
          reward ⟨{some pivot}, Finset.singleton_nonempty (some pivot)⟩ (some pivot)) *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some pivot, Option.some_ne_none pivot⟩ -
          quittingTerminalPayoff (quittingDeleteReward reward (· = none)) childProfile
            ⟨some pivot, Option.some_ne_none pivot⟩) := by
  exact (withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess
    reward certificate childProfile).trans
    (add_le_add le_rfl (withdrawalNeverResidual_le_pivotDebt reward childProfile pivot
      certificate.neverExcess certificate.neverExcess_nonneg hpivot))

omit [Nonempty ι] in
/-- Augmented finite child weights for subsequent exact deletion transport. -/
def WithdrawalFutureJoinRewardCertificate.positiveSingletonWeight
    {kind : WithdrawalFutureJoinKind}
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : WithdrawalFutureJoinRewardCertificate kind reward)
    (pivot i : ι) : ℝ :=
  certificate.debtWeight i + if i = pivot then
    certificate.neverExcess /
      reward ⟨{some pivot}, Finset.singleton_nonempty (some pivot)⟩ (some pivot) else 0

omit [Nonempty ι] in
theorem WithdrawalFutureJoinRewardCertificate.positiveSingletonWeight_nonneg
    {kind : WithdrawalFutureJoinKind}
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : WithdrawalFutureJoinRewardCertificate kind reward)
    (pivot i : ι)
    (hpivot : 0 < reward ⟨{some pivot}, Finset.singleton_nonempty (some pivot)⟩
      (some pivot)) :
    0 ≤ certificate.positiveSingletonWeight pivot i := by
  unfold WithdrawalFutureJoinRewardCertificate.positiveSingletonWeight
  apply add_nonneg (certificate.debtWeight_nonneg i)
  split_ifs
  · exact div_nonneg certificate.neverExcess_nonneg hpivot.le
  · exact le_rfl

omit [Nonempty ι] in
/-- Literal source amplification: the original coefficient sum plus excess/singleton. -/
theorem WithdrawalFutureJoinRewardCertificate.sum_positiveSingletonWeight
    {kind : WithdrawalFutureJoinKind}
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : WithdrawalFutureJoinRewardCertificate kind reward) (pivot : ι) :
    (∑ i, certificate.positiveSingletonWeight pivot i) =
      (∑ i, certificate.debtWeight i) + certificate.neverExcess /
        reward ⟨{some pivot}, Finset.singleton_nonempty (some pivot)⟩ (some pivot) := by
  simp [WithdrawalFutureJoinRewardCertificate.positiveSingletonWeight,
    Finset.sum_add_distrib]

/-- The charged correction is precisely a weighted actual child debt bound. -/
theorem withdrawalFutureJoin_quietLift_outsideDebt_le_positiveSingletonWeights
    {kind : WithdrawalFutureJoinKind}
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : WithdrawalFutureJoinRewardCertificate kind reward)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile)
    (pivot : ι)
    (hpivot : 0 < reward ⟨{some pivot}, Finset.singleton_nonempty (some pivot)⟩
      (some pivot)) :
    let lifted := quittingLiftDeletedProfile reward (· = none) childProfile
    quittingBehaviorDeviationPayoffCap reward lifted none -
        quittingTerminalPayoff reward lifted none ≤
      ∑ i, certificate.positiveSingletonWeight pivot i *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some i, Option.some_ne_none i⟩ -
          quittingTerminalPayoff (quittingDeleteReward reward (· = none)) childProfile
            ⟨some i, Option.some_ne_none i⟩) := by
  have h := withdrawalFutureJoin_quietLift_outsideDebt_le_of_positiveSingleton
    reward certificate childProfile pivot hpivot
  simpa [WithdrawalFutureJoinRewardCertificate.positiveSingletonWeight,
    add_mul, Finset.sum_add_distrib, ite_mul] using h

end GameTheory
