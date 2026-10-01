import UniformEquilibrium.Quitting.Classification.QuietExtension.WithdrawalNeverResidual
import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalQuietLift
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalFullBehavioralDebt
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityMixedFullBehavioralDebt
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityTerminalQuietLift
import UniformEquilibrium.Quitting.Classification.QuietExtension.CancellationWithdrawalFullBehavioralDebt

/-! # Literal withdrawal F/J rows with the Never row omitted

The kind records the actual response operation, its raw-table floor, and its
proved coefficient. These certificates contain only nonnegative weights and
finite reward inequalities. Evaluated-security refers to the nonpositive raw
floor; every omitted-Never conclusion in this module is terminal-only.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The five source operations; no strategic comparison is certificate data. -/
inductive WithdrawalFutureJoinKind
  | patient | deadline | evaluatedSecurity | terminalSecurity | cancellation

/-- The actual source withdrawal gain, including its singleton floor. -/
def WithdrawalFutureJoinKind.gain (kind : WithdrawalFutureJoinKind)
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (A : Finset ι) (hA : A.Nonempty) : ℝ :=
  match kind with
  | .patient => patientWithdrawalGainFloor reward i A hA
  | .deadline | .cancellation => deadlineWithdrawalGainFloor reward i A hA
  | .evaluatedSecurity => deadlineSecurityGainFloor reward i A hA
  | .terminalSecurity => deadlineSecurityGainFloorWithRestart reward
      (deadlineWithdrawalSecurityFloor reward i) i A hA

/-- Only patient withdrawal and cancellation contribute on the future event. -/
def WithdrawalFutureJoinKind.futureWeight (kind : WithdrawalFutureJoinKind) (weight : ℝ) : ℝ :=
  match kind with
  | .patient | .cancellation => weight
  | .deadline | .evaluatedSecurity | .terminalSecurity => 0

/-- Patient withdrawal alone has the favorable terminal all-Never alternative. -/
def WithdrawalFutureJoinKind.neverBonus (kind : WithdrawalFutureJoinKind)
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (weight : ι → ℝ) : ℝ :=
  match kind with
  | .patient => ∑ i, weight i * patientWithdrawalOwnNeverAlternative reward i
  | .deadline | .evaluatedSecurity | .terminalSecurity | .cancellation => 0

/-- Separate response experiments add; disjoint deadline responses take a maximum. -/
def WithdrawalFutureJoinKind.debtWeight (kind : WithdrawalFutureJoinKind)
    (advance withdrawal : ℝ) : ℝ :=
  match kind with
  | .patient | .cancellation => advance + withdrawal
  | .deadline | .evaluatedSecurity | .terminalSecurity => max advance withdrawal

/-- Original raw F/J rows, without an N row or a supplied response strategy. -/
structure WithdrawalFutureJoinRewardCertificate (kind : WithdrawalFutureJoinKind)
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) where
  advanceWeight : ι → ℝ
  withdrawalWeight : ι → ℝ
  advanceWeight_nonneg : ∀ i, 0 ≤ advanceWeight i
  withdrawalWeight_nonneg : ∀ i, 0 ≤ withdrawalWeight i
  future_row : ∀ A (hA : A.Nonempty),
    reward ⟨{none}, Finset.singleton_nonempty none⟩ none -
        reward ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩ none ≤
      ∑ i, (advanceWeight i *
          (reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) -
            reward ⟨cappedClockChildCoalition A,
              cappedClockChildCoalition_nonempty hA⟩ (some i)) +
        kind.futureWeight (withdrawalWeight i) * kind.gain reward i A hA)
  join_row : ∀ A (hA : A.Nonempty),
    reward ⟨cappedClockJoinedCoalition A, cappedClockJoinedCoalition_nonempty A⟩ none -
        reward ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩ none ≤
      ∑ i, (advanceWeight i *
          (reward ⟨cappedClockChildCoalition (insert i A),
              cappedClockChildCoalition_nonempty (Finset.insert_nonempty i A)⟩ (some i) -
            reward ⟨cappedClockChildCoalition A,
              cappedClockChildCoalition_nonempty hA⟩ (some i)) +
        withdrawalWeight i * kind.gain reward i A hA)

abbrev PatientWithdrawalFutureJoinCertificate :=
  WithdrawalFutureJoinRewardCertificate (ι := ι) .patient
abbrev DeadlineWithdrawalFutureJoinCertificate :=
  WithdrawalFutureJoinRewardCertificate (ι := ι) .deadline
abbrev DeadlineSecurityFutureJoinCertificate :=
  WithdrawalFutureJoinRewardCertificate (ι := ι) .evaluatedSecurity
abbrev DeadlineSecurityTerminalFutureJoinCertificate :=
  WithdrawalFutureJoinRewardCertificate (ι := ι) .terminalSecurity
abbrev CancellationWithdrawalFutureJoinCertificate :=
  WithdrawalFutureJoinRewardCertificate (ι := ι) .cancellation

/-- The original N-row right side, before taking its positive-part residual. -/
def WithdrawalFutureJoinRewardCertificate.neverRightSide
    {kind : WithdrawalFutureJoinKind}
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : WithdrawalFutureJoinRewardCertificate kind reward) : ℝ :=
  (∑ i, certificate.advanceWeight i *
    reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)) +
  kind.neverBonus reward certificate.withdrawalWeight

/-- Exact nonnegative residual of the omitted original N row. -/
def WithdrawalFutureJoinRewardCertificate.neverExcess
    {kind : WithdrawalFutureJoinKind}
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : WithdrawalFutureJoinRewardCertificate kind reward) : ℝ :=
  max (reward ⟨{none}, Finset.singleton_nonempty none⟩ none -
    certificate.neverRightSide) 0

theorem WithdrawalFutureJoinRewardCertificate.neverExcess_nonneg
    {kind : WithdrawalFutureJoinKind}
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : WithdrawalFutureJoinRewardCertificate kind reward) :
    0 ≤ certificate.neverExcess := le_max_right _ _

/-- The actual full-debt coefficient dictated by the source response operation. -/
def WithdrawalFutureJoinRewardCertificate.debtWeight
    {kind : WithdrawalFutureJoinKind}
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : WithdrawalFutureJoinRewardCertificate kind reward) (i : ι) : ℝ :=
  kind.debtWeight (certificate.advanceWeight i) (certificate.withdrawalWeight i)

theorem WithdrawalFutureJoinRewardCertificate.debtWeight_nonneg
    {kind : WithdrawalFutureJoinKind}
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : WithdrawalFutureJoinRewardCertificate kind reward) (i : ι) :
    0 ≤ certificate.debtWeight i := by
  cases kind
  all_goals
    first
    | exact add_nonneg (certificate.advanceWeight_nonneg i)
        (certificate.withdrawalWeight_nonneg i)
    | exact (certificate.advanceWeight_nonneg i).trans (le_max_left _ _)

private theorem zeroFloor_shift
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (excess : ℝ) (i : ι) :
    deadlineWithdrawalZeroFloor (withdrawalOutsideTerminalShift reward excess) i =
      deadlineWithdrawalZeroFloor reward i := by
  unfold deadlineWithdrawalZeroFloor
  simp only [withdrawalOutsideTerminalShift_some]

private theorem patientFloor_shift
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (excess : ℝ) (i : ι) :
    patientWithdrawalFloor (withdrawalOutsideTerminalShift reward excess) i =
      patientWithdrawalFloor reward i := by
  unfold patientWithdrawalFloor patientWithdrawalOwnNeverAlternative
  simp only [withdrawalOutsideTerminalShift_some]

omit [Fintype ι] in
private theorem securityRow_shift
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (excess : ℝ) (i : ι) (hazard : ℝ)
    (row : Option {A : Finset ι // A.Nonempty ∧ i ∉ A}) :
    deadlineWithdrawalSecurityRow (withdrawalOutsideTerminalShift reward excess)
        i hazard row = deadlineWithdrawalSecurityRow reward i hazard row := by
  cases row <;> simp only [deadlineWithdrawalSecurityRow,
    withdrawalOutsideTerminalShift_some]

omit [Fintype ι] in
private theorem securityFeasible_shift
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (excess : ℝ) (i : ι) (hazard value : ℝ) :
    DeadlineWithdrawalSecurityFeasible (withdrawalOutsideTerminalShift reward excess)
        i hazard value ↔ DeadlineWithdrawalSecurityFeasible reward i hazard value := by
  unfold DeadlineWithdrawalSecurityFeasible
  simp only [securityRow_shift]

private theorem securityValue_shift
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (excess : ℝ) (i : ι) :
    deadlineWithdrawalSecurityValue (withdrawalOutsideTerminalShift reward excess) i =
      deadlineWithdrawalSecurityValue reward i := by
  obtain ⟨first, hfirst, hmaxFirst⟩ := deadlineWithdrawalSecurityValue_spec
    (withdrawalOutsideTerminalShift reward excess) i
  obtain ⟨second, hsecond, hmaxSecond⟩ := deadlineWithdrawalSecurityValue_spec reward i
  exact le_antisymm
    (hmaxSecond first _ ((securityFeasible_shift reward excess i first _).mp hfirst))
    (hmaxFirst second _ ((securityFeasible_shift reward excess i second _).mpr hsecond))

private theorem securityFloor_shift
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (excess : ℝ) (i : ι) :
    deadlineWithdrawalSecurityFloor (withdrawalOutsideTerminalShift reward excess) i =
      deadlineWithdrawalSecurityFloor reward i := by
  unfold deadlineWithdrawalSecurityFloor
  rw [zeroFloor_shift, securityValue_shift]

theorem WithdrawalFutureJoinKind.gain_shift
    (kind : WithdrawalFutureJoinKind)
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (excess : ℝ) (i : ι) (A : Finset ι) (hA : A.Nonempty) :
    kind.gain (withdrawalOutsideTerminalShift reward excess) i A hA =
      kind.gain reward i A hA := by
  have hgain : deadlineWithdrawalGainFloor (withdrawalOutsideTerminalShift reward excess)
      i A hA = deadlineWithdrawalGainFloor reward i A hA := by
    unfold deadlineWithdrawalGainFloor
    simp only [withdrawalOutsideTerminalShift_some, zeroFloor_shift]
  cases kind with
  | patient =>
      change deadlineSecurityGainFloorWithRestart
          (withdrawalOutsideTerminalShift reward excess)
          (patientWithdrawalFloor (withdrawalOutsideTerminalShift reward excess) i) i A hA =
        deadlineSecurityGainFloorWithRestart reward (patientWithdrawalFloor reward i) i A hA
      unfold deadlineSecurityGainFloorWithRestart
      rw [hgain, patientFloor_shift, zeroFloor_shift]
  | deadline => exact hgain
  | cancellation => exact hgain
  | evaluatedSecurity =>
      change deadlineSecurityGainFloorWithRestart
          (withdrawalOutsideTerminalShift reward excess)
          (min (deadlineWithdrawalSecurityFloor
            (withdrawalOutsideTerminalShift reward excess) i) 0) i A hA =
        deadlineSecurityGainFloorWithRestart reward
          (min (deadlineWithdrawalSecurityFloor reward i) 0) i A hA
      unfold deadlineSecurityGainFloorWithRestart
      rw [hgain, securityFloor_shift, zeroFloor_shift]
  | terminalSecurity =>
      change deadlineSecurityGainFloorWithRestart
          (withdrawalOutsideTerminalShift reward excess)
          (deadlineWithdrawalSecurityFloor
            (withdrawalOutsideTerminalShift reward excess) i) i A hA =
        deadlineSecurityGainFloorWithRestart reward
          (deadlineWithdrawalSecurityFloor reward i) i A hA
      unfold deadlineSecurityGainFloorWithRestart
      rw [hgain, securityFloor_shift, zeroFloor_shift]

omit [DecidableEq ι] in
private theorem neverBonus_shift
    (kind : WithdrawalFutureJoinKind)
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (excess : ℝ) (weight : ι → ℝ) :
    kind.neverBonus (withdrawalOutsideTerminalShift reward excess) weight =
      kind.neverBonus reward weight := by
  cases kind
  all_goals first
    | rfl
    | simp only [WithdrawalFutureJoinKind.neverBonus,
        patientWithdrawalOwnNeverAlternative, withdrawalOutsideTerminalShift_some]

/-- The previously checked full raw source predicate corresponding to a kind. -/
def WithdrawalFutureJoinKind.FullCertificate (kind : WithdrawalFutureJoinKind)
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) : Type :=
  match kind with
  | .patient => PatientWithdrawalRewardCertificate reward
  | .deadline => DeadlineWithdrawalRewardCertificate reward
  | .evaluatedSecurity => DeadlineSecurityRewardCertificate reward
  | .terminalSecurity => DeadlineSecurityTerminalRewardCertificate reward
  | .cancellation => CancellationWithdrawalRewardCertificate reward

/-- Internally repair only the N row by the precise residual. Original F/J
rows are unchanged because the outsider's terminal translation cancels. -/
def WithdrawalFutureJoinRewardCertificate.toShifted
    {kind : WithdrawalFutureJoinKind}
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : WithdrawalFutureJoinRewardCertificate kind reward) :
    kind.FullCertificate (withdrawalOutsideTerminalShift reward certificate.neverExcess) := by
  let shifted := withdrawalOutsideTerminalShift reward certificate.neverExcess
  have hneverOriginal : shifted ⟨{none}, Finset.singleton_nonempty none⟩ none ≤
      certificate.neverRightSide := by
    dsimp only [shifted]
    rw [withdrawalOutsideTerminalShift_none]
    have h := le_max_left
      (reward ⟨{none}, Finset.singleton_nonempty none⟩ none -
        certificate.neverRightSide) 0
    change _ ≤ certificate.neverExcess at h
    linarith
  have hnever : shifted ⟨{none}, Finset.singleton_nonempty none⟩ none ≤
      (∑ i, certificate.advanceWeight i *
        shifted ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)) +
      kind.neverBonus shifted certificate.withdrawalWeight := by
    simpa only [shifted, withdrawalOutsideTerminalShift_some, neverBonus_shift,
      WithdrawalFutureJoinRewardCertificate.neverRightSide] using hneverOriginal
  have hfuture (A : Finset ι) (hA : A.Nonempty) :
      shifted ⟨{none}, Finset.singleton_nonempty none⟩ none -
          shifted ⟨cappedClockChildCoalition A,
            cappedClockChildCoalition_nonempty hA⟩ none ≤
        ∑ i, (certificate.advanceWeight i *
            (shifted ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) -
              shifted ⟨cappedClockChildCoalition A,
                cappedClockChildCoalition_nonempty hA⟩ (some i)) +
          kind.futureWeight (certificate.withdrawalWeight i) * kind.gain shifted i A hA) := by
    simpa only [shifted, withdrawalOutsideTerminalShift_none,
      withdrawalOutsideTerminalShift_some, sub_sub_sub_cancel_right,
      WithdrawalFutureJoinKind.gain_shift] using certificate.future_row A hA
  have hjoin (A : Finset ι) (hA : A.Nonempty) :
      shifted ⟨cappedClockJoinedCoalition A,
            cappedClockJoinedCoalition_nonempty A⟩ none -
          shifted ⟨cappedClockChildCoalition A,
            cappedClockChildCoalition_nonempty hA⟩ none ≤
        ∑ i, (certificate.advanceWeight i *
            (shifted ⟨cappedClockChildCoalition (insert i A),
                cappedClockChildCoalition_nonempty (Finset.insert_nonempty i A)⟩ (some i) -
              shifted ⟨cappedClockChildCoalition A,
                cappedClockChildCoalition_nonempty hA⟩ (some i)) +
          certificate.withdrawalWeight i * kind.gain shifted i A hA) := by
    simpa only [shifted, withdrawalOutsideTerminalShift_none,
      withdrawalOutsideTerminalShift_some, sub_sub_sub_cancel_right,
      WithdrawalFutureJoinKind.gain_shift] using certificate.join_row A hA
  cases kind with
  | patient =>
      exact {
        advanceWeight := certificate.advanceWeight
        withdrawalWeight := certificate.withdrawalWeight
        advanceWeight_nonneg := certificate.advanceWeight_nonneg
        withdrawalWeight_nonneg := certificate.withdrawalWeight_nonneg
        never_row := hnever
        future_row := hfuture
        join_row := hjoin }
  | deadline =>
      exact {
        advanceWeight := certificate.advanceWeight
        withdrawalWeight := certificate.withdrawalWeight
        advanceWeight_nonneg := certificate.advanceWeight_nonneg
        withdrawalWeight_nonneg := certificate.withdrawalWeight_nonneg
        never_row := by
          simpa only [WithdrawalFutureJoinKind.neverBonus, add_zero] using hnever
        future_row := by
          intro A hA
          simpa only [WithdrawalFutureJoinKind.futureWeight, zero_mul, add_zero]
            using hfuture A hA
        join_row := hjoin }
  | evaluatedSecurity =>
      exact {
        advanceWeight := certificate.advanceWeight
        withdrawalWeight := certificate.withdrawalWeight
        advanceWeight_nonneg := certificate.advanceWeight_nonneg
        withdrawalWeight_nonneg := certificate.withdrawalWeight_nonneg
        never_row := by
          simpa only [WithdrawalFutureJoinKind.neverBonus, add_zero] using hnever
        future_row := by
          intro A hA
          simpa only [WithdrawalFutureJoinKind.futureWeight, zero_mul, add_zero]
            using hfuture A hA
        join_row := hjoin }
  | terminalSecurity =>
      exact {
        advanceWeight := certificate.advanceWeight
        withdrawalWeight := certificate.withdrawalWeight
        advanceWeight_nonneg := certificate.advanceWeight_nonneg
        withdrawalWeight_nonneg := certificate.withdrawalWeight_nonneg
        never_row := by
          simpa only [WithdrawalFutureJoinKind.neverBonus, add_zero] using hnever
        future_row := by
          intro A hA
          simpa only [WithdrawalFutureJoinKind.futureWeight, zero_mul, add_zero]
            using hfuture A hA
        join_row := by
          intro A hA
          simpa only [WithdrawalFutureJoinKind.gain, add_zero] using hjoin A hA }
  | cancellation =>
      exact {
        advanceWeight := certificate.advanceWeight
        withdrawalWeight := certificate.withdrawalWeight
        advanceWeight_nonneg := certificate.advanceWeight_nonneg
        withdrawalWeight_nonneg := certificate.withdrawalWeight_nonneg
        never_row := by
          simpa only [WithdrawalFutureJoinKind.neverBonus, add_zero] using hnever
        future_row := hfuture
        join_row := hjoin }

end GameTheory
