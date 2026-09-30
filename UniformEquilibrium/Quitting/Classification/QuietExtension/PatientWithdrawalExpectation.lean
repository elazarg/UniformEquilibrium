import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalDomination
import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalExpectedLimit

/-! # Bounded expectation of the patient terminal comparison -/

noncomputable section

namespace GameTheory

open _root_.Math.Probability _root_.Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
/-- The terminal specialization of the existing evaluated payoff bound. -/
private theorem abs_patientTerminalClockPayoff_le
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (clocks : Option ι → Option ℕ) (who : Option ι) :
    |quittingPureClockTerminalPayoff reward clocks who| ≤ quittingRewardBound reward := by
  simpa only [quittingPureClockEvaluatedPayoff_terminalEvaluation,
    quittingTerminalEvaluation_zero, one_mul] using
    abs_quittingPureClockEvaluatedPayoff_le reward quittingTerminalEvaluation
      quittingTerminalEvaluation_nonneg quittingTerminalEvaluation_antitone clocks who

omit [DecidableEq ι] in
/-- Actual terminal outsider gains are bounded independently of clock dates. -/
theorem abs_patientOutsideClockGain_le
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (times : ι → Option ℕ) (deadline : Option ℕ) :
    |cappedClockActualOutsideGain reward times deadline| ≤ 2 * quittingRewardBound reward := by
  unfold cappedClockActualOutsideGain
  calc
    |_ - _| ≤ |quittingPureClockTerminalPayoff reward
        (outsideDeadlineClocks times deadline) none| +
      |quittingPureClockTerminalPayoff reward (quietParentClocks times) none| := abs_sub _ _
    _ ≤ quittingRewardBound reward + quittingRewardBound reward := add_le_add
      (abs_patientTerminalClockPayoff_le reward _ _) (abs_patientTerminalClockPayoff_le reward _ _)
    _ = _ := by ring

/-- Actual terminal advancement gains have the same date-independent bound. -/
theorem abs_patientAdvanceClockGain_le
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (times : ι → Option ℕ) (deadline : Option ℕ) (i : ι) :
    |cappedClockActualChildGain reward times deadline i| ≤ 2 * quittingRewardBound reward := by
  unfold cappedClockActualChildGain
  calc
    |_ - _| ≤ |quittingPureClockTerminalPayoff reward
        (cappedChildParentClocks times deadline i) (some i)| +
      |quittingPureClockTerminalPayoff reward (quietParentClocks times) (some i)| := abs_sub _ _
    _ ≤ quittingRewardBound reward + quittingRewardBound reward := add_le_add
      (abs_patientTerminalClockPayoff_le reward _ _) (abs_patientTerminalClockPayoff_le reward _ _)
    _ = _ := by ring

/-- Literal patient payoff-limit gains are bounded, so no summability premise
on a supplied strategy or stopping law is needed. -/
theorem abs_patientWithdrawalTerminalGain_le
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (times : ι → Option ℕ) (deadline : Option ℕ) (i : ι) :
    |patientWithdrawalTerminalGain reward times deadline i| ≤
      2 * quittingRewardBound reward := by
  unfold patientWithdrawalTerminalGain
  calc
    |_ - _| ≤ |patientWithdrawalTerminalPayoffLimit reward times deadline i| +
      |quittingPureClockTerminalPayoff reward (quietParentClocks times) (some i)| := abs_sub _ _
    _ ≤ quittingRewardBound reward + quittingRewardBound reward := add_le_add
      (abs_patientWithdrawalTerminalPayoffLimit_le reward times deadline i)
      (abs_patientTerminalClockPayoff_le reward _ _)
    _ = _ := by ring

/-- Literal patient rows integrate over every fixed coupled clock law.
Independence is required only by the separate legal-response cap adapters. -/
theorem expect_patientWithdrawalOutsideGain_le_weighted_childExpectations
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : PatientWithdrawalRewardCertificate reward)
    (law : PMF ((ι → Option ℕ) × Option ℕ)) :
    expect law (fun sample => cappedClockActualOutsideGain reward sample.1 sample.2) ≤
      ∑ i, (certificate.advanceWeight i *
          expect law (fun sample => cappedClockActualChildGain reward sample.1 sample.2 i) +
        certificate.withdrawalWeight i *
          expect law (fun sample => patientWithdrawalTerminalGain reward sample.1 sample.2 i)) :=
      by
  let advance (i : ι) (sample : (ι → Option ℕ) × Option ℕ) :=
    cappedClockActualChildGain reward sample.1 sample.2 i
  let patient (i : ι) (sample : (ι → Option ℕ) × Option ℕ) :=
    patientWithdrawalTerminalGain reward sample.1 sample.2 i
  let weighted (i : ι) (sample : (ι → Option ℕ) × Option ℕ) :=
    certificate.advanceWeight i * advance i sample +
      certificate.withdrawalWeight i * patient i sample
  let bound (i : ι) :=
    (|certificate.advanceWeight i| + |certificate.withdrawalWeight i|) *
      (2 * quittingRewardBound reward)
  have hbound (i : ι) (sample : (ι → Option ℕ) × Option ℕ) :
      |weighted i sample| ≤ bound i := by
    calc
      |_ + _| ≤ |certificate.advanceWeight i * advance i sample| +
        |certificate.withdrawalWeight i * patient i sample| := abs_add_le _ _
      _ ≤ |certificate.advanceWeight i| * (2 * quittingRewardBound reward) +
          |certificate.withdrawalWeight i| * (2 * quittingRewardBound reward) := by
        rw [abs_mul, abs_mul]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (abs_patientAdvanceClockGain_le reward _ _ i) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left
            (abs_patientWithdrawalTerminalGain_le reward _ _ i) (abs_nonneg _))
      _ = _ := by dsimp [bound]; ring
  have hpoint : expect law (fun sample =>
      cappedClockActualOutsideGain reward sample.1 sample.2) ≤
      expect law (fun sample => ∑ i, weighted i sample) := by
    apply expect_mono_of_pointwise_summable
    · intro sample
      exact patientWithdrawalActualOutsideGain_le_weighted_childGains
        reward certificate sample.1 sample.2
    · exact expect_summable_of_bounded law _ fun sample => abs_patientOutsideClockGain_le
        reward sample.1 sample.2
    · apply expect_summable_of_bounded law _ (C := ∑ i, bound i)
      intro sample
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => hbound i sample)
  have hsum : expect law (fun sample => ∑ i, weighted i sample) =
      ∑ i, expect law (weighted i) := by
    simpa using expect_finset_sum_of_bounded law Finset.univ weighted bound
      (fun i _ sample => hbound i sample)
  rw [hsum] at hpoint
  refine hpoint.trans_eq (Finset.sum_congr rfl fun i _ => ?_)
  change expect law (fun sample => certificate.advanceWeight i * advance i sample +
      certificate.withdrawalWeight i * patient i sample) = _
  rw [expect_add_of_summable]
  · rw [expect_const_mul, expect_const_mul]
  · exact expect_summable_of_bounded law _
      (C := |certificate.advanceWeight i| * (2 * quittingRewardBound reward)) fun sample => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_patientAdvanceClockGain_le reward _ _ i) (abs_nonneg _)
  · exact expect_summable_of_bounded law _
      (C := |certificate.withdrawalWeight i| * (2 * quittingRewardBound reward)) fun sample => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_patientWithdrawalTerminalGain_le reward _ _ i) (abs_nonneg _)

end GameTheory
