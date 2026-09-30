import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalExpectation
import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalFullCap
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalOutsideMarginal

/-!
# Patient terminal full-debt bound from literal reward rows

The advancement and patient response are separately legal unilateral
experiments. Their expected gains are each below the same unrestricted child
debt; nonnegative raw weights therefore give lambda plus mu, not a maximum.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private theorem patient_expect_sub_of_bounds {Ω : Type*} (law : PMF Ω)
    (f g : Ω → ℝ) {C D : ℝ}
    (hf : ∀ sample, |f sample| ≤ C) (hg : ∀ sample, |g sample| ≤ D) :
    expect law (fun sample => f sample - g sample) = expect law f - expect law g := by
  change expect law (fun sample => f sample + -g sample) = _
  rw [expect_add_of_summable]
  · rw [expect_neg]
    ring
  · exact expect_summable_of_bounded law f hf
  · simpa only [mul_neg] using (expect_summable_of_bounded law g hg).neg

omit [DecidableEq ι] in
private theorem patient_terminal_payoff_bound
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (clocks : Option ι → Option ℕ) (who : Option ι) :
    |quittingPureClockTerminalPayoff reward clocks who| ≤ quittingRewardBound reward := by
  simpa only [quittingPureClockEvaluatedPayoff_terminalEvaluation,
    quittingTerminalEvaluation_zero, one_mul] using
    abs_quittingPureClockEvaluatedPayoff_le reward quittingTerminalEvaluation
      quittingTerminalEvaluation_nonneg quittingTerminalEvaluation_antitone clocks who

/-- Every complete outsider stopping law obeys the literal patient terminal
bound by lambda-plus-mu times the actual unrestricted child debts. -/
theorem patientWithdrawal_outsideStoppingLawGain_le_weighted_behaviorDebt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : PatientWithdrawalRewardCertificate reward)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) :
    quittingStoppingLawExpectedPayoff reward
        (cappedClockParentSourceLaws childLaws outsideLaw) none -
      quittingStoppingLawExpectedPayoff reward (quietParentStoppingLaws childLaws) none ≤
      ∑ i, certificate.debtWeight i *
        (quittingBehaviorDeviationPayoffCap reward
            (quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)) (some i) -
          quittingStoppingLawExpectedPayoff reward
            (quietParentStoppingLaws childLaws) (some i)) := by
  let law := cappedClockIndependentSample childLaws outsideLaw
  have hquiet (who : Option ι) : expect law (fun sample =>
      quittingPureClockTerminalPayoff reward (quietParentClocks sample.1) who) =
      quittingStoppingLawExpectedPayoff reward (quietParentStoppingLaws childLaws) who := by
    simpa only [quittingPureClockEvaluatedPayoff_terminalEvaluation,
      quittingStoppingLawEvaluatedPayoff_terminalEvaluation] using
      expect_cappedClockIndependentSample_quiet_eq_stoppingLaw
        reward quittingTerminalEvaluation childLaws outsideLaw who
  have hleft : expect law (fun sample =>
      cappedClockActualOutsideGain reward sample.1 sample.2) =
      quittingStoppingLawExpectedPayoff reward
          (cappedClockParentSourceLaws childLaws outsideLaw) none -
        quittingStoppingLawExpectedPayoff reward (quietParentStoppingLaws childLaws) none := by
    change expect law (fun sample => quittingPureClockTerminalPayoff reward
      (outsideDeadlineClocks sample.1 sample.2) none -
      quittingPureClockTerminalPayoff reward (quietParentClocks sample.1) none) = _
    rw [patient_expect_sub_of_bounds law _ _
      (fun sample => patient_terminal_payoff_bound reward _ _)
      (fun sample => patient_terminal_payoff_bound reward _ _), hquiet]
    congr 1
    simpa only [quittingPureClockEvaluatedPayoff_terminalEvaluation,
      quittingStoppingLawEvaluatedPayoff_terminalEvaluation] using
      expect_cappedClockIndependentSample_outside_eq_stoppingLaw
        reward quittingTerminalEvaluation childLaws outsideLaw
  have hpatient (i : ι) : expect law (fun sample =>
      patientWithdrawalTerminalGain reward sample.1 sample.2 i) ≤
      quittingBehaviorDeviationPayoffCap reward
          (quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)) (some i) -
        quittingStoppingLawExpectedPayoff reward (quietParentStoppingLaws childLaws) (some i) :=
        by
    change expect law (fun sample =>
      patientWithdrawalTerminalPayoffLimit reward sample.1 sample.2 i -
      quittingPureClockTerminalPayoff reward (quietParentClocks sample.1) (some i)) ≤ _
    rw [patient_expect_sub_of_bounds law _ _
      (fun sample => abs_patientWithdrawalTerminalPayoffLimit_le reward sample.1 sample.2 i)
      (fun sample => patient_terminal_payoff_bound reward _ _), hquiet]
    exact sub_le_sub_right
      (patientWithdrawal_expectedTerminalPayoffLimit_le_behaviorDeviationCap
        reward childLaws outsideLaw i) _
  have hadvance (i : ι) : expect law (fun sample =>
      cappedClockActualChildGain reward sample.1 sample.2 i) ≤
      quittingBehaviorDeviationPayoffCap reward
          (quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)) (some i) -
        quittingStoppingLawExpectedPayoff reward (quietParentStoppingLaws childLaws) (some i) :=
        by
    have hcapped := expect_parentSource_cappedChild_eq_stoppingLawEvaluatedPayoff
      reward quittingTerminalEvaluation childLaws outsideLaw i
    rw [← map_cappedClockIndependentSample_outside childLaws outsideLaw, expect_map] at hcapped
    simp only [outsideDeadlineClocks, quittingPureClockEvaluatedPayoff_terminalEvaluation,
      quittingStoppingLawEvaluatedPayoff_terminalEvaluation] at hcapped
    change expect law (fun sample => quittingPureClockTerminalPayoff reward
      (cappedChildParentClocks sample.1 sample.2 i) (some i) -
      quittingPureClockTerminalPayoff reward (quietParentClocks sample.1) (some i)) ≤ _
    rw [patient_expect_sub_of_bounds law _ _
      (fun sample => patient_terminal_payoff_bound reward _ _)
      (fun sample => patient_terminal_payoff_bound reward _ _), hquiet, hcapped]
    apply sub_le_sub_right
    simpa only [quittingStoppingLawEvaluatedPayoff_terminalEvaluation,
      quittingBehaviorEvaluatedDeviationPayoffCap_terminalEvaluation] using
      cappedChild_stoppingLawEvaluatedPayoff_le_behaviorDeviationCap reward
        quittingTerminalEvaluation quittingTerminalEvaluation_nonneg
        quittingTerminalEvaluation_antitone childLaws outsideLaw i
  have hpoint := expect_patientWithdrawalOutsideGain_le_weighted_childExpectations
    reward certificate law
  rw [hleft] at hpoint
  refine hpoint.trans (Finset.sum_le_sum fun i _ => ?_)
  calc
    _ ≤ certificate.advanceWeight i *
          (quittingBehaviorDeviationPayoffCap reward
              (quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)) (some i) -
            quittingStoppingLawExpectedPayoff reward (quietParentStoppingLaws childLaws)
              (some i)) +
        certificate.withdrawalWeight i *
          (quittingBehaviorDeviationPayoffCap reward
              (quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)) (some i) -
            quittingStoppingLawExpectedPayoff reward (quietParentStoppingLaws childLaws)
              (some i)) := add_le_add
      (mul_le_mul_of_nonneg_left (hadvance i) (certificate.advanceWeight_nonneg i))
      (mul_le_mul_of_nonneg_left (hpatient i) (certificate.withdrawalWeight_nonneg i))
    _ = _ := by rw [PatientWithdrawalRewardCertificate.debtWeight]; ring

/-- Supremizing over all actual behavioral outsider replacements preserves
the source-produced patient terminal full-debt bound. -/
theorem patientWithdrawal_outsideBehaviorDebt_le_weighted_childDebt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : PatientWithdrawalRewardCertificate reward)
    (childLaws : ι → PMF (Option ℕ)) :
    quittingBehaviorDeviationPayoffCap reward
        (quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)) none -
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)) none ≤
      ∑ i, certificate.debtWeight i *
        (quittingBehaviorDeviationPayoffCap reward
            (quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)) (some i) -
          quittingTerminalPayoff reward
            (quittingStoppingLawProfile reward (quietParentStoppingLaws childLaws)) (some i)) := by
  have h := outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt_add_const_of_stoppingLaw
    reward certificate.debtWeight quittingTerminalEvaluation childLaws 0
    (fun outsideLaw => by
      simpa only [quittingStoppingLawEvaluatedPayoff_terminalEvaluation,
        quittingBehaviorEvaluatedDeviationPayoffCap_terminalEvaluation, add_zero] using
        patientWithdrawal_outsideStoppingLawGain_le_weighted_behaviorDebt
          reward certificate childLaws outsideLaw)
  simpa only [quittingBehaviorEvaluatedDeviationPayoffCap_terminalEvaluation,
    quittingBehaviorEvaluatedPayoff_terminalEvaluation, add_zero] using h

end GameTheory
