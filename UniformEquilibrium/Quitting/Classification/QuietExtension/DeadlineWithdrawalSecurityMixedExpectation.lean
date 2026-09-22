import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityMixedDomination
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockExpectationDomination

/-! # Bounded expectation of the security-restart row comparison -/

noncomputable section

namespace GameTheory

open _root_.Math _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Fresh private averaging preserves the uniform reward bound. -/
theorem abs_deadlineSecurityActualEvaluatedChildGain_le
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (hnonneg : ∀ time, 0 ≤ evaluation time) (hantitone : Antitone evaluation)
    (times : ι → Option ℕ) (deadline : Option ℕ) (i : ι) :
    |deadlineSecurityActualEvaluatedChildGain reward evaluation times deadline i| ≤
      2 * (evaluation 0 * quittingRewardBound reward) := by
  unfold deadlineSecurityActualEvaluatedChildGain
  calc
    |_ - _| ≤ |_root_.Math.Probability.expect _ _| +
        |quittingPureClockEvaluatedPayoff reward evaluation
          (quietParentClocks times) (some i)| := abs_sub _ _
    _ ≤ evaluation 0 * quittingRewardBound reward +
        evaluation 0 * quittingRewardBound reward := add_le_add
      (abs_expect_le_of_abs_le _ _ fun clock =>
        abs_quittingPureClockEvaluatedPayoff_le reward evaluation hnonneg hantitone _ _)
      (abs_quittingPureClockEvaluatedPayoff_le reward evaluation hnonneg hantitone _ _)
    _ = _ := by ring

omit [DecidableEq ι] in
private theorem abs_deadlineEvaluatedGain_le
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (first second : Option ι → Option ℕ) (who : Option ι) :
    |quittingPureClockEvaluatedPayoff reward evaluation first who -
        quittingPureClockEvaluatedPayoff reward evaluation second who| ≤
      2 * (evaluation 0 * quittingRewardBound reward) := by
  calc
    |_ - _| ≤
        |quittingPureClockEvaluatedPayoff reward evaluation first who| +
          |quittingPureClockEvaluatedPayoff reward evaluation second who| :=
      abs_sub _ _
    _ ≤ evaluation 0 * quittingRewardBound reward +
        evaluation 0 * quittingRewardBound reward := add_le_add
      (abs_quittingPureClockEvaluatedPayoff_le reward evaluation
        evaluation_nonneg evaluation_antitone first who)
      (abs_quittingPureClockEvaluatedPayoff_le reward evaluation
        evaluation_nonneg evaluation_antitone second who)
    _ = _ := by ring

/-- The literal deterministic a/b comparison integrates over any coupled
clock law; independence is only needed later to identify legal marginals. -/
theorem expect_deadlineSecurity_pointwise_le
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : DeadlineSecurityRewardCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (law : PMF ((ι → Option ℕ) × Option ℕ)) :
    expect law (fun sample => cappedClockActualEvaluatedOutsideGain reward evaluation
        sample.1 sample.2) ≤
      expect law (fun sample => ∑ i,
        (certificate.advanceWeight i *
            cappedClockActualEvaluatedChildGain reward evaluation
              sample.1 sample.2 i +
          certificate.withdrawalWeight i *
            deadlineSecurityActualEvaluatedChildGain reward evaluation
              sample.1 sample.2 i)) := by
  let gainBound := 2 * (evaluation 0 * quittingRewardBound reward)
  let weightSum := ∑ i, (certificate.advanceWeight i + certificate.withdrawalWeight i)
  have hgainBound : 0 ≤ gainBound := by
    dsimp [gainBound]
    exact mul_nonneg (by norm_num)
      (mul_nonneg (evaluation_nonneg 0) (quittingRewardBound_nonneg reward))
  have hweightSum : 0 ≤ weightSum := by
    dsimp [weightSum]
    exact Finset.sum_nonneg fun i _ => add_nonneg
      (certificate.advanceWeight_nonneg i) (certificate.withdrawalWeight_nonneg i)
  apply Math.ProbabilityMassFunction.expect_mono_of_pointwise_bounded
    _ _ _ _ (C := gainBound + weightSum * gainBound)
  · intro sample
    have h := abs_deadlineEvaluatedGain_le reward evaluation
      evaluation_nonneg evaluation_antitone
      (outsideDeadlineClocks sample.1 sample.2)
      (quietParentClocks sample.1) none
    change |cappedClockActualEvaluatedOutsideGain reward evaluation
      sample.1 sample.2| ≤ gainBound at h
    exact h.trans (le_add_of_nonneg_right (mul_nonneg hweightSum hgainBound))
  · intro sample
    calc
      |∑ i, (certificate.advanceWeight i *
          cappedClockActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i +
        certificate.withdrawalWeight i *
          deadlineSecurityActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i)| ≤
        ∑ i, |certificate.advanceWeight i *
            cappedClockActualEvaluatedChildGain reward evaluation
              sample.1 sample.2 i +
          certificate.withdrawalWeight i *
            deadlineSecurityActualEvaluatedChildGain reward evaluation
              sample.1 sample.2 i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (certificate.advanceWeight i + certificate.withdrawalWeight i) *
          gainBound := by
        apply Finset.sum_le_sum
        intro i _
        calc
          |_ + _| ≤ |certificate.advanceWeight i *
              cappedClockActualEvaluatedChildGain reward evaluation
                sample.1 sample.2 i| +
              |certificate.withdrawalWeight i *
                deadlineSecurityActualEvaluatedChildGain reward evaluation
                  sample.1 sample.2 i| := abs_add_le _ _
          _ ≤ certificate.advanceWeight i * gainBound +
                certificate.withdrawalWeight i * gainBound := by
            rw [abs_mul, abs_mul,
              abs_of_nonneg (certificate.advanceWeight_nonneg i),
              abs_of_nonneg (certificate.withdrawalWeight_nonneg i)]
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left
                (abs_deadlineEvaluatedGain_le reward evaluation
                  evaluation_nonneg evaluation_antitone
                  (cappedChildParentClocks sample.1 sample.2 i)
                  (quietParentClocks sample.1) (some i))
                (certificate.advanceWeight_nonneg i)
            · exact mul_le_mul_of_nonneg_left
                (abs_deadlineSecurityActualEvaluatedChildGain_le reward evaluation
                  evaluation_nonneg evaluation_antitone sample.1 sample.2 i)
                (certificate.withdrawalWeight_nonneg i)
          _ = _ := by ring
      _ = weightSum * gainBound := by rw [Finset.sum_mul]
      _ ≤ gainBound + weightSum * gainBound := by linarith
  intro sample
  exact deadlineSecurityActualEvaluatedOutsideGain_le_weighted_childGains
    reward certificate evaluation evaluation_nonneg evaluation_antitone
    sample.1 sample.2

end GameTheory
