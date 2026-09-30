import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalRestartDominationCore
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalOutsideMarginal

/-!
# Full stopping-law gain from the shared mixed-restart interface

The internal raw-row error is retained until every actual private replacement
has been compared with its unrestricted behavioral cap. Security producers
construct the restart family and discharge its deterministic floor premise.
-/

noncomputable section

namespace GameTheory

open _root_.Math _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {floor : ι → ℝ} {rowError : ℝ}

/-- The disjoint-event mixture coefficient in the generic internal interface. -/
def DeadlineRestartRewardCertificate.debtWeight
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : DeadlineRestartRewardCertificate reward floor rowError) (i : ι) : ℝ :=
  max (certificate.advanceWeight i) (certificate.withdrawalWeight i)

omit [Nonempty ι] in
theorem DeadlineRestartRewardCertificate.debtWeight_nonneg
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : DeadlineRestartRewardCertificate reward floor rowError) (i : ι) :
    0 ≤ certificate.debtWeight i :=
  le_trans (certificate.advanceWeight_nonneg i) (le_max_left _ _)

/-- Fresh private averaging preserves the uniform reward bound. -/
theorem abs_deadlineSecurityActualEvaluatedChildGain_leWithRestart
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (restart : ℕ → PMF (Option ℕ))
    (evaluation : WithTop ℕ → ℝ)
    (hnonneg : ∀ time, 0 ≤ evaluation time) (hantitone : Antitone evaluation)
    (times : ι → Option ℕ) (deadline : Option ℕ) (i : ι) :
    |deadlineSecurityActualEvaluatedChildGainWithRestart reward restart evaluation times deadline
      i| ≤
      2 * (evaluation 0 * quittingRewardBound reward) := by
  unfold deadlineSecurityActualEvaluatedChildGainWithRestart
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

private theorem expect_deadlineSub_of_bounded {Ω : Type*} (law : PMF Ω)
    (f g : Ω → ℝ) {C D : ℝ}
    (hf : ∀ sample, |f sample| ≤ C)
    (hg : ∀ sample, |g sample| ≤ D) :
    expect law (fun sample => f sample - g sample) =
      expect law f - expect law g := by
  change expect law (fun sample => f sample + -g sample) = _
  rw [expect_add_of_summable]
  · rw [expect_neg]
    ring
  · exact expect_summable_of_bounded law f hf
  · simpa [mul_neg] using (expect_summable_of_bounded law g hg).neg

/-- The full D comparison for each complete outsider stopping law, with
literal `max(a_i,b_i)` and no correlation or supplied response cap. -/
theorem deadlineSecurity_outsideStoppingLawGain_le_weighted_behaviorDebtWithRestart
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (restart : ι → ℕ → PMF (Option ℕ))
    (certificate : DeadlineRestartRewardCertificate reward floor rowError)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (hrowError : 0 ≤ rowError)
    (hbefore : ∀ i date chosen, chosen ≤ date → restart i date (some chosen) = 0)
    (hplan : ∀ i (date : ℕ) (opponents : ι → Option ℕ), opponents i = none →
      (∀ j, (date : WithTop ℕ) < quittingStoppingTimeValue (opponents j)) →
      evaluation date * floor i ≤ expect (restart i date)
        (fun clock => quittingPureClockEvaluatedPayoff reward evaluation
          (Function.update (quietParentClocks opponents) (some i) clock) (some i))) :
    quittingStoppingLawEvaluatedPayoff reward evaluation
        (cappedClockParentSourceLaws childLaws outsideLaw) none -
      quittingStoppingLawEvaluatedPayoff reward evaluation
        (quietParentStoppingLaws childLaws) none ≤
      (∑ i, certificate.debtWeight i *
        (quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
            (quittingStoppingLawProfile reward
              (quietParentStoppingLaws childLaws)) (some i) -
          quittingStoppingLawEvaluatedPayoff reward evaluation
            (quietParentStoppingLaws childLaws) (some i))) + evaluation 0 * rowError := by
  let law := cappedClockIndependentSample childLaws outsideLaw
  let gainBound := 2 * (evaluation 0 * quittingRewardBound reward)
  have hGainBound (first second : Option ι → Option ℕ) (who : Option ι) :
      |quittingPureClockEvaluatedPayoff reward evaluation first who -
        quittingPureClockEvaluatedPayoff reward evaluation second who| ≤
          gainBound := by
    calc
      |_ - _| ≤ |quittingPureClockEvaluatedPayoff reward evaluation first who| +
          |quittingPureClockEvaluatedPayoff reward evaluation second who| :=
        abs_sub _ _
      _ ≤ evaluation 0 * quittingRewardBound reward +
          evaluation 0 * quittingRewardBound reward := add_le_add
        (abs_quittingPureClockEvaluatedPayoff_le reward evaluation
          evaluation_nonneg evaluation_antitone first who)
        (abs_quittingPureClockEvaluatedPayoff_le reward evaluation
          evaluation_nonneg evaluation_antitone second who)
      _ = gainBound := by dsimp [gainBound]; ring
  have hweightedBound (i : ι) (sample : (ι → Option ℕ) × Option ℕ) :
      |certificate.advanceWeight i *
          cappedClockActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i +
        certificate.withdrawalWeight i *
          deadlineSecurityActualEvaluatedChildGainWithRestart reward (restart i) evaluation
            sample.1 sample.2 i| ≤
        (certificate.advanceWeight i + certificate.withdrawalWeight i) *
          gainBound := by
    calc
      |_ + _| ≤
          |certificate.advanceWeight i *
            cappedClockActualEvaluatedChildGain reward evaluation
              sample.1 sample.2 i| +
          |certificate.withdrawalWeight i *
            deadlineSecurityActualEvaluatedChildGainWithRestart reward (restart i) evaluation
              sample.1 sample.2 i| := abs_add_le _ _
      _ ≤ certificate.advanceWeight i * gainBound +
          certificate.withdrawalWeight i * gainBound := by
        rw [abs_mul, abs_mul,
          abs_of_nonneg (certificate.advanceWeight_nonneg i),
          abs_of_nonneg (certificate.withdrawalWeight_nonneg i)]
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left
            (hGainBound (cappedChildParentClocks sample.1 sample.2 i)
              (quietParentClocks sample.1) (some i))
            (certificate.advanceWeight_nonneg i)
        · exact mul_le_mul_of_nonneg_left
            (abs_deadlineSecurityActualEvaluatedChildGain_leWithRestart reward (restart i)
              evaluation
              evaluation_nonneg evaluation_antitone sample.1 sample.2 i)
            (certificate.withdrawalWeight_nonneg i)
      _ = (certificate.advanceWeight i + certificate.withdrawalWeight i) *
          gainBound := by ring
  have hsum : expect law (fun sample => ∑ i, (
      certificate.advanceWeight i *
        cappedClockActualEvaluatedChildGain reward evaluation
          sample.1 sample.2 i +
      certificate.withdrawalWeight i *
        deadlineSecurityActualEvaluatedChildGainWithRestart reward (restart i) evaluation
          sample.1 sample.2 i)) =
      ∑ i, expect law (fun sample =>
        certificate.advanceWeight i *
          cappedClockActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i +
        certificate.withdrawalWeight i *
          deadlineSecurityActualEvaluatedChildGainWithRestart reward (restart i) evaluation
            sample.1 sample.2 i) := by
    simpa using expect_finset_sum_of_bounded law Finset.univ
      (fun i sample => certificate.advanceWeight i *
        cappedClockActualEvaluatedChildGain reward evaluation
          sample.1 sample.2 i +
        certificate.withdrawalWeight i *
          deadlineSecurityActualEvaluatedChildGainWithRestart reward (restart i) evaluation
            sample.1 sample.2 i)
      (fun i =>
        (certificate.advanceWeight i + certificate.withdrawalWeight i) *
          gainBound)
      (fun i _ sample => hweightedBound i sample)
  let weighted (sample : (ι → Option ℕ) × Option ℕ) := ∑ i, (
    certificate.advanceWeight i *
      cappedClockActualEvaluatedChildGain reward evaluation sample.1 sample.2 i +
    certificate.withdrawalWeight i *
      deadlineSecurityActualEvaluatedChildGainWithRestart reward (restart i)
        evaluation sample.1 sample.2 i)
  let totalBound := ∑ i,
    (certificate.advanceWeight i + certificate.withdrawalWeight i) * gainBound
  have htotal (sample : (ι → Option ℕ) × Option ℕ) : |weighted sample| ≤ totalBound := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => hweightedBound i sample)
  have hgainNonneg : 0 ≤ gainBound := by
    exact mul_nonneg (by norm_num)
      (mul_nonneg (evaluation_nonneg _) (quittingRewardBound_nonneg reward))
  have htotalNonneg : 0 ≤ totalBound := by
    exact Finset.sum_nonneg fun i _ => mul_nonneg
      (add_nonneg (certificate.advanceWeight_nonneg i)
        (certificate.withdrawalWeight_nonneg i)) hgainNonneg
  have hpoint : expect law (fun sample => cappedClockActualEvaluatedOutsideGain
      reward evaluation sample.1 sample.2) ≤
      expect law weighted + evaluation 0 * rowError := by
    have hmono : expect law (fun sample => cappedClockActualEvaluatedOutsideGain
        reward evaluation sample.1 sample.2) ≤
        expect law (fun sample => weighted sample + evaluation 0 * rowError) := by
      apply Math.ProbabilityMassFunction.expect_mono_of_pointwise_bounded
        _ _ _ _ (C := gainBound + totalBound + |evaluation 0 * rowError|)
      · intro sample
        calc
          |cappedClockActualEvaluatedOutsideGain reward evaluation sample.1 sample.2| ≤
              gainBound := hGainBound (outsideDeadlineClocks sample.1 sample.2)
                (quietParentClocks sample.1) none
          _ ≤ gainBound + totalBound := le_add_of_nonneg_right htotalNonneg
          _ ≤ gainBound + totalBound + |evaluation 0 * rowError| :=
            le_add_of_nonneg_right (abs_nonneg _)
      · intro sample
        calc
          |weighted sample + evaluation 0 * rowError| ≤
              |weighted sample| + |evaluation 0 * rowError| := abs_add_le _ _
          _ ≤ totalBound + |evaluation 0 * rowError| :=
            add_le_add (htotal sample) le_rfl
          _ ≤ gainBound + totalBound + |evaluation 0 * rowError| :=
            add_le_add (show totalBound ≤ gainBound + totalBound from
              le_add_of_nonneg_left hgainNonneg) le_rfl
      · intro sample
        exact deadlineSecurityActualEvaluatedOutsideGain_le_weighted_childGainsWithRestart
          reward restart certificate evaluation evaluation_nonneg evaluation_antitone
          sample.1 sample.2 hrowError hbefore hplan
    rw [expect_add_of_summable law weighted (fun _ => evaluation 0 * rowError)
      (expect_summable_of_bounded law weighted htotal)
      (expect_summable_of_bounded law _ (fun _ => le_rfl)), expect_const] at hmono
    exact hmono
  change _ ≤ expect law (fun sample => ∑ i, (
    certificate.advanceWeight i * cappedClockActualEvaluatedChildGain reward evaluation
      sample.1 sample.2 i + certificate.withdrawalWeight i *
        deadlineSecurityActualEvaluatedChildGainWithRestart reward (restart i)
          evaluation sample.1 sample.2 i)) + evaluation 0 * rowError at hpoint
  rw [hsum] at hpoint
  have hmixed : (∑ i, expect law (fun sample =>
        certificate.advanceWeight i *
          cappedClockActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i +
        certificate.withdrawalWeight i *
          deadlineSecurityActualEvaluatedChildGainWithRestart reward (restart i) evaluation
            sample.1 sample.2 i)) =
      ∑ i, certificate.debtWeight i *
        (quittingStoppingLawEvaluatedPayoff reward evaluation
            (deadlineSecurityMixedChildParentStoppingLawsWithRestart (restart i) childLaws
              outsideLaw i
              (certificate.advanceWeight i)
              (certificate.withdrawalWeight i)
              (certificate.advanceWeight_nonneg i)
              (certificate.withdrawalWeight_nonneg i)) (some i) -
          quittingStoppingLawEvaluatedPayoff reward evaluation
            (quietParentStoppingLaws childLaws) (some i)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact (deadlineSecurityMixedPrivateReplacement_integratedGainWithRestart
      reward (restart i) evaluation
      evaluation_nonneg evaluation_antitone childLaws outsideLaw i
      (certificate.advanceWeight i) (certificate.withdrawalWeight i)
      (certificate.advanceWeight_nonneg i)
      (certificate.withdrawalWeight_nonneg i)).symm
  rw [hmixed] at hpoint
  have hleft : expect law (fun sample =>
      cappedClockActualEvaluatedOutsideGain reward evaluation
        sample.1 sample.2) =
      quittingStoppingLawEvaluatedPayoff reward evaluation
          (cappedClockParentSourceLaws childLaws outsideLaw) none -
        quittingStoppingLawEvaluatedPayoff reward evaluation
          (quietParentStoppingLaws childLaws) none := by
    change expect law (fun sample =>
      quittingPureClockEvaluatedPayoff reward evaluation
          (outsideDeadlineClocks sample.1 sample.2) none -
        quittingPureClockEvaluatedPayoff reward evaluation
          (quietParentClocks sample.1) none) = _
    have hsub := expect_deadlineSub_of_bounded law
      (fun sample => quittingPureClockEvaluatedPayoff reward evaluation
        (outsideDeadlineClocks sample.1 sample.2) none)
      (fun sample => quittingPureClockEvaluatedPayoff reward evaluation
        (quietParentClocks sample.1) none)
      (C := evaluation 0 * quittingRewardBound reward)
      (D := evaluation 0 * quittingRewardBound reward)
      (by
        intro sample
        exact abs_quittingPureClockEvaluatedPayoff_le reward evaluation
          evaluation_nonneg evaluation_antitone
          (outsideDeadlineClocks sample.1 sample.2) none)
      (by
        intro sample
        exact abs_quittingPureClockEvaluatedPayoff_le reward evaluation
          evaluation_nonneg evaluation_antitone
          (quietParentClocks sample.1) none)
    rw [hsub, expect_cappedClockIndependentSample_outside_eq_stoppingLaw,
      expect_cappedClockIndependentSample_quiet_eq_stoppingLaw]
  rw [hleft] at hpoint
  exact hpoint.trans (add_le_add (Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left
      (sub_le_sub_right
        (deadlineSecurityMixedChild_payoff_le_behaviorDeviationCapWithRestart
          reward (restart i) evaluation evaluation_nonneg evaluation_antitone
          childLaws outsideLaw i (certificate.advanceWeight i)
          (certificate.withdrawalWeight i)
          (certificate.advanceWeight_nonneg i)
          (certificate.withdrawalWeight_nonneg i)) _)
      (certificate.debtWeight_nonneg i)) le_rfl)


end GameTheory
