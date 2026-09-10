import MathUE.PMFProduct.Basic
import MathUE.ProbabilityMassFunction.FiniteSumExpectation
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockStoppingLaw
import UniformEquilibrium.Quitting.RewardBound


/-!
# Expectation bridge for capped-clock pointwise domination

This module integrates the literal deterministic comparison over independent
child clocks and one fresh outsider clock.  It does not exchange a supremum
with an expectation and does not assume a response cap is attained.
-/

noncomputable section

namespace GameTheory

open Math Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Independent sample of the whole child clock tuple and one fresh outsider
clock. -/
def cappedClockIndependentSample
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) :
    PMF ((ι → Option ℕ) × Option ℕ) :=
  (pmfPi childLaws).bind fun times =>
    outsideLaw.map fun deadline => (times, deadline)

private theorem abs_quittingPureClockEvaluatedPayoff_le
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (times : Option ι → Option ℕ) (who : Option ι) :
    |quittingPureClockEvaluatedPayoff reward evaluation times who| ≤
      evaluation 0 * quittingRewardBound reward := by
  unfold quittingPureClockEvaluatedPayoff
  cases quittingFirstStoppingOutcome times with
  | none =>
      simp only [abs_zero]
      exact mul_nonneg (evaluation_nonneg 0) (quittingRewardBound_nonneg reward)
  | some outcome =>
      rw [abs_mul, abs_of_nonneg (evaluation_nonneg _)]
      exact mul_le_mul
        (evaluation_antitone bot_le)
        (abs_reward_le_quittingRewardBound reward outcome who)
        (abs_nonneg _) (evaluation_nonneg _)

private theorem abs_actualEvaluatedGain_le
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

/-- Integrating the literal pointwise theorem over independent child and
outsider clocks preserves its inequality.  Summability is supplied internally
by the finite reward bound, so no analytic or strategic witness is assumed. -/
theorem expect_cappedClockActualEvaluatedOutsideGain_le_weighted_childGain
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CappedClockParentRewardCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) :
    expect (cappedClockIndependentSample childLaws outsideLaw) (fun sample =>
        cappedClockActualEvaluatedOutsideGain reward evaluation
          sample.1 sample.2) ≤
      expect (cappedClockIndependentSample childLaws outsideLaw) (fun sample =>
        ∑ i, certificate.weight i *
          cappedClockActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i) := by
  let gainBound := 2 * (evaluation 0 * quittingRewardBound reward)
  let weightSum := ∑ i, certificate.weight i
  have hGainBound : 0 ≤ gainBound := by
    dsimp [gainBound]
    exact mul_nonneg (by norm_num)
      (mul_nonneg (evaluation_nonneg 0) (quittingRewardBound_nonneg reward))
  have hWeightSum : 0 ≤ weightSum := by
    dsimp [weightSum]
    exact Finset.sum_nonneg fun i _ => certificate.weight_nonneg i
  apply Math.ProbabilityMassFunction.expect_mono_of_pointwise_bounded
    _ _ _ _
      (C := gainBound + weightSum * gainBound)
  · intro sample
    have h := abs_actualEvaluatedGain_le reward evaluation
      evaluation_nonneg evaluation_antitone
      (outsideDeadlineClocks sample.1 sample.2)
      (quietParentClocks sample.1) none
    change |cappedClockActualEvaluatedOutsideGain reward evaluation
      sample.1 sample.2| ≤ _
    change |cappedClockActualEvaluatedOutsideGain reward evaluation
      sample.1 sample.2| ≤ gainBound at h
    exact h.trans (by nlinarith)
  · intro sample
    calc
      |∑ i, certificate.weight i *
          cappedClockActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i| ≤
          ∑ i, |certificate.weight i *
            cappedClockActualEvaluatedChildGain reward evaluation
              sample.1 sample.2 i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, certificate.weight i * gainBound := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_nonneg (certificate.weight_nonneg i)]
        exact mul_le_mul_of_nonneg_left
          (abs_actualEvaluatedGain_le reward evaluation
            evaluation_nonneg evaluation_antitone
            (cappedChildParentClocks sample.1 sample.2 i)
            (quietParentClocks sample.1) (some i))
          (certificate.weight_nonneg i)
      _ = weightSum * gainBound := by
        rw [Finset.sum_mul]
      _ ≤ gainBound + weightSum * gainBound := by linarith
  intro sample
  exact cappedClockActualEvaluatedOutsideGain_le_weighted_actualChildGain
    reward certificate evaluation evaluation_nonneg evaluation_antitone
      sample.1 sample.2

/-- The integrated right side is the finite weighted sum of the separately
integrated actual child experiments. -/
theorem expect_cappedClock_weighted_childGain_eq_sum_expect
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CappedClockParentRewardCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) :
    expect (cappedClockIndependentSample childLaws outsideLaw) (fun sample =>
        ∑ i, certificate.weight i *
          cappedClockActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i) =
      ∑ i, certificate.weight i *
        expect (cappedClockIndependentSample childLaws outsideLaw) (fun sample =>
          cappedClockActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i) := by
  let law := cappedClockIndependentSample childLaws outsideLaw
  let gainBound := 2 * (evaluation 0 * quittingRewardBound reward)
  have hgain (i : ι) (sample : (ι → Option ℕ) × Option ℕ) :
      |cappedClockActualEvaluatedChildGain reward evaluation
          sample.1 sample.2 i| ≤ gainBound := by
    exact abs_actualEvaluatedGain_le reward evaluation
      evaluation_nonneg evaluation_antitone
      (cappedChildParentClocks sample.1 sample.2 i)
      (quietParentClocks sample.1) (some i)
  have hcomm (S : Finset ι) :
      expect law (fun sample => ∑ i ∈ S, certificate.weight i *
          cappedClockActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i) =
        ∑ i ∈ S, certificate.weight i *
          expect law (fun sample =>
            cappedClockActualEvaluatedChildGain reward evaluation
              sample.1 sample.2 i) := by
    rw [Math.Probability.expect_finset_sum_of_bounded law S
      (fun i sample => certificate.weight i *
        cappedClockActualEvaluatedChildGain reward evaluation
          sample.1 sample.2 i)
      (fun i => |certificate.weight i| * gainBound)]
    · apply Finset.sum_congr rfl
      intro i _
      rw [expect_const_mul]
    · intro i _ sample
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hgain i sample) (abs_nonneg _)
  simpa [law] using hcomm Finset.univ

/-- Integrated pointwise domination with every child counterfactual exposed as
its own expectation. -/
theorem expect_cappedClockActualEvaluatedOutsideGain_le_sum_childExpectations
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CappedClockParentRewardCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) :
    expect (cappedClockIndependentSample childLaws outsideLaw) (fun sample =>
        cappedClockActualEvaluatedOutsideGain reward evaluation
          sample.1 sample.2) ≤
      ∑ i, certificate.weight i *
        expect (cappedClockIndependentSample childLaws outsideLaw) (fun sample =>
          cappedClockActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i) := by
  rw [← expect_cappedClock_weighted_childGain_eq_sum_expect reward certificate
    evaluation evaluation_nonneg evaluation_antitone childLaws outsideLaw]
  exact expect_cappedClockActualEvaluatedOutsideGain_le_weighted_childGain
    reward certificate evaluation evaluation_nonneg evaluation_antitone
      childLaws outsideLaw

end GameTheory
