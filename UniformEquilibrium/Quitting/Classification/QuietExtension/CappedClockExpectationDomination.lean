import MathUE.PMFProduct.Basic
import MathUE.ProbabilityMassFunction.FiniteSumExpectation
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockStoppingLaw
import UniformEquilibrium.Quitting.RewardBound

/-!
# Expectation bridge for capped-clock pointwise domination

This module integrates the literal deterministic comparison over any coupled
child/outsider clock law. Independence is needed later to identify the samples
with legal unilateral experiments, not for this expectation inequality.
No supremum is exchanged with an expectation and no response cap is assumed attained.
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

/-- A nonnegative antitone clock evaluation bounds every literal evaluated
payoff by its value at time zero times the finite reward-table bound. -/
theorem abs_quittingPureClockEvaluatedPayoff_le
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

/-- Integrating the slack pointwise theorem over any coupled child/outsider
clock law preserves its inequality. Summability is supplied internally. -/
theorem expect_cappedClockActualEvaluatedOutsideGain_le_weighted_childGain_add_slack
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CappedClockParentRewardSlackCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (law : PMF ((ι → Option ℕ) × Option ℕ)) :
    expect law (fun sample =>
        cappedClockActualEvaluatedOutsideGain reward evaluation
          sample.1 sample.2) ≤
      expect law (fun sample =>
        (∑ i, certificate.weight i *
          cappedClockActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i) +
        certificate.neverSlack *
          cappedClockEvaluatedNeverSlackFactor evaluation
            sample.1 sample.2) := by
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
      (C := gainBound + weightSum * gainBound +
        certificate.neverSlack * evaluation 0)
  · intro sample
    have h := abs_actualEvaluatedGain_le reward evaluation
      evaluation_nonneg evaluation_antitone
      (outsideDeadlineClocks sample.1 sample.2)
      (quietParentClocks sample.1) none
    change |cappedClockActualEvaluatedOutsideGain reward evaluation
      sample.1 sample.2| ≤ _
    change |cappedClockActualEvaluatedOutsideGain reward evaluation
      sample.1 sample.2| ≤ gainBound at h
    have hslack : 0 ≤ certificate.neverSlack * evaluation 0 :=
      mul_nonneg certificate.neverSlack_nonneg (evaluation_nonneg 0)
    exact h.trans (by nlinarith)
  · intro sample
    calc
      |(∑ i, certificate.weight i *
          cappedClockActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i) +
        certificate.neverSlack *
          cappedClockEvaluatedNeverSlackFactor evaluation sample.1 sample.2| ≤
          (∑ i, |certificate.weight i *
            cappedClockActualEvaluatedChildGain reward evaluation
              sample.1 sample.2 i|) +
          |certificate.neverSlack *
            cappedClockEvaluatedNeverSlackFactor evaluation
              sample.1 sample.2| := by
        exact (abs_add_le _ _).trans (add_le_add_left
          (Finset.abs_sum_le_sum_abs _ _) _)
      _ ≤ (∑ i, certificate.weight i * gainBound) +
          certificate.neverSlack * evaluation 0 := by
        apply add_le_add
        · apply Finset.sum_le_sum
          intro i _
          rw [abs_mul, abs_of_nonneg (certificate.weight_nonneg i)]
          exact mul_le_mul_of_nonneg_left
            (abs_actualEvaluatedGain_le reward evaluation
              evaluation_nonneg evaluation_antitone
              (cappedChildParentClocks sample.1 sample.2 i)
              (quietParentClocks sample.1) (some i))
            (certificate.weight_nonneg i)
        · rw [abs_mul, abs_of_nonneg certificate.neverSlack_nonneg]
          exact mul_le_mul_of_nonneg_left
            (abs_cappedClockEvaluatedNeverSlackFactor_le evaluation
              evaluation_nonneg evaluation_antitone sample.1 sample.2)
            certificate.neverSlack_nonneg
      _ = weightSum * gainBound +
          certificate.neverSlack * evaluation 0 := by
        rw [Finset.sum_mul]
      _ ≤ gainBound + weightSum * gainBound +
          certificate.neverSlack * evaluation 0 := by linarith
  intro sample
  exact cappedClockActualEvaluatedOutsideGain_le_weighted_actualChildGain_add_slack
    reward certificate evaluation evaluation_nonneg evaluation_antitone
      sample.1 sample.2

/-- Exact N/F/J expectation domination is the zero-slack specialization. -/
theorem expect_cappedClockActualEvaluatedOutsideGain_le_weighted_childGain
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CappedClockParentRewardCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (law : PMF ((ι → Option ℕ) × Option ℕ)) :
    expect law (fun sample =>
        cappedClockActualEvaluatedOutsideGain reward evaluation
          sample.1 sample.2) ≤
      expect law (fun sample =>
        ∑ i, certificate.weight i *
          cappedClockActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i) := by
  simpa [CappedClockParentRewardCertificate.withZeroSlack] using
    expect_cappedClockActualEvaluatedOutsideGain_le_weighted_childGain_add_slack
      reward certificate.withZeroSlack evaluation evaluation_nonneg
        evaluation_antitone law

/-- The integrated right side is the finite weighted sum of the separately
integrated actual child experiments, for arbitrary fixed weights. -/
theorem expect_cappedClock_weighted_childGain_eq_sum_expect_of_weight
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (weight : ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (law : PMF ((ι → Option ℕ) × Option ℕ)) :
    expect law (fun sample =>
        ∑ i, weight i *
          cappedClockActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i) =
      ∑ i, weight i *
        expect law (fun sample =>
          cappedClockActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i) := by
  let gainBound := 2 * (evaluation 0 * quittingRewardBound reward)
  have hgain (i : ι) (sample : (ι → Option ℕ) × Option ℕ) :
      |cappedClockActualEvaluatedChildGain reward evaluation
          sample.1 sample.2 i| ≤ gainBound := by
    exact abs_actualEvaluatedGain_le reward evaluation
      evaluation_nonneg evaluation_antitone
      (cappedChildParentClocks sample.1 sample.2 i)
      (quietParentClocks sample.1) (some i)
  have hcomm (S : Finset ι) :
      expect law (fun sample => ∑ i ∈ S, weight i *
          cappedClockActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i) =
        ∑ i ∈ S, weight i *
          expect law (fun sample =>
            cappedClockActualEvaluatedChildGain reward evaluation
              sample.1 sample.2 i) := by
    rw [Math.Probability.expect_finset_sum_of_bounded law S
      (fun i sample => weight i *
        cappedClockActualEvaluatedChildGain reward evaluation
          sample.1 sample.2 i)
      (fun i => |weight i| * gainBound)]
    · apply Finset.sum_congr rfl
      intro i _
      rw [expect_const_mul]
    · intro i _ sample
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hgain i sample) (abs_nonneg _)
  simpa using hcomm Finset.univ

/-- Certificate-facing wrapper for the arbitrary-weight integration identity. -/
theorem expect_cappedClock_weighted_childGain_eq_sum_expect
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CappedClockParentRewardCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (law : PMF ((ι → Option ℕ) × Option ℕ)) :
    expect law (fun sample =>
        ∑ i, certificate.weight i *
          cappedClockActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i) =
      ∑ i, certificate.weight i *
        expect law (fun sample =>
          cappedClockActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i) := by
  exact expect_cappedClock_weighted_childGain_eq_sum_expect_of_weight
    reward certificate.weight evaluation evaluation_nonneg
      evaluation_antitone law

/-- Integrated pointwise domination with every child counterfactual exposed as
its own expectation. -/
theorem expect_cappedClockActualEvaluatedOutsideGain_le_sum_childExpectations
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CappedClockParentRewardCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (law : PMF ((ι → Option ℕ) × Option ℕ)) :
    expect law (fun sample =>
        cappedClockActualEvaluatedOutsideGain reward evaluation
          sample.1 sample.2) ≤
      ∑ i, certificate.weight i *
        expect law (fun sample =>
          cappedClockActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i) := by
  rw [← expect_cappedClock_weighted_childGain_eq_sum_expect reward certificate
    evaluation evaluation_nonneg evaluation_antitone law]
  exact expect_cappedClockActualEvaluatedOutsideGain_le_weighted_childGain
    reward certificate evaluation evaluation_nonneg evaluation_antitone
      law

/-- Integrated terminal slack domination, with the correction exposed as the
expected literal child joint-Never indicator. -/
theorem expect_cappedClockActualOutsideGain_le_sum_childExpectations_add_slack
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CappedClockParentRewardSlackCertificate reward)
    (law : PMF ((ι → Option ℕ) × Option ℕ)) :
    expect law (fun sample =>
        cappedClockActualOutsideGain reward sample.1 sample.2) ≤
      (∑ i, certificate.weight i *
        expect law (fun sample =>
          cappedClockActualChildGain reward sample.1 sample.2 i)) +
      certificate.neverSlack *
        expect law (fun sample => cappedClockJointNeverIndicator sample.1) := by
  let weighted := fun sample : (ι → Option ℕ) × Option ℕ =>
    ∑ i, certificate.weight i *
      cappedClockActualChildGain reward sample.1 sample.2 i
  let factor := fun sample : (ι → Option ℕ) × Option ℕ =>
    cappedClockEvaluatedNeverSlackFactor cappedClockTerminalEvaluation
      sample.1 sample.2
  have h :=
    expect_cappedClockActualEvaluatedOutsideGain_le_weighted_childGain_add_slack
      reward certificate cappedClockTerminalEvaluation
        cappedClockTerminalEvaluation_nonneg
        cappedClockTerminalEvaluation_antitone law
  simp only [cappedClockActualEvaluatedOutsideGain,
    cappedClockActualEvaluatedChildGain,
    quittingPureClockEvaluatedPayoff_terminalEvaluation] at h
  change expect law (fun sample =>
      cappedClockActualOutsideGain reward sample.1 sample.2) ≤
    expect law (fun sample => weighted sample +
      certificate.neverSlack * factor sample) at h
  have hweightedBound (sample : (ι → Option ℕ) × Option ℕ) :
      |weighted sample| ≤
        (∑ i, |certificate.weight i|) * (2 * quittingRewardBound reward) := by
    calc
      |weighted sample| ≤ ∑ i, |certificate.weight i *
          cappedClockActualChildGain reward sample.1 sample.2 i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |certificate.weight i| * (2 * quittingRewardBound reward) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        have hgain := abs_actualEvaluatedGain_le reward
          cappedClockTerminalEvaluation cappedClockTerminalEvaluation_nonneg
            cappedClockTerminalEvaluation_antitone
            (cappedChildParentClocks sample.1 sample.2 i)
            (quietParentClocks sample.1) (some i)
        have hgain' :
            |cappedClockActualChildGain reward sample.1 sample.2 i| ≤
              2 * quittingRewardBound reward := by
          simpa [cappedClockActualChildGain,
            quittingPureClockEvaluatedPayoff_terminalEvaluation,
            cappedClockTerminalEvaluation] using hgain
        exact mul_le_mul_of_nonneg_left
          hgain'
          (abs_nonneg _)
      _ = _ := by rw [Finset.sum_mul]
  have hfactorBound (sample : (ι → Option ℕ) × Option ℕ) :
      |factor sample| ≤ 1 := by
    simpa [factor, cappedClockTerminalEvaluation] using
      abs_cappedClockEvaluatedNeverSlackFactor_le
        cappedClockTerminalEvaluation cappedClockTerminalEvaluation_nonneg
          cappedClockTerminalEvaluation_antitone sample.1 sample.2
  have hcorrectionBound (sample : (ι → Option ℕ) × Option ℕ) :
      |certificate.neverSlack * factor sample| ≤ certificate.neverSlack := by
    rw [abs_mul, abs_of_nonneg certificate.neverSlack_nonneg]
    simpa using mul_le_mul_of_nonneg_left
      (hfactorBound sample) certificate.neverSlack_nonneg
  rw [Math.Probability.expect_add_of_summable] at h
  · rw [expect_const_mul] at h
    have hweightedExpect : expect law weighted =
        ∑ i, certificate.weight i *
          expect law (fun sample =>
            cappedClockActualChildGain reward sample.1 sample.2 i) := by
      simpa [weighted, cappedClockActualChildGain,
        cappedClockActualEvaluatedChildGain,
        quittingPureClockEvaluatedPayoff_terminalEvaluation] using
          (expect_cappedClock_weighted_childGain_eq_sum_expect_of_weight
            reward certificate.weight cappedClockTerminalEvaluation
              cappedClockTerminalEvaluation_nonneg
              cappedClockTerminalEvaluation_antitone law)
    rw [hweightedExpect] at h
    have hfactorExpect : expect law factor ≤
        expect law (fun sample => cappedClockJointNeverIndicator sample.1) := by
      apply Math.ProbabilityMassFunction.expect_mono_of_pointwise_bounded
        law factor (fun sample => cappedClockJointNeverIndicator sample.1)
      · intro sample
        exact cappedClockEvaluatedNeverSlackFactor_terminal_le_jointNeverIndicator
          sample.1 sample.2
      · exact hfactorBound
      · intro sample
        exact abs_cappedClockJointNeverIndicator_le_one sample.1
    exact h.trans (add_le_add_right
      (mul_le_mul_of_nonneg_left hfactorExpect certificate.neverSlack_nonneg) _)
  · exact Math.Probability.expect_summable_of_bounded law weighted hweightedBound
  · exact Math.Probability.expect_summable_of_bounded law _ hcorrectionBound

end GameTheory
