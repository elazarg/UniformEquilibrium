import UniformEquilibrium.Quitting.Classification.QuietExtension.CancellationWithdrawalComparison
import MathUE.ProbabilityMassFunction.FiniteSumExpectation

/-! # Bounded integration of evaluated cancellation

The deterministic raw-row comparison is integrated over any coupled clock law.
Finite weighted sums commute with expectation by uniform boundedness, without
strategy convergence, a patient limit, or a supplied response-cap field.
This statement is not yet the actual parent behavioral-debt/family consumer.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability _root_.Math.ProbabilityMassFunction
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Every coupled law satisfies the integrated evaluated cancellation comparison. -/
theorem expect_cancellationWithdrawalOutsideGain_le_sum_childExpectations
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CancellationWithdrawalRewardCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (law : PMF ((ι → Option ℕ) × Option ℕ)) :
    expect law (fun sample => cappedClockActualEvaluatedOutsideGain reward evaluation
        sample.1 sample.2) ≤
      ∑ i, (certificate.advanceWeight i *
          expect law (fun sample => cappedClockActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i) +
        certificate.withdrawalWeight i *
          expect law (fun sample => cancellationActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i)) := by
  let gainBound := 2 * (evaluation 0 * quittingRewardBound reward)
  let advance (i : ι) (sample : (ι → Option ℕ) × Option ℕ) :=
    cappedClockActualEvaluatedChildGain reward evaluation sample.1 sample.2 i
  let cancellation (i : ι) (sample : (ι → Option ℕ) × Option ℕ) :=
    cancellationActualEvaluatedChildGain reward evaluation sample.1 sample.2 i
  let weighted (i : ι) (sample : (ι → Option ℕ) × Option ℕ) :=
    certificate.advanceWeight i * advance i sample +
      certificate.withdrawalWeight i * cancellation i sample
  let bound (i : ι) :=
    (|certificate.advanceWeight i| + |certificate.withdrawalWeight i|) * gainBound
  have hadvance (i : ι) (sample : (ι → Option ℕ) × Option ℕ) :
      |advance i sample| ≤ gainBound :=
    abs_quittingPureClockEvaluatedPayoff_sub_le reward evaluation
      evaluation_nonneg evaluation_antitone
      (cappedChildParentClocks sample.1 sample.2 i) (quietParentClocks sample.1) (some i)
  have hcancellation (i : ι) (sample : (ι → Option ℕ) × Option ℕ) :
      |cancellation i sample| ≤ gainBound :=
    abs_quittingPureClockEvaluatedPayoff_sub_le reward evaluation
      evaluation_nonneg evaluation_antitone
      (cancellationParentClocks sample.1 sample.2 i) (quietParentClocks sample.1) (some i)
  have hbound (i : ι) (sample : (ι → Option ℕ) × Option ℕ) :
      |weighted i sample| ≤ bound i := by
    calc
      |_ + _| ≤ |certificate.advanceWeight i * advance i sample| +
          |certificate.withdrawalWeight i * cancellation i sample| := abs_add_le _ _
      _ ≤ |certificate.advanceWeight i| * gainBound +
          |certificate.withdrawalWeight i| * gainBound := by
        rw [abs_mul, abs_mul]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hadvance i sample) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (hcancellation i sample) (abs_nonneg _))
      _ = _ := by dsimp [bound]; ring
  have hpoint : expect law (fun sample => cappedClockActualEvaluatedOutsideGain
      reward evaluation sample.1 sample.2) ≤
      expect law (fun sample => ∑ i, weighted i sample) := by
    apply expect_mono_of_pointwise_summable
    · intro sample
      exact cancellationWithdrawalActualEvaluatedOutsideGain_le_weighted_childGains
        reward certificate evaluation evaluation_nonneg evaluation_antitone sample.1 sample.2
    · exact expect_summable_of_bounded law _ fun sample =>
        abs_quittingPureClockEvaluatedPayoff_sub_le reward evaluation
          evaluation_nonneg evaluation_antitone
          (outsideDeadlineClocks sample.1 sample.2) (quietParentClocks sample.1) none
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
      certificate.withdrawalWeight i * cancellation i sample) = _
  rw [expect_add_of_summable]
  · rw [expect_const_mul, expect_const_mul]
  · exact expect_summable_of_bounded law _
      (C := |certificate.advanceWeight i| * gainBound) fun sample => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hadvance i sample) (abs_nonneg _)
  · exact expect_summable_of_bounded law _
      (C := |certificate.withdrawalWeight i| * gainBound) fun sample => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hcancellation i sample) (abs_nonneg _)

end GameTheory
