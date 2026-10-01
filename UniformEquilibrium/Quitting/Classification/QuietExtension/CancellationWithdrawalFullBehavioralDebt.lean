import UniformEquilibrium.Quitting.Classification.QuietExtension.CancellationWithdrawalExpectation
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockIndependentGain
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockEvaluatedChildDeletionAdapter

/-! # Full evaluated cancellation debt at the actual quiet lift

Advance and future cancellation are separate legal independent-law experiments.
Both are capped by the same unchanged child debt, giving their summed coefficient.
The raw rows use the passive zero floor at every nonnegative antitone evaluation.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance cancellationWithdrawalDebtChildNonempty :
    Nonempty {who : Option ι // ¬ who = none} :=
  Nonempty.map (fun who => ⟨some who, Option.some_ne_none who⟩)
    (inferInstance : Nonempty ι)

/-- Each actual complete outsider law satisfies the cancellation debt bound.
Both child operations have their own product marginal and complete behavioral cap. -/
theorem cancellationWithdrawal_outsideStoppingLawGain_le_weighted_behaviorDebt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CancellationWithdrawalRewardCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) :
    quittingStoppingLawEvaluatedPayoff reward evaluation
        (cappedClockParentSourceLaws childLaws outsideLaw) none -
      quittingStoppingLawEvaluatedPayoff reward evaluation
        (quietParentStoppingLaws childLaws) none ≤
      ∑ i, certificate.debtWeight i *
        (quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
            (quittingStoppingLawProfile reward
              (quietParentStoppingLaws childLaws)) (some i) -
          quittingStoppingLawEvaluatedPayoff reward evaluation
            (quietParentStoppingLaws childLaws) (some i)) := by
  have hpoint := expect_cancellationWithdrawalOutsideGain_le_sum_childExpectations
    reward certificate evaluation evaluation_nonneg evaluation_antitone
      (cappedClockIndependentSample childLaws outsideLaw)
  rw [expect_cappedClockIndependentSample_outsideGain_eq_stoppingLawGain
    reward evaluation evaluation_nonneg evaluation_antitone childLaws outsideLaw] at hpoint
  refine hpoint.trans (Finset.sum_le_sum fun i _ => ?_)
  calc
    _ ≤ certificate.advanceWeight i *
          (quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
              (quittingStoppingLawProfile reward
                (quietParentStoppingLaws childLaws)) (some i) -
            quittingStoppingLawEvaluatedPayoff reward evaluation
              (quietParentStoppingLaws childLaws) (some i)) +
        certificate.withdrawalWeight i *
          (quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
              (quittingStoppingLawProfile reward
                (quietParentStoppingLaws childLaws)) (some i) -
            quittingStoppingLawEvaluatedPayoff reward evaluation
              (quietParentStoppingLaws childLaws) (some i)) := add_le_add
      (mul_le_mul_of_nonneg_left
        (expect_cappedClockIndependentSample_childGain_le_behaviorDebt
          reward evaluation evaluation_nonneg evaluation_antitone childLaws outsideLaw i)
        (certificate.advanceWeight_nonneg i))
      (mul_le_mul_of_nonneg_left
        (cancellation_expectedEvaluatedGain_le_behaviorDeviationDebt
          reward evaluation evaluation_nonneg evaluation_antitone childLaws outsideLaw i)
        (certificate.withdrawalWeight_nonneg i))
    _ = _ := by rw [CancellationWithdrawalRewardCertificate.debtWeight, add_mul]

/-- The supremum over every behavioral outsider replacement preserves the
source-proved cancellation bound, including complete Never responses. -/
theorem cancellationWithdrawal_outsideBehaviorDebt_le_weighted_childDebt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CancellationWithdrawalRewardCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (childLaws : ι → PMF (Option ℕ)) :
    quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
        (quittingStoppingLawProfile reward
          (quietParentStoppingLaws childLaws)) none -
      quittingBehaviorEvaluatedPayoff reward evaluation
        (quittingStoppingLawProfile reward
          (quietParentStoppingLaws childLaws)) none ≤
      ∑ i, certificate.debtWeight i *
        (quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
            (quittingStoppingLawProfile reward
              (quietParentStoppingLaws childLaws)) (some i) -
          quittingBehaviorEvaluatedPayoff reward evaluation
            (quittingStoppingLawProfile reward
              (quietParentStoppingLaws childLaws)) (some i)) := by
  simpa only [add_zero] using
    (outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt_add_const_of_stoppingLaw
      reward certificate.debtWeight evaluation childLaws 0
      (fun outsideLaw => by
        simpa only [add_zero] using
          cancellationWithdrawal_outsideStoppingLawGain_le_weighted_behaviorDebt
            reward certificate evaluation evaluation_nonneg evaluation_antitone
              childLaws outsideLaw))

/-- The bound applies to the actual Never lift of every child profile, with
its full evaluated payoff and deviation envelope preserved exactly. -/
theorem cancellationWithdrawal_quietLift_outsideBehaviorDebt_le_weighted_childDebt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CancellationWithdrawalRewardCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile) :
    let lifted := quittingLiftDeletedProfile reward (· = none) childProfile
    quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation lifted none -
        quittingBehaviorEvaluatedPayoff reward evaluation lifted none ≤
      ∑ i, certificate.debtWeight i *
        (quittingBehaviorEvaluatedDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) evaluation childProfile
              ⟨some i, Option.some_ne_none i⟩ -
          quittingBehaviorEvaluatedPayoff
            (quittingDeleteReward reward (· = none)) evaluation childProfile
              ⟨some i, Option.some_ne_none i⟩) := by
  simpa only [add_zero] using
    (quietLift_outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt_add_const_of_canonical
      reward certificate.debtWeight evaluation childProfile 0
      (by
        simpa only [add_zero] using
          cancellationWithdrawal_outsideBehaviorDebt_le_weighted_childDebt
            reward certificate evaluation evaluation_nonneg evaluation_antitone
              (quietOutsiderChildLaws reward childProfile)))

end GameTheory
