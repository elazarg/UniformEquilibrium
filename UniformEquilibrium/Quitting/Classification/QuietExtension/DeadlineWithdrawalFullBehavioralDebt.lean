import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalMixedGain
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalOutsideMarginal
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockEvaluatedChildDeletionAdapter

/-!
# Full behavioral deadline-withdrawal debt comparison

The deterministic all-evaluation D rows, bounded product expectations, and
the legal private mixed response together control every outsider behavioral
replacement. The fixed quiet-lift target is then transported to actual child
behavioral debts without changing the profile.
-/

noncomputable section

namespace GameTheory

open _root_.Math _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance deadlineWithdrawalDebtChildNonempty :
    Nonempty {who : Option ι // ¬ who = none} :=
  Nonempty.map (fun who => ⟨some who, Option.some_ne_none who⟩)
    (inferInstance : Nonempty ι)

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
theorem deadlineWithdrawal_outsideStoppingLawGain_le_weighted_behaviorDebt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : DeadlineWithdrawalRewardCertificate reward)
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
          deadlineWithdrawalActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i| ≤
        (certificate.advanceWeight i + certificate.withdrawalWeight i) *
          gainBound := by
    calc
      |_ + _| ≤
          |certificate.advanceWeight i *
            cappedClockActualEvaluatedChildGain reward evaluation
              sample.1 sample.2 i| +
          |certificate.withdrawalWeight i *
            deadlineWithdrawalActualEvaluatedChildGain reward evaluation
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
            (hGainBound (withdrawnChildParentClocks sample.1 sample.2 i)
              (quietParentClocks sample.1) (some i))
            (certificate.withdrawalWeight_nonneg i)
      _ = (certificate.advanceWeight i + certificate.withdrawalWeight i) *
          gainBound := by ring
  have hsum : expect law (fun sample => ∑ i, (
      certificate.advanceWeight i *
        cappedClockActualEvaluatedChildGain reward evaluation
          sample.1 sample.2 i +
      certificate.withdrawalWeight i *
        deadlineWithdrawalActualEvaluatedChildGain reward evaluation
          sample.1 sample.2 i)) =
      ∑ i, expect law (fun sample =>
        certificate.advanceWeight i *
          cappedClockActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i +
        certificate.withdrawalWeight i *
          deadlineWithdrawalActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i) := by
    simpa using expect_finset_sum_of_bounded law Finset.univ
      (fun i sample => certificate.advanceWeight i *
        cappedClockActualEvaluatedChildGain reward evaluation
          sample.1 sample.2 i +
        certificate.withdrawalWeight i *
          deadlineWithdrawalActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i)
      (fun i =>
        (certificate.advanceWeight i + certificate.withdrawalWeight i) *
          gainBound)
      (fun i _ sample => hweightedBound i sample)
  have hpoint := expect_deadlineWithdrawal_pointwise_le reward certificate
    evaluation evaluation_nonneg evaluation_antitone law
  rw [hsum] at hpoint
  have hmixed : (∑ i, expect law (fun sample =>
        certificate.advanceWeight i *
          cappedClockActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i +
        certificate.withdrawalWeight i *
          deadlineWithdrawalActualEvaluatedChildGain reward evaluation
            sample.1 sample.2 i)) =
      ∑ i, certificate.debtWeight i *
        (quittingStoppingLawEvaluatedPayoff reward evaluation
            (deadlineMixedChildParentStoppingLaws childLaws outsideLaw i
              (certificate.advanceWeight i)
              (certificate.withdrawalWeight i)
              (certificate.advanceWeight_nonneg i)
              (certificate.withdrawalWeight_nonneg i)) (some i) -
          quittingStoppingLawEvaluatedPayoff reward evaluation
            (quietParentStoppingLaws childLaws) (some i)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact (deadlineMixedPrivateReplacement_integratedGain reward evaluation
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
  exact hpoint.trans (Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left
      (sub_le_sub_right
        (deadlineMixedChild_stoppingLawEvaluatedPayoff_le_behaviorDeviationCap
          reward evaluation evaluation_nonneg evaluation_antitone
          childLaws outsideLaw i (certificate.advanceWeight i)
          (certificate.withdrawalWeight i)
          (certificate.advanceWeight_nonneg i)
          (certificate.withdrawalWeight_nonneg i)) _)
      (certificate.debtWeight_nonneg i))

/-- Taking the supremum over every behavioral outsider replacement preserves
the D bound at the fixed quiet stopping-law profile. -/
theorem deadlineWithdrawal_outsideBehaviorDebt_le_weighted_childDebt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : DeadlineWithdrawalRewardCertificate reward)
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
  simpa using
    (outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt_add_const_of_stoppingLaw
      reward certificate.debtWeight evaluation childLaws 0
      (fun outsideLaw => by simpa using
        (deadlineWithdrawal_outsideStoppingLawGain_le_weighted_behaviorDebt
          reward certificate evaluation evaluation_nonneg
          evaluation_antitone childLaws outsideLaw)))

/-- The literal all-evaluation D bound on the actual Never lift of every
child behavioral profile, with unchanged child target and full deviation caps. -/
theorem deadlineWithdrawal_quietLift_outsideBehaviorDebt_le_weighted_childDebt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : DeadlineWithdrawalRewardCertificate reward)
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
  simpa using
    (quietLift_outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt_add_const_of_canonical
      reward certificate.debtWeight evaluation childProfile 0
      (by simpa using
        (deadlineWithdrawal_outsideBehaviorDebt_le_weighted_childDebt
          reward certificate evaluation evaluation_nonneg evaluation_antitone
          (quietOutsiderChildLaws reward childProfile))))

/-- The corresponding one-outsider sum-debt bound has the exact coefficient
`1 + max(a_i,b_i)` on each actual child debt. -/
theorem deadlineWithdrawal_quietLift_totalBehaviorDebt_le_weighted_childDebt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : DeadlineWithdrawalRewardCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile) :
    let lifted := quittingLiftDeletedProfile reward (· = none) childProfile
    (∑ who : Option ι, (
      quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation lifted who -
        quittingBehaviorEvaluatedPayoff reward evaluation lifted who)) ≤
      ∑ i, (1 + certificate.debtWeight i) *
        (quittingBehaviorEvaluatedDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) evaluation childProfile
              ⟨some i, Option.some_ne_none i⟩ -
          quittingBehaviorEvaluatedPayoff
            (quittingDeleteReward reward (· = none)) evaluation childProfile
              ⟨some i, Option.some_ne_none i⟩) := by
  dsimp only
  rw [Fintype.sum_option]
  have hchild (i : ι) :
      quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
          (quittingLiftDeletedProfile reward (· = none) childProfile) (some i) -
        quittingBehaviorEvaluatedPayoff reward evaluation
          (quittingLiftDeletedProfile reward (· = none) childProfile) (some i) =
      quittingBehaviorEvaluatedDeviationPayoffCap
          (quittingDeleteReward reward (· = none)) evaluation childProfile
            ⟨some i, Option.some_ne_none i⟩ -
        quittingBehaviorEvaluatedPayoff
          (quittingDeleteReward reward (· = none)) evaluation childProfile
            ⟨some i, Option.some_ne_none i⟩ := by
    exact quittingBehaviorEvaluatedDeviationDebt_liftDeletedProfile
      (deleted := (· = none)) (reward := reward) (evaluation := evaluation)
      (profile := childProfile) (who := ⟨some i, Option.some_ne_none i⟩)
  simp_rw [hchild]
  have hout := deadlineWithdrawal_quietLift_outsideBehaviorDebt_le_weighted_childDebt
    reward certificate evaluation evaluation_nonneg evaluation_antitone
      childProfile
  dsimp only at hout
  calc
    _ ≤ (∑ i, certificate.debtWeight i *
          (quittingBehaviorEvaluatedDeviationPayoffCap
              (quittingDeleteReward reward (· = none)) evaluation childProfile
                ⟨some i, Option.some_ne_none i⟩ -
            quittingBehaviorEvaluatedPayoff
              (quittingDeleteReward reward (· = none)) evaluation childProfile
                ⟨some i, Option.some_ne_none i⟩)) +
        ∑ i, (quittingBehaviorEvaluatedDeviationPayoffCap
              (quittingDeleteReward reward (· = none)) evaluation childProfile
                ⟨some i, Option.some_ne_none i⟩ -
            quittingBehaviorEvaluatedPayoff
              (quittingDeleteReward reward (· = none)) evaluation childProfile
                ⟨some i, Option.some_ne_none i⟩) := by
      linarith [hout]
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

end GameTheory
