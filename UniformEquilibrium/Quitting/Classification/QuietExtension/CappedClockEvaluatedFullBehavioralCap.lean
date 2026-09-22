import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockEvaluatedActualPayoffAdapter
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockExpectationDomination

/-!
# Full evaluated behavioral cap from capped clocks

The exact capped-clock rows bound every complete outsider stopping law under a
nonnegative antitone evaluation.  Extracting the stopping law of an arbitrary
behavioral replacement then bounds the outsider's unrestricted behavioral
deviation cap.  No maximizing replacement is assumed.
-/

noncomputable section

namespace GameTheory

open _root_.Math _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Every complete outsider stopping law obeys the weighted full evaluated
behavioral-debt bound of the child coordinates in the quiet parent profile. -/
theorem outsideStoppingLawEvaluatedGain_le_weighted_behaviorDeviationDebt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CappedClockParentRewardCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) :
    quittingStoppingLawEvaluatedPayoff reward evaluation
        (cappedClockParentSourceLaws childLaws outsideLaw) none -
      quittingStoppingLawEvaluatedPayoff reward evaluation
        (quietParentStoppingLaws childLaws) none ≤
      ∑ i, certificate.weight i *
        (quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
            (quittingStoppingLawProfile reward
              (quietParentStoppingLaws childLaws)) (some i) -
          quittingStoppingLawEvaluatedPayoff reward evaluation
            (quietParentStoppingLaws childLaws) (some i)) := by
  let source := pmfPi (cappedClockParentSourceLaws childLaws outsideLaw)
  let coupled : PMF ((ι → Option ℕ) × Option ℕ) := source.map fun clocks =>
    (fun i => clocks (some i), clocks none)
  have h := expect_cappedClockActualEvaluatedOutsideGain_le_sum_childExpectations
    reward certificate evaluation evaluation_nonneg evaluation_antitone coupled
  simp only [coupled, expect_map] at h
  simp only [cappedClockActualEvaluatedOutsideGain,
    cappedClockActualEvaluatedChildGain] at h
  have hpayBound (who : Option ι)
      (f : (Option ι → Option ℕ) → (Option ι → Option ℕ)) :
      Summable fun clocks =>
        (source clocks).toReal *
          quittingPureClockEvaluatedPayoff reward evaluation (f clocks) who :=
    Math.Probability.expect_summable_of_bounded source _ fun clocks =>
      abs_quittingPureClockEvaluatedPayoff_le reward evaluation
        evaluation_nonneg evaluation_antitone (f clocks) who
  have hexpectSub (who : Option ι)
      (f g : (Option ι → Option ℕ) → (Option ι → Option ℕ)) :
      expect source (fun clocks =>
          quittingPureClockEvaluatedPayoff reward evaluation (f clocks) who -
            quittingPureClockEvaluatedPayoff reward evaluation (g clocks) who) =
        expect source (fun clocks =>
          quittingPureClockEvaluatedPayoff reward evaluation (f clocks) who) -
        expect source (fun clocks =>
          quittingPureClockEvaluatedPayoff reward evaluation (g clocks) who) := by
    change expect source (fun clocks =>
        quittingPureClockEvaluatedPayoff reward evaluation (f clocks) who +
          -quittingPureClockEvaluatedPayoff reward evaluation (g clocks) who) = _
    rw [expect_add_of_summable]
    · rw [expect_neg]
      ring
    · exact hpayBound who f
    · simpa [mul_neg] using (hpayBound who g).neg
  rw [hexpectSub none] at h
  simp_rw [hexpectSub (some _)] at h
  rw [expect_parentSource_outside_eq_stoppingLawEvaluatedPayoff
      reward evaluation childLaws outsideLaw,
    expect_parentSource_quiet_eq_stoppingLawEvaluatedPayoff
      reward evaluation childLaws outsideLaw none] at h
  refine h.trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [expect_parentSource_cappedChild_eq_stoppingLawEvaluatedPayoff
      reward evaluation childLaws outsideLaw i,
    expect_parentSource_quiet_eq_stoppingLawEvaluatedPayoff
      reward evaluation childLaws outsideLaw (some i)]
  apply mul_le_mul_of_nonneg_left _ (certificate.weight_nonneg i)
  exact sub_le_sub_right
    (cappedChild_stoppingLawEvaluatedPayoff_le_behaviorDeviationCap
      reward evaluation evaluation_nonneg evaluation_antitone
        childLaws outsideLaw i) _

/-- The outsider's unrestricted behavioral evaluated debt in the quiet parent
profile is bounded by the weighted evaluated debts of the child coordinates. -/
theorem outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CappedClockParentRewardCertificate reward)
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
      ∑ i, certificate.weight i *
        (quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
            (quittingStoppingLawProfile reward
              (quietParentStoppingLaws childLaws)) (some i) -
          quittingBehaviorEvaluatedPayoff reward evaluation
            (quittingStoppingLawProfile reward
              (quietParentStoppingLaws childLaws)) (some i)) := by
  let quietProfile := quittingStoppingLawProfile reward
    (quietParentStoppingLaws childLaws)
  apply sub_le_iff_le_add.mpr
  unfold quittingBehaviorEvaluatedDeviationPayoffCap
  apply csSup_le
  · exact ⟨quittingBehaviorEvaluatedPayoff reward evaluation
        (Function.update quietProfile none (quietProfile none)) none,
      ⟨quietProfile none, rfl⟩⟩
  rintro payoff ⟨deviation, rfl⟩
  let outsideLaw := quittingBehaviorStoppingLaw reward deviation
  have hlaws : quittingBehaviorStoppingLaws reward
      (Function.update quietProfile none deviation) =
      cappedClockParentSourceLaws childLaws outsideLaw := by
    funext player
    cases player with
    | none => rfl
    | some i =>
        change quittingBehaviorStoppingLaw reward
            (quittingStoppingLawBehaviorStrategy reward (some i)
              (childLaws i)) = childLaws i
        exact quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy
          reward (some i) (childLaws i)
  have h :=
    outsideStoppingLawEvaluatedGain_le_weighted_behaviorDeviationDebt
      reward certificate evaluation evaluation_nonneg evaluation_antitone
        childLaws outsideLaw
  rw [← hlaws] at h
  have hquiet (who : Option ι) :
      quittingStoppingLawEvaluatedPayoff reward evaluation
          (quietParentStoppingLaws childLaws) who =
        quittingBehaviorEvaluatedPayoff reward evaluation quietProfile who := by
    exact (quittingBehaviorEvaluatedPayoff_stoppingLawProfile
      reward evaluation (quietParentStoppingLaws childLaws) who).symm
  simp_rw [hquiet] at h
  change quittingBehaviorEvaluatedPayoff reward evaluation
      (Function.update quietProfile none deviation) none ≤ _
  change quittingBehaviorEvaluatedPayoff reward evaluation
      (Function.update quietProfile none deviation) none ≤
    (∑ i, certificate.weight i *
      (quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
          quietProfile (some i) -
        quittingBehaviorEvaluatedPayoff reward evaluation
          quietProfile (some i))) +
      quittingBehaviorEvaluatedPayoff reward evaluation quietProfile none
  change quittingBehaviorEvaluatedPayoff reward evaluation
      (Function.update quietProfile none deviation) none -
        quittingBehaviorEvaluatedPayoff reward evaluation quietProfile none ≤
    ∑ i, certificate.weight i *
      (quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
          quietProfile (some i) -
        quittingBehaviorEvaluatedPayoff reward evaluation
          quietProfile (some i)) at h
  linarith

end GameTheory
