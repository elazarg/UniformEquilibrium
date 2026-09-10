import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockActualPayoffAdapter
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockExpectationDomination

/-!
# Full behavioral cap from the capped-clock comparison
-/

noncomputable section

namespace GameTheory

open Math Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Every complete outsider stopping law gains at most the weighted sum of the
children's full behavioral deviation debts from the actual quiet profile. -/
theorem outsideStoppingLawGain_le_weighted_behaviorDeviationDebt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CappedClockParentRewardCertificate reward)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) :
    quittingStoppingLawExpectedPayoff reward
        (cappedClockParentSourceLaws childLaws outsideLaw) none -
      quittingStoppingLawExpectedPayoff reward
        (quietParentStoppingLaws childLaws) none ≤
      ∑ i, certificate.weight i *
        (quittingBehaviorDeviationPayoffCap reward
            (quittingStoppingLawProfile reward
              (quietParentStoppingLaws childLaws)) (some i) -
          quittingStoppingLawExpectedPayoff reward
            (quietParentStoppingLaws childLaws) (some i)) := by
  let source := pmfPi (cappedClockParentSourceLaws childLaws outsideLaw)
  let coupled : PMF ((ι → Option ℕ) × Option ℕ) := source.map fun clocks =>
    (fun i => clocks (some i), clocks none)
  have h := expect_cappedClockActualEvaluatedOutsideGain_le_sum_childExpectations
    reward certificate cappedClockTerminalEvaluation
      cappedClockTerminalEvaluation_nonneg
      cappedClockTerminalEvaluation_antitone coupled
  simp only [cappedClockActualEvaluatedOutsideGain,
    cappedClockActualEvaluatedChildGain,
    quittingPureClockEvaluatedPayoff_terminalEvaluation] at h
  simp only [coupled, Math.Probability.expect_map] at h
  have hpayBound (who : Option ι)
      (f : (Option ι → Option ℕ) → (Option ι → Option ℕ)) :
      Summable fun clocks =>
        (source clocks).toReal * quittingPureClockTerminalPayoff reward
          (f clocks) who :=
    Math.Probability.expect_summable_of_bounded source _ fun clocks =>
      (by
        have hb := abs_quittingPureClockEvaluatedPayoff_le reward
          cappedClockTerminalEvaluation cappedClockTerminalEvaluation_nonneg
            cappedClockTerminalEvaluation_antitone (f clocks) who
        rw [quittingPureClockEvaluatedPayoff_terminalEvaluation] at hb
        simpa [cappedClockTerminalEvaluation] using hb)
  have hexpectSub (who : Option ι)
      (f g : (Option ι → Option ℕ) → (Option ι → Option ℕ)) :
      Math.Probability.expect source (fun clocks => quittingPureClockTerminalPayoff reward
          (f clocks) who - quittingPureClockTerminalPayoff reward (g clocks) who) =
        Math.Probability.expect source (fun clocks => quittingPureClockTerminalPayoff reward
          (f clocks) who) -
        Math.Probability.expect source (fun clocks => quittingPureClockTerminalPayoff reward
          (g clocks) who) := by
    change Math.Probability.expect source (fun clocks =>
        quittingPureClockTerminalPayoff reward (f clocks) who +
          -quittingPureClockTerminalPayoff reward (g clocks) who) = _
    rw [Math.Probability.expect_add_of_summable]
    · rw [Math.Probability.expect_neg]
      ring
    · exact hpayBound who f
    · simpa [mul_neg] using (hpayBound who g).neg
  rw [hexpectSub none] at h
  simp_rw [hexpectSub (some _)] at h
  rw [expect_parentSource_outside_eq_stoppingLawExpectedPayoff
      reward childLaws outsideLaw,
    expect_parentSource_quiet_eq_stoppingLawExpectedPayoff
      reward childLaws outsideLaw none] at h
  refine h.trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [expect_parentSource_cappedChild_eq_stoppingLawExpectedPayoff
      reward childLaws outsideLaw i,
    expect_parentSource_quiet_eq_stoppingLawExpectedPayoff
      reward childLaws outsideLaw (some i)]
  apply mul_le_mul_of_nonneg_left _ (certificate.weight_nonneg i)
  exact sub_le_sub_right
    (cappedChild_stoppingLawExpectedPayoff_le_behaviorDeviationCap
      reward childLaws outsideLaw i) _

/-- The outsider's full unrestricted behavioral deviation cap above the quiet
profile is bounded by the weighted sum of the children's full behavioral
deviation debts.  The supremum is taken only after the bound is proved for
every actual outsider strategy. -/
theorem outsideBehaviorDeviationDebt_le_weighted_childBehaviorDeviationDebt
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CappedClockParentRewardCertificate reward)
    (childLaws : ι → PMF (Option ℕ)) :
    quittingBehaviorDeviationPayoffCap reward
        (quittingStoppingLawProfile reward
          (quietParentStoppingLaws childLaws)) none -
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (quietParentStoppingLaws childLaws)) none ≤
      ∑ i, certificate.weight i *
        (quittingBehaviorDeviationPayoffCap reward
            (quittingStoppingLawProfile reward
              (quietParentStoppingLaws childLaws)) (some i) -
          quittingTerminalPayoff reward
            (quittingStoppingLawProfile reward
              (quietParentStoppingLaws childLaws)) (some i)) := by
  let quietProfile := quittingStoppingLawProfile reward
    (quietParentStoppingLaws childLaws)
  apply sub_le_iff_le_add.mpr
  unfold quittingBehaviorDeviationPayoffCap
  apply csSup_le
  · exact ⟨quittingTerminalPayoff reward
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
  have h := outsideStoppingLawGain_le_weighted_behaviorDeviationDebt
    reward certificate childLaws outsideLaw
  rw [← hlaws,
    quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff]
    at h
  simp_rw [← quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff] at h
  change quittingTerminalPayoff reward
      (Function.update quietProfile none deviation) none ≤ _
  change quittingTerminalPayoff reward
      (Function.update quietProfile none deviation) none ≤
    (∑ i, certificate.weight i *
      (quittingBehaviorDeviationPayoffCap reward quietProfile (some i) -
        quittingTerminalPayoff reward quietProfile (some i))) +
      quittingTerminalPayoff reward quietProfile none
  linarith

end GameTheory
