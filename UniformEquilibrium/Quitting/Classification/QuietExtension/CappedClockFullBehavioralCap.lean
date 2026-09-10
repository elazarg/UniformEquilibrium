import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockActualPayoffAdapter
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockExpectationDomination

/-!
# Full behavioral cap from the capped-clock comparison
-/

noncomputable section

namespace GameTheory

open Math Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
private theorem expect_parentSource_jointNeverIndicator_eq_prod_none
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) :
    Math.Probability.expect
        (pmfPi (cappedClockParentSourceLaws childLaws outsideLaw))
        (fun clocks => cappedClockJointNeverIndicator
          (fun i => clocks (some i))) =
      ∏ i, (childLaws i none).toReal := by
  let fullIndicator : (Option ι → Option ℕ) → ℝ := fun clocks =>
    if clocks = fun _ => none then 1 else 0
  have hindicator (times : ι → Option ℕ) :
      fullIndicator (quietParentClocks times) =
        cappedClockJointNeverIndicator times := by
    by_cases htimes : times = fun _ => none
    · subst times
      have hquiet : quietParentClocks (fun _ : ι => none) =
          fun _ : Option ι => none := by
        funext player
        cases player <;> rfl
      simp [fullIndicator, cappedClockJointNeverIndicator, hquiet]
    · have hquiet : quietParentClocks times ≠ fun _ => none := by
        intro h
        apply htimes
        funext i
        exact congrFun h (some i)
      simp [fullIndicator, cappedClockJointNeverIndicator, htimes, hquiet]
  have hmap := map_pmfPi_cappedClockParentSourceLaws_quiet
    childLaws outsideLaw
  have hexpect := congrArg
    (fun law => Math.Probability.expect law fullIndicator) hmap
  rw [Math.Probability.expect_map] at hexpect
  simp_rw [hindicator] at hexpect
  rw [hexpect]
  have hsingleton (law : PMF (Option ι → Option ℕ))
      (point : Option ι → Option ℕ) :
      Math.Probability.expect law
          (fun other => if other = point then 1 else 0) =
        (law point).toReal := by
    unfold Math.Probability.expect
    rw [tsum_eq_single point]
    · simp
    · intro other hne
      simp [hne]
  rw [hsingleton]
  simp only [Math.PMFProduct.pmfPi_apply, ENNReal.toReal_prod]
  simp [quietParentStoppingLaws, Fintype.prod_option]

/-- Every complete outsider stopping law obeys the weighted child-debt bound
plus the explicit slack times actual child joint-Never mass. -/
theorem outsideStoppingLawGain_le_weighted_behaviorDeviationDebt_add_slack
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CappedClockParentRewardSlackCertificate reward)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) :
    quittingStoppingLawExpectedPayoff reward
        (cappedClockParentSourceLaws childLaws outsideLaw) none -
      quittingStoppingLawExpectedPayoff reward
        (quietParentStoppingLaws childLaws) none ≤
      (∑ i, certificate.weight i *
        (quittingBehaviorDeviationPayoffCap reward
            (quittingStoppingLawProfile reward
              (quietParentStoppingLaws childLaws)) (some i) -
          quittingStoppingLawExpectedPayoff reward
            (quietParentStoppingLaws childLaws) (some i))) +
      certificate.neverSlack * ∏ i, (childLaws i none).toReal := by
  let source := pmfPi (cappedClockParentSourceLaws childLaws outsideLaw)
  let coupled : PMF ((ι → Option ℕ) × Option ℕ) := source.map fun clocks =>
    (fun i => clocks (some i), clocks none)
  have h := expect_cappedClockActualOutsideGain_le_sum_childExpectations_add_slack
    reward certificate coupled
  simp only [coupled, Math.Probability.expect_map] at h
  simp only [cappedClockActualOutsideGain, cappedClockActualChildGain] at h
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
      reward childLaws outsideLaw none,
    expect_parentSource_jointNeverIndicator_eq_prod_none childLaws outsideLaw] at h
  refine h.trans ?_
  have hsum :
      (∑ i, certificate.weight i *
        (Math.Probability.expect source (fun clocks =>
            quittingPureClockTerminalPayoff reward
              (cappedChildParentClocks (fun j => clocks (some j))
                (clocks none) i) (some i)) -
          Math.Probability.expect source (fun clocks =>
            quittingPureClockTerminalPayoff reward
              (quietParentClocks fun j => clocks (some j)) (some i)))) ≤
        ∑ i, certificate.weight i *
          (quittingBehaviorDeviationPayoffCap reward
              (quittingStoppingLawProfile reward
                (quietParentStoppingLaws childLaws)) (some i) -
            quittingStoppingLawExpectedPayoff reward
              (quietParentStoppingLaws childLaws) (some i)) := by
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
  simpa only [add_comm] using add_le_add_right hsum
    (certificate.neverSlack * ∏ i, (childLaws i none).toReal)

/-- Exact N/F/J stopping-law domination is the zero-slack specialization. -/
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
  simpa [CappedClockParentRewardCertificate.withZeroSlack] using
    outsideStoppingLawGain_le_weighted_behaviorDeviationDebt_add_slack
      reward certificate.withZeroSlack childLaws outsideLaw

/-- The outsider's full unrestricted behavioral debt obeys the slack bound.
The supremum is taken only after the estimate for every actual strategy. -/
theorem outsideBehaviorDeviationDebt_le_weighted_childBehaviorDeviationDebt_add_slack
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CappedClockParentRewardSlackCertificate reward)
    (childLaws : ι → PMF (Option ℕ)) :
    quittingBehaviorDeviationPayoffCap reward
        (quittingStoppingLawProfile reward
          (quietParentStoppingLaws childLaws)) none -
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (quietParentStoppingLaws childLaws)) none ≤
      (∑ i, certificate.weight i *
        (quittingBehaviorDeviationPayoffCap reward
            (quittingStoppingLawProfile reward
              (quietParentStoppingLaws childLaws)) (some i) -
          quittingTerminalPayoff reward
            (quittingStoppingLawProfile reward
            (quietParentStoppingLaws childLaws)) (some i))) +
      certificate.neverSlack * ∏ i, (childLaws i none).toReal := by
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
  have h := outsideStoppingLawGain_le_weighted_behaviorDeviationDebt_add_slack
    reward certificate childLaws outsideLaw
  rw [← hlaws,
    quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff]
    at h
  simp_rw [← quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff] at h
  change quittingTerminalPayoff reward
      (Function.update quietProfile none deviation) none ≤ _
  change quittingTerminalPayoff reward
      (Function.update quietProfile none deviation) none ≤
    ((∑ i, certificate.weight i *
      (quittingBehaviorDeviationPayoffCap reward quietProfile (some i) -
        quittingTerminalPayoff reward quietProfile (some i))) +
      certificate.neverSlack * ∏ i, (childLaws i none).toReal) +
      quittingTerminalPayoff reward quietProfile none
  linarith

/-- Exact N/F/J full behavioral domination is the zero-slack specialization. -/
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
  simpa [CappedClockParentRewardCertificate.withZeroSlack] using
    outsideBehaviorDeviationDebt_le_weighted_childBehaviorDeviationDebt_add_slack
      reward certificate.withZeroSlack childLaws

end GameTheory
