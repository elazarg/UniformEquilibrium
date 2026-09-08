import UniformEquilibrium.Diagnostics.Quitting.InverseMembershipStretchExclusion

/-!
# Supported strict reversals for actual averaged-best membership directions

The hypotheses refer to the final table's actual expected endpoint differences
and unrestricted debts. Positive averaged debt and one negative supported gap
produce an opposite strict gap at another supported draw, with both original
and final signs retained. No pointwise best-action hypothesis is assumed.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The actual two expected root endpoints always admit averaged-best binary directions. -/
theorem exists_quittingAveragedBestDirections
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (root : ι → PMF Bool) :
    ∃ preferred : ι → Bool, ∀ who, 0 ≤ expect (pmfPi root)
      (quittingDirectedMembershipGap reward who (preferred who)) := by
  have hexists (who : ι) : ∃ choice : Bool,
      0 ≤ expect (pmfPi root) (quittingDirectedMembershipGap reward who choice) := by
    by_cases h : oneDateProductContinueEndpoint reward root who ≤
        oneDateProductQuitEndpoint reward root who
    · refine ⟨true, ?_⟩
      rw [expect_quittingDirectedMembershipGap]
      exact sub_nonneg.mpr h
    · refine ⟨false, ?_⟩
      rw [expect_quittingDirectedMembershipGap]
      exact sub_nonneg.mpr (le_of_not_ge h)
  choose preferred hbest using hexists
  exact ⟨preferred, hbest⟩

/-- A sure quitter with positive full debt cannot have Quit as an averaged-best action. -/
theorem quittingAveragedBestAction_eq_false_of_sure_and_positiveDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (preferred : Bool)
    {opponent : ι} (hne : opponent ≠ who) (hsure : (root opponent true).toReal = 1)
    (hwho : (root who true).toReal = 1)
    (hbest : 0 ≤ expect (pmfPi root) (quittingDirectedMembershipGap reward who preferred))
    (hpositive : 0 < quittingTerminalDeviationDebt reward
      (quittingOneDateThenNeverProfile reward root) who) : preferred = false := by
  have hdebt := quittingTerminalDeviationDebt_oneDateThenNever_eq_losingMass_mul_gap
    reward root who preferred hne hsure hbest
  cases preferred with
  | false => rfl
  | true =>
      have hpure := eq_pure_true_of_true_toReal_eq_one (root who) hwho
      simp only [Bool.not_true, hpure, PMF.pure_apply, Bool.false_eq_true, if_false,
        ENNReal.toReal_zero, zero_mul] at hdebt
      exact (ne_of_gt hpositive hdebt).elim

/-- A negative supported original edge and positive final averaged-best debt force
opposite supported strict signs at the same owner, at both literal reward tables. -/
theorem exists_supported_oppositeMembershipGaps_of_negativeGap_and_positiveDebt
    (original final : {S : Finset ι // S.Nonempty} → Payoff ι) {alpha : ℝ}
    (halpha : 0 ≤ alpha)
    (hagrees : QuittingAgreesWithMembershipStretch original final alpha)
    (horiginalBound : ∀ terminal who, |original terminal who| ≤ 1)
    (root : ι → PMF Bool) (preferred : ι → Bool)
    (hscreen : ∀ who, ∃ opponent, opponent ≠ who ∧ (root opponent true).toReal = 1)
    (hbest : ∀ who, 0 ≤ expect (pmfPi root)
      (quittingDirectedMembershipGap final who (preferred who)))
    (hpositive : ∀ who, 0 < quittingTerminalDeviationDebt final
      (quittingOneDateThenNeverProfile final root) who)
    (hnegative : ∃ who action, action ∈ (pmfPi root).support ∧
      quittingDirectedMembershipGap original who (preferred who) action < 0) :
    ∃ who negative positive,
      negative ∈ (pmfPi root).support ∧ positive ∈ (pmfPi root).support ∧
      quittingDirectedMembershipGap original who (preferred who) negative < 0 ∧
      0 < quittingDirectedMembershipGap original who (preferred who) positive ∧
      quittingDirectedMembershipGap final who (preferred who) negative < 0 ∧
      0 < quittingDirectedMembershipGap final who (preferred who) positive := by
  obtain ⟨who, negative, hnegativeSupport, hnegativeGap⟩ := hnegative
  obtain ⟨opponent, hne, hsure⟩ := hscreen who
  have htransform (action : ι → Bool) (hsupport : action ∈ (pmfPi root).support) :=
    quittingDirectedMembershipGap_eq_stretch_on_support
      original final alpha hagrees root who (preferred who) hne hsure action hsupport
  have hbound (action : ι → Bool) :=
    abs_quittingDirectedMembershipGap_le_two original horiginalBound who (preferred who) action
  have hnegativeFinal : quittingDirectedMembershipGap final who (preferred who) negative < 0 := by
    rw [htransform negative hnegativeSupport]
    exact (Math.signedEndpointGapStretch_neg_iff_of_abs_le_two
      halpha (hbound negative)).mpr hnegativeGap
  have hdebtPositive := hpositive who
  rw [quittingTerminalDeviationDebt_oneDateThenNever_eq_losingMass_mul_gap
    final root who (preferred who) hne hsure (hbest who)] at hdebtPositive
  have hmean : 0 < expect (pmfPi root)
      (quittingDirectedMembershipGap final who (preferred who)) := by
    by_contra hnot
    exact (not_le_of_gt hdebtPositive)
      (mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg (le_of_not_gt hnot))
  have hexists : ∃ action, action ∈ (pmfPi root).support ∧
      0 < quittingDirectedMembershipGap final who (preferred who) action := by
    by_contra hnone
    have hle : expect (pmfPi root)
        (quittingDirectedMembershipGap final who (preferred who)) ≤
          expect (pmfPi root) (fun _ => (0 : ℝ)) := by
      apply Math.ProbabilityMassFunction.expect_mono_on_support
      intro action hsupport
      apply le_of_not_gt
      intro hgap
      exact hnone ⟨action, hsupport, hgap⟩
    rw [expect_const] at hle
    exact (not_le_of_gt hmean) hle
  obtain ⟨positive, hpositiveSupport, hpositiveFinal⟩ := hexists
  have hpositiveOriginal :
      0 < quittingDirectedMembershipGap original who (preferred who) positive := by
    rw [htransform positive hpositiveSupport] at hpositiveFinal
    exact (Math.signedEndpointGapStretch_pos_iff_of_abs_le_two
      halpha (hbound positive)).mp hpositiveFinal
  exact ⟨who, negative, positive, hnegativeSupport, hpositiveSupport,
    hnegativeGap, hpositiveOriginal, hnegativeFinal, hpositiveFinal⟩

end GameTheory
