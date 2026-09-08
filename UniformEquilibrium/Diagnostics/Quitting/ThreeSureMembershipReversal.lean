import UniformEquilibrium.Diagnostics.Quitting.MembershipStretchSupportedReversal

/-!
# Canonical two-configuration reversals in a three-sure root

All players other than the named optional player quit surely. The same actual
root is retained, and its two supported optional configurations are written as
literal action functions. Opposite strict gaps force genuine mixing of the
optional marginal and a reversing sure owner whose best direction is Continue.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The pure action with one specified optional bit and all other players quitting. -/
def quittingSingleOptionalAction (optional : ι) (choice : Bool) : ι → Bool :=
  Function.update (fun _ => true) optional choice

theorem quittingRoot_supported_action_eq_singleOptionalAction
    (root : ι → PMF Bool) (optional : ι)
    (hsure : ∀ who, who ≠ optional → (root who true).toReal = 1)
    (action : ι → Bool) (hsupport : action ∈ (pmfPi root).support) :
    action = quittingSingleOptionalAction optional (action optional) := by
  funext who
  by_cases hwho : who = optional
  · subst who
    simp [quittingSingleOptionalAction]
  · rw [quittingSingleOptionalAction, Function.update_of_ne hwho]
    exact quittingRoot_supported_action_eq_true_of_sure root who (hsure who hwho) action hsupport

/-- A player's own optional bit cannot affect its directed membership gap. -/
theorem quittingDirectedMembershipGap_optional_eq_on_support
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (optional : ι) (preferred : Bool)
    (hsure : ∀ who, who ≠ optional → (root who true).toReal = 1)
    (action : ι → Bool) (hsupport : action ∈ (pmfPi root).support) :
    quittingDirectedMembershipGap reward optional preferred action =
      quittingDirectedMembershipGap reward optional preferred (fun _ => true) := by
  rw [quittingRoot_supported_action_eq_singleOptionalAction root optional hsure action hsupport]
  exact quittingDirectedMembershipGap_update reward optional preferred (action optional) _

/-- Two supported draws differing at a coordinate make that Boolean marginal genuinely mixed. -/
theorem quittingRoot_marginal_mem_Ioo_of_supported_action_disagreement
    (root : ι → PMF Bool) (who : ι) (first second : ι → Bool)
    (hfirst : first ∈ (pmfPi root).support) (hsecond : second ∈ (pmfPi root).support)
    (hne : first who ≠ second who) : (root who true).toReal ∈ Set.Ioo (0 : ℝ) 1 := by
  have hnotZero : (root who true).toReal ≠ 0 := by
    intro hzero
    have hpure := eq_pure_false_of_true_toReal_eq_zero (root who) hzero
    have hfixed (action : ι → Bool) (hsupport : action ∈ (pmfPi root).support) :
        action who = false := by
      apply eq_of_mem_support_pmfPi_update_pure root who false
      rwa [← hpure, Function.update_eq_self]
    exact hne ((hfixed first hfirst).trans (hfixed second hsecond).symm)
  have hnotOne : (root who true).toReal ≠ 1 := by
    intro hone
    exact hne ((quittingRoot_supported_action_eq_true_of_sure root who hone first hfirst).trans
      (quittingRoot_supported_action_eq_true_of_sure root who hone second hsecond).symm)
  have hnonneg : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hfalse : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
  constructor
  · exact lt_of_le_of_ne hnonneg (Ne.symm hnotZero)
  · exact lt_of_le_of_ne (by linarith) hnotOne

/-- Supported opposite gaps in an all-but-one-sure root belong to a sure owner,
and become opposite Continue-minus-Quit gaps at its two canonical optional configurations. -/
theorem exists_sureOwner_canonical_optional_reversal_of_supported_oppositeGaps
    (original final : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (optional : ι) (preferred : ι → Bool)
    (hsure : ∀ who, who ≠ optional → (root who true).toReal = 1)
    (hscreen : ∀ who, ∃ opponent, opponent ≠ who ∧ (root opponent true).toReal = 1)
    (hbest : ∀ who, 0 ≤ expect (pmfPi root)
      (quittingDirectedMembershipGap final who (preferred who)))
    (hpositive : ∀ who, 0 < quittingTerminalDeviationDebt final
      (quittingOneDateThenNeverProfile final root) who)
    (hreversal : ∃ who negative positive,
      negative ∈ (pmfPi root).support ∧ positive ∈ (pmfPi root).support ∧
      quittingDirectedMembershipGap original who (preferred who) negative < 0 ∧
      0 < quittingDirectedMembershipGap original who (preferred who) positive ∧
      quittingDirectedMembershipGap final who (preferred who) negative < 0 ∧
      0 < quittingDirectedMembershipGap final who (preferred who) positive) :
    (root optional true).toReal ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∃ (who : ι) (negative positive : Bool), who ≠ optional ∧ negative ≠ positive ∧
        quittingSingleOptionalAction optional negative ∈ (pmfPi root).support ∧
        quittingSingleOptionalAction optional positive ∈ (pmfPi root).support ∧
        quittingDirectedMembershipGap original who false
          (quittingSingleOptionalAction optional negative) < 0 ∧
        0 < quittingDirectedMembershipGap original who false
          (quittingSingleOptionalAction optional positive) ∧
        quittingDirectedMembershipGap final who false
          (quittingSingleOptionalAction optional negative) < 0 ∧
        0 < quittingDirectedMembershipGap final who false
          (quittingSingleOptionalAction optional positive) := by
  obtain ⟨who, negative, positive, hnSupport, hpSupport, hnOld, hpOld, hnFinal, hpFinal⟩ :=
    hreversal
  have hwho : who ≠ optional := by
    intro heq
    subst who
    rw [quittingDirectedMembershipGap_optional_eq_on_support
      final root optional (preferred optional) hsure negative hnSupport] at hnFinal
    rw [quittingDirectedMembershipGap_optional_eq_on_support
      final root optional (preferred optional) hsure positive hpSupport] at hpFinal
    linarith
  have hnAction := quittingRoot_supported_action_eq_singleOptionalAction
    root optional hsure negative hnSupport
  have hpAction := quittingRoot_supported_action_eq_singleOptionalAction
    root optional hsure positive hpSupport
  have hdistinct : negative optional ≠ positive optional := by
    intro heq
    have heqAction : negative = positive := by rw [hnAction, hpAction, heq]
    rw [heqAction] at hnFinal
    linarith
  have hmixed := quittingRoot_marginal_mem_Ioo_of_supported_action_disagreement
    root optional negative positive hnSupport hpSupport hdistinct
  obtain ⟨opponent, hne, hscreened⟩ := hscreen who
  have hpreferred := quittingAveragedBestAction_eq_false_of_sure_and_positiveDebt
    final root who (preferred who) hne hscreened (hsure who hwho) (hbest who) (hpositive who)
  refine ⟨hmixed, who, negative optional, positive optional, hwho, hdistinct, ?_, ?_, ?_⟩
  · rwa [← hnAction]
  · rwa [← hpAction]
  · rw [← hnAction, ← hpAction, ← hpreferred]
    exact ⟨hnOld, hpOld, hnFinal, hpFinal⟩

/-- The literal positive-minimum stretch source forces genuine optional mixing and
a sure owner's strict Continue-minus-Quit reversal at the two optional configurations. -/
theorem exists_sureOwner_strictOptionalReversal_of_membershipStretch_positiveMinimum_finFour
    (original final : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) {alpha : ℝ}
    (halpha : 0 < alpha)
    (hagrees : QuittingAgreesWithMembershipStretch original final alpha)
    (horiginalBound : ∀ terminal who, |original terminal who| ≤ 1)
    (hfinalBound : ∀ terminal who, |final terminal who| ≤ 1)
    (root : Fin 4 → PMF Bool) (optional : Fin 4)
    (hsure : ∀ who, who ≠ optional → (root who true).toReal = 1)
    (hpositive : 0 < quittingTerminalExploitabilityInf final)
    (hinfOrder : quittingTerminalExploitabilityInf final ≤
      quittingTerminalExploitabilityInf original)
    (hminimum : quittingTerminalExploitability final
        (quittingOneDateThenNeverProfile final root) =
      quittingTerminalExploitabilityInf final) :
    (root optional true).toReal ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∃ (who : Fin 4) (negative positive : Bool), who ≠ optional ∧ negative ≠ positive ∧
        quittingSingleOptionalAction optional negative ∈ (pmfPi root).support ∧
        quittingSingleOptionalAction optional positive ∈ (pmfPi root).support ∧
        quittingDirectedMembershipGap original who false
          (quittingSingleOptionalAction optional negative) < 0 ∧
        0 < quittingDirectedMembershipGap original who false
          (quittingSingleOptionalAction optional positive) ∧
        quittingDirectedMembershipGap final who false
          (quittingSingleOptionalAction optional negative) < 0 ∧
        0 < quittingDirectedMembershipGap final who false
          (quittingSingleOptionalAction optional positive) := by
  have hscreen (who : Fin 4) :
      ∃ opponent, opponent ≠ who ∧ (root opponent true).toReal = 1 := by
    have hcard : ({optional, who} : Finset (Fin 4)).card <
        (Finset.univ : Finset (Fin 4)).card := by
      exact Finset.card_le_two.trans_lt (by norm_num)
    obtain ⟨opponent, _, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    have hne : opponent ≠ optional ∧ opponent ≠ who := by simpa using hnot
    exact ⟨opponent, hne.2, hsure opponent hne.1⟩
  obtain ⟨first, _, hfirst⟩ := hscreen optional
  obtain ⟨second, hsecondFirst, hsecond⟩ := hscreen first
  obtain ⟨preferred, hbest, hdebtPositive, hreversal⟩ :=
    exists_supported_oppositeMembershipGaps_of_membershipStretch_positiveMinimum_finFour
      original final halpha hagrees horiginalBound hfinalBound root first second
        (Ne.symm hsecondFirst) hfirst hsecond hpositive hinfOrder hminimum
  exact exists_sureOwner_canonical_optional_reversal_of_supported_oppositeGaps
    original final root optional preferred hsure hscreen hbest hdebtPositive hreversal

end GameTheory
