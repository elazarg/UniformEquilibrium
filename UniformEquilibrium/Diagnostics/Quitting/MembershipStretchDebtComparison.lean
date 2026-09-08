import UniformEquilibrium.Diagnostics.Quitting.MembershipStretch
import MathUE.ProbabilityMassFunction.SupportExpectationEquality

/-!
# Local full-debt comparison under the same membership stretch

These comparisons concern the same unpadded product root at the original
and final tables. Pointwise coherence is required only on the original
product support. Equality with positive debt forces every supported edge
to be zero or saturated. No global minimum or reward-table producer is assumed.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A coherent supported edge weakly expands at the final table. -/
theorem quittingDirectedMembershipGap_le_final_on_support
    (original final : {S : Finset ι // S.Nonempty} → Payoff ι) {alpha : ℝ}
    (halpha : 0 ≤ alpha)
    (hagrees : QuittingAgreesWithMembershipStretch original final alpha)
    (hbound : ∀ terminal who, |original terminal who| ≤ 1)
    (root : ι → PMF Bool) (who : ι) (preferred : Bool) {opponent : ι}
    (hne : opponent ≠ who) (hsure : (root opponent true).toReal = 1)
    (action : ι → Bool) (hsupport : action ∈ (pmfPi root).support)
    (hgap : 0 ≤ quittingDirectedMembershipGap original who preferred action) :
    quittingDirectedMembershipGap original who preferred action ≤
      quittingDirectedMembershipGap final who preferred action := by
  rw [quittingDirectedMembershipGap_eq_stretch_on_support
    original final alpha hagrees root who preferred hne hsure action hsupport]
  exact Math.le_signedEndpointGapStretch halpha hgap
    ((le_abs_self _).trans
      (abs_quittingDirectedMembershipGap_le_two original hbound who preferred action))

/-- Undoing a coherent membership stretch cannot increase this owner's full unpadded debt. -/
theorem quittingTerminalDeviationDebt_original_le_final_of_membershipStretch
    (original final : {S : Finset ι // S.Nonempty} → Payoff ι) {alpha : ℝ}
    (halpha : 0 ≤ alpha)
    (hagrees : QuittingAgreesWithMembershipStretch original final alpha)
    (hbound : ∀ terminal who, |original terminal who| ≤ 1)
    (root : ι → PMF Bool) (who : ι) (preferred : Bool) {opponent : ι}
    (hne : opponent ≠ who) (hsure : (root opponent true).toReal = 1)
    (hcoherent : ∀ action ∈ (pmfPi root).support,
      0 ≤ quittingDirectedMembershipGap original who preferred action) :
    quittingTerminalDeviationDebt original
        (quittingOneDateThenNeverProfile original root) who ≤
      quittingTerminalDeviationDebt final
        (quittingOneDateThenNeverProfile final root) who := by
  have hle (action : ι → Bool) (hsupport : action ∈ (pmfPi root).support) :=
    quittingDirectedMembershipGap_le_final_on_support original final halpha hagrees hbound
      root who preferred hne hsure action hsupport (hcoherent action hsupport)
  have hfinalCoherent (action : ι → Bool) (hsupport : action ∈ (pmfPi root).support) :
      0 ≤ quittingDirectedMembershipGap final who preferred action :=
    (hcoherent action hsupport).trans (hle action hsupport)
  rw [quittingTerminalDeviationDebt_oneDateThenNever_eq_losingMass_mul_gap
      original root who preferred hne hsure
        (expect_quittingDirectedMembershipGap_nonneg_of_supported
          original root who preferred hcoherent),
    quittingTerminalDeviationDebt_oneDateThenNever_eq_losingMass_mul_gap
      final root who preferred hne hsure
        (expect_quittingDirectedMembershipGap_nonneg_of_supported
          final root who preferred hfinalCoherent)]
  exact mul_le_mul_of_nonneg_left
    (Math.ProbabilityMassFunction.expect_mono_on_support (pmfPi root)
      (quittingDirectedMembershipGap original who preferred)
      (quittingDirectedMembershipGap final who preferred) hle)
    ENNReal.toReal_nonneg

/-- Equal positive full debts force positive losing mass and saturation on every supported draw. -/
theorem losingMass_pos_and_membershipGap_saturated_of_equal_positive_debt
    (original final : {S : Finset ι // S.Nonempty} → Payoff ι) {alpha : ℝ}
    (halpha : 0 < alpha)
    (hagrees : QuittingAgreesWithMembershipStretch original final alpha)
    (hbound : ∀ terminal who, |original terminal who| ≤ 1)
    (root : ι → PMF Bool) (who : ι) (preferred : Bool) {opponent : ι}
    (hne : opponent ≠ who) (hsure : (root opponent true).toReal = 1)
    (hcoherent : ∀ action ∈ (pmfPi root).support,
      0 ≤ quittingDirectedMembershipGap original who preferred action)
    (hequal : quittingTerminalDeviationDebt original
        (quittingOneDateThenNeverProfile original root) who =
      quittingTerminalDeviationDebt final (quittingOneDateThenNeverProfile final root) who)
    (hpositive : 0 < quittingTerminalDeviationDebt final
      (quittingOneDateThenNeverProfile final root) who) :
    0 < (root who (!preferred)).toReal ∧
      ∀ action ∈ (pmfPi root).support,
        quittingDirectedMembershipGap original who preferred action = 0 ∨
          quittingDirectedMembershipGap original who preferred action = 2 := by
  have hle (action : ι → Bool) (hsupport : action ∈ (pmfPi root).support) :=
    quittingDirectedMembershipGap_le_final_on_support original final halpha.le hagrees hbound
      root who preferred hne hsure action hsupport (hcoherent action hsupport)
  have hfinalCoherent (action : ι → Bool) (hsupport : action ∈ (pmfPi root).support) :
      0 ≤ quittingDirectedMembershipGap final who preferred action :=
    (hcoherent action hsupport).trans (hle action hsupport)
  have horiginal := quittingTerminalDeviationDebt_oneDateThenNever_eq_losingMass_mul_gap
    original root who preferred hne hsure
      (expect_quittingDirectedMembershipGap_nonneg_of_supported
        original root who preferred hcoherent)
  have hfinal := quittingTerminalDeviationDebt_oneDateThenNever_eq_losingMass_mul_gap
    final root who preferred hne hsure
      (expect_quittingDirectedMembershipGap_nonneg_of_supported
        final root who preferred hfinalCoherent)
  have hmassNe : (root who (!preferred)).toReal ≠ 0 := by
    intro hzero
    rw [hfinal, hzero, zero_mul] at hpositive
    exact (lt_irrefl 0) hpositive
  have hmass : 0 < (root who (!preferred)).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hmassNe)
  have hexpect : expect (pmfPi root) (quittingDirectedMembershipGap original who preferred) =
      expect (pmfPi root) (quittingDirectedMembershipGap final who preferred) := by
    rw [horiginal, hfinal] at hequal
    exact mul_left_cancel₀ hmassNe hequal
  have hpointwise :=
    (Math.ProbabilityMassFunction.expect_eq_iff_eq_on_support_of_le_on_support
      (pmfPi root) (quittingDirectedMembershipGap original who preferred)
      (quittingDirectedMembershipGap final who preferred) hle).mp hexpect
  refine ⟨hmass, ?_⟩
  intro action hsupport
  exact (quittingDirectedMembershipGap_eq_iff_zero_or_two_on_support
    original final halpha hagrees root who preferred hne hsure action hsupport
      (hcoherent action hsupport)).mp (hpointwise action hsupport).symm

end GameTheory
