import UniformEquilibrium.Diagnostics.Quitting.MembershipStretchMinimumEquality
import UniformEquilibrium.Diagnostics.Quitting.SaturatedMembershipPureVertex

/-!
# Inverse membership-stretch exclusion at a positive attained minimum

The supported vertex is the same deterministic action at the original and final
tables. Its debts are actual unrestricted behavioral-deviation debts, not a
restricted root-action certificate. The four-player exclusion derives the
strict-half bound from actual global attainment. Infimum ordering remains an
explicit source hypothesis; this file does not construct a maximizing table.
-/

noncomputable section

namespace GameTheory

open Math.PMFProduct QuittingBoundaryHolonomy

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Saturation selects one supported pure root with zero full debt at both literal tables. -/
theorem exists_supported_pureRoot_zeroDebt_at_both_membershipStretch_tables
    (original final : {S : Finset ι // S.Nonempty} → Payoff ι) {alpha : ℝ}
    (hagrees : QuittingAgreesWithMembershipStretch original final alpha)
    (root : ι → PMF Bool) (preferred : ι → Bool)
    (hscreen : ∀ who, ∃ opponent, opponent ≠ who ∧ (root opponent true).toReal = 1)
    (hsaturated : ∀ who action, action ∈ (pmfPi root).support →
      quittingDirectedMembershipGap original who (preferred who) action = 0 ∨
        quittingDirectedMembershipGap original who (preferred who) action = 2)
    (hdebt : (∑ who, quittingTerminalDeviationDebt original
      (quittingOneDateThenNeverProfile original root) who) < 2) :
    ∃ action ∈ (pmfPi root).support,
      ∀ who,
        quittingTerminalDeviationDebt original
          (quittingOneDateThenNeverProfile original
            (fun player => PMF.pure (action player))) who = 0 ∧
        quittingTerminalDeviationDebt final
          (quittingOneDateThenNeverProfile final
            (fun player => PMF.pure (action player))) who = 0 := by
  obtain ⟨action, hsupport, hzero⟩ := exists_supported_pureRoot_zeroDebt_of_saturatedGaps
    original root preferred hscreen hsaturated hdebt
  refine ⟨action, hsupport, ?_⟩
  intro who
  obtain ⟨opponent, hne, hsure⟩ := hscreen who
  have hnonneg : 0 ≤ quittingDirectedMembershipGap original who (preferred who) action := by
    rcases hsaturated who action hsupport with hgap | hgap <;> simp [hgap]
  have hgapEqual : quittingDirectedMembershipGap final who (preferred who) action =
      quittingDirectedMembershipGap original who (preferred who) action := by
    rw [quittingDirectedMembershipGap_eq_stretch_on_support
      original final alpha hagrees root who (preferred who) hne hsure action hsupport]
    rcases hsaturated who action hsupport with hgap | hgap
    · rw [hgap, Math.signedEndpointGapStretch_zero]
    · rw [hgap]
      norm_num [Math.signedEndpointGapStretch]
      ring
  have hquit := quittingRoot_supported_action_eq_true_of_sure
    root opponent hsure action hsupport
  refine ⟨hzero who, ?_⟩
  rw [quittingTerminalDeviationDebt_pureRoot_eq_losingMembershipGap
    final action who (preferred who) hne hquit (by rwa [hgapEqual]), hgapEqual]
  have hzeroWho := hzero who
  rw [quittingTerminalDeviationDebt_pureRoot_eq_losingMembershipGap
    original action who (preferred who) hne hquit hnonneg] at hzeroWho
  exact hzeroWho

/-- For four players, supported coherence is incompatible with the literal ordered-infimum
stretch source and a positive globally minimizing unpadded final root. -/
theorem not_membershipStretch_coherent_positiveMinimum_finFour
    (original final : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) {alpha : ℝ}
    (halpha : 0 < alpha)
    (hagrees : QuittingAgreesWithMembershipStretch original final alpha)
    (horiginalBound : ∀ terminal who, |original terminal who| ≤ 1)
    (hfinalBound : ∀ terminal who, |final terminal who| ≤ 1)
    (root : Fin 4 → PMF Bool) (preferred : Fin 4 → Bool) (first second : Fin 4)
    (hdistinct : first ≠ second)
    (hfirst : (root first true).toReal = 1)
    (hsecond : (root second true).toReal = 1)
    (hcoherent : ∀ who action, action ∈ (pmfPi root).support →
      0 ≤ quittingDirectedMembershipGap original who (preferred who) action)
    (hpositive : 0 < quittingTerminalExploitabilityInf final)
    (hinfOrder : quittingTerminalExploitabilityInf final ≤
      quittingTerminalExploitabilityInf original)
    (hminimum : quittingTerminalExploitability final
        (quittingOneDateThenNeverProfile final root) =
      quittingTerminalExploitabilityInf final) : False := by
  obtain ⟨_, _, hties⟩ :=
    membershipStretch_sameRoot_minimumEquality_and_supportedSaturation
      original final halpha hagrees horiginalBound hfinalBound root preferred first second
        hdistinct hfirst hsecond hcoherent hpositive hinfOrder hminimum
  have hscreen (who : Fin 4) :
      ∃ opponent, opponent ≠ who ∧ (root opponent true).toReal = 1 := by
    by_cases hwho : first = who
    · refine ⟨second, ?_, hsecond⟩
      intro heq
      exact hdistinct (hwho.trans heq.symm)
    · exact ⟨first, hwho, hfirst⟩
  have hglobal (candidate : (quittingGame final).BehaviorProfile) :
      quittingTerminalExploitability final (quittingOneDateThenNeverProfile final root) ≤
        quittingTerminalExploitability final candidate := by
    rw [hminimum]
    exact quittingTerminalExploitabilityInf_le final candidate
  have hhalf : quittingTerminalExploitabilityInf final < (1 : ℝ) / 2 := by
    have hlt := quittingTerminalExploitability_lt_half_of_attained_positive_minimum
      final (quittingOneDateThenNeverProfile final root) hfinalBound hglobal
        (by rwa [hminimum])
    rwa [hminimum] at hlt
  have hsum : (∑ who, quittingTerminalDeviationDebt original
      (quittingOneDateThenNeverProfile original root) who) < 2 := by
    simp_rw [fun who => (hties who).1]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num only [Nat.cast_ofNat]
    linarith
  obtain ⟨action, _, hzero⟩ :=
    exists_supported_pureRoot_zeroDebt_at_both_membershipStretch_tables
      original final hagrees root preferred hscreen
        (fun who => (hties who).2.2.2) hsum
  have hmaximum : quittingTerminalExploitability final
      (quittingOneDateThenNeverProfile final
        (fun player => PMF.pure (action player))) ≤ 0 := by
    rw [quittingTerminalExploitability_eq_max_debt]
    apply finitePlayerMax_le
    intro who
    exact le_of_eq (hzero who).2
  have hle := (quittingTerminalExploitabilityInf_le final
    (quittingOneDateThenNeverProfile final
      (fun player => PMF.pure (action player)))).trans hmaximum
  exact (not_le_of_gt hpositive) hle

end GameTheory
