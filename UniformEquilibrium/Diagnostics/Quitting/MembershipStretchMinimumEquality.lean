import UniformEquilibrium.Diagnostics.Quitting.MembershipStretchDebtComparison
import UniformEquilibrium.Diagnostics.Quitting.PositiveMaximumDebtMinimum
import UniformEquilibrium.Quitting.Terminal.TerminalDebtPrefixDescent

/-!
# Same-root global equality under membership stretching

The global comparison retains the original table, final table, common stretch
parameter, and unpadded product root. Ordering the actual global infima forces
old-root attainment before the old all-player-ties theorem is used. The source
construction must still supply that infimum ordering; no contact certificate
or worst-table producer is manufactured here.
-/

noncomputable section

namespace GameTheory

open Math.PMFProduct QuittingBoundaryHolonomy

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Infimum ordering at the same literal source forces equality and supported-edge saturation. -/
theorem membershipStretch_sameRoot_minimumEquality_and_supportedSaturation
    (original final : {S : Finset ι // S.Nonempty} → Payoff ι) {alpha : ℝ}
    (halpha : 0 < alpha)
    (hagrees : QuittingAgreesWithMembershipStretch original final alpha)
    (horiginalBound : ∀ terminal who, |original terminal who| ≤ 1)
    (hfinalBound : ∀ terminal who, |final terminal who| ≤ 1)
    (root : ι → PMF Bool) (preferred : ι → Bool) (first second : ι)
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
      quittingTerminalExploitabilityInf final) :
    quittingTerminalExploitabilityInf original = quittingTerminalExploitabilityInf final ∧
      quittingTerminalExploitability original
          (quittingOneDateThenNeverProfile original root) =
        quittingTerminalExploitabilityInf original ∧
      ∀ who,
        quittingTerminalDeviationDebt original
            (quittingOneDateThenNeverProfile original root) who =
          quittingTerminalExploitabilityInf final ∧
        quittingTerminalDeviationDebt final
            (quittingOneDateThenNeverProfile final root) who =
          quittingTerminalExploitabilityInf final ∧
        0 < (root who (!(preferred who))).toReal ∧
        ∀ action ∈ (pmfPi root).support,
          quittingDirectedMembershipGap original who (preferred who) action = 0 ∨
            quittingDirectedMembershipGap original who (preferred who) action = 2 := by
  have hopponent (who : ι) :
      ∃ opponent, opponent ≠ who ∧ (root opponent true).toReal = 1 := by
    by_cases hwho : first = who
    · refine ⟨second, ?_, hsecond⟩
      intro heq
      exact hdistinct (hwho.trans heq.symm)
    · exact ⟨first, hwho, hfirst⟩
  have hdebtLe (who : ι) :
      quittingTerminalDeviationDebt original
          (quittingOneDateThenNeverProfile original root) who ≤
        quittingTerminalDeviationDebt final
          (quittingOneDateThenNeverProfile final root) who := by
    obtain ⟨opponent, hne, hsure⟩ := hopponent who
    exact quittingTerminalDeviationDebt_original_le_final_of_membershipStretch
      original final halpha.le hagrees horiginalBound root who (preferred who) hne hsure
        (hcoherent who)
  have hmaximumLe : quittingTerminalExploitability original
        (quittingOneDateThenNeverProfile original root) ≤
      quittingTerminalExploitability final (quittingOneDateThenNeverProfile final root) := by
    rw [quittingTerminalExploitability_eq_max_debt,
      quittingTerminalExploitability_eq_max_debt]
    apply finitePlayerMax_le
    intro who
    exact (hdebtLe who).trans (le_finitePlayerMax _ who)
  have hinfEqual : quittingTerminalExploitabilityInf original =
      quittingTerminalExploitabilityInf final := by
    apply le_antisymm _ hinfOrder
    exact (quittingTerminalExploitabilityInf_le original
      (quittingOneDateThenNeverProfile original root)).trans
        (hmaximumLe.trans_eq hminimum)
  have horiginalMinimum : quittingTerminalExploitability original
        (quittingOneDateThenNeverProfile original root) =
      quittingTerminalExploitabilityInf original := by
    apply le_antisymm _ (quittingTerminalExploitabilityInf_le original _)
    rw [hinfEqual]
    exact hmaximumLe.trans_eq hminimum
  have horiginalGlobal (candidate : (quittingGame original).BehaviorProfile) :
      quittingTerminalExploitability original
          (quittingOneDateThenNeverProfile original root) ≤
        quittingTerminalExploitability original candidate := by
    rw [horiginalMinimum]
    exact quittingTerminalExploitabilityInf_le original candidate
  have hfinalGlobal (candidate : (quittingGame final).BehaviorProfile) :
      quittingTerminalExploitability final (quittingOneDateThenNeverProfile final root) ≤
        quittingTerminalExploitability final candidate := by
    rw [hminimum]
    exact quittingTerminalExploitabilityInf_le final candidate
  have horiginalPositive : 0 < quittingTerminalExploitability original
      (quittingOneDateThenNeverProfile original root) := by
    rwa [horiginalMinimum, hinfEqual]
  have hfinalPositive : 0 < quittingTerminalExploitability final
      (quittingOneDateThenNeverProfile final root) := by
    rwa [hminimum]
  have horiginalTies (who : ι) : quittingTerminalDeviationDebt original
        (quittingOneDateThenNeverProfile original root) who =
      quittingTerminalExploitabilityInf final := by
    rw [quittingTerminalDeviationDebt_eq_exploitability_of_attained_positive_minimum
      original _ horiginalBound horiginalGlobal horiginalPositive who,
      horiginalMinimum, hinfEqual]
  have hfinalTies (who : ι) : quittingTerminalDeviationDebt final
        (quittingOneDateThenNeverProfile final root) who =
      quittingTerminalExploitabilityInf final := by
    rw [quittingTerminalDeviationDebt_eq_exploitability_of_attained_positive_minimum
      final _ hfinalBound hfinalGlobal hfinalPositive who, hminimum]
  refine ⟨hinfEqual, horiginalMinimum, ?_⟩
  intro who
  obtain ⟨opponent, hne, hsure⟩ := hopponent who
  have hsaturation := losingMass_pos_and_membershipGap_saturated_of_equal_positive_debt
    original final halpha hagrees horiginalBound root who (preferred who) hne hsure
      (hcoherent who) ((horiginalTies who).trans (hfinalTies who).symm)
      (by rwa [hfinalTies who])
  exact ⟨horiginalTies who, hfinalTies who, hsaturation⟩

end GameTheory
