import UniformEquilibrium.Diagnostics.Quitting.InverseMembershipStretchExclusion
import UniformEquilibrium.Diagnostics.Quitting.ZeroSingletonBehavioralLawProductBase

/-!
# Literal carrier entrance to inverse membership-stretch exclusion

A positive joint carrier minimum with zero Never and singleton masses supplies
one unpadded two-sure product root. Its full prescribed-payoff/cap pair and law
are both retained. The original reward table and common stretch parameter are
not reconstructed from final-table contact data: their literal correspondence
and actual global-infimum ordering remain explicit inputs.
-/

noncomputable section

namespace GameTheory

open Math.PMFProduct

/-- One literal root realizes the entire positive minimum and law, and no choice of
directed actions can be coherent on all supported configurations at the original table. -/
theorem exists_twoSureRoot_with_supported_negativeGap_of_membershipStretch_carrierMinimum
    (original final : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) {alpha : ℝ}
    (halpha : 0 < alpha)
    (hagrees : QuittingAgreesWithMembershipStretch original final alpha)
    (horiginalBound : ∀ terminal who, |original terminal who| ≤ 1)
    (hfinalBound : ∀ terminal who, |final terminal who| ≤ 1)
    (point : QuittingTerminalSemanticLawPoint (Fin 4))
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier final)
    (hNever : point.2 none = 0)
    (hSingleton : ∀ who, point.2 (some (quittingSingletonTerminal who)) = 0)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier final,
      quittingTerminalSemanticExploitability point.1 ≤
        quittingTerminalSemanticExploitability candidate)
    (hpositive : 0 < quittingTerminalSemanticExploitability point.1)
    (hinfOrder : quittingTerminalExploitabilityInf final ≤
      quittingTerminalExploitabilityInf original) :
    ∃ (root : Fin 4 → PMF Bool) (first second : Fin 4),
      first ≠ second ∧ (root first true).toReal = 1 ∧ (root second true).toReal = 1 ∧
      quittingTerminalSemanticPair final
        (quittingOneDateThenNeverProfile final root) = point.1 ∧
      quittingTerminalOutcomeMass final
        (quittingOneDateThenNeverProfile final root) = point.2 ∧
      quittingTerminalExploitability final
        (quittingOneDateThenNeverProfile final root) = quittingTerminalExploitabilityInf final ∧
      ∀ preferred : Fin 4 → Bool, ∃ who action,
        action ∈ (pmfPi root).support ∧
          quittingDirectedMembershipGap original who (preferred who) action < 0 := by
  have hsemantic := terminalSemanticLawCarrier_fst_mem_carrier point hpoint
  have hstrict (who : Fin 4) : final (quittingSingletonTerminal who) who < point.1.2 who := by
    have hmargin := minimumTerminalSemantic_exploitabilitySingletonMargin
      final point.1 hsemantic hminimum hpositive who
    linarith
  obtain ⟨root, first, second, hdistinct, hfirst, hsecond, hpair, hlaw, _, _⟩ :=
    exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin
      final point hpoint hNever hSingleton (by norm_num) hstrict
  have hactual : quittingTerminalExploitability final
      (quittingOneDateThenNeverProfile final root) =
        quittingTerminalSemanticExploitability point.1 :=
    congrArg quittingTerminalSemanticExploitability hpair
  have hrootMinimum : quittingTerminalExploitability final
      (quittingOneDateThenNeverProfile final root) = quittingTerminalExploitabilityInf final := by
    apply le_antisymm _ (quittingTerminalExploitabilityInf_le final _)
    change quittingTerminalExploitability final (quittingOneDateThenNeverProfile final root) ≤
      sInf (Set.range fun candidate : (quittingGame final).BehaviorProfile =>
        quittingTerminalExploitability final candidate)
    have hnonempty : (Set.range fun candidate : (quittingGame final).BehaviorProfile =>
        quittingTerminalExploitability final candidate).Nonempty :=
      ⟨_, ⟨quittingOneDateThenNeverProfile final root, rfl⟩⟩
    apply le_csInf hnonempty
    rintro value ⟨candidate, rfl⟩
    rw [hactual]
    exact hminimum _ (subset_closure ⟨candidate, rfl⟩)
  have hinfPositive : 0 < quittingTerminalExploitabilityInf final := by
    rwa [← hrootMinimum, hactual]
  refine ⟨root, first, second, hdistinct, hfirst, hsecond, hpair, hlaw, hrootMinimum, ?_⟩
  intro preferred
  by_contra hnone
  have hcoherent (who : Fin 4) (action : Fin 4 → Bool)
      (hsupport : action ∈ (pmfPi root).support) :
      0 ≤ quittingDirectedMembershipGap original who (preferred who) action := by
    apply le_of_not_gt
    intro hgap
    exact hnone ⟨who, action, hsupport, hgap⟩
  exact not_membershipStretch_coherent_positiveMinimum_finFour
    original final halpha hagrees horiginalBound hfinalBound root preferred first second
      hdistinct hfirst hsecond hcoherent hinfPositive hinfOrder hrootMinimum

end GameTheory
