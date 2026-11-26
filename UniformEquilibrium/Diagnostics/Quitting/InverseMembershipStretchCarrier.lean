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

private theorem terminalExploitability_eq_inf_of_minimum_pair
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (pair : QuittingTerminalSemanticPair ι)
    (hvalue : quittingTerminalExploitability reward profile =
      quittingTerminalSemanticExploitability pair)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticExploitability pair ≤
        quittingTerminalSemanticExploitability candidate) :
    quittingTerminalExploitability reward profile = quittingTerminalExploitabilityInf reward := by
  let value := fun candidate : (quittingGame reward).BehaviorProfile =>
    quittingTerminalExploitability reward candidate
  have hlower : ∀ v ∈ Set.range value, value profile ≤ v := by
    rintro v ⟨candidate, hcand⟩
    rw [← hcand]
    change quittingTerminalExploitability reward profile ≤
      quittingTerminalSemanticExploitability (quittingTerminalSemanticPair reward candidate)
    rw [hvalue]
    exact hminimum (quittingTerminalSemanticPair reward candidate)
      (quittingTerminalSemanticPair_mem_carrier reward candidate)
  have hinf : value profile ≤ sInf (Set.range value) :=
    le_csInf ⟨value profile, ⟨profile, rfl⟩⟩ hlower
  exact le_antisymm hinf (quittingTerminalExploitabilityInf_le reward profile)

private theorem exists_negative_gap_of_incoherent {α β : Type*}
    (support : Set β) (gap : α → β → ℝ)
    (hincoherent : ¬ ∀ who action, action ∈ support → 0 ≤ gap who action) :
    ∃ who action, action ∈ support ∧ gap who action < 0 := by
  by_contra hnone
  exact hincoherent fun who action ha => le_of_not_gt fun h => hnone ⟨who, action, ha, h⟩

private theorem terminalExploitability_eq_inf_and_pos_of_realized_minimum
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (pair : QuittingTerminalSemanticPair ι)
    (hpair : quittingTerminalSemanticPair reward profile = pair)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticExploitability pair ≤
        quittingTerminalSemanticExploitability candidate)
    (hpositive : 0 < quittingTerminalSemanticExploitability pair) :
    quittingTerminalExploitability reward profile = quittingTerminalExploitabilityInf reward ∧
      0 < quittingTerminalExploitabilityInf reward := by
  have hactual : quittingTerminalExploitability reward profile =
      quittingTerminalSemanticExploitability pair :=
    (quittingTerminalSemanticExploitability_pair reward profile).symm.trans
      (congrArg (quittingTerminalSemanticExploitability (ι := ι)) hpair)
  have hroot := terminalExploitability_eq_inf_of_minimum_pair reward profile pair hactual hminimum
  exact ⟨hroot, hpositive.trans_eq (hactual.symm.trans hroot)⟩

private theorem exists_twoSureRoot_realizing_positive_minimum
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticLawPoint ι)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hNever : point.2 none = 0)
    (hSingleton : ∀ who, point.2 (some (quittingSingletonTerminal who)) = 0)
    (hcard : 1 < Fintype.card ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticExploitability point.1 ≤
        quittingTerminalSemanticExploitability candidate)
    (hpositive : 0 < quittingTerminalSemanticExploitability point.1) :
    ∃ (root : ι → PMF Bool) (first second : ι),
      first ≠ second ∧ (root first true).toReal = 1 ∧ (root second true).toReal = 1 ∧
      quittingTerminalSemanticPair reward
        (quittingOneDateThenNeverProfile reward root) = point.1 ∧
      quittingTerminalOutcomeMass reward
        (quittingOneDateThenNeverProfile reward root) = point.2 ∧
      quittingTerminalExploitability reward
        (quittingOneDateThenNeverProfile reward root) = quittingTerminalExploitabilityInf reward ∧
      0 < quittingTerminalExploitabilityInf reward := by
  have hsemantic := terminalSemanticLawCarrier_fst_mem_carrier point hpoint
  have hstrict (who : ι) : reward (quittingSingletonTerminal who) who < point.1.2 who :=
    sub_pos.mp (hpositive.trans_le
      (minimumTerminalSemantic_exploitabilitySingletonMargin
        reward point.1 hsemantic hminimum hpositive who))
  obtain ⟨root, first, second, hdistinct, hfirst, hsecond, hpair, hlaw, _, _⟩ :=
    exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin
      reward point hpoint hNever hSingleton hcard hstrict
  obtain ⟨hrootMinimum, hinfPositive⟩ :=
    terminalExploitability_eq_inf_and_pos_of_realized_minimum reward
      (quittingOneDateThenNeverProfile reward root) point.1 hpair hminimum hpositive
  exact ⟨root, first, second, hdistinct, hfirst, hsecond, hpair, hlaw, hrootMinimum,
    hinfPositive⟩

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
  obtain ⟨root, first, second, hdistinct, hfirst, hsecond, hpair, hlaw, hrootMinimum,
      hinfPositive⟩ :=
    exists_twoSureRoot_realizing_positive_minimum final point hpoint hNever hSingleton
      (by norm_num : 1 < Fintype.card (Fin 4)) hminimum hpositive
  refine ⟨root, first, second, hdistinct, hfirst, hsecond, hpair, hlaw, hrootMinimum, ?_⟩
  intro preferred
  let gap (who : Fin 4) (action : Fin 4 → Bool) :=
    quittingDirectedMembershipGap original who (preferred who) action
  exact exists_negative_gap_of_incoherent (pmfPi root).support gap fun hcoherent =>
    not_membershipStretch_coherent_positiveMinimum_finFour
      original final halpha hagrees horiginalBound hfinalBound root preferred first second
      hdistinct hfirst hsecond hcoherent hinfPositive hinfOrder hrootMinimum

end GameTheory
