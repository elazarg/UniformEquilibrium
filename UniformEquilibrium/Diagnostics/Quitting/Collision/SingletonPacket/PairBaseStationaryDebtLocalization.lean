/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourSoloWallDispatch

/-!
# Unconditional pair-base stationary debt localization

Force any prescribed two-player base on `Fin 4` to Quit and select an exact
Nash point of the induced game on its complement.  Both complementary
coordinates realize their unrestricted behavioral caps.  Hence a terminal
exploitability witness localizes a full-gap debtor, and a literal paid
first-disagreement row, to the prescribed base.

This localization needs no leave--join sign or quantitative absorption
hypothesis.  Such a sign is needed only for a lower bound on mass outside the
base, not for the actual stationary paid source constructed here.
-/

noncomputable section

namespace GameTheory

open Finset
open Math.Probability Math.PMFProduct

/-- The two labels complementary to a pair base on `Fin 4`. -/
def finFourPairBaseComplement (base : Finset (Fin 4)) : Finset (Fin 4) :=
  Finset.univ \ base

/-- Actual stationary semantic data obtained from an arbitrary two-player
sure-Quit base on `Fin 4`. -/
structure FinFourPairBaseStationaryDebtLocalization
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (witness : QuittingTerminalExploitabilityWitness reward)
    (base : Finset (Fin 4)) where
  base_card : base.card = 2
  point : mixedPolytope
    (quittingBinaryForm (finFourPairBaseComplement base)).sig
  point_mem : point ∈
    quittingPersistentBaseNashSet reward base
      (finFourPairBaseComplement base)
  source_mem : quittingTerminalSemanticPair reward
      (quittingStationaryProfile reward
        (quittingPersistentBaseRoot base
          (finFourPairBaseComplement base) point)) ∈
    quittingTerminalSemanticCarrier reward
  free_solved : ∀ who ∈ finFourPairBaseComplement base,
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingStationaryProfile reward
            (quittingPersistentBaseRoot base
              (finFourPairBaseComplement base) point))) who = 0 ∧
      quittingPunishmentValue reward who ≤
        quittingTerminalPayoff reward
          (quittingStationaryProfile reward
            (quittingPersistentBaseRoot base
              (finFourPairBaseComplement base) point)) who
  debtor : Fin 4
  debtor_mem : debtor ∈ base
  debtor_gap : witness.terminalGap ≤
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingStationaryProfile reward
          (quittingPersistentBaseRoot base
            (finFourPairBaseComplement base) point))) debtor
  paid_row : Nonempty (QuittingPaidFirstDisagreementRow reward
    (quittingStationaryProfile reward
      (quittingPersistentBaseRoot base
        (finFourPairBaseComplement base) point))
    debtor witness.terminalGap)

/-- Every two-element base yields an actual stationary source whose terminal
gap and paid row are localized to that base. -/
theorem nonempty_finFourPairBaseStationaryDebtLocalization
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (base : Finset (Fin 4)) (hbaseCard : base.card = 2) :
    Nonempty (FinFourPairBaseStationaryDebtLocalization reward witness
      base) := by
  have hbase : base.Nonempty := by
    exact (Finset.one_lt_card_iff_nontrivial.mp (by omega)).nonempty
  have hdisjoint : Disjoint base (finFourPairBaseComplement base) := by
    rw [Finset.disjoint_left]
    intro who hwho
    simp [finFourPairBaseComplement, hwho]
  obtain ⟨point, hpoint⟩ :=
    quittingPersistentBaseNashSet_nonempty reward base
      (finFourPairBaseComplement base)
  let root := quittingPersistentBaseRoot base
    (finFourPairBaseComplement base) point
  let profile := quittingStationaryProfile reward root
  let pair := quittingTerminalSemanticPair reward profile
  have hfreeSemantic := persistentBase_inducedNash_free_semantics
    base (finFourPairBaseComplement base) hbase hdisjoint point hpoint
  have hfreeSolved : ∀ who ∈ finFourPairBaseComplement base,
      quittingTerminalSemanticDebt pair who = 0 ∧
        quittingPunishmentValue reward who ≤
          quittingTerminalPayoff reward profile who := by
    intro who hwho
    have hsemantic := hfreeSemantic who hwho
    have hsolved : pair.2 who = pair.1 who := by
      change (quittingTerminalSemanticPair reward profile).2 who =
        quittingTerminalPayoff reward profile who
      rw [show profile = quittingStationaryProfile reward root by rfl,
        quittingTerminalSemanticPair_stationary_envelope_eq_cap]
      exact hsemantic.1.symm
    constructor
    · unfold quittingTerminalSemanticDebt
      rw [hsolved]
      exact sub_self _
    · exact hsemantic.2
  have hsourceMem : pair ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward profile
  obtain ⟨debtor, deviation, hexploit⟩ :=
    witness.terminalExploitability profile
  have hdeviationCap := quittingTerminalPayoff_update_stationary_le_cap
    reward root debtor deviation
  have hdebtorGap : witness.terminalGap ≤
      quittingTerminalSemanticDebt pair debtor := by
    change witness.terminalGap ≤
      (quittingTerminalSemanticPair reward profile).2 debtor -
        quittingTerminalPayoff reward profile debtor
    rw [show profile = quittingStationaryProfile reward root by rfl,
      quittingTerminalSemanticPair_stationary_envelope_eq_cap]
    linarith
  have hdebtorMem : debtor ∈ base := by
    by_contra hnot
    have hfree : debtor ∈ finFourPairBaseComplement base := by
      simp [finFourPairBaseComplement, hnot]
    rw [(hfreeSolved debtor hfree).1] at hdebtorGap
    linarith [witness.terminalGap_pos]
  have hpaid : Nonempty (QuittingPaidFirstDisagreementRow reward profile
      debtor witness.terminalGap) := by
    have hcapDebt : witness.terminalGap ≤
        quittingStationaryUnilateralCap reward root debtor -
          quittingTerminalPayoff reward profile debtor := by
      have hgap := hdebtorGap
      change witness.terminalGap ≤
        (quittingTerminalSemanticPair reward profile).2 debtor -
          quittingTerminalPayoff reward profile debtor at hgap
      rw [show profile = quittingStationaryProfile reward root by rfl,
        quittingTerminalSemanticPair_stationary_envelope_eq_cap] at hgap
      exact hgap
    rcases exists_oriented_quitNow_never_gap_of_stationary_cap_debt
        reward root debtor hcapDebt with hquit | hnever
    · obtain ⟨row, -, -⟩ :=
        exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub
          reward profile debtor none (some 0) witness.terminalGap
            witness.terminalGap_pos hquit
      exact ⟨row⟩
    · obtain ⟨row, -, -⟩ :=
        exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub
          reward profile debtor (some 0) none witness.terminalGap
            witness.terminalGap_pos hnever
      exact ⟨row⟩
  exact ⟨{
    base_card := hbaseCard
    point := point
    point_mem := hpoint
    source_mem := hsourceMem
    free_solved := hfreeSolved
    debtor := debtor
    debtor_mem := hdebtorMem
    debtor_gap := hdebtorGap
    paid_row := hpaid }⟩

end GameTheory
