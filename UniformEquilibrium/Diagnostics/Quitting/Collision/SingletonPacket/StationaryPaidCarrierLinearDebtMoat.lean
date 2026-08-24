/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.LeaveJoinStationaryTwoDebtorHandoff
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourCarrierSourceChargeDebtErrorGate

/-!
# Stationary paid carriers and the linear debt moat

This module composes the actual stationary two-debtor handoff with the
complete minimum-fiber linear basin.  Near the minimum carrier fiber, every
approximate root pays linearly for absorption.  The same conclusion is then
specialized to the literal terminal-semantic pair of the stationary handoff.

No charged root or return path is produced.
-/

noncomputable section

namespace GameTheory

open Set Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

namespace FinFourCarrierSourceChargeDebtErrorGate

/-- At the prescribed coordinate of any carrier pair, either the source lies
above the compact debt moat or every approximate root pays the sharp Fin4
linear absorption bound. -/
theorem debt_or_absorption_le_four_mul_error_div
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {chargeThreshold error : ℝ}
    (gate : FinFourCarrierSourceChargeDebtErrorGate
      reward chargeThreshold)
    (source : QuittingTerminalSemanticPair (Fin 4))
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (root : Fin 4 → PMF Bool)
    (hnash : IsεQuittingRootNash reward source.1 error root) :
    quittingTerminalSemanticDebtSum gate.base + gate.eta ≤
        quittingTerminalSemanticDebtSum source ∨
      quittingRootAbsorptionMass root ≤ 4 * error / gate.c := by
  by_cases hdebt : quittingTerminalSemanticDebtSum gate.base + gate.eta ≤
      quittingTerminalSemanticDebtSum source
  · exact Or.inl hdebt
  · right
    have hsourceClose := gate.source_close source hsource (lt_of_not_ge hdebt)
    have hKnonempty : gate.K.Nonempty := by
      rw [gate.minimum_projection]
      exact (quittingTerminalSemanticMinimumFiber_nonempty
        reward gate.base gate.base_mem).image Prod.fst
    have hsourceMem : source.1 ∈ gate.N := by
      apply gate.thickening_subset
      apply (Metric.mem_thickening_iff_infDist_lt hKnonempty).2
      exact hsourceClose.trans (by linarith [gate.rho_pos])
    have hlinear := gate.linear_defect source.1 hsourceMem root
    have hdefect :=
      quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash
        reward source.1 root error hnash
    norm_num [Fintype.card_fin] at hdefect
    apply (le_div_iff₀ gate.c_pos).2
    nlinarith

/-- In the exact case, failure of the carrier debt moat forces the literal
all-Continue identity root. -/
theorem debt_or_exactRoot_eq_allContinue
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {chargeThreshold : ℝ}
    (gate : FinFourCarrierSourceChargeDebtErrorGate
      reward chargeThreshold)
    (source : QuittingTerminalSemanticPair (Fin 4))
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (root : Fin 4 → PMF Bool)
    (hnash : IsεQuittingRootNash reward source.1 0 root) :
    quittingTerminalSemanticDebtSum gate.base + gate.eta ≤
        quittingTerminalSemanticDebtSum source ∨
      root = quittingAllContinueRoot ∧
        quittingRootSuccessorPayoff reward source.1 root = source.1 ∧
        quittingRootAbsorptionMass root = 0 := by
  rcases gate.debt_or_absorption_le_four_mul_error_div
      source hsource root hnash with hdebt | habsorption
  · exact Or.inl hdebt
  · right
    have habsorptionNonneg := quittingRootAbsorptionMass_nonneg root
    have habsorptionZero : quittingRootAbsorptionMass root = 0 := by
      norm_num at habsorption
      linarith
    have hcontinue : quittingStationaryContinueMass root = 1 := by
      unfold quittingRootAbsorptionMass at habsorptionZero
      linarith
    have hroot : root = quittingAllContinueRoot :=
      eq_quittingAllContinueRoot_of_continueMass_eq_one root hcontinue
    refine ⟨hroot, ?_, habsorptionZero⟩
    rw [hroot, quittingRootSuccessorPayoff_allContinueRoot_eq]

end FinFourCarrierSourceChargeDebtErrorGate

/-- The actual stationary two-debtor handoff together with the complete
minimum-fiber debt/error gate. -/
structure FinFourStationaryPaidCarrierLinearDebtMoat
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (witness : QuittingTerminalExploitabilityWitness reward)
    (M : ℝ) (leaver spectator joiner fourth : Fin 4)
    (chargeThreshold : ℝ) where
  handoff : FinFourLeaveJoinStationaryTwoDebtorHandoff reward witness M
    leaver spectator joiner fourth
  gate : FinFourCarrierSourceChargeDebtErrorGate reward chargeThreshold

/-- Any checked stationary handoff on a hypothetical counterexample composes
with the carrier-source gate at every positive charge threshold. -/
theorem nonempty_finFourStationaryPaidCarrierLinearDebtMoat
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hno : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    {M : ℝ} {leaver spectator joiner fourth : Fin 4}
    (handoff : FinFourLeaveJoinStationaryTwoDebtorHandoff reward witness M
      leaver spectator joiner fourth)
    {chargeThreshold : ℝ} (hchargeThreshold : 0 < chargeThreshold) :
    Nonempty (FinFourStationaryPaidCarrierLinearDebtMoat reward witness M
      leaver spectator joiner fourth chargeThreshold) := by
  obtain ⟨gate⟩ :=
    exists_finFour_carrierSourceChargeDebtErrorGate_of_no_uniformPayoff
      reward hno hchargeThreshold
  exact ⟨⟨handoff, gate⟩⟩

namespace FinFourStationaryPaidCarrierLinearDebtMoat

/-- The semantic pair of the stored stationary profile is an actual carrier
point, without taking a closure limit. -/
theorem sourcePair_mem_carrier
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {M : ℝ} {leaver spectator joiner fourth : Fin 4}
    {chargeThreshold : ℝ}
    (source : FinFourStationaryPaidCarrierLinearDebtMoat reward witness M
      leaver spectator joiner fourth chargeThreshold) :
    finFourLeaveJoinSemanticPair reward spectator leaver joiner
        source.handoff.point ∈ quittingTerminalSemanticCarrier reward := by
  exact quittingTerminalSemanticPair_mem_carrier reward
    (finFourLeaveJoinProfile reward spectator leaver joiner
      source.handoff.point)

/-- Source-native form of the carrier debt-versus-absorption alternative for
the literal stationary paid profile. -/
theorem source_debt_or_absorption_le_four_mul_error_div
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {M : ℝ} {leaver spectator joiner fourth : Fin 4}
    {chargeThreshold error : ℝ}
    (source : FinFourStationaryPaidCarrierLinearDebtMoat reward witness M
      leaver spectator joiner fourth chargeThreshold)
    (root : Fin 4 → PMF Bool)
    (hnash : IsεQuittingRootNash reward
      (finFourLeaveJoinSemanticPair reward spectator leaver joiner
        source.handoff.point).1 error root) :
    quittingTerminalSemanticDebtSum source.gate.base + source.gate.eta ≤
        quittingTerminalSemanticDebtSum
          (finFourLeaveJoinSemanticPair reward spectator leaver joiner
            source.handoff.point) ∨
      quittingRootAbsorptionMass root ≤ 4 * error / source.gate.c := by
  exact source.gate.debt_or_absorption_le_four_mul_error_div
    _ source.sourcePair_mem_carrier root hnash

/-- An exact charged path starting at the literal stationary paid payoff must
start above the fixed carrier debt moat. -/
theorem source_debt_of_punishmentFloorAdmissiblePath
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {M : ℝ} {leaver spectator joiner fourth : Fin 4}
    {chargeThreshold : ℝ}
    (sourceData : FinFourStationaryPaidCarrierLinearDebtMoat reward witness M
      leaver spectator joiner fourth chargeThreshold)
    (source target : QuittingPunishmentFloorAdmissibleState reward)
    (path : (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
      source target)
    (hsource : source.1.1.1 =
      (finFourLeaveJoinSemanticPair reward spectator leaver joiner
        sourceData.handoff.point).1)
    (hcharge : chargeThreshold ≤ path.chargeSum) :
    quittingTerminalSemanticDebtSum sourceData.gate.base +
        sourceData.gate.eta ≤
      quittingTerminalSemanticDebtSum
        (finFourLeaveJoinSemanticPair reward spectator leaver joiner
          sourceData.handoff.point) := by
  exact sourceData.gate.debt_of_punishmentFloorAdmissiblePath
    _ sourceData.sourcePair_mem_carrier source target path hsource hcharge

end FinFourStationaryPaidCarrierLinearDebtMoat

end GameTheory
