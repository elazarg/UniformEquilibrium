/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.FullSupportProjectiveQBarResidual
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumLawFiniteAtom
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn
import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.Quitting.SimpleBranches

/-!
# Four-player compatibility wrappers for minimum-law finite atoms

The generic punishment-normal minimum-law theorem is owned by
`TerminalSemanticMinimumLawFiniteAtom`.  This module retains the original
four-player hard-residual corollaries and import path.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability StochasticGame
open scoped Topology

/-- Every globally minimizing joint law in the four-player hard residual has a positive finite
coalition coordinate.  Positivity of the minimum is derived from the residual witness. -/
theorem exists_positive_finiteLawAtom_of_finFourHardResidual_minimum
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (point : QuittingTerminalSemanticLawPoint (Fin 4))
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ terminal : {S : Finset (Fin 4) // S.Nonempty},
      0 < point.2 (some terminal) := by
  have hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who := by
    intro who
    simpa [IsQuittingNormalPlayer, quittingSoloSelfPayoff,
      quittingSingletonTerminal] using residual.all_punishmentNormal who
  exact
    exists_positive_finiteLawAtom_of_punishmentNormal_minimum_of_not_uniformPayoff
      reward residual.witness.not_exists_uniformEquilibriumPayoff hnormal
      point hpoint hminimum

/-! ## Same-point causalization -/

/-- The finite atom of a supplied four-player hard-residual minimum joint law enters the checked
deep causal suffix-atom construction at that same carrier point. -/
theorem finFourHardResidual_minimumLaw_causalSuffixAtom
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (point : QuittingTerminalSemanticLawPoint (Fin 4))
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate) :
    Nonempty (QuittingMinimumLawCausalSuffixAtom reward point) := by
  have hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who := by
    intro who
    simpa [IsQuittingNormalPlayer, quittingSoloSelfPayoff,
      quittingSingletonTerminal] using residual.all_punishmentNormal who
  exact
    nonempty_minimumLawCausalSuffixAtom_of_punishmentNormal_of_not_uniformPayoff
      reward residual.witness.not_exists_uniformEquilibriumPayoff hnormal
      point hpoint hminimum

/-- A four-player hard residual alone selects a globally minimizing joint-law point, proves its
positive finite atom, and causalizes that atom while preserving the selected point and minimum
provenance. -/
theorem exists_finFourHardResidual_minimumLaw_causalSuffixAtom
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound) :
    ∃ point : QuittingTerminalSemanticLawPoint (Fin 4),
      point ∈ quittingTerminalSemanticLawCarrier reward ∧
      point.1 ∈ quittingTerminalSemanticCarrier reward ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum point.1 ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      0 < quittingTerminalDebtSumInf reward ∧
      quittingTerminalSemanticDebtSum point.1 =
        quittingTerminalDebtSumInf reward ∧
      Nonempty (QuittingMinimumLawCausalSuffixAtom reward point) := by
  obtain ⟨point, hpoint, hcarrier, hminimum, hminimumValue⟩ :=
    exists_minimum_terminalSemanticLawCarrier_of_not_uniformPayoff reward
      residual.witness.not_exists_uniformEquilibriumPayoff
  have hinf : 0 < quittingTerminalDebtSumInf reward :=
    quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff.mpr
      residual.witness.not_exists_uniformEquilibriumPayoff
  exact ⟨point, hpoint, hcarrier, hminimum, hinf, hminimumValue,
    finFourHardResidual_minimumLaw_causalSuffixAtom
      reward bound residual point hpoint hminimum⟩

end GameTheory
