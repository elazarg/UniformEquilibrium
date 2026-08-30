/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.LawTightCapNashStrictMinimum
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourMinimumLawFiniteAtom

/-!
# Fin4 source for the law-tight strict-minimum chambers

The no-uniform-payoff hypothesis supplies a positive law-tight saturation
minimum with a positive finite terminal atom.  The dimension-free strict
classification then gives full debt support, a reset-rigid same-law return,
or a singleton/Never binding-collision cycle at that same minimum.

This is a carrier-level Fin4 source and classification.  It does not realize
the minimum by one behavioral profile, consume any chamber, or prove a
uniform-equilibrium payoff.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification

/-- A Fin4 no-uniform-payoff witness supplies a law-tight hull minimum that
retains a positive finite atom. -/
theorem exists_finFourLawTightSaturationMinimum_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hno : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ (origin minimum : QuittingTerminalSemanticLawPoint (Fin 4))
        (terminal : {S : Finset (Fin 4) // S.Nonempty}),
      IsQuittingLawTightCapNashSaturationMinimum reward origin minimum ∧
      0 < minimum.2 (some terminal) := by
  obtain ⟨residual⟩ :=
    nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff
      reward (abs_reward_le_quittingRewardBound reward) hno
  obtain ⟨origin, horigin, _horiginSemantic, hminimum, hinf,
      horiginDebt, atom⟩ :=
    exists_finFourHardResidual_minimumLaw_causalSuffixAtom
      reward (quittingRewardBound reward) residual
  obtain ⟨atom⟩ := atom
  obtain ⟨minimum, hminimumHull, _hfloor, _hcone, hatom⟩ :=
    exists_quittingLawTightCapNashSaturationMinimum_retaining_atom
      reward (quittingTerminalDebtSumInf reward) hinf
        (fun point hpoint ↦ by
          rw [← horiginDebt]
          exact hminimum point.1
            (terminalSemanticLawCarrier_fst_mem_carrier point hpoint))
        origin horigin atom.terminal atom.terminalMass_pos
  exact ⟨origin, minimum, atom.terminal, hminimumHull, hatom⟩

/-- A literal Fin4 no-uniform-payoff source supplies a positive law-tight
minimum and the strict three-chamber carrier classification at that same
minimum. -/
theorem finFour_noUniformPayoff_exists_lawTightStrictMinimumChamber
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hno : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ (origin minimum : QuittingTerminalSemanticLawPoint (Fin 4))
        (terminal : {S : Finset (Fin 4) // S.Nonempty}),
      origin ∈ quittingTerminalSemanticLawCarrier reward ∧
      IsQuittingLawTightCapNashSaturationMinimum reward origin minimum ∧
      0 < quittingTerminalSemanticDebtSum minimum.1 ∧
      0 < minimum.2 (some terminal) ∧
      ((∀ who, 0 < quittingTerminalSemanticDebt minimum.1 who) ∨
        Nonempty (QuittingLawTightResetRigidChamber
          reward origin minimum minimum origin.1) ∨
        Nonempty (QuittingSingletonNeverBindingCycleChamber reward minimum)) := by
  obtain ⟨residual⟩ :=
    nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff
      reward (abs_reward_le_quittingRewardBound reward) hno
  obtain ⟨origin, horigin, _horiginSemantic, hsourceMinimum, hinf,
      horiginDebt, ⟨atom⟩⟩ :=
    exists_finFourHardResidual_minimumLaw_causalSuffixAtom
      reward (quittingRewardBound reward) residual
  obtain ⟨minimum, hminimum, hminimumFloor, _hcone, hatom⟩ :=
    exists_quittingLawTightCapNashSaturationMinimum_retaining_atom
      reward (quittingTerminalDebtSumInf reward) hinf
        (fun point hpoint ↦ by
          rw [← horiginDebt]
          exact hsourceMinimum point.1
            (terminalSemanticLawCarrier_fst_mem_carrier point hpoint))
        origin horigin atom.terminal atom.terminalMass_pos
  have hsourcePositive :
      0 < quittingTerminalSemanticDebtSum origin.1 := by
    rw [horiginDebt]
    exact hinf
  have hminimumPositive :
      0 < quittingTerminalSemanticDebtSum minimum.1 :=
    hinf.trans_le hminimumFloor
  have hbranch :=
    lawTightStrictSaturation_fullDebt_or_resetRigid_or_singletonNeverCycle
      residual.witness origin.1 hsourceMinimum hsourcePositive
        origin minimum minimum horigin hminimum hminimumPositive
          hminimum.minimum_mem_face atom.terminal hatom
  exact ⟨origin, minimum, atom.terminal, horigin, hminimum,
    hminimumPositive, hatom, hbranch⟩

end GameTheory
