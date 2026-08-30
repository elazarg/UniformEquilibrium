/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.LawTightCapNashGlobalMinimumMoat
import UniformEquilibrium.Diagnostics.Quitting.LawTightCapNashStrictMinimum
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourMinimumLawFiniteAtom

/-!
# Fin4 global-minimum moat and strict-minimum chambers

The no-uniform-payoff hypothesis supplies a positive law-tight saturation
minimum with a positive finite terminal atom.  Global-minimum inheritance gives
an origin-debt singleton moat.  Applied to the dimension-free strict
classification, that moat excludes the singleton/Never binding-collision arm,
leaving full debt support or a reset-rigid same-law return.

This is a carrier-level Fin4 source with a branch-local consumer.  It does not
realize the minimum by one behavioral profile, consume either remaining
chamber, provide source chronology, or prove a uniform-equilibrium payoff.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification

/-- A canonical Fin4 no-uniform-payoff source retains the origin and minimum
global-debt data, the literal origin-debt singleton moat, and the two surviving
strict-minimum chambers. -/
theorem finFour_noUniformPayoff_exists_lawTightGlobalMinimumMoatTwoChamber
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hno : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ (origin minimum : QuittingTerminalSemanticLawPoint (Fin 4))
        (terminal : {S : Finset (Fin 4) // S.Nonempty}),
      origin ∈ quittingTerminalSemanticLawCarrier reward ∧
      IsQuittingLawTightCapNashSaturationMinimum reward origin minimum ∧
      0 < quittingTerminalSemanticDebtSum origin.1 ∧
      0 < quittingTerminalSemanticDebtSum minimum.1 ∧
      0 < minimum.2 (some terminal) ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum origin.1 ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      quittingTerminalSemanticDebtSum origin.1 =
        quittingTerminalSemanticDebtSum minimum.1 ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum minimum.1 ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      (∀ who, quittingTerminalSemanticDebtSum origin.1 ≤
        minimum.1.2 who - reward (quittingSingletonTerminal who) who) ∧
      ((∀ who, 0 < quittingTerminalSemanticDebt minimum.1 who) ∨
        Nonempty (QuittingLawTightResetRigidChamber
          reward origin minimum minimum origin.1)) := by
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
  obtain ⟨_hminimumSemantic, heq, hminimumGlobal, hmoat⟩ :=
    lawTightCapNashMinimum_globalMinimumOriginDebtMoat horigin hsourceMinimum
      hminimum hminimumPositive
  have hbranch :=
    lawTightStrictSaturation_fullDebt_or_resetRigid_or_singletonNeverCycle
      residual.witness origin.1 hsourceMinimum hsourcePositive
        origin minimum minimum horigin hminimum hminimumPositive
          hminimum.minimum_mem_face atom.terminal hatom
  have htwo :
      (∀ who, 0 < quittingTerminalSemanticDebt minimum.1 who) ∨
        Nonempty (QuittingLawTightResetRigidChamber
          reward origin minimum minimum origin.1) := by
    rcases hbranch with hfull | hreset | hsingleton
    · exact Or.inl hfull
    · exact Or.inr hreset
    · obtain ⟨singleton⟩ := hsingleton
      have howner := hmoat singleton.support.owner
      rw [singleton.cap_binding, sub_self] at howner
      exact False.elim ((not_lt_of_ge howner) hsourcePositive)
  exact ⟨origin, minimum, atom.terminal, horigin, hminimum,
    hsourcePositive, hminimumPositive, hatom, hsourceMinimum, heq,
    hminimumGlobal, hmoat, htwo⟩

/-- Compatibility projection retaining the historical minimum-and-atom
surface. -/
theorem exists_finFourLawTightSaturationMinimum_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hno : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ (origin minimum : QuittingTerminalSemanticLawPoint (Fin 4))
        (terminal : {S : Finset (Fin 4) // S.Nonempty}),
      IsQuittingLawTightCapNashSaturationMinimum reward origin minimum ∧
      0 < minimum.2 (some terminal) := by
  obtain ⟨origin, minimum, terminal, _horigin, hminimum,
      _horiginPositive, _hminimumPositive, hatom, _horiginGlobal,
      _heq, _hminimumGlobal, _hmoat, _hbranch⟩ :=
    finFour_noUniformPayoff_exists_lawTightGlobalMinimumMoatTwoChamber
      reward hno
  exact ⟨origin, minimum, terminal, hminimum, hatom⟩

/-- Compatibility weakening of the canonical two-chamber theorem to the
historical three-chamber result type. -/
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
  obtain ⟨origin, minimum, terminal, horigin, hminimum,
      _horiginPositive, hminimumPositive, hatom, _horiginGlobal,
      _heq, _hminimumGlobal, _hmoat, hbranch⟩ :=
    finFour_noUniformPayoff_exists_lawTightGlobalMinimumMoatTwoChamber
      reward hno
  refine ⟨origin, minimum, terminal, horigin, hminimum,
    hminimumPositive, hatom, ?_⟩
  rcases hbranch with hfull | hreset
  · exact Or.inl hfull
  · exact Or.inr (Or.inl hreset)

end GameTheory
