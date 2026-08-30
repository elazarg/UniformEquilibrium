/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.FinFourLawTightCapNashStrictMinimum
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourMinimumFiberIsolation

/-!
# Collapse of the Fin4 law-tight strict minimum to two chambers

The Fin4 law-tight saturation minimum is selected from a hull whose origin is
already a global minimum of terminal semantic debt.  Because the origin itself
belongs to the hull, hull minimality and global minimality force the selected
point to have the same globally minimal debt.

Punishment normality then places its prescribed payoff strictly above every
own singleton reward.  This is incompatible with the singleton/Never chamber:
that chamber has a zero-debt owner whose cap is exactly its singleton reward.
Thus a hypothetical Fin4 counterexample leaves only full positive-debt support
or the same-law reset-rigid chamber.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification

/-- **Two-chamber collapse at the global minimum.**

A literal Fin4 no-uniform-payoff hypothesis supplies a law-tight saturation
minimum which is itself a global terminal-semantic debt minimizer, is strictly
above every own singleton reward in its prescribed coordinate, retains a
positive finite atom, and has either full positive-debt support or a
reset-rigid same-law return.  The singleton/Never binding-cycle chamber is
impossible. -/
theorem finFour_noUniformPayoff_exists_globalLawTightFullDebt_or_resetRigid
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hno : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ (origin minimum : QuittingTerminalSemanticLawPoint (Fin 4))
        (terminal : {S : Finset (Fin 4) // S.Nonempty}),
      origin ∈ quittingTerminalSemanticLawCarrier reward ∧
      IsQuittingLawTightCapNashSaturationMinimum reward origin minimum ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum minimum.1 ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      quittingTerminalSemanticDebtSum minimum.1 =
        quittingTerminalSemanticDebtSum origin.1 ∧
      0 < quittingTerminalSemanticDebtSum minimum.1 ∧
      0 < minimum.2 (some terminal) ∧
      (∀ who,
        reward (quittingSingletonTerminal who) who < minimum.1.1 who) ∧
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
  obtain ⟨minimum, hminimum, _hminimumFloor, _hcone, hatom⟩ :=
    exists_quittingLawTightCapNashSaturationMinimum_retaining_atom
      reward (quittingTerminalDebtSumInf reward) hinf
        (fun point hpoint ↦ by
          rw [← horiginDebt]
          exact hsourceMinimum point.1
            (terminalSemanticLawCarrier_fst_mem_carrier point hpoint))
        origin horigin atom.terminal atom.terminalMass_pos
  have hminimumJoint : minimum ∈
      quittingTerminalSemanticLawCarrier reward :=
    quittingLawTightCapNashSaturationHull_subset_carrier
      reward origin horigin hminimum.mem
  have hminimumSemantic : minimum.1 ∈
      quittingTerminalSemanticCarrier reward :=
    terminalSemanticLawCarrier_fst_mem_carrier minimum hminimumJoint
  have hminimumLeOrigin :
      quittingTerminalSemanticDebtSum minimum.1 ≤
        quittingTerminalSemanticDebtSum origin.1 :=
    hminimum.debt_le origin
      (quittingLawTightCapNashSaturationHull_origin_mem reward origin)
  have horiginLeMinimum :
      quittingTerminalSemanticDebtSum origin.1 ≤
        quittingTerminalSemanticDebtSum minimum.1 :=
    hsourceMinimum minimum.1 hminimumSemantic
  have hminimumDebt :
      quittingTerminalSemanticDebtSum minimum.1 =
        quittingTerminalSemanticDebtSum origin.1 :=
    le_antisymm hminimumLeOrigin horiginLeMinimum
  have hminimumGlobal : ∀ candidate ∈
      quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum.1 ≤
        quittingTerminalSemanticDebtSum candidate := by
    intro candidate hcandidate
    rw [hminimumDebt]
    exact hsourceMinimum candidate hcandidate
  have hsourcePositive :
      0 < quittingTerminalSemanticDebtSum origin.1 := by
    rw [horiginDebt]
    exact hinf
  have hminimumPositive :
      0 < quittingTerminalSemanticDebtSum minimum.1 := by
    rw [hminimumDebt]
    exact hsourcePositive
  have hnormal : ∀ who,
      quittingPunishmentValue reward who ≤
        reward (quittingSingletonTerminal who) who := by
    intro who
    simpa [IsQuittingNormalPlayer, quittingSoloSelfPayoff,
      quittingSingletonTerminal] using residual.all_punishmentNormal who
  have hstrict : ∀ who,
      reward (quittingSingletonTerminal who) who < minimum.1.1 who :=
    minimumTerminalSemantic_strictSingleton_of_punishmentNormal
      minimum.1 hminimumSemantic hminimumGlobal hminimumPositive hnormal
  have hbranch :=
    lawTightStrictSaturation_fullDebt_or_resetRigid_or_singletonNeverCycle
      residual.witness origin.1 hsourceMinimum hsourcePositive
        origin minimum minimum horigin hminimum hminimumPositive
          hminimum.minimum_mem_face atom.terminal hatom
  refine ⟨origin, minimum, atom.terminal, horigin, hminimum,
    hminimumGlobal, hminimumDebt, hminimumPositive, hatom, hstrict, ?_⟩
  rcases hbranch with hfull | hreset | hsingle
  · exact Or.inl hfull
  · exact Or.inr hreset
  · obtain ⟨chamber⟩ := hsingle
    have hzero := chamber.support.owner_debt_zero
    unfold quittingTerminalSemanticDebt at hzero
    rw [chamber.cap_binding] at hzero
    linarith [hstrict chamber.support.owner]

end GameTheory
