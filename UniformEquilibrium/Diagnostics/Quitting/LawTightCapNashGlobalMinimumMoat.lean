/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.LawTightCapNashMinimumFace
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget

/-!
# Global-minimum singleton moats for law-tight cap--Nash hulls

A point on the minimum equality level set inherits global debt minimality from
a globally minimizing carrier origin.  At positive minimum debt, the standard
singleton-margin estimate therefore gives a literal moat whose left-hand side
is the origin debt.

These are conditional carrier-level statements.  They do not supply an
origin, a behavioral realization, source chronology, a chamber consumer, or a
uniform-equilibrium payoff.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A point on the hull-minimum level set inherits semantic-carrier membership,
global debt minimality, and the singleton moat measured by the origin debt. -/
theorem lawTightCapNashMinimumFace_globalMinimumOriginDebtMoat
    {origin minimum point : QuittingTerminalSemanticLawPoint ι}
    (horigin : origin ∈ quittingTerminalSemanticLawCarrier reward)
    (horiginMinimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum origin.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimum : IsQuittingLawTightCapNashSaturationMinimum
      reward origin minimum)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum.1)
    (hpoint : point ∈ quittingLawTightCapNashSaturationMinimumFace
      reward origin minimum) :
    point.1 ∈ quittingTerminalSemanticCarrier reward ∧
      quittingTerminalSemanticDebtSum origin.1 =
        quittingTerminalSemanticDebtSum point.1 ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum point.1 ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      ∀ who, quittingTerminalSemanticDebtSum origin.1 ≤
        point.1.2 who - reward (quittingSingletonTerminal who) who := by
  have hpointJoint : point ∈ quittingTerminalSemanticLawCarrier reward :=
    quittingLawTightCapNashSaturationHull_subset_carrier
      reward origin horigin hpoint.1
  have hpointSemantic : point.1 ∈ quittingTerminalSemanticCarrier reward :=
    terminalSemanticLawCarrier_fst_mem_carrier point hpointJoint
  have hpointLeOrigin :
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum origin.1 := by
    rw [hpoint.2]
    exact hminimum.debt_le origin
      (quittingLawTightCapNashSaturationHull_origin_mem reward origin)
  have horiginLePoint :
      quittingTerminalSemanticDebtSum origin.1 ≤
        quittingTerminalSemanticDebtSum point.1 :=
    horiginMinimum point.1 hpointSemantic
  have heq : quittingTerminalSemanticDebtSum origin.1 =
      quittingTerminalSemanticDebtSum point.1 :=
    le_antisymm horiginLePoint hpointLeOrigin
  have hpointMinimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate := by
    intro candidate hcandidate
    rw [← heq]
    exact horiginMinimum candidate hcandidate
  have hpointPositive : 0 < quittingTerminalSemanticDebtSum point.1 := by
    rw [hpoint.2]
    exact hminimumPositive
  refine ⟨hpointSemantic, heq, hpointMinimum, fun who ↦ ?_⟩
  rw [heq]
  exact minimumTerminalSemantic_singletonMargin point.1 hpointSemantic
    hpointMinimum hpointPositive who

/-- The hull minimum itself inherits global debt minimality and the singleton
moat measured by the origin debt. -/
theorem lawTightCapNashMinimum_globalMinimumOriginDebtMoat
    {origin minimum : QuittingTerminalSemanticLawPoint ι}
    (horigin : origin ∈ quittingTerminalSemanticLawCarrier reward)
    (horiginMinimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum origin.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimum : IsQuittingLawTightCapNashSaturationMinimum
      reward origin minimum)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum.1) :
    minimum.1 ∈ quittingTerminalSemanticCarrier reward ∧
      quittingTerminalSemanticDebtSum origin.1 =
        quittingTerminalSemanticDebtSum minimum.1 ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum minimum.1 ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      ∀ who, quittingTerminalSemanticDebtSum origin.1 ≤
        minimum.1.2 who - reward (quittingSingletonTerminal who) who :=
  lawTightCapNashMinimumFace_globalMinimumOriginDebtMoat
    horigin horiginMinimum hminimum hminimumPositive hminimum.minimum_mem_face

end GameTheory
