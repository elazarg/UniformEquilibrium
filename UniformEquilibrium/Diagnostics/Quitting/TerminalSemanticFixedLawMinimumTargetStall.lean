/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceCapReturn
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceRatio

/-!
# A minimum target makes the fixed-law reset dispatch stall

The fixed-law reset dispatch retains a complete terminal law and a positive
incidence coordinate.  Those are tail-law facts.  They do not force fresh
absorption by the exact cap--Nash root selected in the dynamic branch.

This file records the sharp minimum-target boundary.  If the supplied reset
target has no more total debt than the global-minimum source, the returned
reset-face point is itself on the minimum fiber.  The strictly descending
dynamic branch would then prefix to a carrier point below the global minimum,
so it is impossible.  The dispatch must take its all-Continue branch.

Thus source-matched paid rows or unit incidence in such a target do not by
themselves produce a return.  A return consumer still needs a quantitative
fresh-absorption charge large enough to pay the returned point's excess debt.
-/

noncomputable section

namespace GameTheory

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

/-- If a fixed-law reset target lies no higher than the minimum source, the
dynamic dispatch necessarily selects the all-Continue cap face. -/
theorem QuittingFixedLawResetDispatch.allContinue_of_target_debt_le_source
    {source target : QuittingTerminalSemanticPair iota}
    {mass : QuittingTerminalOutcome iota → ℝ}
    {owner other : iota} {returned : QuittingTerminalSemanticPair iota}
    (dispatch : QuittingFixedLawResetDispatch (reward := reward)
      source target mass owner other returned)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (htarget : quittingTerminalSemanticDebtSum target ≤
      quittingTerminalSemanticDebtSum source) :
    IsεQuittingRootNash reward returned.2 0
        (quittingAllContinueRoot : iota → PMF Bool) ∧
      quittingTerminalSemanticPrefix reward quittingAllContinueRoot
        returned = returned := by
  have hreturned : quittingTerminalSemanticDebtSum returned =
      quittingTerminalSemanticDebtSum source := by
    exact le_antisymm (dispatch.target_ge.trans htarget) dispatch.source_le
  rcases dispatch.dynamic_exit with hexit | hstall
  · obtain ⟨root, _hnash, _habsorption, _hcontinue, hstrict,
        hjoint, _hreset, _hincidence⟩ := hexit
    have hprefixCarrier :
        quittingTerminalSemanticPrefix reward root returned ∈
          quittingTerminalSemanticCarrier reward :=
      terminalSemanticLawCarrier_fst_mem_carrier
        (point := (quittingTerminalSemanticPrefix reward root returned,
          quittingTerminalOutcomeLawPrefix root mass)) hjoint
    have hlower := hminimum
      (quittingTerminalSemanticPrefix reward root returned) hprefixCarrier
    rw [hreturned] at hstrict
    exact (not_lt_of_ge hlower hstrict).elim
  · exact hstall

end GameTheory
