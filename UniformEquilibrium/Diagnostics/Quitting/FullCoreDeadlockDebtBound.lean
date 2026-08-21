/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawExploitabilityFloor
import UniformEquilibrium.Quitting.Classification.LCP.FullCore.DeadlockGlobalContraction

/-!
# Exploitability bound for full-core deadlock completions

A full-core deadlock completion has an actual terminal-semantic carrier point
of total debt exactly `1/14`. Every terminal exploitability gap lower-bounds
total debt at every carrier point. Therefore the stored gap of any
counterexample regime on this family is at most `1/14`.

This quantitative restriction does not show that the gap vanishes and does
not produce a terminal approximate equilibrium.
-/

noncomputable section

namespace GameTheory

open FullCoreDeadlock

/-- Every terminal exploitability gap on a full-core deadlock completion is
at most `1/14`. -/
theorem HasTerminalExploitabilityGap.fullCoreDeadlock_le_one_fourteenth
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    {gap : ℝ} (hexploit : HasTerminalExploitabilityGap reward gap)
    (hcompletion : IsFullCoreDeadlockCompletion reward) :
    gap ≤ 1 / 14 := by
  apply hcompletion.globalDebtFloor_le_one_fourteenth
  intro pair hpair
  exact terminalExploitabilityGap_le_terminalSemanticDebtSum_of_mem_carrier
    reward pair hexploit hpair

/-- A counterexample regime on a full-core deadlock completion has terminal
exploitability gap at most `1/14`. -/
theorem QuittingCounterexampleRegime.fullCoreDeadlock_terminalGap_le_one_fourteenth
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (regime : QuittingCounterexampleRegime reward)
    (hcompletion : IsFullCoreDeadlockCompletion reward) :
    regime.terminalGap ≤ 1 / 14 := by
  exact regime.terminalExploitability.fullCoreDeadlock_le_one_fourteenth
    hcompletion

end GameTheory
