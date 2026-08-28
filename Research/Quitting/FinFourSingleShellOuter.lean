/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import MathUE.Topology.SingleOuterApproximation
import Research.Quitting.EscapeAwareQuantileClockHierarchy

/-!
# The normalized Fin4 single-shell outer bound

This is the analytic target of the exact rational interval-tree checker.  It
uses only the final shell at the requested positive level, not the cumulative
intersection through that level.  No certificate generator or decision
procedure is asserted here.
-/

noncomputable section

namespace GameTheory

open Math.Topology

/-- Minimum terminal semantic exploitability on the single normalized Fin4
quantile-clock shell. -/
def finFourSingleShellLower
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    (level : ℕ) : ℝ :=
  NestedOuterApproximation.shellLowerValue
    (escapeAwareQuantileClockSystem reward
      (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward))
    quittingTerminalSemanticExploitability level

/-- The final-shell value has the exact `24 / level` bracket against the
unrestricted behavioral exploitability infimum. -/
theorem finFourSingleShell_quantitative_bracket
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    {level : ℕ} (hlevel : 0 < level) :
    finFourSingleShellLower reward hreward level ≤
        quittingTerminalExploitabilityInf reward ∧
      quittingTerminalExploitabilityInf reward ≤
        escapeAwareQuantileClockUpper reward
          (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
          level ∧
      escapeAwareQuantileClockUpper reward
            (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
            level - finFourSingleShellLower reward hreward level ≤
        24 / (level : ℝ) := by
  let compression :=
    hasEscapeAwareQuantileClockCompression_of_normalized reward hreward
  have hbracket :=
    (escapeAwareQuantileClockSystem reward compression).shell_quantitative_bracket
      quittingTerminalSemanticExploitability 0 2
      quittingTerminalSemanticExploitability_nonneg
      continuous_quittingTerminalSemanticExploitability (by norm_num)
      abs_quittingTerminalSemanticExploitability_sub_le hlevel
  rw [escapeAwareQuantileClock_attainableInf_eq reward compression] at hbracket
  change
    (escapeAwareQuantileClockSystem reward compression).shellLowerValue
          quittingTerminalSemanticExploitability level ≤
        quittingTerminalExploitabilityInf reward ∧
      quittingTerminalExploitabilityInf reward ≤
        (escapeAwareQuantileClockSystem reward compression).upperValue
          quittingTerminalSemanticExploitability level ∧
      (escapeAwareQuantileClockSystem reward compression).upperValue
            quittingTerminalSemanticExploitability level -
          (escapeAwareQuantileClockSystem reward compression).shellLowerValue
            quittingTerminalSemanticExploitability level ≤
        24 / (level : ℝ)
  refine ⟨hbracket.1, hbracket.2.1, hbracket.2.2.trans_eq ?_⟩
  change 2 * quantileClockRadius (Fin 4) level = 24 / (level : ℝ)
  rw [quantileClockRadius_fin4]
  ring

/-- A checked lower bound on the single shell is a checked lower bound on the
actual unrestricted terminal exploitability infimum. -/
theorem finFourSingleShellLower_le_exploitabilityInf
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    {level : ℕ} (hlevel : 0 < level) {gamma : ℝ}
    (hlower : gamma ≤ finFourSingleShellLower reward hreward level) :
    gamma ≤ quittingTerminalExploitabilityInf reward :=
  hlower.trans (finFourSingleShell_quantitative_bracket
    reward hreward hlevel).1

end GameTheory
