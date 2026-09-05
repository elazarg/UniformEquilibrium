/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.TerminalSemanticPair
import UniformEquilibrium.Quitting.Classification.Existence.UniformPayoffTerminalSemanticCarrier

/-!
# Exact product-root closure of uniform quitting payoffs

An exact Nash product root may be prefixed to any uniform-payoff tail.  The
resulting Bellman successor is again a uniform payoff.  The root may have zero
or positive survival probability, including the all-Continue and sure-
absorption endpoints.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Prefixing a uniform-payoff tail by an exact Nash product root preserves
uniform-payoff implementability against unrestricted behavioral deviations. -/
theorem isUniformEquilibriumPayoff_rootSuccessor_of_isZeroRootNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (htail : (quittingGame reward).IsUniformEquilibriumPayoff none tail)
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingRootSuccessorPayoff reward tail root) := by
  apply isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier
  rw [← quittingTerminalSemanticPrefix_diagonal_eq_of_isZeroNash
    reward tail root hnash]
  exact quittingTerminalSemanticPrefix_mem_carrier reward root (tail, tail)
    (diagonal_mem_terminalSemanticCarrier_of_isUniformEquilibriumPayoff
      reward tail htail)

end GameTheory
