/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.ActiveSetSupport

/-!
# Exact opponent-coalition mass

The opponent-coalition mass is the probability that every member of a selected
coalition Quits and every other opponent Continues. The distinguished player's own
action is deliberately omitted. This coordinate is reusable independently of any Nash
defect or diagnostic interpretation.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Probability that the opponents' exact Quit coalition is `coalition`.
The intended coalitions are contained in `univ.erase who`. -/
def quittingOpponentCoalitionMass
    (root : ι → PMF Bool) (who : ι) (coalition : Finset ι) : ℝ :=
  (∏ player ∈ coalition, (root player true).toReal) *
    ∏ player ∈ Finset.univ.erase who \ coalition,
      (root player false).toReal

theorem quittingOpponentCoalitionMass_nonneg
    (root : ι → PMF Bool) (who : ι) (coalition : Finset ι) :
    0 ≤ quittingOpponentCoalitionMass root who coalition := by
  exact mul_nonneg
    (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg)
    (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg)

end GameTheory
