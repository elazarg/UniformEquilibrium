/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.PeriodOne.TangentReadout
import UniformEquilibrium.Quitting.Boundary.Holonomy.TerminalExploitabilityRepair

/-!
# Terminal repair restriction for a period-one counterexample readout

The generic terminal-gap repair and elementary-cap results live in the
boundary-holonomy production lane. This adapter specializes them to the
selected one-root prefixes and actual suffixes of a counterexample seam. The
conclusion is a co-realized terminal obstruction, not an attachment theorem
for the active tangent owner.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {witness : QuittingTerminalExploitabilityWitness reward}

namespace QuittingPositiveDebtDynamicTailWitness
namespace TerminalExploitabilityWitnessPeriodOneTangentReadout

variable (seam : QuittingPositiveDebtDynamicTailWitness witness)
variable (readout : TerminalExploitabilityWitnessPeriodOneTangentReadout seam)

/-- Every selected one-root prefix inherits the regime's terminal-gap floor
for the infimum over all co-realized behavioral tails.  This conclusion is
independent of tangent sign; it is the existing terminal obstruction, not an
attachment theorem for the active owner. -/
theorem terminalGap_le_periodOne_behavioralTailRepairValue (index : ℕ) :
    witness.terminalGap ≤
      @QuittingBoundaryHolonomy.behavioralTailRepairValue ι _ _
        witness.nonempty_players reward
        (quittingFiniteBoundaryHolonomy reward
          (quittingPeriodOneRootSequence
            (seam.periodOneReadoutRoot readout.start index)) 0 0) := by
  letI : Nonempty ι := witness.nonempty_players
  exact terminalExploitabilityGap_le_behavioralTailRepairValue reward
    (quittingPeriodOneRootSequence
      (seam.periodOneReadoutRoot readout.start index)) 1 (by omega)
    witness.terminalExploitability

/-- For every selected root, elementary compression of its actual suffix
returns a co-realized terminal obstruction larger than half the regime gap.
This is likewise independent of the active-positive packet branch. -/
theorem exists_elementaryTailCap_periodOne_terminalObstruction (index : ℕ) :
    ∃ cap : QuittingElementaryTailCap ι, ∃ cutoff,
      witness.terminalGap / 2 < @quittingTerminalExploitability ι _ _
        witness.nonempty_players reward
        (quittingPhaseSwitchProfile reward
          (quittingPeriodOneRootSequence
            (seam.periodOneReadoutRoot readout.start index))
          (quittingElementaryTailRoots
            (seam.periodOneReadoutActualSuffix readout.start index)
            cutoff cap) 1) := by
  letI : Nonempty ι := witness.nonempty_players
  have hhalf : 0 < witness.terminalGap / 2 := by
    linarith [witness.terminalGap_pos]
  obtain ⟨cap, cutoff, hcap⟩ :=
    exists_elementaryTailCap_terminalExploitability_gt_sub reward
      (quittingPeriodOneRootSequence
        (seam.periodOneReadoutRoot readout.start index))
      (seam.periodOneReadoutActualSuffix readout.start index) 1
      (by omega) hhalf
      witness.terminalExploitability
  refine ⟨cap, cutoff, ?_⟩
  have hhalfEq : witness.terminalGap - witness.terminalGap / 2 =
      witness.terminalGap / 2 := by ring
  rw [← hhalfEq]
  exact hcap

end TerminalExploitabilityWitnessPeriodOneTangentReadout
end QuittingPositiveDebtDynamicTailWitness

end GameTheory
