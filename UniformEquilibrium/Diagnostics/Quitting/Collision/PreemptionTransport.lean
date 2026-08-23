/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.PreemptionCycle
import UniformEquilibrium.Quitting.Classification.PreemptionTransport

/-!
# Static preemption-transport no-go in a terminal exploitability witness

A table-justified charging pays at least the solo table's observer-switch cost.
The payoff cells are therefore a potential for the augmented graph, so weak
duality makes every such charged cycle nonpositive.  This closes the static
transport route without asserting anything about profile-derived phase values,
observer-indexed continuations, or debt coordinates.
-/

noncomputable section

open Math Math.MaxAffineTransport

namespace GameTheory

variable {player : Type} [Fintype player] [DecidableEq player]
variable {reward : {S : Finset player // S.Nonempty} → Payoff player}

/-- A charging of the observer-switch edges that the witness's solo table
justifies. -/
structure QuittingStaticObserverSwitchData
    (witness : QuittingTerminalExploitabilityWitness reward)
    (cycle : QuittingSoloPreemptionCycle reward witness.terminalGap) where
  /-- The weight charged to the observer switch out of each phase's head. -/
  cost : ℕ → ℝ
  /-- The witness's solo table pays the charge at every switch. -/
  observerSwitchCost_le : ∀ time : ℕ, cycle.observerSwitchCost time ≤ cost time

namespace QuittingSoloPreemptionCycle

variable {witness : QuittingTerminalExploitabilityWitness reward}

/-- Charging each observer switch by the exact loss in the solo table gives
the least table-justified charging. -/
def tightStaticObserverSwitchData (witness : QuittingTerminalExploitabilityWitness reward)
    (cycle : QuittingSoloPreemptionCycle reward witness.terminalGap) :
    QuittingStaticObserverSwitchData witness cycle where
  cost := cycle.observerSwitchCost
  observerSwitchCost_le _ := le_rfl

instance nonempty_quittingStaticObserverSwitchData
    (witness : QuittingTerminalExploitabilityWitness reward)
    (cycle : QuittingSoloPreemptionCycle reward witness.terminalGap) :
    Nonempty (QuittingStaticObserverSwitchData witness cycle) :=
  ⟨tightStaticObserverSwitchData witness cycle⟩

end QuittingSoloPreemptionCycle

namespace QuittingStaticObserverSwitchData

variable {witness : QuittingTerminalExploitabilityWitness reward}
variable {cycle : QuittingSoloPreemptionCycle reward witness.terminalGap}

/-- The charged data closes the joined system on the payoff cells. -/
theorem isLaxSection (data : QuittingStaticObserverSwitchData witness cycle) :
    IsLaxSection cycle.augmentedCellGraph (cycle.augmentedCellLabel data.cost)
      (quittingPayoffCellValue reward) :=
  cycle.isLaxSection_augmentedCellLabel data.observerSwitchCost_le

/-- One gap per forced edge, minus the charge of each observer switch. -/
def augmentedCycleWeight (data : QuittingStaticObserverSwitchData witness cycle) : ℝ :=
  (cycle.period : ℝ) * witness.terminalGap -
    ∑ time ∈ Finset.range cycle.period, data.cost time

/-- The augmented cycle weight is the weight of the corresponding closed
walk. -/
theorem augmentedCycleWeight_eq_walkWeight
    (data : QuittingStaticObserverSwitchData witness cycle) :
    data.augmentedCycleWeight =
      Math.MaxPlusPotential.walkWeight (cycle.augmentedCellWeight data.cost)
        cycle.augmentedCellWalk :=
  (cycle.walkWeight_augmentedCellWalk data.cost).symm

/-- The payoff-cell potential makes every table-justified augmented cycle
nonpositive. -/
theorem augmentedCycleWeight_nonpos
    (data : QuittingStaticObserverSwitchData witness cycle) :
    data.augmentedCycleWeight ≤ 0 := by
  rw [data.augmentedCycleWeight_eq_walkWeight]
  exact (cycle.isPotential_augmentedCellWeight data.observerSwitchCost_le).closedWalk_nonpos
    cycle.augmentedCellWalk

/-- A positive table-justified augmented cycle is impossible. -/
theorem elim (data : QuittingStaticObserverSwitchData witness cycle)
    (hweight : 0 < data.augmentedCycleWeight) : False :=
  absurd data.augmentedCycleWeight_nonpos (not_le.2 hweight)

end QuittingStaticObserverSwitchData

namespace QuittingSoloPreemptionCycle

/-- No table-justified charging carries a positive augmented cycle. -/
theorem isEmpty_positiveObserverSwitchData
    (witness : QuittingTerminalExploitabilityWitness reward)
    (cycle : QuittingSoloPreemptionCycle reward witness.terminalGap) :
    ¬∃ data : QuittingStaticObserverSwitchData witness cycle,
      0 < data.augmentedCycleWeight :=
  fun ⟨data, hweight⟩ ↦ data.elim hweight

end QuittingSoloPreemptionCycle

end GameTheory

end
