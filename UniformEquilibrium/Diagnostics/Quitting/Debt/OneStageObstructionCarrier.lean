/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Chronology.AbsorptionClockBallisticity
import UniformEquilibrium.Quitting.Debt.Dynamic.OneStageObstructionCarrier

/-!
# Counterexample-seam membership in the one-stage obstruction carrier

The production carrier packages boxed floor-admissible exact dynamic-debt
edges and their raw one-stage obstruction flows. This adapter proves that the
canonical counterexample seam supplies carrier members, nonemptiness, and
attained co-state support values.
-/

noncomputable section

namespace GameTheory

open Math.LinearProgramming.FlowCostateDuality
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {witness : QuittingTerminalExploitabilityWitness reward}

namespace QuittingPositiveDebtDynamicTailWitness

variable (seam : QuittingPositiveDebtDynamicTailWitness witness)

/-- Every adjacent pair of canonical tail states is an exact boxed
floor-admissible source edge. -/
theorem tailEdge_mem_quittingFloorDynamicDebtEdgeGraph (time : ℕ) :
    (seam.tail time, seam.tail (time + 1)) ∈
      quittingFloorDynamicDebtEdgeGraph reward := by
  refine ⟨⟨seam.tail_mem time, seam.tail_mem (time + 1),
    seam.tail_edge time⟩, ?_⟩
  intro who
  exact ⟨seam.punishmentValue_le_tailValue time who,
    seam.punishmentValue_le_tailValue (time + 1) who⟩

/-- The edge presentation and the literal canonical one-stage tail window
produce the same unnormalized two-grade flow. -/
theorem quittingDebtEdgeObstructionFlow_tailEdge_eq (time : ℕ) :
    quittingDebtEdgeObstructionFlow
        (seam.tail time, seam.tail (time + 1)) =
      (seam.finiteRootWindow time 1).toObstructionRawGradedFlow
        (fun date ↦ (seam.tail date).1.1) := by
  funext grade coordinate
  cases grade with
  | charge =>
      cases coordinate with
      | inl channel =>
          cases channel with
          | singleton owner =>
              simp [QuittingFiniteRootWindow.toObstructionRawGradedFlow_charge,
                QuittingPositiveDebtDynamicTailWitness.finiteRootWindow,
                QuittingFiniteRootWindow.rawCharge_singleton_value,
                QuittingFiniteRootWindow.singletonMass,
                QuittingFiniteRootWindow.survivalWeight,
                QuittingFiniteRootWindow.rootAt,
                quittingDynamicDebtTailRoots]
          | collision =>
              simp [QuittingFiniteRootWindow.toObstructionRawGradedFlow_charge,
                QuittingPositiveDebtDynamicTailWitness.finiteRootWindow,
                QuittingFiniteRootWindow.rawCharge_collision_value,
                QuittingFiniteRootWindow.collisionMass,
                QuittingFiniteRootWindow.survivalWeight,
                QuittingFiniteRootWindow.rootAt,
                quittingDynamicDebtTailRoots]
      | inr who => simp
  | coboundary =>
      cases coordinate with
      | inl channel => simp
      | inr who => rfl

/-- Every literal one-stage window of the canonical non-plateau extraction
belongs to the exact compact raw-obstruction carrier. -/
theorem oneStageTailFlow_mem_quittingOneStageObstructionCarrier (time : ℕ) :
    (seam.finiteRootWindow time 1).toObstructionRawGradedFlow
        (fun date ↦ (seam.tail date).1.1) ∈
      quittingOneStageObstructionCarrier reward := by
  refine ⟨(seam.tail time, seam.tail (time + 1)),
    seam.tailEdge_mem_quittingFloorDynamicDebtEdgeGraph time, ?_⟩
  exact (seam.quittingDebtEdgeObstructionFlow_tailEdge_eq time).symm

/-- The canonical tail makes the exact one-stage carrier nonempty. -/
theorem quittingOneStageObstructionCarrier_nonempty
    (seam : QuittingPositiveDebtDynamicTailWitness witness) :
    (quittingOneStageObstructionCarrier reward).Nonempty :=
  ⟨(seam.finiteRootWindow 0 1).toObstructionRawGradedFlow
      (fun date ↦ (seam.tail date).1.1),
    seam.oneStageTailFlow_mem_quittingOneStageObstructionCarrier 0⟩

end QuittingPositiveDebtDynamicTailWitness

namespace QuittingPositiveDebtDynamicTailWitness

/-- In a terminal exploitability witness, the canonical tail supplies nonemptiness, so
every finite co-state has an attained support value on the exact carrier. -/
theorem exists_hasSupportValue_oneStageObstructionCarrier
    (seam : QuittingPositiveDebtDynamicTailWitness witness)
    (costate : Costate QuittingObstructionGrade
      (QuittingObstructionCoordinate ι)) :
    ∃ value,
      HasSupportValue costate
        (quittingOneStageObstructionCarrier reward) value :=
  exists_hasSupportValue_quittingOneStageObstructionCarrier reward
    (quittingOneStageObstructionCarrier_nonempty seam) costate

end QuittingPositiveDebtDynamicTailWitness

end GameTheory
