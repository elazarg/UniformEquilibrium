/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Debt.OneStageObstructionCarrier
import UniformEquilibrium.Quitting.Debt.Dynamic.DebtSourceObstructionCarrier

/-!
# Counterexample-seam debt-source obstruction adapters

The production owner defines the enriched carrier, chronological fold, and
debt-source co-states. This adapter supplies the counterexample seam's
all-Continue zero source and identifies its exposed faces with augmented-cap
transport.
-/

noncomputable section

namespace GameTheory

open Math.LinearProgramming.FlowCostateDuality
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

namespace QuittingCounterexampleSeamWitness

variable (seam : QuittingCounterexampleSeamWitness regime)

/-- Every canonical one-stage tail edge belongs to the exact enriched carrier
and retains its actual diagonal dynamic-debt source. -/
theorem debtSourceTailEdgeFlow_mem (time : ℕ) :
    quittingDebtSourceObstructionFlow
        (seam.tail time, seam.tail (time + 1)) ∈
      quittingDebtSourceOneStageObstructionCarrier reward := by
  exact ⟨(seam.tail time, seam.tail (time + 1)),
    seam.tailEdge_mem_quittingFloorDynamicDebtEdgeGraph time, rfl⟩

/-- The limiting all-Continue dynamic-debt point, written in the ambient
source type of the enriched carrier. -/
def limitDebtPoint : QuittingDebtPoint ι :=
  ((seam.limit.value, quittingAllContinueSimplexRoot), seam.limit.debt)

/-- The limiting all-Continue self-loop is an exact floor-admissible source
edge. -/
theorem limitDebtPoint_selfLoop_mem :
    (seam.limitDebtPoint, seam.limitDebtPoint) ∈
      quittingFloorDynamicDebtEdgeGraph reward := by
  refine ⟨⟨seam.limit.state_mem, seam.limit.state_mem,
    seam.limit.exactSelfLoop⟩, ?_⟩
  intro who
  exact ⟨seam.punishmentValue_le_limitValue who,
    seam.punishmentValue_le_limitValue who⟩

/-- The limiting all-Continue self-loop supplies an attained point of the
enriched carrier. -/
theorem limitDebtSourceObstructionFlow_mem :
    quittingDebtSourceObstructionFlow
        (seam.limitDebtPoint, seam.limitDebtPoint) ∈
      quittingDebtSourceOneStageObstructionCarrier reward :=
  ⟨(seam.limitDebtPoint, seam.limitDebtPoint),
    seam.limitDebtPoint_selfLoop_mem, rfl⟩

@[simp]
theorem limitDebtPoint_source_eq_zero (who : ι) :
    quittingDebtSourceObstructionFlow
        (seam.limitDebtPoint, seam.limitDebtPoint)
        .charge (Sum.inr who) = 0 := by
  simp [limitDebtPoint, quittingDynamicDebtSeam,
    quittingRootOfSimplex_allContinueSimplexRoot,
    quittingAllContinueRoot, PMF.pure_apply]

end QuittingCounterexampleSeamWitness

namespace QuittingCounterexampleSeamWitness

variable (seam : QuittingCounterexampleSeamWitness regime)

include seam in
/-- The negative selected-source co-state exposes exactly the flows whose
selected dynamic-debt source vanishes.  Nonnegativity comes from the exact
boxed source; attainment of zero comes from the all-Continue limit
self-loop. -/
theorem mem_exposedFace_quittingDebtSourceZeroFaceCostate_iff
    (selected : ι)
    (flow : RawGradedFlow QuittingObstructionGrade
      (QuittingDebtSourceObstructionCoordinate ι)) :
    flow ∈ exposedFace (quittingDebtSourceZeroFaceCostate selected)
        (quittingDebtSourceOneStageObstructionCarrier reward) ↔
      flow ∈ quittingDebtSourceOneStageObstructionCarrier reward ∧
        flow .charge (Sum.inr selected) = 0 := by
  exact mem_exposedFace_quittingDebtSourceZeroFaceCostate_iff_of_zero_mem
    selected seam.limitDebtSourceObstructionFlow_mem
      (seam.limitDebtPoint_source_eq_zero selected) flow

include seam in
/-- For an exact source edge, selected zero-face membership is precisely the
playerwise augmented-cap transport equation at that edge. -/
theorem debtSourceFlow_mem_zeroFace_iff_cap_transport_apply
    (edge : QuittingDebtPoint ι × QuittingDebtPoint ι)
    (hedge : edge ∈ quittingFloorDynamicDebtEdgeGraph reward)
    (selected : ι) :
    quittingDebtSourceObstructionFlow edge ∈
        exposedFace (quittingDebtSourceZeroFaceCostate selected)
          (quittingDebtSourceOneStageObstructionCarrier reward) ↔
      quittingDynamicDebtCap edge.1 selected =
        quittingRootSuccessorPayoff reward
          (quittingDynamicDebtCap edge.2)
          (quittingRootOfSimplex edge.1.1.2) selected := by
  exact
    quittingDebtSourceObstructionFlow_mem_zeroFace_iff_cap_transport_apply_of_zero_mem
      selected seam.limitDebtSourceObstructionFlow_mem
        (seam.limitDebtPoint_source_eq_zero selected) edge hedge

include seam in
/-- Membership in every playerwise zero-source face is exactly the vector
augmented-cap transport condition of `DynamicDebtCapBridge`. -/
theorem debtSourceFlow_mem_all_zeroFaces_iff_cap_transport
    (edge : QuittingDebtPoint ι × QuittingDebtPoint ι)
    (hedge : edge ∈ quittingFloorDynamicDebtEdgeGraph reward) :
    (∀ selected,
      quittingDebtSourceObstructionFlow edge ∈
        exposedFace (quittingDebtSourceZeroFaceCostate selected)
          (quittingDebtSourceOneStageObstructionCarrier reward)) ↔
      quittingDynamicDebtCap edge.1 =
        quittingRootSuccessorPayoff reward
          (quittingDynamicDebtCap edge.2)
          (quittingRootOfSimplex edge.1.1.2) := by
  exact
    quittingDebtSourceObstructionFlow_mem_all_zeroFaces_iff_cap_transport_of_zero_mem
      seam.limitDebtSourceObstructionFlow_mem
        seam.limitDebtPoint_source_eq_zero edge hedge

end QuittingCounterexampleSeamWitness

end GameTheory
