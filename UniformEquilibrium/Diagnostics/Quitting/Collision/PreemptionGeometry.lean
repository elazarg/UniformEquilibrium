/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.FiniteSerialRelation
import UniformEquilibrium.Diagnostics.Quitting.Collision.PreemptionCycle
import UniformEquilibrium.Quitting.Classification.PreemptionGeometry

/-!
# Collision-anchored preemption geometry

The immediate singleton collision and the strict preemption cycle forced by a
four-player counterexample can be synchronized.  Start the preemption walk at
the collision owner, use the full-gap propagation theorem after every reached
edge, and retain the collider as a distinguished marker.

On at most four players the result is one of seventeen marked
geometries.  Forgetting the collider position leaves six rooted lasso shapes,
with `(tail length, cycle length)` equal to

`(0,2), (0,3), (0,4), (1,2), (1,3), or (2,2)`.

This is a necessary localization of a terminal exploitability witness.  It does not say
that any of the seventeen table-level geometries is itself contradictory.
-/

noncomputable section

namespace GameTheory

variable {player : Type} [Fintype player] [DecidableEq player]
variable {reward : {S : Finset player // S.Nonempty} → Payoff player}

namespace QuittingTerminalExploitabilityWitness

/-- **Four-player marked-geometry classification.**  On at most four players,
one collision certificate can be chosen whose owner roots a simple strict
preemption lasso and whose collider occupies one of the seventeen canonical
positions relative to that lasso. -/
theorem exists_collisionAnchoredPreemptionGeometry_of_card_le_four
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hcard : Fintype.card player ≤ 4) :
    ∃ certificate : QuittingImmediateSingletonCollision reward witness.terminalGap,
      Nonempty (Math.FiniteSerialRelation.MarkedRootedLasso
        (QuittingSoloPreempts reward witness.terminalGap)
        certificate.owner certificate.collider) := by
  obtain ⟨certificate⟩ := witness.exists_immediateSingletonCollision
  have hviable : -witness.terminalGap <
      quittingSoloReward reward certificate.owner certificate.owner := by
    linarith [witness.terminalGap_pos, certificate.owner_solo_floor]
  have hroot : ∃ next, QuittingSoloPreempts reward witness.terminalGap
      certificate.owner next := witness.exists_soloPreemptor hviable
  refine ⟨certificate,
    Math.FiniteSerialRelation.markedRootedLasso_of_card_le_four
      (QuittingSoloPreempts reward witness.terminalGap) certificate.owner
      hcard ?_ hroot ?_ certificate.collider_ne_owner⟩
  · intro owner hedge
    exact hedge.1 rfl
  · intro predecessor current hedge
    exact witness.exists_soloPreemptor_of_soloPreempts hedge

/-- The exact four-player specialization of the marked classification. -/
theorem exists_collisionAnchoredPreemptionGeometry_of_card_eq_four
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hcard : Fintype.card player = 4) :
    ∃ certificate : QuittingImmediateSingletonCollision reward witness.terminalGap,
      Nonempty (Math.FiniteSerialRelation.MarkedRootedLasso
        (QuittingSoloPreempts reward witness.terminalGap)
        certificate.owner certificate.collider) :=
  witness.exists_collisionAnchoredPreemptionGeometry_of_card_le_four hcard.le

end QuittingTerminalExploitabilityWitness

end GameTheory
