/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.PairBasePaidResetEndpointEdge

/-!
# Payoff escape after a positive pair-base endpoint edge

An exact positive punishment-floor edge can always be extended to an infinite
exact floor orbit by the generic anchored-orbit selector.  Under a terminal
exploitability witness, however, that continuation cannot return even
approximately to the payoff at the edge's tail: the fixed-edge payoff-closure
consumer would otherwise produce a uniform-equilibrium payoff.

The result below records the sharp obstruction.  It does not claim that the
selected orbit is recurrent, nor that its Bellman annotations are realized
payoffs of one behavioral profile.
-/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

namespace QuittingTerminalExploitabilityWitness

/-- A positive exact floor-admissible edge in a counterexample leaves a
uniform payoff neighborhood of its tail permanently: every state reachable
from its current endpoint differs from the tail payoff by a fixed positive
amount in at least one coordinate.

This is stronger than excluding an exact return.  It rules out feeding the
edge to the checked fixed-edge payoff-closure consumer, including through an
infinite exact orbit selected after the edge. -/
theorem exists_payoffEscapeRadius_of_positiveAdmissibleEdge
    (witness : QuittingTerminalExploitabilityWitness reward)
    (edge : QuittingPunishmentFloorAdmissibleEdge reward)
    (hpositive : 0 < edge.toBoxEdge.absorptionCharge) :
    ∃ endpointError : ℝ, 0 < endpointError ∧
      ∀ (target : QuittingPunishmentFloorAdmissibleState reward)
        (_path :
          (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
            edge.current target),
        ∃ who, endpointError <
          |edge.tail.1.1.1 who - target.1.1.1 who| := by
  by_contra hescape
  have hclosure : ∀ endpointError : ℝ, 0 < endpointError →
      ∃ (target : QuittingPunishmentFloorAdmissibleState reward)
        (_path :
          (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
            edge.current target),
        ∀ who,
          |edge.tail.1.1.1 who - target.1.1.1 who| ≤ endpointError := by
    push Not at hescape
    intro endpointError hendpointError
    obtain ⟨target, path, hclose⟩ := hescape endpointError hendpointError
    exact ⟨target, path, hclose⟩
  exact witness.not_exists_uniformEquilibriumPayoff
    (quittingGame_exists_uniformEquilibriumPayoff_of_positiveEdge_payoffClosure
      edge hpositive hclosure)

end QuittingTerminalExploitabilityWitness

end GameTheory
