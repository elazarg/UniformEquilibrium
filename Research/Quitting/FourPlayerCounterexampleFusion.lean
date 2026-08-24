/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Chronology.StrictCovectorDynamicTail
import UniformEquilibrium.Diagnostics.Quitting.Collision.PreemptionGeometry
import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.Preemption
import UniformEquilibrium.Diagnostics.Quitting.FourPlayerReturnedBlockGap
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget
import UniformEquilibrium.Quitting.AbsorptionPath.PunishmentNormalPathStrategicSnell
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.AmbientCarrierElimination

/-!
# Four-player counterexample fusion

This module intersects the independently proved packet, terminal-semantic,
preemption, LCP, returned-block, and strict-covector restrictions on a
hypothetical four-player quitting counterexample.

There are two substantive connectors.  First, every positive packet atom is
punishment-normal, and the packet energy theorem selects two such atoms whose
reciprocal normalized-matrix entries have positive sum.  They therefore cannot
preempt one another in both directions at the positive counterexample margin.
Second, the four-player full-core theorem makes the normal-core support clause
in the ambient returned-block gap vacuous.  Thus the relative-error gap applies
to every bounded ambient returned block, not merely to core-supported blocks.

The final theorem selects all current necessary conditions from one
hypothetical counterexample.  It neither proves that such a counterexample is
consistent nor constructs an equilibrium.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification
open ThreeCoreAmbientCarrierElimination

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Joint four-player necessary-residual theorem.  Besides the named independent
restrictions, the packet pair is forced to lie in the punishment-normal set
and cannot itself be a margin-`gamma` preemption two-cycle, while the
returned-block gap is genuinely ambient because the normal core is full. -/
theorem exists_fourPlayerCounterexample_fusedResidual
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hplayers : Fintype.card ι = 4)
    (hnot : ¬∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ witness : QuittingTerminalExploitabilityWitness reward,
      HasPositiveMinimumTerminalSemanticPlateau reward ∧
      (∃ packet : QuittingNormalizedSingletonSourcePacket reward,
        ∃ first second,
          0 < packet.mass first ∧
          0 < packet.mass second ∧
          first ≠ second ∧
          IsQuittingNormalPlayer reward first ∧
          IsQuittingNormalPlayer reward second ∧
          0 < normalizedSoloMatrix reward first second +
            normalizedSoloMatrix reward second first ∧
          ¬(QuittingSoloPreempts reward witness.terminalGap first second ∧
            QuittingSoloPreempts reward witness.terminalGap second first)) ∧
      Nonempty
        (QuittingImmediateSingletonCollision reward witness.terminalGap) ∧
      Nonempty (QuittingSoloPreemptionCycle reward witness.terminalGap) ∧
      (∃ certificate :
          QuittingImmediateSingletonCollision reward witness.terminalGap,
        Nonempty (Math.FiniteSerialRelation.MarkedRootedLasso
          (QuittingSoloPreempts reward witness.terminalGap)
          certificate.owner certificate.collider)) ∧
      normalCore (normalizedSoloMatrix reward) = Finset.univ ∧
      PunishmentNormalResidualHardClass reward ∧
      (∀ K : ℝ, HasAmbientReturnedBlockRelativeErrorGap reward K) ∧
      ∃ seam : QuittingPositiveDebtDynamicTailWitness witness,
        HasStrictCovectorPositiveSurvival seam := by
  obtain ⟨witness⟩ :=
    nonempty_terminalExploitabilityWitness_of_not_exists_uniformEquilibriumPayoff
      reward hnot
  obtain ⟨packet⟩ := witness.nonempty_normalizedSingletonSourcePacket
  obtain ⟨first, second, hfirst, hsecond, hne, hnormalFirst,
      hnormalSecond, hmatrix, hnotMutual⟩ :=
    witness.exists_normal_packetPair_not_mutuallyPreempting packet
  have hplateau :=
    noUniformPayoff_implies_positiveMinimumSemanticPlateau witness
  have hcollision := witness.exists_immediateSingletonCollision
  have hcycle := witness.nonempty_soloPreemptionCycle
  have hgeometry :=
    witness.exists_collisionAnchoredPreemptionGeometry_of_card_eq_four hplayers
  have hcore :=
    normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff
      reward hplayers hnot
  have hard :=
    punishmentNormalResidualHardClass_of_strategicFork_of_not_exists_uniformEquilibriumPayoff
      reward (quittingPunishmentNormalPathStrategicFork reward) hnot
  have hreturned : ∀ K : ℝ,
      HasAmbientReturnedBlockRelativeErrorGap reward K :=
    hasAmbientReturnedBlockRelativeErrorGap_of_fourPlayer_counterexample
      reward hplayers hnot
  obtain ⟨seam, hcovector⟩ :=
    witness.exists_strictCovectorPositiveSurvivalTail
  exact ⟨witness, hplateau,
    ⟨packet, first, second, hfirst, hsecond, hne, hnormalFirst,
      hnormalSecond, hmatrix, hnotMutual⟩,
    hcollision, hcycle, hgeometry, hcore, hard, hreturned,
    seam, hcovector⟩

end GameTheory
